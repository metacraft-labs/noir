//! An **AVM public-execution** oracle host, so an Aztec contract's public entrypoints can
//! be stepped in a debugger instead of halting on their first oracle.
//!
//! # Why this exists, and why it is the AVM set specifically
//!
//! `DefaultDebugForeignCallExecutor` handles only the `__debug_*` instrumentation calls and
//! returns [`ForeignCallError::NoHandler`] for everything else. An Aztec contract calls an
//! oracle within a handful of opcodes of entry, so every one of `SimpleToken`'s 27
//! entrypoints stopped after the tracer's own entry step.
//!
//! There is already a working Aztec oracle host in the `aztec-avm-runtime` repository
//! (`browser/src/wallet/private_oracles.ts`), and the obvious question is why a second one
//! is needed. The answer is a measurement, not a preference. That host is built on the
//! vendored PXE registry `ORACLE_REGISTRY`, which has **68 entries: 49 `aztec_utl_*`, 16
//! `aztec_prv_*`, 3 `aztec_misc_*`, and zero `aztec_avm_*`**. The vendored aztec-nr closure
//! declares **133** `#[oracle(..)]` names. The two sets are in an exact subset relation —
//! every registry entry is declared in the tree, and no registry entry is absent from it —
//! so the TS host is a faithful implementation of the *private execution* oracle interface
//! and of nothing else.
//!
//! `SimpleToken`'s public entrypoints do not call those oracles at all. They call the
//! **AVM** interface, of which the registry serves none. The two places are not a
//! duplication that failed to be shared; they serve disjoint halves of Aztec's oracle
//! surface. This module is the AVM half.
//!
//! # Fidelity — read this before trusting a value in the debugger
//!
//! A debugger that invents an oracle's answer teaches its user something false about their
//! program, so every answer here is classified and **counted**, and the classification is
//! part of the API rather than a comment. See [`Fidelity`]:
//!
//! * [`Fidelity::Faithful`] — the answer is what a real host would produce, because it is
//!   fully determined by state this execution itself created (a value written earlier in
//!   the same call, an emitted effect, a version check with no return value).
//! * [`Fidelity::Environment`] — the answer is read from the [`AztecContext`] the caller
//!   supplied. It is a fact about the transaction the caller is asserting, not a value this
//!   module chose. Wrong context in, wrong answer out — but nothing is invented.
//! * [`Fidelity::DebugLocal`] — the answer comes from this module's in-memory world-state
//!   stand-in, which starts empty. **These are plausible, not correct.** Public storage
//!   reads a real node would answer from the public data tree are answered here as zero
//!   until something in the same session writes them.
//!
//! Anything requiring state this process genuinely does not have — note discovery,
//! membership witnesses, cross-contract dispatch — is **refused by name** rather than
//! guessed at, and the refusal reason names what is missing. Refusing is why
//! `unsupported()` returns `NoHandler` instead of an empty result: an empty result is
//! indistinguishable from a real answer of zero.

use std::collections::{BTreeMap, BTreeSet};

use acvm::{
    AcirField, FieldElement,
    acir::brillig::{ForeignCallParam, ForeignCallResult},
    pwg::ForeignCallWaitInfo,
};
use nargo::foreign_calls::{ForeignCallError, ForeignCallExecutor};

/// How much a given answer can be trusted. Recorded per call, never inferred later.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fidelity {
    /// Determined by state this execution created. Identical to a real host's answer.
    Faithful,
    /// Read from the caller-supplied [`AztecContext`].
    Environment,
    /// From the in-memory world-state stand-in. Plausible, NOT correct.
    DebugLocal,
}

/// One oracle answer, kept so a session can report what it was actually told.
#[derive(Debug, Clone)]
pub struct OracleAnswer {
    pub name: String,
    pub fidelity: Fidelity,
}

/// The transaction context a caller asserts. Every [`Fidelity::Environment`] answer is read
/// straight out of this, so a debugger UI can show the user what it is stepping inside of.
#[derive(Debug, Clone)]
pub struct AztecContext {
    pub contract_address: FieldElement,
    pub sender: FieldElement,
    pub chain_id: FieldElement,
    pub version: FieldElement,
    pub block_number: u32,
    pub timestamp: u64,
    pub is_static_call: bool,
    pub transaction_fee: FieldElement,
    pub l2_gas_left: u32,
    pub da_gas_left: u32,
    pub min_fee_per_l2_gas: u128,
    pub min_fee_per_da_gas: u128,
}

impl Default for AztecContext {
    fn default() -> Self {
        Self {
            contract_address: FieldElement::from(1u128),
            sender: FieldElement::from(2u128),
            chain_id: FieldElement::from(31337u128),
            version: FieldElement::from(1u128),
            block_number: 1,
            timestamp: 1,
            is_static_call: false,
            transaction_fee: FieldElement::from(0u128),
            l2_gas_left: 1_000_000_000,
            da_gas_left: 1_000_000_000,
            min_fee_per_l2_gas: 0,
            min_fee_per_da_gas: 0,
        }
    }
}

/// What `aztec_avm_nullifierExists` answers for a nullifier this session never emitted.
///
/// This is a **declared premise**, not a default that quietly picks the convenient answer.
/// aztec-nr's generated initialization check computes a Poseidon digest of the contract
/// address and asserts the resulting nullifier EXISTS; a contract being debugged is
/// normally one that has already been deployed and initialized, so `AlreadyDeployed` is the
/// premise that matches that situation. `EmptyState` models a chain on which nothing has
/// happened, and makes initialized contracts fail their own init check — which is correct
/// behaviour for that premise, not a bug.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NullifierPremise {
    /// Unknown nullifiers do not exist. Models a genuinely empty chain.
    EmptyState,
    /// Unknown nullifiers exist. Models "the contract under debug is already deployed".
    AlreadyDeployed,
}

/// The AVM oracle host. Handles the `aztec_avm_*` interface plus the two `aztec_misc_*`
/// oracles that have no state at all, and returns `NoHandler` for everything else so an
/// unrecognised oracle still stops execution instead of silently receiving zero.
pub struct AztecAvmOracleHost {
    pub context: AztecContext,
    pub nullifier_premise: NullifierPremise,
    /// Public storage, keyed by `(contract_address, slot)`. Starts EMPTY: a read of a slot
    /// nothing wrote in this session answers zero, and is recorded as [`Fidelity::DebugLocal`].
    storage: BTreeMap<(FieldElement, FieldElement), FieldElement>,
    /// Nullifiers emitted during this session. A query for one of these is
    /// [`Fidelity::Faithful`] — this execution created it.
    emitted_nullifiers: BTreeSet<FieldElement>,
    /// Note hashes emitted during this session.
    emitted_note_hashes: Vec<FieldElement>,
    /// Public log messages emitted during this session.
    pub public_logs: Vec<Vec<FieldElement>>,
    /// Returndata from the most recent `aztec_avm_return`.
    returndata: Vec<FieldElement>,
    /// Every answer given, in call order.
    pub answers: Vec<OracleAnswer>,
    /// Every oracle refused, with the reason. Deduplicated by name.
    pub refusals: BTreeMap<String, String>,
}

impl Default for AztecAvmOracleHost {
    fn default() -> Self {
        Self::new(AztecContext::default(), NullifierPremise::AlreadyDeployed)
    }
}

impl AztecAvmOracleHost {
    pub fn new(context: AztecContext, nullifier_premise: NullifierPremise) -> Self {
        Self {
            context,
            nullifier_premise,
            storage: BTreeMap::new(),
            emitted_nullifiers: BTreeSet::new(),
            emitted_note_hashes: Vec::new(),
            public_logs: Vec::new(),
            returndata: Vec::new(),
            answers: Vec::new(),
            refusals: BTreeMap::new(),
        }
    }

    /// How many answers of each fidelity this session gave. The basis for a debugger
    /// telling its user how much of what it showed them was real.
    pub fn fidelity_counts(&self) -> BTreeMap<Fidelity, usize> {
        let mut counts = BTreeMap::new();
        for answer in &self.answers {
            *counts.entry(answer.fidelity).or_default() += 1;
        }
        counts
    }

    /// The distinct oracle names answered, with the fidelity each was answered at.
    pub fn answered_names(&self) -> BTreeMap<String, Fidelity> {
        let mut by_name = BTreeMap::new();
        for answer in &self.answers {
            by_name.entry(answer.name.clone()).or_insert(answer.fidelity);
        }
        by_name
    }

    fn record(&mut self, name: &str, fidelity: Fidelity) {
        self.answers.push(OracleAnswer { name: name.to_string(), fidelity });
    }

    /// An answer with no return value — a sink. Still recorded, because "this effect was
    /// emitted and went nowhere" is something a debugger's user needs to be able to see.
    fn sink(&mut self, name: &str, fidelity: Fidelity) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.record(name, fidelity);
        Ok(ForeignCallResult::default())
    }

    fn single(
        &mut self,
        name: &str,
        fidelity: Fidelity,
        value: FieldElement,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.record(name, fidelity);
        Ok(ForeignCallResult { values: vec![ForeignCallParam::Single(value)] })
    }

    fn array(
        &mut self,
        name: &str,
        fidelity: Fidelity,
        values: Vec<FieldElement>,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.record(name, fidelity);
        Ok(ForeignCallResult { values: vec![ForeignCallParam::Array(values)] })
    }

    /// Refuse by name. `NoHandler` rather than an empty result, deliberately: an empty
    /// result is indistinguishable from a real answer of zero, and would turn a missing
    /// oracle into a wrong value the user has no way to notice.
    fn unsupported(
        &mut self,
        name: &str,
        needs: &str,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.refusals.insert(name.to_string(), needs.to_string());
        Err(ForeignCallError::NoHandler(name.to_string()))
    }

    fn input_field(call: &ForeignCallWaitInfo<FieldElement>, index: usize) -> FieldElement {
        match call.inputs.get(index) {
            Some(ForeignCallParam::Single(v)) => *v,
            Some(ForeignCallParam::Array(values)) => values.first().copied().unwrap_or_default(),
            None => FieldElement::default(),
        }
    }

    fn input_fields(call: &ForeignCallWaitInfo<FieldElement>, index: usize) -> Vec<FieldElement> {
        match call.inputs.get(index) {
            Some(param) => param.fields(),
            None => Vec::new(),
        }
    }
}

impl ForeignCallExecutor<FieldElement> for AztecAvmOracleHost {
    fn execute(
        &mut self,
        call: &ForeignCallWaitInfo<FieldElement>,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        let name = call.function.as_str();
        let bool_field = |b: bool| if b { FieldElement::one() } else { FieldElement::zero() };

        match name {
            // ---------------------------------------------------------------------------
            // Stateless, no return value. Faithful: there is no value to get wrong.
            // ---------------------------------------------------------------------------
            // The version check exists so a PXE can refuse a contract built against an
            // incompatible oracle interface. This host implements the interface the
            // vendored tree declares, so accepting is the correct answer, not a shortcut.
            "aztec_misc_assertCompatibleOracleVersion" => {
                self.sink(name, Fidelity::Faithful)
            }
            // A logging sink. Upstream's own host also only forwards these to a logger.
            "aztec_misc_log" => self.sink(name, Fidelity::Faithful),

            // ---------------------------------------------------------------------------
            // Transaction context. Read from `AztecContext`, never chosen here.
            // ---------------------------------------------------------------------------
            "aztec_avm_address" => {
                let v = self.context.contract_address;
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_sender" => {
                let v = self.context.sender;
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_chainId" => {
                let v = self.context.chain_id;
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_version" => {
                let v = self.context.version;
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_blockNumber" => {
                let v = FieldElement::from(self.context.block_number as u128);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_timestamp" => {
                let v = FieldElement::from(self.context.timestamp as u128);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_isStaticCall" => {
                let v = bool_field(self.context.is_static_call);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_transactionFee" => {
                let v = self.context.transaction_fee;
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_l2GasLeft" => {
                let v = FieldElement::from(self.context.l2_gas_left as u128);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_daGasLeft" => {
                let v = FieldElement::from(self.context.da_gas_left as u128);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_minFeePerL2Gas" => {
                let v = FieldElement::from(self.context.min_fee_per_l2_gas);
                self.single(name, Fidelity::Environment, v)
            }
            "aztec_avm_minFeePerDaGas" => {
                let v = FieldElement::from(self.context.min_fee_per_da_gas);
                self.single(name, Fidelity::Environment, v)
            }

            // ---------------------------------------------------------------------------
            // Effects this execution emits. Pure sinks — faithful by construction.
            // ---------------------------------------------------------------------------
            "aztec_avm_emitNullifier" => {
                let nullifier = Self::input_field(call, 0);
                self.emitted_nullifiers.insert(nullifier);
                self.sink(name, Fidelity::Faithful)
            }
            "aztec_avm_emitNoteHash" => {
                let note_hash = Self::input_field(call, 0);
                self.emitted_note_hashes.push(note_hash);
                self.sink(name, Fidelity::Faithful)
            }
            "aztec_avm_emitPublicLog" => {
                let message = Self::input_fields(call, 0);
                self.public_logs.push(message);
                self.sink(name, Fidelity::Faithful)
            }
            "aztec_avm_sendL2ToL1Msg" => self.sink(name, Fidelity::Faithful),
            "aztec_avm_revert" => self.sink(name, Fidelity::Faithful),
            "aztec_avm_return" => {
                self.returndata = Self::input_fields(call, 0);
                self.sink(name, Fidelity::Faithful)
            }

            // ---------------------------------------------------------------------------
            // Public storage. The in-memory stand-in: faithful for a slot this session
            // wrote, DebugLocal (zero) for one it did not.
            // ---------------------------------------------------------------------------
            "aztec_avm_storageWrite" => {
                let slot = Self::input_field(call, 0);
                let value = Self::input_field(call, 1);
                let contract = self.context.contract_address;
                self.storage.insert((contract, slot), value);
                self.sink(name, Fidelity::Faithful)
            }
            "aztec_avm_storageRead" => {
                let slot = Self::input_field(call, 0);
                // The oracle takes the contract address explicitly; honour it rather than
                // assuming the read is always against the executing contract.
                let contract = match call.inputs.get(1) {
                    Some(ForeignCallParam::Single(v)) => *v,
                    _ => self.context.contract_address,
                };
                match self.storage.get(&(contract, slot)).copied() {
                    // Written in this session: this is exactly what a real host would say.
                    Some(value) => self.single(name, Fidelity::Faithful, value),
                    // Never written here. A real node would answer from the public data
                    // tree; this answers zero, and says so.
                    None => self.single(name, Fidelity::DebugLocal, FieldElement::zero()),
                }
            }

            // ---------------------------------------------------------------------------
            // Nullifier existence. Faithful for one this session emitted; otherwise the
            // DECLARED premise, recorded as DebugLocal because it is a claim about a chain
            // this process cannot see.
            // ---------------------------------------------------------------------------
            "aztec_avm_nullifierExists" => {
                let nullifier = Self::input_field(call, 0);
                if self.emitted_nullifiers.contains(&nullifier) {
                    self.single(name, Fidelity::Faithful, bool_field(true))
                } else {
                    let exists = matches!(self.nullifier_premise, NullifierPremise::AlreadyDeployed);
                    self.single(name, Fidelity::DebugLocal, bool_field(exists))
                }
            }
            "aztec_avm_noteHashExists" => {
                let note_hash = Self::input_field(call, 0);
                let exists = self.emitted_note_hashes.contains(&note_hash);
                let fidelity = if exists { Fidelity::Faithful } else { Fidelity::DebugLocal };
                self.single(name, fidelity, bool_field(exists))
            }

            // ---------------------------------------------------------------------------
            // Calldata. The AVM supplies a public function's arguments through
            // `calldataCopy` rather than through the witness. This host is stepping a
            // single function whose arguments already arrived through the ABI, so there is
            // no separate calldata buffer: zeroes, declared.
            // ---------------------------------------------------------------------------
            "aztec_avm_calldataCopy" => {
                let copy_size = Self::input_field(call, 1).to_u128() as usize;
                self.array(name, Fidelity::DebugLocal, vec![FieldElement::zero(); copy_size])
            }

            // ---------------------------------------------------------------------------
            // Refused. Each needs state or machinery this process does not have, and each
            // says which.
            // ---------------------------------------------------------------------------
            "aztec_avm_call" | "aztec_avm_staticCall" => self.unsupported(
                name,
                "cross-contract dispatch: needs the callee's bytecode and a nested AVM frame",
            ),
            "aztec_avm_successCopy" | "aztec_avm_returndataSize" | "aztec_avm_returndataCopy" => {
                self.unsupported(name, "reads the result of `aztec_avm_call`, which is refused")
            }
            "aztec_avm_l1ToL2MsgExists" => {
                self.unsupported(name, "needs the L1-to-L2 message tree")
            }
            "aztec_avm_getContractInstanceClassId"
            | "aztec_avm_getContractInstanceDeployer"
            | "aztec_avm_getContractInstanceImmutablesHash"
            | "aztec_avm_getContractInstanceInitializationHash" => self.unsupported(
                name,
                "needs the contract-instance directory; `aztec-avm-runtime`'s wallet holds one",
            ),

            // Not ours. `aztec_prv_*` / `aztec_utl_*` are the PRIVATE execution interface,
            // which `aztec-avm-runtime`'s `private_oracles.ts` implements against a wallet
            // and a note database. Refusing by name keeps the two halves distinguishable
            // instead of answering zero on behalf of a host that is not this one.
            other if other.starts_with("aztec_prv_") || other.starts_with("aztec_utl_") => {
                self.unsupported(
                    other,
                    "private-execution oracle: served by aztec-avm-runtime's private_oracles.ts, \
                     which needs a wallet, a note database and a world-state source",
                )
            }
            other if other.starts_with("aztec_txe_") => {
                self.unsupported(other, "TXE test-environment oracle: needs a TXE node")
            }

            // Everything else — including the `__debug_*` calls — belongs to another layer.
            _ => Err(ForeignCallError::NoHandler(name.to_string())),
        }
    }
}

/// A handle onto a host that an executor chain has taken ownership of.
///
/// The chain is built out of `impl Trait` values that are moved into the debug context, so
/// the host itself is not reachable afterwards — but what it answered, and at what
/// fidelity, is exactly what a caller needs to report. Cloning this shares one host.
#[derive(Clone, Default)]
pub struct SharedAvmOracleHost(std::rc::Rc<std::cell::RefCell<AztecAvmOracleHost>>);

impl std::fmt::Debug for SharedAvmOracleHost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Borrowing here would panic if a call is in flight, so report shape, not contents.
        f.debug_struct("SharedAvmOracleHost").finish_non_exhaustive()
    }
}

impl SharedAvmOracleHost {
    pub fn new(context: AztecContext, nullifier_premise: NullifierPremise) -> Self {
        Self(std::rc::Rc::new(std::cell::RefCell::new(AztecAvmOracleHost::new(
            context,
            nullifier_premise,
        ))))
    }

    pub fn borrow(&self) -> std::cell::Ref<'_, AztecAvmOracleHost> {
        self.0.borrow()
    }
}

impl ForeignCallExecutor<FieldElement> for SharedAvmOracleHost {
    fn execute(
        &mut self,
        call: &ForeignCallWaitInfo<FieldElement>,
    ) -> Result<ForeignCallResult<FieldElement>, ForeignCallError> {
        self.0.borrow_mut().execute(call)
    }
}
