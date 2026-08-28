//! Resolve a Noir **package tree** that lives entirely in memory.
//!
//! `compiler/wasm` already accepts an in-memory set of sources —
//! [`crate::compile::PathToFileSourceMap`], handed to
//! [`crate::compile::file_manager_with_source_map`] — but it does **not** know what a
//! `Nargo.toml` is. The crate graph arrives pre-computed from JavaScript as a
//! [`crate::compile::DependencyGraph`], and everything that produces one — reading the
//! manifest, walking `[dependencies]`, deciding which file is the crate root — lives in
//! `src/noir/*.ts` and needs `@ltd/j-toml`, a `FileManager` shim and, for a `git`
//! dependency, a live `fetch`.
//!
//! This module moves that half into the compiler, so a host with a `path -> source` map
//! needs nothing else. It is deliberately **pure**: no `std::fs`, no `std::env`, no
//! `std::process`, no networking and no clock, so it behaves identically on
//! `wasm32-unknown-unknown` and natively — which is what lets the tests below be the
//! evidence for what a page does.
//!
//! # What it does that the TypeScript path does not
//!
//! - **`[package].entry` is honoured.** `src/noir/package.ts:62-80` hard-codes `lib.nr` /
//!   `main.nr` and ignores the field; native `nargo` honours it
//!   (`tooling/nargo_toml/src/lib.rs:193-200`) and refuses a missing one by name. A
//!   manifest that names a custom entry therefore compiles a *different file* through
//!   `noir_wasm` than through `nargo`, silently. Here it is honoured, and a custom entry
//!   that is not in the tree is refused naming that path.
//! - **A `git` dependency is REFUSED BY NAME.** The shipped resolver chain
//!   (`src/noir/noir-wasm-compiler.ts:71-79`) answers a GitHub dependency by downloading
//!   a zip over the network, and answers any other git host with the anonymous
//!   `Dependency not resolved` (`src/noir/dependencies/dependency-manager.ts:122-124`).
//!   A virtual filesystem cannot fetch, and a fetch is not what a caller asked for, so
//!   this is an error carrying the dependency's name, the manifest and the manifest LINE
//!   the entry sits on. It is never a silent skip and never a plausible empty value.
//! - **Library sources keep their real paths.** `package.ts:112-114` re-keys every
//!   library source to `<alias>/<suffix>` so that
//!   `compile_new.rs`'s `add_noir_lib` can find `<alias>/lib.nr`. That works, and it
//!   means a diagnostic inside a dependency names a path the caller's VFS does not
//!   contain. Here each package is registered with [`noirc_driver::prepare_dependency`]
//!   at its own entry path, exactly as native `nargo` does
//!   (`tooling/nargo/src/lib.rs:35-50`), so **every** position in a diagnostic — root or
//!   dependency — is a path the caller supplied.
//!
//! # The shape of the answer
//!
//! [`resolve_vfs`] does the reading and the walking and returns a [`ResolvedProgram`]: a
//! plan. [`compile_resolved`] turns a plan into a `Context` and compiles it. They are
//! separate because the plan is worth having on its own — it is what a host hands to a
//! *different* consumer of the same tree (a tracer, say) so that two tools agree about
//! which files are in the program and which one is the root.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use fm::{FileManager, NormalizePath, codespan_files::Files as _};
use nargo::parse_all;
use noirc_driver::{
    CompileOptions, add_dep, file_manager_with_stdlib, prepare_crate, prepare_dependency,
};
use noirc_errors::CustomDiagnostic;
use noirc_frontend::graph::{CrateId, CrateName};
use noirc_frontend::hir::Context;
use serde::{Deserialize, Serialize};

/// The manifest file name, as `nargo` spells it.
pub const MANIFEST_FILE_NAME: &str = "Nargo.toml";

/// The source extension the compiler recognises.
const SOURCE_EXTENSION: &str = "nr";

// ---------------------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------------------

/// Where in a manifest something went wrong. Both are 1-based, as an editor counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ManifestPosition {
    pub line: usize,
    pub column: usize,
}

/// Everything [`resolve_vfs`] can refuse, each naming what it refused.
///
/// Every variant carries the manifest it was reading, because "a dependency is missing"
/// without saying whose dependency it is has to be diagnosed by re-reading the tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VfsError {
    /// The package directory has no `Nargo.toml` in the tree.
    MissingManifest { manifest: String },
    /// The manifest is not valid TOML.
    ManifestNotToml { manifest: String, at: Option<ManifestPosition>, message: String },
    /// `[package].name` is absent, or is not a valid crate name.
    BadPackageName { manifest: String, name: Option<String> },
    /// `[package].type` is absent or is not one of `lib` / `bin` / `contract`.
    BadPackageType { manifest: String, package_type: Option<String> },
    /// A dependency name is not a valid crate name.
    BadDependencyName { manifest: String, at: Option<ManifestPosition>, name: String },
    /// The crate root named by `[package].entry`, or the default one, is not in the tree.
    MissingEntry { manifest: String, entry: String, was_declared: bool },
    /// A `path` dependency points at a directory with no manifest in the tree.
    MissingDependencyManifest {
        manifest: String,
        at: Option<ManifestPosition>,
        dependency: String,
        expected: String,
    },
    /// A `git` dependency. Refused: a virtual filesystem cannot fetch.
    GitDependency {
        manifest: String,
        at: Option<ManifestPosition>,
        dependency: String,
        git: String,
        tag: Option<String>,
    },
    /// A dependency table that is neither `path` nor `git`.
    UnknownDependencyShape {
        manifest: String,
        at: Option<ManifestPosition>,
        dependency: String,
        keys: Vec<String>,
    },
    /// A dependency resolved to a package that is not a library.
    DependencyNotALibrary {
        manifest: String,
        at: Option<ManifestPosition>,
        dependency: String,
        package_type: String,
    },
    /// The package graph contains a cycle.
    DependencyCycle { chain: Vec<String> },
    /// The same dependency name resolves to two different directories.
    ConflictingDependency { dependency: String, first: String, second: String },
}

impl VfsError {
    /// The manifest this error is about, when it is about one.
    pub fn manifest(&self) -> Option<&str> {
        match self {
            VfsError::MissingManifest { manifest }
            | VfsError::ManifestNotToml { manifest, .. }
            | VfsError::BadPackageName { manifest, .. }
            | VfsError::BadPackageType { manifest, .. }
            | VfsError::BadDependencyName { manifest, .. }
            | VfsError::MissingEntry { manifest, .. }
            | VfsError::MissingDependencyManifest { manifest, .. }
            | VfsError::GitDependency { manifest, .. }
            | VfsError::UnknownDependencyShape { manifest, .. }
            | VfsError::DependencyNotALibrary { manifest, .. } => Some(manifest),
            VfsError::DependencyCycle { .. } | VfsError::ConflictingDependency { .. } => None,
        }
    }

    /// The position inside that manifest, when there is one.
    pub fn position(&self) -> Option<ManifestPosition> {
        match self {
            VfsError::ManifestNotToml { at, .. }
            | VfsError::BadDependencyName { at, .. }
            | VfsError::MissingDependencyManifest { at, .. }
            | VfsError::GitDependency { at, .. }
            | VfsError::UnknownDependencyShape { at, .. }
            | VfsError::DependencyNotALibrary { at, .. } => *at,
            _ => None,
        }
    }

    /// A stable machine-readable tag, so a host can branch without matching prose.
    pub fn kind(&self) -> &'static str {
        match self {
            VfsError::MissingManifest { .. } => "missing-manifest",
            VfsError::ManifestNotToml { .. } => "manifest-not-toml",
            VfsError::BadPackageName { .. } => "bad-package-name",
            VfsError::BadPackageType { .. } => "bad-package-type",
            VfsError::BadDependencyName { .. } => "bad-dependency-name",
            VfsError::MissingEntry { .. } => "missing-entry",
            VfsError::MissingDependencyManifest { .. } => "missing-dependency-manifest",
            VfsError::GitDependency { .. } => "git-dependency-refused",
            VfsError::UnknownDependencyShape { .. } => "unknown-dependency-shape",
            VfsError::DependencyNotALibrary { .. } => "dependency-not-a-library",
            VfsError::DependencyCycle { .. } => "dependency-cycle",
            VfsError::ConflictingDependency { .. } => "conflicting-dependency",
        }
    }
}

impl std::fmt::Display for VfsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Every message begins `<manifest>[:line:col]: ` when it is about a manifest, so a
        // host can print it unchanged and an editor can jump to it.
        if let Some(manifest) = self.manifest() {
            write!(f, "{manifest}")?;
            if let Some(at) = self.position() {
                write!(f, ":{}:{}", at.line, at.column)?;
            }
            write!(f, ": ")?;
        }

        match self {
            VfsError::MissingManifest { manifest } => {
                write!(f, "no {MANIFEST_FILE_NAME} at this path in the virtual filesystem")?;
                let _ = manifest;
            }
            VfsError::ManifestNotToml { message, .. } => {
                write!(f, "the manifest is not valid TOML: {message}")?;
            }
            VfsError::BadPackageName { name, .. } => match name {
                Some(name) => write!(
                    f,
                    "`[package].name` is `{name}`, which is not a valid Noir crate name"
                )?,
                None => write!(f, "`[package].name` is missing")?,
            },
            VfsError::BadPackageType { package_type, .. } => match package_type {
                Some(t) => write!(
                    f,
                    "`[package].type` is `{t}`; it must be one of `lib`, `bin` or `contract`"
                )?,
                None => write!(f, "`[package].type` is missing")?,
            },
            VfsError::BadDependencyName { name, .. } => {
                write!(f, "`{name}` is not a valid Noir crate name")?;
            }
            VfsError::MissingEntry { entry, was_declared, .. } => {
                if *was_declared {
                    write!(
                        f,
                        "`[package].entry` names `{entry}`, which is not in the virtual filesystem"
                    )?;
                } else {
                    write!(
                        f,
                        "the crate root `{entry}` is not in the virtual filesystem"
                    )?;
                }
            }
            VfsError::MissingDependencyManifest { dependency, expected, .. } => {
                write!(
                    f,
                    "the dependency `{dependency}` resolves to `{expected}`, \
                     which is not in the virtual filesystem"
                )?;
            }
            VfsError::GitDependency { dependency, git, tag, .. } => {
                write!(f, "the dependency `{dependency}` is a GIT dependency (git = \"{git}\"")?;
                if let Some(tag) = tag {
                    write!(f, ", tag = \"{tag}\"")?;
                }
                write!(
                    f,
                    "). A virtual filesystem cannot fetch it, and fetching one is not what \
                     compiling from a virtual filesystem means. Vendor it into the tree and \
                     depend on it by `path`, or resolve it before you build the tree."
                )?;
            }
            VfsError::UnknownDependencyShape { dependency, keys, .. } => {
                write!(
                    f,
                    "the dependency `{dependency}` declares neither `path` nor `git` (it has {})",
                    if keys.is_empty() {
                        "no keys at all".to_string()
                    } else {
                        format!("`{}`", keys.join("`, `"))
                    }
                )?;
            }
            VfsError::DependencyNotALibrary { dependency, package_type, .. } => {
                write!(f, "the dependency `{dependency}` is a `{package_type}`, not a `lib`")?;
            }
            VfsError::DependencyCycle { chain } => {
                write!(f, "the package graph contains a cycle: {}", chain.join(" -> "))?;
            }
            VfsError::ConflictingDependency { dependency, first, second } => {
                write!(
                    f,
                    "the dependency name `{dependency}` resolves to two different packages, \
                     `{first}` and `{second}`"
                )?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------
// The manifest, as this module reads it
// ---------------------------------------------------------------------------------------

#[derive(Deserialize)]
struct RawManifest {
    package: Option<RawPackage>,
    #[serde(default)]
    dependencies: BTreeMap<String, toml::Spanned<RawDependency>>,
}

#[derive(Deserialize)]
struct RawPackage {
    name: Option<String>,
    #[serde(rename = "type")]
    package_type: Option<String>,
    entry: Option<String>,
}

/// Every dependency shape at once, rather than an untagged enum.
///
/// `nargo_toml`'s `DependencyConfig` is `#[serde(untagged)]` over `Github{git,tag,..}` and
/// `Path{path}`, so a table that is *nearly* a git dependency — `{ git = "..." }` with no
/// `tag` — matches neither arm and comes back as a TOML type error naming the whole
/// `[dependencies]` table. Reading every key separately is what lets the refusal below
/// name the dependency rather than the table it is in.
#[derive(Deserialize)]
struct RawDependency {
    path: Option<String>,
    git: Option<String>,
    tag: Option<String>,
    directory: Option<String>,
    #[serde(flatten)]
    rest: BTreeMap<String, toml::Value>,
}

impl RawDependency {
    fn declared_keys(&self) -> Vec<String> {
        let mut keys: Vec<String> = Vec::new();
        if self.path.is_some() {
            keys.push("path".to_string());
        }
        if self.git.is_some() {
            keys.push("git".to_string());
        }
        if self.tag.is_some() {
            keys.push("tag".to_string());
        }
        if self.directory.is_some() {
            keys.push("directory".to_string());
        }
        keys.extend(self.rest.keys().cloned());
        keys
    }
}

// ---------------------------------------------------------------------------------------
// The plan
// ---------------------------------------------------------------------------------------

/// One package in the resolved tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ResolvedPackage {
    /// The alias the depending package knows it by; the root package's is its own name.
    pub alias: String,
    /// `[package].name`.
    pub name: String,
    /// `lib`, `bin` or `contract`.
    pub package_type: String,
    /// The directory the manifest is in, as a VFS path.
    pub directory: String,
    /// The manifest, as a VFS path.
    pub manifest: String,
    /// The crate root, as a VFS path.
    pub entry_point: String,
    /// Whether `[package].entry` named it, rather than the default.
    pub entry_was_declared: bool,
    /// The `.nr` files this package contributes, as VFS paths, in tree order.
    pub sources: Vec<String>,
    /// This package's own dependency aliases, in manifest order.
    pub dependencies: Vec<String>,
}

/// A whole program, resolved out of a virtual filesystem and ready to compile.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ResolvedProgram {
    /// The crate root of the entry package, as a VFS path.
    pub entry_point: String,
    /// `lib`, `bin` or `contract` — what the entry package's manifest says.
    pub package_type: String,
    /// The entry package first, then every library, in breadth-first discovery order.
    pub packages: Vec<ResolvedPackage>,
    /// Every `.nr` file the program is made of, as VFS paths, deduplicated and sorted.
    ///
    /// This is the set a second consumer of the same tree must agree with, which is why
    /// it is part of the plan rather than something a caller re-derives.
    pub sources: Vec<String>,
}

impl ResolvedProgram {
    /// The entry package.
    pub fn root(&self) -> &ResolvedPackage {
        &self.packages[0]
    }
}

// ---------------------------------------------------------------------------------------
// Resolution
// ---------------------------------------------------------------------------------------

/// Normalise a VFS path to the spelling the map is keyed by.
fn vfs_key(path: &Path) -> String {
    let normalized = path.normalize();
    let s = normalized.to_string_lossy().to_string();
    // `Path::normalize()` leaves `./a` as `a`, which is what the map holds; a leading
    // `/` is preserved, because a caller that keys its tree absolutely is not wrong.
    s
}

fn join_vfs(dir: &str, rel: &str) -> String {
    if dir.is_empty() || dir == "." {
        vfs_key(Path::new(rel))
    } else {
        vfs_key(&Path::new(dir).join(rel))
    }
}

/// Byte offset -> 1-based (line, column) in `text`.
fn position_in(text: &str, offset: usize) -> ManifestPosition {
    let offset = offset.min(text.len());
    let mut line = 1usize;
    let mut last_newline = 0usize;
    for (i, b) in text.as_bytes().iter().enumerate().take(offset) {
        if *b == b'\n' {
            line += 1;
            last_newline = i + 1;
        }
    }
    // Count characters rather than bytes so a manifest with a non-ASCII comment before
    // the dependency does not report a column past the end of the line.
    let column = text[last_newline..offset].chars().count() + 1;
    ManifestPosition { line, column }
}

/// Resolve a package tree held in `files`, rooted at `package_dir`.
///
/// `files` is the caller's whole virtual filesystem: any `path -> contents` map. Only the
/// manifests and the `.nr` files under each package's `src/` are read; everything else in
/// the tree is ignored, which is what makes the returned `sources` a decision rather than
/// a copy of the input.
pub fn resolve_vfs(
    files: &BTreeMap<PathBuf, String>,
    package_dir: &str,
) -> Result<ResolvedProgram, VfsError> {
    let keyed: BTreeMap<String, &String> =
        files.iter().map(|(p, s)| (vfs_key(p), s)).collect();

    let root_dir = vfs_key(Path::new(package_dir));
    let mut packages: Vec<ResolvedPackage> = Vec::new();
    let mut seen_alias: BTreeMap<String, String> = BTreeMap::new();

    // Breadth-first, the same order `DependencyManager` walks, so the crate ids this
    // produces are stable in the same way.
    struct Job {
        alias: Option<String>,
        directory: String,
        chain: Vec<String>,
    }
    let mut queue: Vec<Job> =
        vec![Job { alias: None, directory: root_dir.clone(), chain: vec![root_dir.clone()] }];

    while !queue.is_empty() {
        let job = queue.remove(0);
        let manifest_path = join_vfs(&job.directory, MANIFEST_FILE_NAME);
        let manifest_text = keyed
            .get(&manifest_path)
            .ok_or_else(|| VfsError::MissingManifest { manifest: manifest_path.clone() })?;

        let manifest: RawManifest = toml::from_str(manifest_text).map_err(|err| {
            VfsError::ManifestNotToml {
                manifest: manifest_path.clone(),
                at: err.span().map(|span| position_in(manifest_text, span.start)),
                message: err.message().to_string(),
            }
        })?;

        let package = manifest.package.as_ref();
        let name = package.and_then(|p| p.name.clone());
        let crate_name = match &name {
            Some(name) if name.parse::<CrateName>().is_ok() => name.clone(),
            other => {
                return Err(VfsError::BadPackageName {
                    manifest: manifest_path.clone(),
                    name: other.clone(),
                });
            }
        };

        let package_type = match package.and_then(|p| p.package_type.clone()) {
            Some(t) if t == "lib" || t == "bin" || t == "contract" => t,
            other => {
                return Err(VfsError::BadPackageType {
                    manifest: manifest_path.clone(),
                    package_type: other,
                });
            }
        };

        // `[package].entry`, honoured — see the module header.
        let declared_entry = package.and_then(|p| p.entry.clone());
        let entry_was_declared = declared_entry.is_some();
        let entry_rel = declared_entry.unwrap_or_else(|| {
            if package_type == "lib" {
                format!("src/lib.{SOURCE_EXTENSION}")
            } else {
                format!("src/main.{SOURCE_EXTENSION}")
            }
        });
        let entry_point = join_vfs(&job.directory, &entry_rel);
        if !keyed.contains_key(&entry_point) {
            return Err(VfsError::MissingEntry {
                manifest: manifest_path.clone(),
                entry: entry_point,
                was_declared: entry_was_declared,
            });
        }

        // Sources: every `.nr` under this package's `src/`. Anything else in the tree —
        // a `Prover.toml`, a README, a stray `.nr` outside `src/` — is deliberately not
        // part of the program, which is the decision this function exists to take.
        let src_prefix = join_vfs(&job.directory, "src");
        let src_prefix_slash = format!("{src_prefix}/");
        let mut sources: Vec<String> = keyed
            .keys()
            .filter(|p| p.starts_with(&src_prefix_slash))
            .filter(|p| Path::new(p).extension().is_some_and(|e| e == SOURCE_EXTENSION))
            .cloned()
            .collect();
        // The entry point may be declared outside `src/`; it is a source either way.
        if !sources.contains(&entry_point) {
            sources.push(entry_point.clone());
        }
        sources.sort();
        sources.dedup();

        // Dependencies.
        let mut dependency_aliases: Vec<String> = Vec::new();
        let mut children: Vec<Job> = Vec::new();
        for (dep_name, spanned) in &manifest.dependencies {
            let at = Some(position_in(manifest_text, spanned.span().start));
            let dep = spanned.get_ref();

            if dep_name.parse::<CrateName>().is_err() {
                return Err(VfsError::BadDependencyName {
                    manifest: manifest_path.clone(),
                    at,
                    name: dep_name.clone(),
                });
            }

            // THE REFUSAL. A `git` key means a fetch, and a virtual filesystem does not
            // fetch. It is named, positioned, and it is a throw — never a skip and never
            // an empty resolution that a later "dependency not found" would explain badly.
            if let Some(git) = &dep.git {
                return Err(VfsError::GitDependency {
                    manifest: manifest_path.clone(),
                    at,
                    dependency: dep_name.clone(),
                    git: git.clone(),
                    tag: dep.tag.clone(),
                });
            }

            let Some(path) = &dep.path else {
                return Err(VfsError::UnknownDependencyShape {
                    manifest: manifest_path.clone(),
                    at,
                    dependency: dep_name.clone(),
                    keys: dep.declared_keys(),
                });
            };

            let dep_dir = if path.starts_with('/') {
                vfs_key(Path::new(path))
            } else {
                join_vfs(&job.directory, path)
            };
            let dep_manifest = join_vfs(&dep_dir, MANIFEST_FILE_NAME);
            if !keyed.contains_key(&dep_manifest) {
                return Err(VfsError::MissingDependencyManifest {
                    manifest: manifest_path.clone(),
                    at,
                    dependency: dep_name.clone(),
                    expected: dep_manifest,
                });
            }

            dependency_aliases.push(dep_name.clone());

            match seen_alias.get(dep_name) {
                Some(existing) if existing != &dep_dir => {
                    return Err(VfsError::ConflictingDependency {
                        dependency: dep_name.clone(),
                        first: existing.clone(),
                        second: dep_dir,
                    });
                }
                Some(_) => continue, // already queued or resolved, and it is the same package
                None => {}
            }

            if job.chain.contains(&dep_dir) {
                let mut chain = job.chain.clone();
                chain.push(dep_dir);
                return Err(VfsError::DependencyCycle { chain });
            }

            seen_alias.insert(dep_name.clone(), dep_dir.clone());
            let mut chain = job.chain.clone();
            chain.push(dep_dir.clone());
            children.push(Job { alias: Some(dep_name.clone()), directory: dep_dir, chain });
        }

        // A dependency must be a library, the same rule `DependencyManager` enforces.
        if job.alias.is_some() && package_type != "lib" {
            let parent = job.chain[job.chain.len() - 2].clone();
            return Err(VfsError::DependencyNotALibrary {
                manifest: join_vfs(&parent, MANIFEST_FILE_NAME),
                at: None,
                dependency: job.alias.clone().unwrap_or_default(),
                package_type,
            });
        }

        packages.push(ResolvedPackage {
            alias: job.alias.clone().unwrap_or_else(|| crate_name.clone()),
            name: crate_name,
            package_type: package_type.clone(),
            directory: job.directory.clone(),
            manifest: manifest_path,
            entry_point,
            entry_was_declared,
            sources,
            dependencies: dependency_aliases,
        });

        queue.extend(children);
    }

    let mut all_sources: BTreeSet<String> = BTreeSet::new();
    for p in &packages {
        all_sources.extend(p.sources.iter().cloned());
    }

    Ok(ResolvedProgram {
        entry_point: packages[0].entry_point.clone(),
        package_type: packages[0].package_type.clone(),
        packages,
        sources: all_sources.into_iter().collect(),
    })
}

// ---------------------------------------------------------------------------------------
// Compilation
// ---------------------------------------------------------------------------------------

/// A diagnostic with a real position, against the paths the caller supplied.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PositionedDiagnostic {
    pub message: String,
    /// The VFS path. `file_manager.path()` returns exactly what was registered.
    pub file: String,
    /// 1-based.
    pub line: usize,
    /// 1-based.
    pub column: usize,
    pub end_line: usize,
    pub end_column: usize,
    /// The byte range, kept because the shipped `Diagnostic` type carries these and a
    /// consumer that already reads them must not have to change.
    pub start: u32,
    pub end: u32,
    pub secondary_messages: Vec<String>,
    pub notes: Vec<String>,
    /// `error`, `warning` or `bug`.
    pub severity: String,
}

/// Build a `Context` over a resolved plan.
///
/// Every package is registered at its own entry path, so a `Location` the frontend
/// produces resolves back to a path the caller put in the tree.
pub fn context_for(
    plan: &ResolvedProgram,
    files: &BTreeMap<PathBuf, String>,
) -> (Context<'static, 'static>, CrateId) {
    let keyed: BTreeMap<String, &String> =
        files.iter().map(|(p, s)| (vfs_key(p), s)).collect();

    let mut file_manager: FileManager = file_manager_with_stdlib(Path::new(""));
    for path in &plan.sources {
        if let Some(source) = keyed.get(path) {
            file_manager.add_file_with_source(Path::new(path), (*source).clone());
        }
    }

    let parsed_files = parse_all(&file_manager);
    let mut context = Context::new(file_manager, parsed_files);

    let root_id = prepare_crate(&mut context, Path::new(&plan.entry_point));

    let mut ids: BTreeMap<String, CrateId> = BTreeMap::new();
    ids.insert(plan.packages[0].directory.clone(), root_id);
    for package in plan.packages.iter().skip(1) {
        let id = prepare_dependency(&mut context, Path::new(&package.entry_point));
        ids.insert(package.directory.clone(), id);
    }

    // Edges, after every crate exists, so a diamond does not depend on discovery order.
    for package in &plan.packages {
        let from = ids[&package.directory];
        for alias in &package.dependencies {
            // The alias is the *name* under which the parent knows the child; find the
            // child by matching the alias recorded on it.
            if let Some(child) = plan.packages.iter().find(|p| &p.alias == alias) {
                if let Ok(crate_name) = alias.parse::<CrateName>() {
                    add_dep(&mut context, from, ids[&child.directory], crate_name);
                }
            }
        }
    }

    (context, root_id)
}

/// Turn the frontend's diagnostics into positioned ones against VFS paths.
pub fn position_diagnostics(
    diagnostics: &[CustomDiagnostic],
    file_manager: &FileManager,
) -> Vec<PositionedDiagnostic> {
    let files = file_manager.as_file_map();

    diagnostics
        .iter()
        .map(|diagnostic| {
            let file = file_manager
                .path(diagnostic.file)
                .map(|p| p.display().to_string())
                .unwrap_or_else(|| "<unknown file>".to_string());

            // The frontend puts the offending span on the first secondary label.
            let (start, end) = diagnostic
                .secondaries
                .first()
                .map(|label| (label.location.span.start(), label.location.span.end()))
                .unwrap_or((0, 0));

            let at = files.location(diagnostic.file, start as usize).ok();
            let to = files.location(diagnostic.file, end as usize).ok();

            PositionedDiagnostic {
                message: diagnostic.message.clone(),
                file,
                line: at.as_ref().map_or(0, |l| l.line_number),
                column: at.as_ref().map_or(0, |l| l.column_number),
                end_line: to.as_ref().map_or(0, |l| l.line_number),
                end_column: to.as_ref().map_or(0, |l| l.column_number),
                start,
                end,
                secondary_messages: diagnostic
                    .secondaries
                    .iter()
                    .map(|l| l.message.clone())
                    .filter(|m| !m.is_empty())
                    .collect(),
                notes: diagnostic.notes.clone(),
                severity: format!("{:?}", diagnostic.kind).to_lowercase(),
            }
        })
        .collect()
}

/// What a compile of a resolved plan produced.
pub enum CompiledFromVfs {
    Program(Box<noirc_artifacts::program::ProgramArtifact>),
    Contract(Box<noirc_artifacts::contract::ContractArtifact>),
}

/// Compile a resolved plan. `as_contract` picks `compile_contract` over `compile_main`.
///
/// Errors come back positioned, against the caller's own paths.
pub fn compile_resolved(
    plan: &ResolvedProgram,
    files: &BTreeMap<PathBuf, String>,
    as_contract: bool,
) -> Result<(CompiledFromVfs, Vec<PositionedDiagnostic>), Vec<PositionedDiagnostic>> {
    let (mut context, root_id) = context_for(plan, files);
    let options = CompileOptions::default();

    if as_contract {
        match noirc_driver::compile_contract(&mut context, root_id, &options) {
            Ok((contract, warnings)) => {
                let optimized = nargo::ops::optimize_contract(contract);
                let positioned = position_diagnostics(
                    &warnings.into_iter().collect::<Vec<_>>(),
                    &context.file_manager,
                );
                Ok((CompiledFromVfs::Contract(Box::new(optimized.into())), positioned))
            }
            Err(errors) => Err(position_diagnostics(&errors, &context.file_manager)),
        }
    } else {
        match noirc_driver::compile_main(&mut context, root_id, &options, None) {
            Ok((program, warnings)) => {
                let optimized = nargo::ops::optimize_program(program);
                let positioned = position_diagnostics(
                    &warnings.into_iter().collect::<Vec<_>>(),
                    &context.file_manager,
                );
                Ok((CompiledFromVfs::Program(Box::new(optimized.into())), positioned))
            }
            Err(errors) => Err(position_diagnostics(&errors, &context.file_manager)),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Tests — native, over the same code a wasm build runs
// ---------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn tree(entries: &[(&str, &str)]) -> BTreeMap<PathBuf, String> {
        entries.iter().map(|(p, s)| (PathBuf::from(*p), (*s).to_string())).collect()
    }

    /// The three-file tree with a local dependency the milestone names.
    fn three_file_tree_with_dep() -> BTreeMap<PathBuf, String> {
        tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\nutil = { path = \"../util\" }\n",
            ),
            (
                "app/src/main.nr",
                "fn main(x: Field) -> pub Field {\n    util::twice(x)\n}\n",
            ),
            ("util/Nargo.toml", "[package]\nname = \"util\"\ntype = \"lib\"\n"),
            ("util/src/lib.nr", "pub fn twice(x: Field) -> Field {\n    x + x\n}\n"),
        ])
    }

    #[test]
    fn a_three_file_tree_with_a_local_dependency_resolves() {
        let files = three_file_tree_with_dep();
        let plan = resolve_vfs(&files, "app").expect("the tree resolves");

        assert_eq!(plan.entry_point, "app/src/main.nr");
        assert_eq!(plan.package_type, "bin");
        assert_eq!(plan.packages.len(), 2);
        assert_eq!(plan.packages[0].name, "app");
        assert_eq!(plan.packages[0].dependencies, vec!["util".to_string()]);
        assert_eq!(plan.packages[1].alias, "util");
        assert_eq!(plan.packages[1].package_type, "lib");
        assert_eq!(plan.packages[1].entry_point, "util/src/lib.nr");
        assert_eq!(
            plan.sources,
            vec!["app/src/main.nr".to_string(), "util/src/lib.nr".to_string()]
        );
    }

    #[test]
    fn a_three_file_tree_with_a_local_dependency_compiles() {
        let files = three_file_tree_with_dep();
        let plan = resolve_vfs(&files, "app").expect("the tree resolves");
        let compiled = compile_resolved(&plan, &files, false);
        match compiled {
            Ok((CompiledFromVfs::Program(program), _)) => {
                assert!(
                    !program.bytecode.functions.is_empty(),
                    "the artifact carries at least one ACIR function"
                );
            }
            Ok(_) => panic!("expected a program"),
            Err(diagnostics) => panic!("expected a compile, got {diagnostics:?}"),
        }
    }

    /// The control the milestone asks for: a missing file fails with THAT path named.
    #[test]
    fn a_missing_dependency_names_the_path_it_looked_for() {
        let mut files = three_file_tree_with_dep();
        files.remove(Path::new("util/Nargo.toml"));

        let err = resolve_vfs(&files, "app").expect_err("a missing dependency manifest refuses");
        assert_eq!(err.kind(), "missing-dependency-manifest");
        let rendered = err.to_string();
        assert!(rendered.contains("util/Nargo.toml"), "names the path: {rendered}");
        assert!(rendered.contains("`util`"), "names the dependency: {rendered}");
    }

    #[test]
    fn a_missing_source_file_names_that_file() {
        let mut files = three_file_tree_with_dep();
        files.remove(Path::new("util/src/lib.nr"));

        let err = resolve_vfs(&files, "app").expect_err("a missing crate root refuses");
        assert_eq!(err.kind(), "missing-entry");
        assert!(err.to_string().contains("util/src/lib.nr"), "{err}");
    }

    #[test]
    fn a_git_dependency_is_refused_naming_itself_and_its_manifest_line() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                // `ecrecover` is on line 6, one-based, and the value's span starts at
                // its opening brace on that line.
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\necrecover = { git = \"https://github.com/colinnielsen/ecrecover-noir\", tag = \"v0.8.0\" }\n",
            ),
            ("app/src/main.nr", "fn main() {}\n"),
        ]);

        let err = resolve_vfs(&files, "app").expect_err("a git dependency is refused");
        assert_eq!(err.kind(), "git-dependency-refused");
        let at = err.position().expect("the refusal carries a position");
        assert_eq!(at.line, 6, "the manifest line the dependency sits on");

        let rendered = err.to_string();
        assert!(rendered.contains("`ecrecover`"), "names the dependency: {rendered}");
        assert!(rendered.contains("app/Nargo.toml:6:"), "names the manifest line: {rendered}");
        assert!(rendered.contains("ecrecover-noir"), "names the git url: {rendered}");
        assert!(rendered.contains("v0.8.0"), "names the tag: {rendered}");
    }

    /// The refusal's position is a measurement of the manifest, not a constant: moving
    /// the dependency down the file moves the number.
    #[test]
    fn the_refusals_line_moves_when_the_dependency_moves() {
        let manifest_top =
            "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\ndep = { git = \"https://example.com/x\", tag = \"v1\" }\n";
        let manifest_low =
            "[package]\nname = \"app\"\ntype = \"bin\"\n\n\n\n\n[dependencies]\ndep = { git = \"https://example.com/x\", tag = \"v1\" }\n";

        let top = tree(&[("app/Nargo.toml", manifest_top), ("app/src/main.nr", "fn main() {}\n")]);
        let low = tree(&[("app/Nargo.toml", manifest_low), ("app/src/main.nr", "fn main() {}\n")]);

        let a = resolve_vfs(&top, "app").expect_err("refused").position().unwrap();
        let b = resolve_vfs(&low, "app").expect_err("refused").position().unwrap();
        assert_eq!(a.line, 6);
        assert_eq!(b.line, 9);
    }

    /// The control for the refusal: a local `path` dependency resolves.
    #[test]
    fn a_path_dependency_resolves_where_a_git_one_is_refused() {
        let files = three_file_tree_with_dep();
        let plan = resolve_vfs(&files, "app").expect("a path dependency resolves");
        assert_eq!(plan.packages.len(), 2);
    }

    /// A git dependency that is *nearly* well formed — no `tag` — is still refused by
    /// name. `nargo_toml`'s untagged enum matches neither arm for this input.
    #[test]
    fn a_git_dependency_without_a_tag_is_still_refused_by_name() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\ndep = { git = \"https://example.com/x\" }\n",
            ),
            ("app/src/main.nr", "fn main() {}\n"),
        ]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "git-dependency-refused");
        assert!(err.to_string().contains("`dep`"), "{err}");
    }

    #[test]
    fn a_dependency_that_is_neither_path_nor_git_is_named() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\ndep = { version = \"1.0\" }\n",
            ),
            ("app/src/main.nr", "fn main() {}\n"),
        ]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "unknown-dependency-shape");
        let rendered = err.to_string();
        assert!(rendered.contains("`dep`"), "{rendered}");
        assert!(rendered.contains("version"), "names the keys it did find: {rendered}");
    }

    #[test]
    fn a_declared_entry_is_honoured_and_a_missing_one_is_named() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\nentry = \"src/other.nr\"\n",
            ),
            ("app/src/other.nr", "fn main() {}\n"),
            ("app/src/main.nr", "fn main() { assert(false); }\n"),
        ]);
        let plan = resolve_vfs(&files, "app").expect("resolves");
        assert_eq!(plan.entry_point, "app/src/other.nr");
        assert!(plan.root().entry_was_declared);

        let mut broken = files.clone();
        broken.remove(Path::new("app/src/other.nr"));
        let err = resolve_vfs(&broken, "app").expect_err("refused");
        assert_eq!(err.kind(), "missing-entry");
        assert!(err.to_string().contains("app/src/other.nr"), "{err}");
        assert!(err.to_string().contains("`[package].entry`"), "{err}");
    }

    #[test]
    fn files_outside_src_are_not_part_of_the_program() {
        let mut files = three_file_tree_with_dep();
        files.insert(PathBuf::from("app/Prover.toml"), "x = \"3\"\n".to_string());
        files.insert(PathBuf::from("app/README.md"), "# app\n".to_string());
        files.insert(
            PathBuf::from("app/scratch.nr"),
            "fn scratch() { assert(false); }\n".to_string(),
        );

        let plan = resolve_vfs(&files, "app").expect("resolves");
        assert_eq!(
            plan.sources,
            vec!["app/src/main.nr".to_string(), "util/src/lib.nr".to_string()],
            "a `.nr` outside `src/` is in the VFS and not in the program"
        );
    }

    #[test]
    fn a_multi_file_single_crate_tree_resolves_every_module() {
        let files = tree(&[
            ("app/Nargo.toml", "[package]\nname = \"app\"\ntype = \"bin\"\n"),
            ("app/src/main.nr", "mod util;\nfn main(x: Field) -> pub Field { util::twice(x) }\n"),
            ("app/src/util.nr", "pub fn twice(x: Field) -> Field { x + x }\n"),
        ]);
        let plan = resolve_vfs(&files, "app").expect("resolves");
        assert_eq!(plan.sources, vec!["app/src/main.nr".to_string(), "app/src/util.nr".to_string()]);

        let compiled = compile_resolved(&plan, &files, false);
        assert!(compiled.is_ok(), "a `mod` in a second file compiles");
    }

    #[test]
    fn a_type_error_reports_the_right_file_line_and_column() {
        let files = tree(&[
            ("app/Nargo.toml", "[package]\nname = \"app\"\ntype = \"bin\"\n"),
            ("app/src/main.nr", "mod util;\nfn main(x: Field) -> pub Field { util::twice(x) }\n"),
            // `twice` returns a Field; declaring `u8` is a type error on line 2.
            ("app/src/util.nr", "pub fn twice(x: Field) -> u8 {\n    x + x\n}\n"),
        ]);
        let plan = resolve_vfs(&files, "app").expect("resolves");
        let diagnostics = compile_resolved(&plan, &files, false).err().expect("a type error");
        assert!(!diagnostics.is_empty(), "at least one diagnostic");

        let in_util: Vec<_> =
            diagnostics.iter().filter(|d| d.file == "app/src/util.nr").collect();
        assert!(
            !in_util.is_empty(),
            "the diagnostic names the VFS path of the file the error is in, got {:?}",
            diagnostics.iter().map(|d| &d.file).collect::<Vec<_>>()
        );
        for d in in_util {
            assert!(d.line >= 1, "a real line, got {}", d.line);
            assert!(d.column >= 1, "a real column, got {}", d.column);
        }
    }

    /// The control: a clean tree reports no diagnostics at all.
    #[test]
    fn a_clean_tree_reports_no_diagnostics() {
        let files = three_file_tree_with_dep();
        let plan = resolve_vfs(&files, "app").expect("resolves");
        let (_, warnings) = compile_resolved(&plan, &files, false).expect("compiles");
        assert!(warnings.is_empty(), "a clean tree warns about nothing: {warnings:?}");
    }

    #[test]
    fn a_transitive_local_dependency_resolves() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\na = { path = \"../a\" }\n",
            ),
            ("app/src/main.nr", "fn main(x: Field) -> pub Field { a::via_b(x) }\n"),
            (
                "a/Nargo.toml",
                "[package]\nname = \"a\"\ntype = \"lib\"\n\n[dependencies]\nb = { path = \"../b\" }\n",
            ),
            ("a/src/lib.nr", "pub fn via_b(x: Field) -> Field { b::twice(x) }\n"),
            ("b/Nargo.toml", "[package]\nname = \"b\"\ntype = \"lib\"\n"),
            ("b/src/lib.nr", "pub fn twice(x: Field) -> Field { x + x }\n"),
        ]);
        let plan = resolve_vfs(&files, "app").expect("resolves");
        assert_eq!(plan.packages.len(), 3);
        assert!(compile_resolved(&plan, &files, false).is_ok(), "the transitive tree compiles");
    }

    #[test]
    fn a_cycle_is_refused_naming_the_chain() {
        let files = tree(&[
            (
                "a/Nargo.toml",
                "[package]\nname = \"a\"\ntype = \"bin\"\n\n[dependencies]\nb = { path = \"../b\" }\n",
            ),
            ("a/src/main.nr", "fn main() {}\n"),
            (
                "b/Nargo.toml",
                "[package]\nname = \"b\"\ntype = \"lib\"\n\n[dependencies]\na2 = { path = \"../a\" }\n",
            ),
            ("b/src/lib.nr", "pub fn f() {}\n"),
        ]);
        let err = resolve_vfs(&files, "a").expect_err("a cycle refuses");
        assert_eq!(err.kind(), "dependency-cycle");
        assert!(err.to_string().contains("a -> b -> a"), "{err}");
    }

    #[test]
    fn a_binary_dependency_is_refused() {
        let files = tree(&[
            (
                "app/Nargo.toml",
                "[package]\nname = \"app\"\ntype = \"bin\"\n\n[dependencies]\nother = { path = \"../other\" }\n",
            ),
            ("app/src/main.nr", "fn main() {}\n"),
            ("other/Nargo.toml", "[package]\nname = \"other\"\ntype = \"bin\"\n"),
            ("other/src/main.nr", "fn main() {}\n"),
        ]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "dependency-not-a-library");
        assert!(err.to_string().contains("`other`"), "{err}");
    }

    #[test]
    fn a_missing_root_manifest_names_the_path() {
        let files = tree(&[("app/src/main.nr", "fn main() {}\n")]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "missing-manifest");
        assert!(err.to_string().contains("app/Nargo.toml"), "{err}");
    }

    #[test]
    fn a_manifest_that_is_not_toml_is_named_with_a_position() {
        let files = tree(&[
            ("app/Nargo.toml", "[package]\nname = \"app\"\ntype = bin\n"),
            ("app/src/main.nr", "fn main() {}\n"),
        ]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "manifest-not-toml");
        assert!(err.to_string().contains("app/Nargo.toml:3:"), "{err}");
    }

    #[test]
    fn a_missing_package_type_is_named_rather_than_defaulted() {
        let files = tree(&[
            ("app/Nargo.toml", "[package]\nname = \"app\"\n"),
            ("app/src/main.nr", "fn main() {}\n"),
        ]);
        let err = resolve_vfs(&files, "app").expect_err("refused");
        assert_eq!(err.kind(), "bad-package-type");
        assert!(err.to_string().contains("`[package].type` is missing"), "{err}");
    }

    #[test]
    fn position_in_counts_lines_and_columns_from_one() {
        let text = "abc\ndef\nghi";
        assert_eq!(position_in(text, 0), ManifestPosition { line: 1, column: 1 });
        assert_eq!(position_in(text, 4), ManifestPosition { line: 2, column: 1 });
        assert_eq!(position_in(text, 6), ManifestPosition { line: 2, column: 3 });
        assert_eq!(position_in(text, 8), ManifestPosition { line: 3, column: 1 });
        // past the end clamps rather than panicking
        assert_eq!(position_in(text, 9_999).line, 3);
    }
}
