# A reproducible producer for sites whose replay engine reads meta.dat v6.
# Keep this historical compiler/writer pair separate from the current recorder:
# their EventLogKind ABIs differ, so substituting an older Nim archive into a
# current nargo build would silently change the meaning of recorded I/O.
{ pkgs }:
let
  compilerRev = "875ee4855112922d4526c5f3e97448386dfc76f6";
  writerRev = "051efd22b00ec3b88676fb07755a65c5a4ca8fde";
  formatRev = "1eae5894ce97001f4b013e50767cc2243a1ed47f";
  compiler = pkgs.fetchFromGitHub {
    name = "noir-fixture6-source";
    owner = "metacraft-labs";
    repo = "noir";
    rev = compilerRev;
    hash = "sha256-aRcDabz76KqfWKUYZyx086G168tU68hQRBmmdJ2QskE=";
  };
  writer = pkgs.fetchFromGitHub {
    name = "nim6";
    owner = "metacraft-labs";
    repo = "codetracer-trace-format-nim";
    rev = writerRev;
    hash = "sha256-+3Q3qbwb2/EiLjzLynPGkXLXMwZBLEV8//KD/OIuAaM=";
  };
  stew = pkgs.fetchFromGitHub {
    name = "stew";
    owner = "status-im";
    repo = "nim-stew";
    rev = "1a5d0b99209f50ff055d9b5216849ba0365f8cf5";
    hash = "sha256-OoKTs5Y5ps0oL43benYf3W6j/KerFZ6xAxaf9mGcaOw=";
  };
  results = pkgs.fetchFromGitHub {
    name = "results";
    owner = "arnetheduck";
    repo = "nim-results";
    rev = "b319652e98a198fa881ca70a76754c2dd6f09804";
    hash = "sha256-chvmxuQw7gxRxXelxxBCXHQGk1LXmg63+VysnJhlxmE=";
  };
  formatPackages = builtins.filter (
    package:
    pkgs.lib.hasPrefix "git+https://github.com/metacraft-labs/codetracer-trace-format?" (
      package.source or ""
    )
  ) (builtins.fromTOML (builtins.readFile "${compiler}/Cargo.lock")).package;
  backportHash = builtins.hashFile "sha256" ./backports/fixture-recording-identity.patch;
in
assert
  formatPackages != [ ]
  && builtins.all (
    package:
    package.source
    == "git+https://github.com/metacraft-labs/codetracer-trace-format?rev=${formatRev}#${formatRev}"
  ) formatPackages;
assert pkgs.lib.hasInfix "MetaDatVersion*: uint16 = 6" (
  builtins.readFile "${writer}/src/codetracer_trace_writer/meta_dat.nim"
);
pkgs.rustPlatform.buildRustPackage {
  pname = "noir-fixture-recorder-v6";
  version = "1.0.0-beta.26";
  src = compiler;
  patches = [ ./backports/fixture-recording-identity.patch ];

  cargoLock = {
    lockFile = "${compiler}/Cargo.lock";
    outputHashes = {
      "codetracer_trace_types-0.19.0" = "sha256-ARB3YPYE5VOkbFgCl1x1i5fOIAkiyhtvtrNHg+W5fBE=";
      "codetracer_trace_writer_nim-0.1.0" = "sha256-ARB3YPYE5VOkbFgCl1x1i5fOIAkiyhtvtrNHg+W5fBE=";
      "clap-markdown-0.1.3" = "sha256-2vG7x+7T7FrymDvbsR35l4pVzgixxq9paXYNeKenrkQ=";
      "sancov-0.1.0" = "sha256-D2q3Xtq64fYKIL0W1bXntyIIXsk6015c0fDHVlam/n4=";
      "sancov-sys-0.1.0" = "sha256-D2q3Xtq64fYKIL0W1bXntyIIXsk6015c0fDHVlam/n4=";
    };
  };
  nativeBuildInputs = [ pkgs.nim ];
  RUSTC_BOOTSTRAP = "1";
  GIT_COMMIT = compilerRev;
  GIT_DIRTY = "true"; # The declared identity backport changes the compiler.
  CODETRACER_TRACE_FORMAT_NIM_DIR = writer;
  CODETRACER_TRACE_FORMAT_NIM_SKIP_NIMBLE_INSTALL = "1";
  CODETRACER_TRACE_FORMAT_NIM_EXTRA_PATHS = "${results}:${stew}";

  cargoBuildFlags = [
    "-p"
    "nargo_cli"
    "--bin"
    "nargo"
  ];
  # This package's boundary is the actual CLI and its emitted containers.
  # Upstream's entire compiler workspace is not needed to validate a backport.
  doCheck = false;
  doInstallCheck = true;
  nativeInstallCheckInputs = [
    pkgs.python3
    # nargo locks its dependency cache even when the package has no dependencies.
    pkgs.writableTmpDirAsHomeHook
  ];
  installCheckPhase = ''
    runHook preInstallCheck
    python3 ${./tests/fixture-recording-identity.py} "$out/bin/nargo"
    runHook postInstallCheck
  '';
  postInstall = ''
    mkdir -p "$out/share/noir-fixture-recorder"
    cat > "$out/share/noir-fixture-recorder/provenance.json" <<EOF
    {"compilerRev":"${compilerRev}","traceFormatRev":"${formatRev}","writerRev":"${writerRev}","metaSchema":6,"backportSha256":"${backportHash}","rustcVersion":"${pkgs.rustc.version}","nimVersion":"${pkgs.nim.version}"}
    EOF
  '';
  passthru = {
    inherit compilerRev writerRev formatRev;
    toolchain = { inherit (pkgs) rustc nim; };
  };
}
