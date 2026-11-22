# ADR-0001: Repository checks (`tools/check.lean`, `tools/codes.lean`) and trusted base

## Status

Accepted

## Context

`lean-intent` establishes its claims about itself by machine-checked theorems rather than tests, and enforces repository-wide invariants through one check program (`tools/check.lean`) paired with a helper executable (`tools/codes.lean`). Every input must be read through the system that owns it rather than by parsing source text by hand.

## Decision

### Invocation and module-file conventions

- `tools/check.lean` runs from the repository root as `lean --run tools/check.lean [--base-ref <ref>]` (all rules), `lean --run tools/check.lean --tests` (test listing; see [ADR-0002](0002-test-listing-and-pinned-lean-tokens.md)), or `lean --run tools/check.lean --comments [<file>]` (comment inventory delegated to the pinned `no-comments` binary; see [ADR-0004](0004-ratcheted-ban-on-lean-comments.md)), where `lean` is elan's shim selecting the toolchain named by `lean-toolchain`.
- It is not invoked through `lake env`, so that it reads and validates `lakefile.toml` before Lake loads the workspace.
- Both `tools/check.lean` and `tools/codes.lean` are Lean `module` files (satisfying `LEAN-MODULE`). Each declares `main` as `public` (`public unsafe def main` in `tools/check.lean`, see [ADR-0002](0002-test-listing-and-pinned-lean-tokens.md); `public def main` in `tools/codes.lean`), since a `module` file's declarations are private unless marked, and imports each library whose programs `lean --run` executes a second time with `meta import` (`Lake` and `Lake.Load.Package` in `tools/check.lean`; `LeanIntent.CodeAudit` in `tools/codes.lean`), because Lean loads compiled code for `lean --run` only where an import carries `meta`.
- `tools/check.lean` exits `0` when every rule holds and `1` when any rule rejects (printing `[RULE] message` lines to stdout). Uncaught errors print to stderr and also exit `1`.

### Owning-system inputs

Every input to `tools/check.lean` is read through its owning system:

- Tracked Lean files: Git's index (`git ls-files -z -- '*.lean'`); library files are those outside `tools/`.
- Project configuration: Lake's TOML parser (`Lake.Toml.loadToml`) and loader (`Lake.loadPackage` with `configLang? := some .toml`), which loads `lakefile.toml` without resolving dependencies and therefore runs no code of the project.
- Selected library modules: Lake's `Lake.LeanLib.getModuleArray`, reading each target's globs over the working tree as a build does.
- Module names, headers, and builds: Lean's `moduleNameOfFileName` and `Parser.parseHeader`, and `lake build --wfail`.
- Comment inventory: the pinned compiled `no-comments` CLI (`rbeauchamp/lean-no-comments` `v0.2.0`, SHA-256-verified against `tools/no-comments.pin` and configured by `.no-comments.json`), which inspects every tracked Lean file through Lean's frontend in isolated native child processes against Lake's workspace/tool setup and resolves Git's merge base of `HEAD` with `--base-ref <ref>` or `origin/main` / `main` ([ADR-0004](0004-ratcheted-ban-on-lean-comments.md)).
- Axioms: Lean's `collectAxioms` over the imported environment of the built library modules.
- Compiled code call graph: Lean's `Lean.IR.findEnvDecl` and `Lean.IR.collectUsedDecls` ([ADR-0003](0003-runtime-process-audit-and-exemptions.md)).
- Declared-type code attestations: `LeanIntent.CodeAudit.audit` run via `tools/codes.lean` in a subprocess with `LEAN_PATH` set to Lake's library build directory (because `tools/check.lean` is not itself built against the library).

### Check rules

- **`LAKE-CONFIG`**: `lakefile.toml` sets only `name`, `defaultTargets`, `leanOptions` (as a table with only `autoImplicit` and `relaxedAutoImplicit`), and `lean_lib` (as an array of tables with only `name`, `roots`, and `globs`), and no `lakefile.lean` exists. In `configExtraKeys`, a non-table `leanOptions`, a non-array `lean_lib`, or a non-table `lean_lib` entry counts as a disallowed key; checking the shapes of the remaining leaf values (`name`, `defaultTargets`, the allowed `leanOptions` values, and `lean_lib` entry values `name`, `roots`, `globs`) is left to Lake's `loadPackage`. This ensures zero external package dependencies and no project code execution during Lake configuration.
- **`LEAN-BUILD`**: The modules selected by Lake's library targets must be identical to the modules of the tracked library files, every target must select at least one module, and `lake build --wfail` must build every library file with zero errors and zero warnings (`sorry` produces a warning). Refuses untracked selected modules, unselected tracked library files, and empty library file lists.
- **`LEAN-MODULE`**: Every tracked Lean file (`tools/` included) must begin with `module` as parsed by `Parser.parseHeader` (`Elab.HeaderSyntax.isModule`), so a downstream project's `module` file can import any library module. A header parse error is a hard error.
- **`AXIOMS`**: No library module declares an axiom, and every constant declared by a library module depends only on Lean's three axioms (`propext`, `Classical.choice`, `Quot.sound`), ruling out `sorryAx`, `native_decide`, and custom axioms. Fails if the library declares no constants.
- **`PROCESS`**: Compiled library code reaches no monitored process/environment runtime C function except through the exempted `Lean.manualRoot` ([ADR-0003](0003-runtime-process-audit-and-exemptions.md)).
- **`CODES`**: Every declared constant across all library modules (worked examples included) passes `LeanIntent.CodeAudit.audit` via `tools/codes.lean`. Fails if no constants are declared.
- **`NO-COMMENTS`**: `tools/no-comments.pin`, `.no-comments.json`, and `tools/comment-ratchet.json` are regular files in the working tree, every tracked Lean file holds exactly the comments recorded by fingerprint and distinct line count in `tools/comment-ratchet.json` (none where no entry exists), and `tools/comment-ratchet.json` records no new/modified comment fingerprint or increased line count relative to the merge base's manifest (invoking `no-comments check` without `--bootstrap` now that `tools/comment-ratchet.json` is committed on `main`, failing closed whenever no merge base can be located; [ADR-0004](0004-ratcheted-ban-on-lean-comments.md)).

### `tools/codes.lean` exit-code protocol

`tools/codes.lean` distinguishes audit refusal from runner failure using three exit codes:

- `0`: audit accepted every constant (prints nothing).
- `1`: audit refused one or more declarations, or the given modules declared zero constants (an empty audit would accept vacuously), printing one refusal line per reason to stdout.
- `2`: runner error (bad arguments, import failure, audit exception, or I/O error). Because Lean exits with status `1` when an uncaught exception escapes `main` — which `tools/check.lean` would misinterpret as an audit refusal — `tools/codes.lean` wraps its entire `main` in `try ... catch` (including catching errors from `IO.eprintln`) and returns `2` on any exception.

## Trusted base and consequences

- The rules read what the build produced, so they hold only if no build-time metaprogram was written to defeat them: elaborating a Lean file executes any metaprograms it invokes.
- Keeping `tools/check.lean` independent of the built library avoids bootstrap cycles at the cost of spawning `tools/codes.lean` as a child process for `CODES`.
- `NO-COMMENTS` trusts the SHA-256-verified `rbeauchamp/lean-no-comments` `v0.2.0` binary pinned in `tools/no-comments.pin` (verified on both `NO_COMMENTS_BIN` overrides and `.lake/cache/no-comments/<sha256>/no-comments`), preserving `LAKE-CONFIG` (zero external Lake package dependencies in `lakefile.toml`).
