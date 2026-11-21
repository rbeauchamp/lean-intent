# ADR-0002: Test listing (`--tests`), subprocess isolation, and pinned Lean v4.35.0 token audit

## Status

Accepted

## Context

`lean-intent` forbids tests as correctness evidence (`.no-mistakes.yaml`, `test.tests_as_evidence.policy: forbid`). A test is code whose verdict comes from running code on chosen inputs rather than from a proof or type-check over every input. The validation pipeline needs a deterministic listing of every test command in the repository (`lean --run tools/check.lean --tests`), returning empty output with exit `0` when none exist and failing loudly whenever a file cannot be analyzed.

## Decision

### Pinned Lean release and token classification (`testsLean := "4.35.0"`)

`--tests` refuses to run under any Lean release other than `testsLean` (`"4.35.0"`), because its token classification is audited directly from that release's elaborators and token table:

- **Audit provenance (v4.34.1 → v4.35.0)**: Lean 4.35.0's token table (with `Lean`, `Lake`, and `Std` imported) contains the same 29 tokens starting with `#` followed by a letter as 4.34.1. Across `Lean.Elab`, `Lean.Meta`, `Std`, and `Lake`, calls to `evalTerm`, `evalExpr`, `evalConst`, and `Meta.nativeEqTrue` differed from 4.34.1 only by one moved declaration, `constructor` tactic configuration evaluation, and removal of `Meta.reduceBoolNative` / `Lean.reduceBool`.
- **`testTokens`** (16 tokens):
  - Evaluators (`evalTerm`, `evalExpr`, `evalConst`, `Meta.nativeEqTrue`) whose verdict decides pass/fail on chosen inputs: `#eval`, `#eval!`, `#guard`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `by_elab`, `test_extern`, `native_decide`.
  - Output/tactic/simp checkers on chosen inputs: `#guard_msgs`, `#guard_panic`, `#guard_expr`, `#check_simp`, `#check_tactic`, `#check_tactic_failure`.
- **Deliberate exclusions**: constructs that evaluate code to an end other than a test verdict (`include_str` path, `#widget`, tactic configuration values, `idbg`, `dbg_trace` which runs only at runtime) and `bv_decide` / `bv_check` (which prove universal goals via certificate checkers and whose added axiom `AXIOMS` rejects).
- **`otherTokens`** (20 tokens): the remaining `#<alpha>` tokens of Lean 4.35.0 — type-check verdicts (`#check`, `#check_failure`, `#check_assertions`, `#synth`, `#reduce`), printers/reporters (`#print`, `#where`, `#version`, `#exit`, `#import_path`, `#show_deprecated_modules`, `#dump_async_env_state`, `#discr_tree_key`, `#discr_tree_simp_key`, `#grind_lint`), command wrappers (`#time`, `#info_trees`, `#with_exporting`), `#widget`, and `#v[`.
- **Fail-closed allowlist**: any token starting with `#` followed by a letter that appears in neither `testTokens` nor `otherTokens` raises an error rather than passing unclassified.
- **`nativeConfig`**: conservatively flags any `decide` configuration item setting `native`, `+native`, or `(native := v)`, as well as any `decide` carrying `(config := c)`, because Lean evaluates `c` into the entire `DecideConfig` struct (including `native`, which routes `decide` through `Meta.nativeEqTrue`).
- **Project-declared elaborators**: any command whose elaboration info tree invokes a project-declared elaborator other than a `Macro` is listed as a test. A `lakefile.toml` `testDriver` is listed as a test too.

### Execution architecture

- **Topological order and subprocess isolation**: `projectTests` reads each file's imports via `Parser.parseHeader`, sorts tracked Lean files topologically (failing on import cycles or empty file lists), and runs `--tests-module <file> <out>` in a fresh child process per file so no module's elaborated `Environment` stays resident in memory while the next file is elaborated (keeping peak memory ~4.76 GiB). Each child writes its `.olean` to a temporary directory removed in `finally`.
- **Sidecar output channel**: `moduleTests` writes each file's test lines to a per-module `.tests` file inside the temporary directory, and `projectTests` reads those files rather than child stdout, because elaborated project commands may print arbitrary text to stdout.
- **Why `main` is `unsafe`**: `--tests-module` and `--comments-module` invoke Lean's `unsafe enableInitializersExecution` so imported modules run their `initialize` declarations and populate environment extensions (parser tables and elaborator extensions). `Check.check`, `projectTests` and the comment inventory (`--comments`) themselves remain safe (non-`unsafe`): each reaches those modes only by running them in child processes (`--comments-module` for `NO-COMMENTS` and `--comments`, `--tests-module` for `projectTests`), as `checkCodes` runs `tools/codes.lean`.
- **Stable line keys (`syntaxKey`).** Each test line encodes `<quoted path> <occurrence-index> <syntaxKey>`. The key records syntax node kinds and children, atom values and identifier names. It omits `SourceInfo`, including positions, whitespace, line comments and plain block comments stored there. Declaration and module docstrings contribute their parsed syntax. Lean's plain-text parser stores the body in an atom. When Verso is enabled for that docstring, Lean parses the body into document syntax and the key encodes that tree recursively. An edit that changes only source information leaves the key unchanged in either mode. See `Lean/Parser/Term.lean` (`docComment`, `commentBody`, `versoCommentBodyFn`) and `Lean/Parser/Command.lean` (`moduleDoc`) at the pinned release.

## Known limitations and consequences

- Kernel-checked `theorem`/`example` declarations on concrete inputs (e.g. `example : f 3 = 9 := by decide`) are not listed; avoiding value-pinning examples is tracked in #83.
- `testsOfModule` currently sets `debug.byAsSorry true` so `Prop`-typed `by` blocks are not elaborated; macros or project-declared tactic elaborators inside `by` blocks are therefore not expanded or inspected (tracked in #94).
- Project-declared deriving handlers are not elaborators and their generated commands use Lean's own elaborators, so `deriving` clauses are not listed (the library's `LeanIntent.Declared` handler generates kernel-checked code and isomorphisms).
