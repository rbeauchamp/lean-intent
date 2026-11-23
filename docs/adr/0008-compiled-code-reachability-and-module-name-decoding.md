# ADR-0008: Compiled-code `_redArg` allowlist and closed-form module-name decoding

## Status

Accepted

## Context

Two verification readers bridge compiled Lean/Lake artifacts into pure proved decision procedures: `LeanIntent/Execution/Code.lean` identifies which compiler-generated IR declarations count as an implementation's compiled code, and `LeanIntent/Required/ModuleName.lean` decodes module names printed by `lake query --json`. Both rely on exact Lean v4.36.0 source properties that must be re-verified on toolchain upgrades (#80).

## Decision

### Compiled-code allowlist (`LeanIntent/Execution/Code.lean`)

- `isCompiledCodeOf isConst impl d` counts only `impl` itself and declarations `d` not present as constants in the environment (`!isConst d`) whose name is formed by appending `_redArg` to a compiled copy of `impl`.
- **Lean v4.36.0 compiler provenance**:
  - `Lean/Compiler/LCNF/ReduceArity.lean` (lines 156–205, specifically lines 172 and 197): when a declaration has unused parameters (such as erased type or proof parameters kept by `ToMono.lean` lines 139 and 393), reduce-arity emits a copy named `<decl>._redArg` and turns `<decl>` into an `@[inline]` wrapper calling it. A caller that gives the wrapper all its parameters may then call only the copy, having inlined the wrapper, while one that applies it to fewer keeps a closure of `<decl>` itself, since the simplifier that runs after reduce-arity inlines no partial application (`Lean/Compiler/LCNF/Passes.lean` lines 128–130, `Lean/Compiler/LCNF/Simp/Config.lean` line 31, `Lean/Compiler/LCNF/Simp/InlineCandidate.lean` lines 99–100); both run `<decl>`'s code and both are counted. Line 172 is the single site producing `_redArg` names.
  - Rejecting environment constants (`isCompiledCodeOf_const`) prevents a user declaration named `impl._redArg` from spoofing compiled code.
- **Deliberately excluded compiler artifacts** (documented remedies live in `docs/execution.md`):
  - Extracted closed terms `c._closed_i` (`Lean/Compiler/LCNF/ExtractClosed.lean`, lines 216–233): cached and shared across unrelated declarations, so reaching one does not establish running `c`.
  - Lifted lambdas from inlined `c`: reached only when callers inline `c`.
  - Specializations `c._at_.caller.spec_i` (`Lean/Compiler/LCNF/Specialize.lean`, lines 30 and 315–318): origin metadata lives in a module-private compiler cache that `lean-intent` does not read (remedy: `@[nospecialize]`, `Lean/Compiler/LCNF/SpecInfo.lean` lines 197–198).

### Closed-form ASCII module-name decoding (`LeanIntent/Required/ModuleName.lean`)

- `Required.moduleName?` accepts only dot-separated segments where each segment begins with an ASCII letter followed by ASCII letters, digits, `_`, or `'`, and fails on every other string.
- **Why general decoding of `Lean.Name.toString` is unsafe**: `escapePart` (`Init/Data/ToString/Name.lean`, lines 55–64 at Lean v4.36.0) wraps components containing `.` in `«...»` while leaving components that already contain `»` untouched, so the single-component names `a.b` and `«a.b»` both print as `«a.b»`. A lenient decoder could map a built module name to an unbuilt module and pass with exit `0`.
- Restricting to the closed ASCII form makes decoding provably injective (`moduleName?_inj`), while projects with non-ASCII or escaped module names pass `Lake.Module` names directly via Lake's API instead of `queryModules`.

### Bounded reachability worklist and `Stored` isolation (`LeanIntent/Execution/Read.lean`)

- `Execution.Read.buildTable` builds the finite reachability table for `reachesIn` by structural recursion over a fuel bound (`s.constCount + 1`, where `LeanIntent.Imported.Stored.constCount` reads `env.const2ModIdx.size`), returning `none` if fuel expires with non-empty work (so `reachesIn` fails closed with an error rather than returning a truncated table; `Environment.getModuleIdxFor?` is unexposed in Lean's module system, so relating `inCone` directly to `s.constCount` is left outside the module proof).
- Whenever `buildTable` returns `some table`, `buildTable_within` and `buildTable_within_succ` prove `Execution.Within (fun n => table.getD n []) root table.size` and `table.size + 1`, `buildTable_reach_eq_reached_iff` proves `Execution.reach` with `table.size + 1` fuel agrees with `Execution.Reaches`, and `buildTable_reach_ne_exhausted` rules out `.exhausted`, eliminating the unreachable `.exhausted` branch in `reachesIn`.
- Per #63 ([ADR-0009](0009-environment-extension-loading-and-reader-guards.md)), `irRefs`, `importersOf`, `reachesIn`, and `executableIn` operate solely on `LeanIntent.Imported.Stored` (`Except String ...`) rather than threading an `Environment`, and `importedModuleOf` is removed; `Execution.Read.check` passes `← LeanIntent.Imported.stored root (← getOptions)` while guarding its own `MetaM` entry points (`nameLit`, `claimOf`, `claims`, `check`) with `LeanIntent.asking`.

## Consequences

- Toolchain upgrades (#80) must re-check `ReduceArity.lean` line 172 and `Init/Data/ToString/Name.lean` lines 55–64.
- Distinguishing dependency packages via `Environment.getModulePackageByIdx?` is tracked in #78.
