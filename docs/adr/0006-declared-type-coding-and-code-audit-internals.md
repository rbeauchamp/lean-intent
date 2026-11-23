# ADR-0006: Declared-type coding, two-phase module split, handler internals, and code audit

## Status

Accepted

## Context

The declared-type coding pipeline spans `LeanIntent/Codes.lean`, `LeanIntent/Clocks.lean`, `LeanIntent/Declared.lean`, `LeanIntent/Declared/Handler.lean`, and `LeanIntent/CodeAudit.lean`. Several non-obvious module-system, kernel-reduction, security, and performance decisions were carried in inline `--` comments, drained comments from `Declared.lean`, and docstrings scheduled for removal.

## Decision

### Two-phase `meta` vs non-`meta` module split

- Under Lean's module system, a `meta` declaration can only be called by another `meta` declaration.
- The deriving handler (`LeanIntent/Declared/Handler.lean`) and rendering engine (`LeanIntent/Render/Text.lean`) must run both at elaboration time (via `meta initialize` / command elaborators) and post-build as ordinary programs (called by `LeanIntent.CodeAudit` and the post-build check readers).
- Therefore the implementations live without `meta` in `LeanIntent.Declared.Handler` and `LeanIntent.Render.Text`, while `LeanIntent.Declared` and `LeanIntent.Render` import them with `meta import` solely to register the deriving handler and elaboration commands.

### Recursive-group encoding and exhaustive path matching

- In `LeanIntent/Codes.lean`, a recursive group's `g` parameter encodes field data and argument types at fixed paths: `[j, c, 0]` holds the chain of non-recursive data fields for type `j`, constructor `c`; `[j, c, 1, f]` holds the argument domain type for recursive field `f`.
- In `LeanIntent/Declared/Handler.lean`, `r` holds only group type indices (`Ty.ref l`) and no field or parameter codes, so Lean's kernel (`Kernel.isDefEq`) decides `Ty.inhabited`, `Ty.grows`, and `Ty.growsAt` uniformly even under free type-parameter variables or metavariables.
- In `LeanIntent/Clocks.lean`, `Ty.paths` matches every constructor of `Ty` with no catch-all branch so that adding a new code former to `Ty` causes a compile-time exhaustiveness failure until its component paths are specified.

### Attestation auditing (`checkAttestation`, `checkRecMaps`, `builtinHeads`)

- **Dynamic `builtinHeads` discovery**: `builtinHeads` reads `Ty` and `Atom` constructors from Lean's environment, computes their kernel WHNF denotation heads via `Kernel.whnf` (which works identically during elaboration and in extensionless `importModules` audit scripts), and classifies non-inductive results against an explicit closed allowlist (`Ty.decl` and `Ty.atom` verified via `Kernel.isDefEq`, `Ty.arrow` as a forall type, and `Ty.muAt` checking that both branches of its `Bool.rec` conditional reduce to inductive heads), failing closed with an error on any unrecognized constructor denotation so attestations cannot assign a second code to any built-in type or a definition reducing to one.
- **Unifier for discovery, kernel for trust**: `checkAttestation` uses fresh metavariables and Lean's unifier only to discover candidate `HasCode` instances, then validates the attested type, derived code, and forward constructor images exclusively via Lean's kernel (`Kernel.isDefEq`). Only the forward map of an `Iso` is compared, because an isomorphism's forward map uniquely determines its inverse.
- **Untrusted candidate lookup for mutual group maps**: Inside `checkAttestation`, looking up `ci.name.modifyBase (·.getPrefix ++ Name.mkSimple s!"to{l}")` supplies only a candidate hint for sibling types in a recursive group (preserving macro scopes on base names); acceptance is decided solely by kernel-checked constructor equations in `checkRecMaps`.
- **Self-audit at derivation time**: `LeanIntent/Declared/Handler.lean` runs `checkAttestation` immediately after elaborating each derived `HasCode` instance so the deriving handler never emits an attestation that `LeanIntent.CodeAudit` would later refuse.

### Reduction, extensionless-environment, scope, and naming internals

- **`whnf` → `Kernel.whnf` fallback in `checkRecMaps`**: MetaM `whnf` can stop short of reducing a recursive map applied to a constructor to `MuVal.base`/`MuVal.node` when a recursive field is a function; `checkRecMaps` falls back to `Kernel.whnf` in that case.
- **Manual `Nat.decLt` proof construction**: `checkRecMaps` constructs `r < A` proofs directly via `of_decide_eq_true (Nat.decLt ...)` with `mkApp` instead of typeclass synthesis, keeping the proof term independent of instances offered by the environment (`tools/codes.lean` now calls `enableInitializersExecution` before `importModules ... (loadExts := true)` per #63 so `CodeAudit.isCarrier` reads loaded instance and class extensions).
- **Extension-loading and carrier enforcement (#63)**: `CodeAudit.audit` begins with `LeanIntent.askingIn`, `isCarrier`, `diagnosticType`, and `requireCodes` begin with `LeanIntent.asking`, and `axiomsIn` requires `LeanIntent.Loaded env`. `CodeAudit.isCarrier` checks Lean's default-instance registrations for `HasCode` and `Covered` (`Lean.Meta.getDefaultInstances`, reading `defaultInstanceExtension`) as well as ordinary instance registration (`Lean.Meta.isInstance`, reading `instanceExtension`) and semantic class recognition (`Lean.Meta.isClass?`, reading `classExtension`) under `withoutExporting`, specified together in `isCarrier_eq`, so non-instance definitions of class type and non-class registered instances are both excluded while `@[default_instance]` carriers are included. Only `relevantIn`, `importers`, `generatedBy`, and `instMonadEnvEnvM` remain `READERS` `stateless` exceptions, backed by Lean `v4.36.0` citations in [ADR-0009](0009-environment-extension-loading-and-reader-guards.md).
- **Namespace-relative naming (`relIdent`) across generated commands (#72)**: `relIdent` (`Name.modifyBase (·.replacePrefix ns .anonymous)`) replaces `_root_ ++ ...` across `mkStandsAndInstance`, `mkRecHasCode` (`let rel := relIdent ns`), and `mkHasCode` (`isoName`) so generated instances, mutual definitions, and theorems resolve relative to the current namespace while preserving macro scopes on macro-declared types.
- **Recursive equation realization (`getEqnsFor?` and `mkEqIdent`, #72)**: Instead of naming `_root_ ++ toName k ++ s!"eq_{c.alt}"` or rewriting with `rw [to{k}]`, `mkRecHasCode` realizes each `act (toName k)`'s equation theorems via `Lean.Meta.getEqnsFor?` inside `withoutExporting` (covering private definitions in `module` files) and references `eqs[c.alt - 1]?` through `mkEqIdent` (an `_internal`/`eqLemma` macro-scoped `Syntax.ident` carrying `[.decl c []]` preresolution) in both `invToDefs` and `toInvAlts`.
- **Section scope isolation (`handler`, #73)**: `handler` clears `varDecls`, `varUIds`, `includedVars`, `omittedVars`, and `levelNames` inside `withScope` so enclosing section `variable`, `include`, `omit`, and `universe` declarations do not alter generated definitions, theorems, or instances.

### Linear-time lazy reverse-dependency collection (`LeanIntent/CodeAudit.lean`)

- In `CodeAudit.audit`, reverse dependencies (`dependents`) are needed only to report carriers of refused attestations. They are therefore computed lazily (`unless refused.isEmpty`), deduplicating each declaration's outgoing references with a per-declaration `Std.HashSet` (`once`) and prepending to `List`s (`c :: ...`) instead of copying `Array`s, keeping collection linear in the number of reached references (preventing the stall observed in #59).

## Consequences

- In Wave 1, `Declared.lean` is cleared to zero comments and inline `--` comments and stale pre-#50/#55 docstrings are deleted from `Declared/Handler.lean`, `CodeAudit.lean`, `Codes.lean`, and `Clocks.lean`, preserving each non-obvious kernel/MetaM invariant and performance choice here; the remaining docstrings in those four files stay tracked in `tools/comment-ratchet.json` for later drain waves. For #63, `CodeAudit.lean`'s module docstring (`8–96`) and `isCarrier` / `isCarrier_eq` docstrings (`284–286`, `291–293`) were also drained (lowering `CodeAudit.lean` from `33` comments / `175` lines to `30` comments / `80` lines) when `isCarrier` was updated to check `isInstance` alongside `isClass?`, with their rationale preserved in [`docs/degenerate-subjects.md`](../degenerate-subjects.md), this ADR, and [ADR-0009](0009-environment-extension-loading-and-reader-guards.md).
