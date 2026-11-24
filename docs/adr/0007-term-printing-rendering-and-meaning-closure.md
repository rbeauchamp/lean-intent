# ADR-0007: Term printing, canonicalization, meaning closure, and rendering internals

## Status

Accepted

## Context

The term-printing and rendering stack (`LeanIntent/Print/Printable.lean`, `LeanIntent/Print/Canon.lean`, `LeanIntent/Print/Meaning.lean`, `LeanIntent/Render.lean`, `LeanIntent/Render/Text.lean`) relies on several non-obvious proof-architecture and MetaM environment invariants recorded in comments removed in Wave 1 (all comments from `Print/Printable.lean`, `Print/Canon.lean`, `Print/Meaning.lean`, and `Render.lean`, plus the plain `--` comments and `elaboratesTo` docstring from `Render/Text.lean`).

## Decision

### Non-vacuity of the closed term printer (`LeanIntent/Print/Printable.lean`)

- `Printable` is defined independently of the printer `pr` and proved equivalent to `(pr bare sc e p).isSome` (`pr_isSome_iff`). This rules out a vacuous printer that satisfies `parse_print` by refusing every input, while ensuring nothing outside the closed printable grammar is emitted.

### Binder canonicalization and metadata erasure (`LeanIntent/Print/Canon.lean`)

- Lean generates macro-scoped binder names (`a✝`) that surface syntax cannot write, and terms can shadow earlier binders or collide with root names of constants referenced in the body. `canon` renames only the binders it must. A binder keeps its name when that name is one component the printer can write and neither an enclosing binder nor the first component of a constant in the term has it (`keeps`), so `∀ n : Nat, True` keeps `n` although its body does not use it. Only a binder that cannot keep its name (macro-scoped, shadowing, or colliding with a constant's root) is changed: a `∀` binder with the default annotation whose body does not use its variable becomes `.anonymous` and is printed as an arrow, and any other takes its name without macro scopes when that can be kept, and else the first of `x`, `x_1`, `x_2`, ... that can (`pick`).
- `Expr.mdata` is stripped before printing because Lean's kernel treats `Expr.mdata data e` as definitionally equal to `e` and ignores binder names; `eraseNames_canon` proves canonicalization changes nothing else.

### Meaning closure (`LeanIntent/Print/Meaning.lean`)

- `meaning` reuses `LeanIntent.Cone.RefersTo` / `declRefs` directly rather than duplicating dependency rules: theorem proofs, opaque constant values, and mutual blocks of definitions/theorems/opaques are excluded because Lean's kernel ignores them.
- `refsVia` dispatches on `RefsMode` (`value | eqn (e : Expr) | typeOnly`): `.value` follows `declRefs (.defnInfo v)`, `.eqn t` substitutes a recursive definition's unfolding equation `t` (plus `v.type`) for its compiled body (`mem_refsVia_eqn`), and `.typeOnly` follows `v.type` alone (`mem_refsVia_typeOnly`) while equation discovery is pending (#90).
- `ctor_mem`, `induct_mem`, and `block_mem` prove that when `meaning` succeeds (`.ok out`), every unstopped constructor (`stop k = false`) of an included inductive, the unstopped inductive (`stop v.induct = false`) of an included constructor, and every unstopped member (`stop i = false`) of an included recursor's mutual block is in `out`; `meaning_unknown` and `meaning_fuel` (via `meaning_error` / `Gap.Holds`) prove soundness of both refusal cases, `meaning_within` proves `Within` on success, and `meaning_ok_iff` characterizes completeness (`(∃ out, meaning lookup eqn stop fuel roots = .ok out) ↔ (∀ c, Reach lookup eqn stop roots c → (lookup c).isSome) ∧ Within lookup eqn stop roots fuel`). `collect` tracks visited names in `Std.HashSet Name` and skips stopped or visited names via `nextActive` without consuming fuel, while `meaning` parameterizes `fuel : Nat` (passed from `Render.Text.definitions` using the current loop environment's constant count `env.constants.map₂.foldl (fun k _ _ => k + 1) env.constants.map₁.size + 1`).

### Rendering MetaM invariants (`LeanIntent/Render/Text.lean`)

- **Re-reading `env` on every fixpoint pass**: In `definitions`, `let env ← getEnv` must run inside each iteration of the bounded fixpoint loop because generating unfolding equations (`getUnfoldEqnFor?` / `realizeConst`) mutates the `MetaM` environment by adding equation declarations.
- **Stopping traversal at the record constant and seeding `Meets`/`HoldsOf`**: `recordPart` inserts the record's own constant into `shown` (since its clauses are already printed statement by statement above) and seeds `roots` with `IntentRecord.Meets` and (whenever consequences are non-empty) `Consequence.HoldsOf` so the rendered document defines what meeting a record and holding of a record mean.
- **Matcher elaboration in `elaboratesTo` and typed `RefsMode` (#89, #90)**: Lean compiles each surface `match` expression into a fresh auxiliary matcher constant on every elaboration, so re-elaborating a readable `match` cannot be structurally equal (`Expr.equal`) to the original matcher constant. `elaboratesTo` disables matcher relaxation by default (`allowMatch := false`, used by `printExact`) and compares `e1 := eraseNames (eraseMData e')` against `e2 := eraseNames (eraseMData e)` via `Expr.equal`; only when `allowMatch` and `holdsMatch env e` hold (`Reader.print`, `allowMatch := true`) does it fall back to `equalModuloMatch env e1 e2`, requiring structural equality across non-matcher nodes and allowing differing constants only when both pass `isMatcherCore env` and `Kernel.isDefEqGuarded env {} (.const c1 us1) (.const c2 us2)` (#89). In `definitions`, `RefsMode` (`value | eqn (e : Expr) | typeOnly`) makes the three traversal states explicit in place of the `.sort .zero` sentinel (#90).
- **Public-import and exposure guards in `unfoldEqn`, `definitions`, and `declSection` (#71)**: In `module` files, `unfoldEqn` (alongside `definitions` and `declSection` catching non-exposed recursive definitions exported as `.axiomInfo` via `wasOriginallyDefn` and `isRecursiveDefinition`, and checking `((env.setExporting false).find? c)`) refuses imported recursive definitions whose module lacks `public import`, naming `public import` as the direct remedy and distinguishing missing `public import` from missing `@[expose]` in the defining module (see [`README.md#module-files`](../../README.md#module-files)).
- **Two-phase split**: `LeanIntent.Render` holds only the `meta` syntax/command elaborators, delegating all rendering programs to `LeanIntent.Render.Text` ([ADR-0006](0006-declared-type-coding-and-code-audit-internals.md)).
- **Extension-loading enforcement (#63)**: Every `MetaM` definition in `LeanIntent.Render.Text` and every command elaborator in `LeanIntent.Render` begins with `LeanIntent.asking` or `LeanIntent.askingIn`, while `bareConsts`, `holdsMatch`, `equalModuloMatch`, `kernelReduction`, `kernelIsDefEq`, `recursionKind`, and `importedModule?` require `(_h : LeanIntent.Loaded env)`. Only `stopAt` remains a `READERS` `stateless` exception, backed by Lean `v4.36.0` citations in [ADR-0009](0009-environment-extension-loading-and-reader-guards.md).

## Consequences

- In Wave 1, `Print/Printable.lean`, `Print/Canon.lean`, `Print/Meaning.lean`, and `Render.lean` are cleared to zero comments, and the plain `--` comments and `elaboratesTo` docstring are removed from `Render/Text.lean`, with these decisions documented here alongside `docs/rendering.md`. Remaining docstrings in `Print.lean`, `Print/RoundTrip.lean`, `Print/Term.lean`, `Print/Token.lean`, and `Render/Text.lean` (including `Render/Text.lean`'s module docstring) stay tracked in `tools/comment-ratchet.json` for later drain waves.
