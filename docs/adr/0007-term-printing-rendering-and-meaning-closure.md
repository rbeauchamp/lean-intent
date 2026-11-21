# ADR-0007: Term printing, canonicalization, meaning closure, and rendering internals

## Status

Accepted

## Context

The term-printing and rendering stack (`LeanIntent/Print/Printable.lean`, `LeanIntent/Print/Canon.lean`, `LeanIntent/Print/Meaning.lean`, `LeanIntent/Render.lean`, `LeanIntent/Render/Text.lean`) relies on several non-obvious proof-architecture and MetaM environment invariants that were previously recorded in comments.

## Decision

### Non-vacuity of the closed term printer (`LeanIntent/Print/Printable.lean`)

- `Printable` is defined independently of the printer `pr` and proved equivalent to `(pr bare sc e p).isSome` (`pr_isSome_iff`). This rules out a vacuous printer that satisfies `parse_print` by refusing every input, while ensuring nothing outside the closed printable grammar is emitted.

### Binder canonicalization and metadata erasure (`LeanIntent/Print/Canon.lean`)

- Lean generates macro-scoped binder names (`a✝`) that surface syntax cannot write, and terms can shadow earlier binders or collide with root names of constants referenced in the body. `canon` renames only the binders it must. A binder keeps its name when that name is one component the printer can write and neither an enclosing binder nor the first component of a constant in the term has it (`keeps`), so `∀ n : Nat, True` keeps `n` although its body does not use it. Only a binder that cannot keep its name (macro-scoped, shadowing, or colliding with a constant's root) is changed: a `∀` binder with the default annotation whose body does not use its variable becomes `.anonymous` and is printed as an arrow, and any other takes its name without macro scopes when that can be kept, and else the first of `x`, `x_1`, `x_2`, ... that can (`pick`).
- `Expr.mdata` is stripped before printing because Lean's kernel treats `Expr.mdata data e` as definitionally equal to `e` and ignores binder names; `eraseNames_canon` proves canonicalization changes nothing else.

### Meaning closure (`LeanIntent/Print/Meaning.lean`)

- `meaning` reuses `LeanIntent.Cone.RefersTo` / `declRefs` directly rather than duplicating dependency rules: theorem proofs, opaque constant values, and mutual blocks of definitions/theorems/opaques are excluded because Lean's kernel ignores them.
- `refsVia` substitutes a recursive definition's unfolding equation (plus its type) for its compiled body so collected definitions reflect what the rendered equation mentions.
- `ctor_mem`, `induct_mem`, and `block_mem` prove that when `meaning` succeeds (`.ok out`), every unstopped constructor (`stop k = false`) of an included inductive, the unstopped inductive (`stop v.induct = false`) of an included constructor, and every unstopped member (`stop i = false`) of an included recursor's mutual block is in `out`; `meaning_unknown` proves the one-way soundness of an unknown-name refusal (any name reported in `.error (.unknown c)` is reachable and missing in `lookup`, while `collect` returns the first missing name it encounters immediately). Replacing the hardcoded `2 ^ 64` worklist fuel and O(n) membership scan in `collect` is tracked in #88.

### Rendering MetaM invariants (`LeanIntent/Render/Text.lean`)

- **Re-reading `env` on every fixpoint pass**: In `definitions`, `let env ← getEnv` must run inside each iteration of the `repeat` loop because generating unfolding equations (`getUnfoldEqnFor?` / `realizeConst`) mutates the `MetaM` environment by adding equation declarations.
- **Stopping traversal at the record constant and seeding `Meets`/`HoldsOf`**: `recordPart` inserts the record's own constant into `shown` (since its clauses are already printed statement by statement above) and seeds `roots` with `IntentRecord.Meets` and (whenever consequences are non-empty) `Consequence.HoldsOf` so the rendered document defines what meeting a record and holding of a record mean.
- **Matcher elaboration in `elaboratesTo`**: Lean compiles each surface `match` expression into a fresh auxiliary matcher constant on every elaboration, so re-elaborating a readable `match` cannot be structurally equal (`Expr.equal`) to the original matcher constant. Confining the `Kernel.isDefEqGuarded` fallback (and disabling it in `printExact`) is tracked in #89; replacing the `.sort .zero` (`Prop`) sentinel in `definitions` with a typed 3-way mode is tracked in #90.
- **Two-phase split**: `LeanIntent.Render` holds only the `meta` syntax/command elaborators, delegating all rendering programs to `LeanIntent.Render.Text` ([ADR-0006](0006-declared-type-coding-and-code-audit-internals.md)).

## Consequences

- Printing, canonicalization, and rendering internals are documented in one place alongside `docs/rendering.md`, without inline comments in `Print/` or `Render/Text.lean`.
