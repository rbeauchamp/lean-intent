# Cone exclusion

**Cone exclusion** (`LeanIntent.Cone.checkRecord`): a decision procedure, with a theorem stating what it decides, that refuses an intent record whose meaning depends on a declaration of its implementation, read from Lean's own environment.

Module: `LeanIntent/Cone.lean`.

**Complete in this version:** cone exclusion with the theorem stating what it decides.

A record written from the code proves nothing about intent: the property `fun f => f = impl` is met by `impl` whatever the owner meant. `LeanIntent.Cone.checkRecord env record impl` reads, from the environment `env`, the declarations that the meaning of the record declared as `record` depends on, transitively, and refuses the record when one of them is a declaration of the implementation: a name the list `impl` gives, or a declaration Lean names under one of them, as it names the auxiliary declarations it makes for a declaration `f` (`f.match_1`, `f._unary`, `f.eq_1`) and a `where` helper (`f.go`). A dependency reached through any declaration, an instance or an auxiliary declaration Lean generates included, is found. `LeanIntent.Cone.requireIndependent` runs the check in `CoreM` and throws an error that says why it refuses.

`checkRecord_eq_ok_iff` states what it decides, for every environment, record and implementation: it accepts exactly when `impl` names at least one declaration and every name it gives is declared, and every name reached from the record is no declaration of the implementation, is declared, and is no axiom other than Lean's three (`propext`, `Classical.choice`, `Quot.sound`), with at most `2 ^ 64` names reached, more than the declarations that fit in a 64-bit address space. A record that depends on any other axiom is refused. `checkRecord_ne_ok_of_reaches` states that a record whose cone reaches a declaration of the implementation is refused, and `exclude_eq_some` states that each refusal names a reached name that fails one of these tests, or that more names are reached than its fuel, `2 ^ 64` in `checkRecord`.

It follows every declaration's type, every definition's value, an inductive type's mutual block, constructors and recursors (`I.rec`, and, for a block with nested occurrences, the recursors `b.rec_1`, `b.rec_2` and so on that Lean names after the block's first type `b`), a constructor's inductive type, and a recursor's mutual block and rules, but not a theorem's proof or an opaque constant's value: Lean's kernel never unfolds an opaque constant, and with definitional proof irrelevance any two proofs of a proposition are equal, so neither changes what the record means. Nor does it follow the mutual block of a definition, theorem or opaque constant, which Lean's kernel does not read; since Lean may compile mutually recursive definitions into one helper named under only one of them (`f._mutual` for `f` and `g`), name every member of such a block as the implementation's. It refuses rather than accepts when it cannot read the whole cone: a reached name with no declaration, or a reached axiom other than Lean's three. In a module of Lean's module system, an imported theorem, and an imported definition whose body is not exposed, are shown as axioms, so run the check where every module is imported in full, such as in a file outside the module system. A property that restates the implementation's body without naming it passes the check; it reaches the owner as "the output is computed exactly as this expression", and noticing that is left to the owner's confirmation.

## Worked examples

- [`LeanIntentExamples/Cone.lean`](../LeanIntentExamples/Cone.lean): on a small environment written by hand, cone exclusion refuses a record that reaches the implementation through a helper (`cheat_refused`) and accepts one that does not (`honest_accepted`).

## What is trusted

- That a record was written before its implementation was read. That it does not depend on its implementation is decided by cone exclusion against the declarations the caller names; that those names, with the declarations Lean names under them, cover the implementation, every member of a block of mutually recursive definitions included, is trusted.
- That Lean's compiler runs cone exclusion as it is defined, and that `Environment.find?` returns the declarations Lean's kernel checked: cone exclusion's theorems are about its definitions.
