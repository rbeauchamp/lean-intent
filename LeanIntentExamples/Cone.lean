import LeanIntent

/-!
# Cone exclusion on a small environment

The check of `LeanIntent.Cone` reads Lean's environment, which no theorem can name, so its
theorems are stated for every environment lookup. This example applies them to a lookup written by
hand, `env`, which holds five declarations as Lean would store them, with their types and values
cut down to what matters here:

    def impl : Type := Prop          -- the implementation
    def helper : Type := impl        -- a helper written from the implementation
    def cheat : Type := helper       -- an intent record that uses the helper
    def vocab : Type := Prop         -- a predicate written before any implementation
    def honest : Type := vocab       -- an intent record that uses only the predicate

`cheat` names no declaration of the implementation itself, yet the check refuses it, because its
cone reaches `impl` through `helper` (`cheat_refused`); it accepts `honest`, whose cone is `honest`
and `vocab` and holds no declaration of `impl` (`honest_accepted`). Together they show the
procedure is not vacuous: on one environment it accepts one record and refuses another.
-/

namespace LeanIntentExamples.Cone

open Lean LeanIntent.Cone

/-- A definition named `n` of type `Type` whose value is `v`. -/
def defn (n : Name) (v : Expr) : ConstantInfo :=
  .defnInfo { name := n, levelParams := [], type := .sort 1, value := v, hints := .abbrev,
              safety := .safe, all := [n] }

/-- The hand-written environment. -/
def env : Name → Option ConstantInfo
  | `impl => some (defn `impl (.sort 0))
  | `helper => some (defn `helper (.const `impl []))
  | `cheat => some (defn `cheat (.const `helper []))
  | `vocab => some (defn `vocab (.sort 0))
  | `honest => some (defn `honest (.const `vocab []))
  | _ => none

/-- The implementation's declarations: `impl` and everything Lean would name under it. -/
def isImpl : Name → Bool := isImplDecl [`impl]

theorem refersTo_defn {n c : Name} {v : Expr} : RefersTo (defn n v) c ↔ Mentions c v ∨ c = n := by
  simp [defn, RefersTo, Mentions]

/-- `cheat` is refused: its cone reaches `impl`, through `helper`. -/
theorem cheat_refused (fuel : Nat) :
    exclude env declRefs isImpl leanAxioms fuel [`cheat] ≠ none := by
  have hHelper : Reaches env RefersTo [`cheat] `helper :=
    .step (.root (List.mem_singleton.mpr rfl)) rfl (refersTo_defn.mpr (.inl rfl))
  have hImpl : Reaches env RefersTo [`cheat] `impl :=
    .step hHelper rfl (refersTo_defn.mpr (.inl rfl))
  exact exclude_ne_none_of_reaches mem_declRefs hImpl (by decide)

/-- The cone of `honest` is `honest` and `vocab`. -/
theorem honest_cone {c : Name} (h : Reaches env RefersTo [`honest] c) :
    c = `honest ∨ c = `vocab := by
  induction h with
  | root hr => exact .inl (List.mem_singleton.mp hr)
  | step _ hd hr ih =>
    rcases ih with rfl | rfl <;> cases hd <;> simp_all [refersTo_defn, Mentions, or_comm]

/-- `honest` is accepted, given fuel for its two declarations. -/
theorem honest_accepted : exclude env declRefs isImpl leanAxioms 2 [`honest] = none := by
  refine (exclude_eq_none_iff mem_declRefs 2).mpr ⟨fun c hc => ?_, [`honest, `vocab], by decide,
    fun c hc => ?_⟩
  · rcases honest_cone hc with rfl | rfl
    · exact ⟨by decide, _, rfl, by simp [defn, ConstantInfo.isAxiom]⟩
    · exact ⟨by decide, _, rfl, by simp [defn, ConstantInfo.isAxiom]⟩
  · rcases honest_cone hc with rfl | rfl <;> simp

end LeanIntentExamples.Cone
