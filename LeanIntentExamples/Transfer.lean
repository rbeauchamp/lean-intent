import LeanIntent

/-!
# What a refinement link does not carry

Refutability and determinacy at the intent record do not make a refining specification refutable
or determinate: the record's guarantee holds of the mapping's image, not of the implementations
themselves. Take the record over `Nat` with the one property `n = 0`, the specification
`fun _ => True` over `Bool`, and the mapping sending every boolean to `0`. The link holds (`link`),
the record meets O3 and O5 with equality (`isZero_o3`, `isZero_o5_eq`), and yet the specification
has no counterexample (`spec_not_refutable`) and two distinct implementations meet it
(`spec_not_determinate`): no counterexample to the record lies in the image.
-/

namespace LeanIntentExamples.Transfer

open LeanIntent

/-- The record over `Nat` whose one property is `n = 0`. -/
def isZero : IntentRecord Nat where
  shape := .value Nat
  dom := []
  props := [⟨"is zero", fun n => n = 0⟩]
  vocab := []

/-- The specification that says nothing. -/
def spec : Bool → Prop := fun _ => True

/-- The mapping that reads every boolean as `0`. -/
def toZero : Bool → Nat := fun _ => 0

theorem isZero_props {n : Nat} : isZero.Props n ↔ n = 0 := by
  simp [IntentRecord.Props, isZero]

theorem link : Refines isZero toZero spec :=
  fun _ _ _ => isZero_props.mpr rfl

theorem isZero_o3 : O3 isZero := by
  refine (o3_correct _).mpr fun p hp => ?_
  rcases List.mem_singleton.mp hp with rfl
  exact ⟨1, by decide⟩

theorem isZero_o5_eq : O5 isZero .eq :=
  (o5_correct _ _).mpr fun u v hu hv => by
    show u = v
    rw [isZero_props.mp hu.2, isZero_props.mp hv.2]

theorem spec_not_refutable : ¬ ∃ b, ¬ spec b := fun ⟨_, h⟩ => h trivial

theorem spec_not_determinate : ¬ ∀ a b, spec a → spec b → a = b :=
  fun h => Bool.noConfusion (h true false trivial trivial)

end LeanIntentExamples.Transfer
