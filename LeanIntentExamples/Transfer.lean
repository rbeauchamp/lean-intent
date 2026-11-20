module

public import LeanIntent.Refinement

public section

namespace LeanIntentExamples.Transfer

open LeanIntent

@[expose] def isZero : IntentRecord Nat where
  shape := .value Nat
  dom := []
  props := [⟨"is zero", fun n => n = 0⟩]
  vocab := []

@[expose] def spec : Bool → Prop := fun _ => True

@[expose] def toZero : Bool → Nat := fun _ => 0

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
