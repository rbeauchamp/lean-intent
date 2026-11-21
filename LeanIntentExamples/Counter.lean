module

public import LeanIntent.Degenerate

public section

namespace LeanIntentExamples.Counter

open LeanIntent

@[expose] def neverDecreases : IntentRecord (Nat → Nat) where
  shape := .step Nat
  dom := []
  props := [⟨"never decreases", fun tick => ∀ n, n ≤ tick n⟩]
  vocab := []

@[expose] def advances : IntentRecord (Nat → Nat) where
  shape := .step Nat
  dom := []
  props := [⟨"adds one", fun tick => ∀ n, tick n = n + 1⟩]
  vocab := []

theorem neverDecreases_not_o4 : ¬ O4 neverDecreases :=
  not_o4_of_idle (w := fun n => n) (fun _ => rfl)
    ⟨fun _ h => (nomatch h), fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact fun n => Nat.le_refl n⟩

theorem advances_o4 : O4 advances := by
  refine (o4_correct _).mpr fun f hf h => ?_
  have h1 := h.2 _ (List.mem_singleton.mpr rfl) 0
  rw [hf 0] at h1
  exact absurd h1 (by decide)

theorem degenerate_subjects :
    (degenerate (Nat → Nat)).map Degenerate.reading = [.subject fun _ => 0, .subject fun n => n] :=
  rfl

theorem neverDecreases_verdicts : Verdicts neverDecreases [false, true] := by
  show ¬ neverDecreases.Meets (fun _ => 0) ∧ neverDecreases.Meets (fun n => n) ∧ True
  refine ⟨fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 1) (by decide), ?_, trivial⟩
  exact ⟨fun _ h => (nomatch h), fun p hp => by
    rcases List.mem_singleton.mp hp with rfl
    exact fun n => Nat.le_refl n⟩

theorem advances_verdicts : Verdicts advances [false, false] := by
  show ¬ advances.Meets (fun _ => 0) ∧ ¬ advances.Meets (fun n => n) ∧ True
  refine ⟨fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 0) (by decide),
    fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 0) (by decide), trivial⟩

@[expose] def neverDecreasesAsValue : IntentRecord (Nat → Nat) := { neverDecreases with shape := .value _ }

theorem neverDecreasesAsValue_o4 : O4 neverDecreasesAsValue := trivial

theorem neverDecreasesAsValue_verdicts : Verdicts neverDecreasesAsValue [false, true] :=
  neverDecreases_verdicts

theorem neverDecreasesAsValue_metBy :
    (metBy (Nat → Nat) [false, true]).map Degenerate.reading = [.subject fun n => n] := rfl

end LeanIntentExamples.Counter
