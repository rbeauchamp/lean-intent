module

public import LeanIntent.Degenerate

public section

namespace LeanIntentExamples.Decision

open LeanIntent

@[expose] def soundClause : Clause (Nat → Bool) := ⟨"sound", fun f => ∀ n, f n = true → n % 2 = 0⟩

@[expose] def completeClause : Clause (Nat → Bool) := ⟨"complete", fun f => ∀ n, n % 2 = 0 → f n = true⟩

@[expose] def soundOnly : IntentRecord (Nat → Bool) where
  shape := .function _ _
  dom := []
  props := [soundClause]
  vocab := []

@[expose] def decides : IntentRecord (Nat → Bool) where
  shape := .function _ _
  dom := []
  props := [soundClause, completeClause]
  vocab := []

theorem degenerate_subjects :
    (degenerate (Nat → Bool)).map Degenerate.reading =
      [.subject fun _ => false, .subject fun _ => true] := rfl

theorem soundOnly_verdicts : Verdicts soundOnly [true, false] := by
  show soundOnly.Meets (fun _ => false) ∧ ¬ soundOnly.Meets (fun _ => true) ∧ True
  refine ⟨⟨fun _ h => (nomatch h), fun p hp => ?_⟩, fun h => ?_, trivial⟩
  · rcases List.mem_singleton.mp hp with rfl
    exact fun _ h => nomatch h
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) 1 rfl) (by decide)

theorem decides_verdicts : Verdicts decides [false, false] := by
  show ¬ decides.Meets (fun _ => false) ∧ ¬ decides.Meets (fun _ => true) ∧ True
  refine ⟨fun h => ?_, fun h => ?_, trivial⟩
  · exact absurd (h.2 _ (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))) 0 rfl)
      (by decide)
  · exact absurd (h.2 _ (List.mem_cons.mpr (.inl rfl)) 1 rfl) (by decide)

end LeanIntentExamples.Decision
