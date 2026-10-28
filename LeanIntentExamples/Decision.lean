import LeanIntent

/-!
# A decision procedure that may always answer no

The subject is a procedure that decides whether a number is even, of type `Nat → Bool`. `Bool` has
finitely many values, so the degenerate class takes the constant function at every one, the
procedure that always answers `false` and the one that always answers `true`, and it has no
projection, since no argument has type `Bool` (`degenerate_subjects`). A record that asks only that
every `true` answer be right, `soundOnly`, is met by the procedure that always answers `false`, and
the check reports it (`soundOnly_verdicts`). The record that also asks that every even number be
answered `true`, `decides`, is met by neither (`decides_verdicts`).
-/

namespace LeanIntentExamples.Decision

open LeanIntent

/-- Every `true` answer is right. -/
def soundClause : Clause (Nat → Bool) := ⟨"sound", fun f => ∀ n, f n = true → n % 2 = 0⟩

/-- Every even number is answered `true`. -/
def completeClause : Clause (Nat → Bool) := ⟨"complete", fun f => ∀ n, n % 2 = 0 → f n = true⟩

/-- The record that asks only for sound answers. -/
def soundOnly : IntentRecord (Nat → Bool) where
  shape := .function _ _
  dom := []
  props := [soundClause]
  vocab := []

/-- The record that asks for sound and complete answers. -/
def decides : IntentRecord (Nat → Bool) where
  shape := .function _ _
  dom := []
  props := [soundClause, completeClause]
  vocab := []

/-- The degenerate subjects of `Nat → Bool`: the constant function at each of `Bool`'s two
values. -/
theorem degenerate_subjects :
    (degenerate (Nat → Bool)).map Degenerate.subject = [fun _ => false, fun _ => true] := rfl

/-- The procedure that always answers `false` meets `soundOnly`; the one that always answers
`true` does not. -/
theorem soundOnly_verdicts : Verdicts soundOnly [true, false] := by
  show soundOnly.Meets (fun _ => false) ∧ ¬ soundOnly.Meets (fun _ => true) ∧ True
  refine ⟨⟨fun _ h => (nomatch h), fun p hp => ?_⟩, fun h => ?_, trivial⟩
  · rcases List.mem_singleton.mp hp with rfl
    exact fun _ h => nomatch h
  · exact absurd (h.2 _ (List.mem_singleton.mpr rfl) 1 rfl) (by decide)

/-- Neither meets `decides`. -/
theorem decides_verdicts : Verdicts decides [false, false] := by
  show ¬ decides.Meets (fun _ => false) ∧ ¬ decides.Meets (fun _ => true) ∧ True
  refine ⟨fun h => ?_, fun h => ?_, trivial⟩
  · exact absurd (h.2 _ (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))) 0 rfl)
      (by decide)
  · exact absurd (h.2 _ (List.mem_cons.mpr (.inl rfl)) 1 rfl) (by decide)

end LeanIntentExamples.Decision
