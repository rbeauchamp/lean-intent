import LeanIntent.Degenerate

/-!
# A counter: progress refuses a record that a step doing nothing meets

The subject is the step of a counter, `Nat → Nat`, declared with shape `step`, so O4 asks that
every step leaving the state unchanged fail the record. A record that says only that the counter
never decreases is met by the step that does nothing, so it fails O4 (`neverDecreases_not_o4`);
a record that says each step adds one meets O4 (`advances_o4`).

The degenerate subjects of `Nat → Nat` are the step to zero and the step that does nothing
(`degenerate_subjects`). The check reports the step that does nothing for `neverDecreases`
(`neverDecreases_verdicts`) and nothing for `advances` (`advances_verdicts`), and since it depends
on the subject's type and not on its declared shape, it still reports that step when
`neverDecreases` is declared, wrongly, as a plain value, which O4 then asks nothing
(`neverDecreasesAsValue_o4`, `neverDecreasesAsValue_verdicts`).
-/

namespace LeanIntentExamples.Counter

open LeanIntent

/-- The counter never decreases: a safety property, which doing nothing meets. -/
def neverDecreases : IntentRecord (Nat → Nat) where
  shape := .step Nat
  dom := []
  props := [⟨"never decreases", fun tick => ∀ n, n ≤ tick n⟩]
  vocab := []

/-- Each step adds one. -/
def advances : IntentRecord (Nat → Nat) where
  shape := .step Nat
  dom := []
  props := [⟨"adds one", fun tick => ∀ n, tick n = n + 1⟩]
  vocab := []

/-- The step that does nothing meets `neverDecreases`, so `neverDecreases` fails O4. -/
theorem neverDecreases_not_o4 : ¬ O4 neverDecreases :=
  not_o4_of_idle (w := fun n => n) (fun _ => rfl)
    ⟨fun _ h => (nomatch h), fun p hp => by
      rcases List.mem_singleton.mp hp with rfl
      exact fun n => Nat.le_refl n⟩

/-- Every step that does nothing fails `advances`, so it meets O4. -/
theorem advances_o4 : O4 advances := by
  refine (o4_correct _).mpr fun f hf h => ?_
  have h1 := h.2 _ (List.mem_singleton.mpr rfl) 0
  rw [hf 0] at h1
  exact absurd h1 (by decide)

/-! ## The degenerate subjects -/

/-- The degenerate subjects of a step of type `Nat → Nat`: the step to zero, since numbers are
infinitely many and the class takes a numeric constant only at zero, and the step that does
nothing, the identity. -/
theorem degenerate_subjects :
    (degenerate (Nat → Nat)).map Degenerate.reading = [.subject fun _ => 0, .subject fun n => n] :=
  rfl

/-- The step that does nothing meets `neverDecreases` and the step to zero does not, so the check
reports the step that does nothing. -/
theorem neverDecreases_verdicts : Verdicts neverDecreases [false, true] := by
  show ¬ neverDecreases.Meets (fun _ => 0) ∧ neverDecreases.Meets (fun n => n) ∧ True
  refine ⟨fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 1) (by decide), ?_, trivial⟩
  exact ⟨fun _ h => (nomatch h), fun p hp => by
    rcases List.mem_singleton.mp hp with rfl
    exact fun n => Nat.le_refl n⟩

/-- Neither meets `advances`, so the check reports nothing. -/
theorem advances_verdicts : Verdicts advances [false, false] := by
  show ¬ advances.Meets (fun _ => 0) ∧ ¬ advances.Meets (fun n => n) ∧ True
  refine ⟨fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 0) (by decide),
    fun h => absurd (h.2 _ (List.mem_singleton.mpr rfl) 0) (by decide), trivial⟩

/-- `neverDecreases` declared with the wrong shape, as a plain value. -/
def neverDecreasesAsValue : IntentRecord (Nat → Nat) := { neverDecreases with shape := .value _ }

/-- O4 asks a plain value nothing, so the record declared with the wrong shape meets it. -/
theorem neverDecreasesAsValue_o4 : O4 neverDecreasesAsValue := trivial

/-- The degenerate check is fixed by the subject's type, not by its declared shape, so it still
reports the step that does nothing. -/
theorem neverDecreasesAsValue_verdicts : Verdicts neverDecreasesAsValue [false, true] :=
  neverDecreases_verdicts

theorem neverDecreasesAsValue_metBy :
    (metBy (Nat → Nat) [false, true]).map Degenerate.reading = [.subject fun n => n] := rfl

end LeanIntentExamples.Counter
