import LeanIntent

/-!
# A counter: progress refuses a record that a step doing nothing meets

The subject is the step of a counter, `Nat → Nat`, declared with shape `step`, so O4 asks that
every step leaving the state unchanged fail the record. A record that says only that the counter
never decreases is met by the step that does nothing, so it fails O4 (`neverDecreases_not_o4`);
a record that says each step adds one meets O4 (`advances_o4`).
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

end LeanIntentExamples.Counter
