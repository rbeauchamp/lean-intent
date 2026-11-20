module

public import LeanIntent.Settled

public section

namespace LeanIntent

universe u

variable {W : Type u}

structure Gloss where
  requires : String
  rulesOut : String
  allows : String
  freedom : String

@[expose] def Consequence.HoldsOf (c : Consequence W) (r : IntentRecord W) : Prop :=
  match c.kind with
  | .entailment => ∀ w, r.Meets w → c.holds w
  | .possibility => HasInstance fun w => r.Meets w ∧ c.holds w

theorem Consequence.holdsOf_iff_keptBy (c : Consequence W) (r : IntentRecord W) :
    c.HoldsOf r ↔ (Answer.mk c .confirmed).KeptBy r := by
  obtain ⟨_, kind, _⟩ := c
  cases kind <;> exact Iff.rfl

structure Shown (r : IntentRecord W) (s : Restatement) where
  consequence : Consequence W
  holds : consequence.HoldsOf r
  gloss : Gloss
  settled : Settled s

structure Explanation (r : IntentRecord W) where
  shape : Gloss
  dom : List Gloss
  props : List Gloss
  vocab : List Gloss
  restatement : Restatement
  consequences : List (Shown r restatement)
  dom_length : dom.length = r.dom.length := by rfl
  props_length : props.length = r.props.length := by rfl
  vocab_length : vocab.length = r.vocab.length := by rfl

end LeanIntent
