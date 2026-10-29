import LeanIntent.Answers

/-!
# Plain-word explanations of an intent record

The one human check in the method is the owner confirming that the formal statement of their
intent says what they meant. They read each statement in two forms side by side: printed exactly,
as the term Lean's kernel checks (`LeanIntent.Render`), and explained in plain words, by a `Gloss`
in four parts: what the statement requires, what it rules out, what it still allows, and the
freedom it leaves, the freedom obligation O5 shows the owner.

A gloss is written by a model and is trusted, not proved: nothing checks that it says what the
statement says. The exact statement beside it is what is proved and checked, and the owner can
read either.

An `Explanation r` gives a gloss for every statement of the intent record `r`: its shape, and each
of its domain hypotheses, properties and vocabulary predicates, in the record's order. Its type
requires as many glosses of each kind as the record has statements, so no statement is left
without one. It also lists the consequences of `r` shown to the owner, the consequences the owner
answers (`LeanIntent.Consequence`), each with its gloss and a proof that it holds of `r` as shown
(`Consequence.HoldsOf`): an entailment, that every model of `r` satisfies it; a possibility, that
some model does. So no consequence is shown to the owner as entailed or as possible unless it is.
The owner's answers to them are kept across revisions by `LeanIntent.Answers`; deciding whether each
answer's authority traces back to a declared owner is lean-intent #5.
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-- A plain-word explanation of one statement, in four parts. Written by a model and trusted, not
proved. -/
structure Gloss where
  /-- What the statement requires. -/
  requires : String
  /-- What it rules out. -/
  rulesOut : String
  /-- What it still allows. -/
  allows : String
  /-- The freedom it leaves, which obligation O5 shows the owner: what two subjects that meet it
  may still differ in. -/
  freedom : String

/-- The consequence `c` holds of the record `r` as it is shown: for an entailment, every model of
`r` satisfies it; for a possibility, some model of `r` does. This is what the owner's confirming it
asks of `r` (`Answer.KeptBy`). -/
def Consequence.HoldsOf (c : Consequence W) (r : IntentRecord W) : Prop :=
  (Answer.mk c .confirmed).KeptBy r

/-- A consequence of the record `r` shown to the owner: the consequence, a proof that it holds of
`r` as shown, and its gloss. -/
structure Shown (r : IntentRecord W) where
  /-- The consequence. -/
  consequence : Consequence W
  /-- It holds of `r` as it is shown. -/
  holds : consequence.HoldsOf r
  /-- Its gloss. -/
  gloss : Gloss

/-- An explanation of the intent record `r` for its owner: a gloss for its shape and for each of its
domain hypotheses, properties and vocabulary predicates, in the record's order, and the
consequences shown to the owner. The default proofs of the three lengths are `rfl`, which holds
whenever the record's lists reduce to lists of known length. -/
structure Explanation (r : IntentRecord W) where
  /-- The gloss of the record's shape. -/
  shape : Gloss
  /-- The glosses of the domain hypotheses, in order. -/
  dom : List Gloss
  /-- The glosses of the properties, in order. -/
  props : List Gloss
  /-- The glosses of the vocabulary predicates, in order. -/
  vocab : List Gloss
  /-- The consequences shown to the owner. -/
  consequences : List (Shown r)
  dom_length : dom.length = r.dom.length := by rfl
  props_length : props.length = r.props.length := by rfl
  vocab_length : vocab.length = r.vocab.length := by rfl

end LeanIntent
