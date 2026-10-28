import LeanIntent.Record

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
without one. It also lists the record's consequences that the owner is asked to confirm or
decline, each a named proposition with its proof (`Consequence`) and its gloss, so that no
consequence shown to the owner is false. Keeping the owner's answers across revisions, and
recording that only the owner gave them, are separate issues of this repository (lean-intent #3
and #5).
-/

namespace LeanIntent

universe u

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

/-- A consequence of a record that the owner is asked to confirm or decline: a named proposition,
such as that the record refutes a subject or meets an obligation, with its proof. The owner is
shown only consequences that hold; declining one says that the record is not what they meant. -/
structure Consequence where
  /-- The name the owner reads the consequence by. -/
  name : String
  /-- The proposition. -/
  statement : Prop
  /-- Its proof. -/
  proof : statement

/-- An explanation of the intent record `r` for its owner: a gloss for its shape and for each of its
domain hypotheses, properties and vocabulary predicates, in the record's order, and its
consequences, each with its gloss. The default proofs of the three lengths are `rfl`, which holds
whenever the record's lists reduce to lists of known length. -/
structure Explanation {W : Type u} (r : IntentRecord W) where
  /-- The gloss of the record's shape. -/
  shape : Gloss
  /-- The glosses of the domain hypotheses, in order. -/
  dom : List Gloss
  /-- The glosses of the properties, in order. -/
  props : List Gloss
  /-- The glosses of the vocabulary predicates, in order. -/
  vocab : List Gloss
  /-- The consequences shown to the owner, each with its gloss. -/
  consequences : List (Consequence × Gloss)
  dom_length : dom.length = r.dom.length := by rfl
  props_length : props.length = r.props.length := by rfl
  vocab_length : vocab.length = r.vocab.length := by rfl

end LeanIntent
