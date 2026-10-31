import LeanIntent.Settled

/-!
# Plain-word explanations of an intent record

The one human check in the method is the owner confirming that the formal statement of their
intent says what they meant. They read each statement in two forms side by side: printed so that
Lean reads it back as the term its kernel checks (`LeanIntent.Render`), and explained in plain
words, by a `Gloss` in four parts: what the statement requires, what it rules out, what it still
allows, and the freedom it leaves, the freedom obligation O5 shows the owner.

A gloss is written by a model and is trusted, not proved: nothing checks that it says what the
statement says. The printed statement beside it is what is proved and checked, and the owner can
read either.

An `Explanation r` gives a gloss for every statement of the intent record `r`: its shape, and each
of its domain hypotheses, properties and vocabulary predicates, in the record's order. Its type
requires as many glosses of each kind as the record has statements, so no statement is left without
one. The owner confirms the record as a plain restatement of their intent, and decides the forks it
leaves open; they are not asked to answer each consequence of it. The explanation records whether an
owner has confirmed that restatement (`LeanIntent.Restatement`), and lists the consequences of `r`
shown with it (`LeanIntent.Consequence`): the forks the owner decides, and any other the explanation
shows. Each comes with its gloss, a proof that it holds of `r` as shown (`Consequence.HoldsOf`): an
entailment, that every model of `r` satisfies it; a possibility, that some model does; and who
settled it (`LeanIntent.Settled`). So no consequence is shown as entailed or as possible unless it
is, none is shown without its status, and the type refuses to call one derived from a confirmation
the record does not hold. The answers to them, the owner's own and the decisions made on the owner's
behalf, are kept across revisions by `LeanIntent.Answers`. An answer recorded in a project's owners'
log names who gave it, a principal acting as owner or one acting under the delegation it names,
which tells the owner's own answer apart from a decision made on the owner's behalf; whether that
authority traces back to a declared owner is decided by `LeanIntent.Trace`, and
`LeanIntent.Confirmation` ties the answers and statuses a project keeps to its log.
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
`r` satisfies it; for a possibility, some model of `r` does. It names no verdict, since a consequence
holds or not whoever answers it, and a rendering prints this definition for every consequence. -/
def Consequence.HoldsOf (c : Consequence W) (r : IntentRecord W) : Prop :=
  match c.kind with
  | .entailment => ∀ w, r.Meets w → c.holds w
  | .possibility => HasInstance fun w => r.Meets w ∧ c.holds w

/-- A consequence holds of `r` as shown exactly when `r` keeps the answer that confirms it. -/
theorem Consequence.holdsOf_iff_keptBy (c : Consequence W) (r : IntentRecord W) :
    c.HoldsOf r ↔ (Answer.mk c .confirmed).KeptBy r := by
  obtain ⟨_, kind, _⟩ := c
  cases kind <;> exact Iff.rfl

/-- A consequence of the record `r` shown with its restatement standing as `s`: the consequence, a
proof that it holds of `r` as shown, its gloss, and who settled it. -/
structure Shown (r : IntentRecord W) (s : Restatement) where
  /-- The consequence. -/
  consequence : Consequence W
  /-- It holds of `r` as it is shown. -/
  holds : consequence.HoldsOf r
  /-- Its gloss. -/
  gloss : Gloss
  /-- Who settled it. -/
  settled : Settled s

/-- An explanation of the intent record `r` for its owner: a gloss for its shape and for each of its
domain hypotheses, properties and vocabulary predicates, in the record's order, whether an owner
confirmed its restatement, and the consequences shown with it. The default proofs of the three
lengths are `rfl`, which holds whenever the record's lists reduce to lists of known length. -/
structure Explanation (r : IntentRecord W) where
  /-- The gloss of the record's shape. -/
  shape : Gloss
  /-- The glosses of the domain hypotheses, in order. -/
  dom : List Gloss
  /-- The glosses of the properties, in order. -/
  props : List Gloss
  /-- The glosses of the vocabulary predicates, in order. -/
  vocab : List Gloss
  /-- Whether an owner confirmed the record's plain restatement. -/
  restatement : Restatement
  /-- The consequences shown, each with who settled it. -/
  consequences : List (Shown r restatement)
  dom_length : dom.length = r.dom.length := by rfl
  props_length : props.length = r.props.length := by rfl
  vocab_length : vocab.length = r.vocab.length := by rfl

end LeanIntent
