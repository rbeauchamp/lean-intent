/-!
# Intent records

An intent record is the first formal statement of what an owner wants from one deliverable, written
before any implementation exists: named properties of a subject, over a vocabulary of predicates,
under named domain hypotheses.

* The *subject* is what the intent is about, a value of a type `W : Type u`: a function, a step of
  a system with state, or any other value. Its `Shape` says which, and so fixes what doing nothing
  means for it (obligation O4).
* Each *property* is a named Lean proposition about the subject, `W → Prop`.
* Each *domain hypothesis* is a named fact about the world that the properties rely on, also a
  `W → Prop`; a hypothesis that does not mention the subject is a constant one. Domain hypotheses
  are listed in the record rather than hidden below it, so that those the owner states are confirmed
  with the restatement of their intent, and one an agent adds is visible as a decision made on the
  owner's behalf, recorded with its reason.
* The *vocabulary* is the predicates the properties are written in, each over its own type.

A record is frozen in the sense Lean gives every declaration: once declared, its value is fixed in
the environment that holds it, and Lean's kernel has checked that each statement has the type the
record declares for it. That a record does not depend on its own implementation is decided by
cone exclusion (`LeanIntent.Cone`). A later revision may change what a record says, but must keep
every consequence confirmed or declined, by the owner or on the owner's behalf
(`LeanIntent.Answers`).
-/

namespace LeanIntent

universe u

/-- A named statement about subjects of type `W`: a domain hypothesis or a property. -/
structure Clause (W : Type u) where
  /-- The name the owner reads the statement by. -/
  name : String
  /-- The statement, a proposition about each subject. -/
  holds : W → Prop

/-- A predicate of a vocabulary: a named property of values of its own type `Arg`. -/
structure Pred where
  /-- The name the owner reads the predicate by. -/
  name : String
  /-- The type of the values the predicate is about. -/
  Arg : Type u
  /-- The predicate. -/
  holds : Arg → Prop

/-- The closed set of subject shapes. A shape fixes, by the subject's type alone, what O4 asks:
nothing of a plain value, totality of a function, and of a subject with state, that each subject
that leaves the state unchanged fails the record. A subject with state is a step of a system: from
a state, optionally with an input, to the next state, optionally with an output. -/
inductive Shape : Type u → Type (u + 1) where
  /-- A value with no behaviour. -/
  | value (W : Type u) : Shape W
  /-- A function, dependent or not. -/
  | function (A : Type u) (B : A → Type u) : Shape ((x : A) → B x)
  /-- A step from a state to the next. -/
  | step (S : Type u) : Shape (S → S)
  /-- A step from a state and an input to the next state. -/
  | stepOn (S I : Type u) : Shape (S → I → S)
  /-- A step from a state to an output and the next state, the shape of `StateM S O`. -/
  | action (S O : Type u) : Shape (S → O × S)
  /-- A step from a state and an input to an output and the next state. -/
  | actionOn (S I O : Type u) : Shape (S → I → O × S)

/-- An intent record for one deliverable whose subject has type `W`. -/
structure IntentRecord (W : Type u) where
  /-- What kind of subject the record is about. -/
  shape : Shape W
  /-- The named domain hypotheses. -/
  dom : List (Clause W)
  /-- The named properties. -/
  props : List (Clause W)
  /-- The predicates the properties are written in. -/
  vocab : List Pred.{u}

namespace IntentRecord

variable {W : Type u}

/-- Every domain hypothesis of `r` holds of `w`. -/
def Dom (r : IntentRecord W) (w : W) : Prop := ∀ d ∈ r.dom, d.holds w

/-- Every property of `r` holds of `w`. -/
def Props (r : IntentRecord W) (w : W) : Prop := ∀ p ∈ r.props, p.holds w

/-- `w` is a model of `r`: every domain hypothesis and every property holds of it. -/
def Meets (r : IntentRecord W) (w : W) : Prop := r.Dom w ∧ r.Props w

/-- `w` fulfils `r`: wherever the domain hypotheses hold of it, so does every property. This is what
an implementation proves of its subject, since the domain hypotheses are facts about the world that
no implementation can establish. -/
def Fulfilled (r : IntentRecord W) (w : W) : Prop := r.Dom w → r.Props w

theorem meets_of_fulfilled {r : IntentRecord W} {w : W} (h : r.Fulfilled w) (hd : r.Dom w) :
    r.Meets w := ⟨hd, h hd⟩

end IntentRecord

end LeanIntent
