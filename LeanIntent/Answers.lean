import LeanIntent.Obligations

/-!
# The owner's answers, kept by every later revision

The owner validates an intent record by confirming its plain restatement and deciding the forks it
leaves open, not by answering each of its consequences. An answer confirms or declines one
consequence: the owner gives it where the consequence is such a fork, and otherwise the agents give
it, as a decision made on the owner's behalf with its reason tied to the owner's intent. Which it is
shows in the project's owners' log, whose answer statement names who gave it, a principal acting as
owner or one acting under the delegation it names (`LeanIntent.Statement`); an `Answer` here names
no author, and `LeanIntent.Attributed` pairs it with who gave it. A consequence is a named predicate
on the subject, of one of two kinds: an *entailment*, which every model of the record satisfies
(what the record requires or rules out), or a
*possibility*, which some model satisfies (what the record still allows). An answer confirms it or
declines it, and each of the four answers is a requirement of every later revision of the record
(`Answer.KeptBy`), whose models are its subjects that meet it (`IntentRecord.Meets`):

| Consequence | Confirmed: every later revision keeps | Declined: every later revision keeps |
|---|---|---|
| entailment `c` | a theorem: every model satisfies `c` | a countermodel: a model that fails `c` |
| possibility `c` | a model that satisfies `c` | a refutation: no model satisfies `c` |

A declined possibility is kept as a theorem, not as a model: when "the record allows returning the
empty list for every input" is declined, by the owner or on the owner's behalf, what must stay true
is that every later revision excludes that subject. A declined entailment is kept as a
countermodel, since a witness is what shows that a revision no longer requires it.

Each kept goal applies the answer's unchanged predicate to the subjects that meet the revision being
checked, under that revision's domain hypotheses. It is never a fact proved about an earlier
revision, which a later one could carry over while it admits the very subject the answer excludes.
So every revision proves each answer again from its own properties and domain hypotheses.

`kept r answers` computes one goal per stored answer, and `keeps_correct` equates their conjunction
with `intendedKeeps`, written by a direct match on the answers and the record, using no definition
of the former or of its helpers (`Goals`, `HasInstance`, `Answer.KeptBy`, `IntentRecord.Meets`,
`IntentRecord.Dom`, `IntentRecord.Props`), for every record and every list of answers, so a former
that dropped an answer, weakened one or stated the goals of one example only would fail it.

`Accepted answers` is the type of the revisions accepted under the stored answers: a record with a
proof that it keeps every one. No value of it holds a revision that breaks a stored answer, and
every revision that keeps them all is the record of one (`accepted_iff`). A refusal names the answer
it breaks: a revision fails to keep the stored answers exactly when it keeps the opposite of one of
them (`not_keeps_iff`), and the opposite of an answer is the witness that breaks it
(`keptBy_opposite`). In Lean, a proof of `Keeps r answers` proves `a.KeptBy r` for each stored
answer `a` (`keeps_iff`), so a revision that breaks one leaves that answer's goal unproved, and the
goal Lean reports names the answer.

A revision may rename its clauses and its vocabulary, change its shape or restate its properties:
whether it keeps the answers depends only on which subjects meet it (`keeps_congr`), and the goal
of every stored answer is formed again from the new record, so no answer is skipped. An answer that
can no longer be stated over the revision is refused, not passed, by Lean's elaborator: a stored
answer about subjects of type `W` asks its goal of a record of type `IntentRecord W`, so a revision
whose subject has another type cannot be the record of an `Accepted answers`, and an answer whose
predicate names a definition the revision removed or renamed fails to elaborate at its own
declaration.

What this module does not establish:

* that a stored answer was given by a declared owner, or under a delegation that traces back to
  one, and that no one else removed or changed one. `LeanIntent.Trace` decides, from a project's
  owners' log, whether each answer recorded there has such authority and is not retracted, and
  `LeanIntent.Confirmation` ties the answers a project keeps here to the statements of its log;
* that an answer's predicate still means what was confirmed or declined. It is a Lean term, read in
  the environment that elaborates it, so a revision that changes the body of a definition the
  predicate uses, the subject type's among them, changes the stored answer's meaning without
  removing it, and a confirmed entailment stated through the record it answers, such as
  `fun f => sorting.Props f`, is kept by every revision of that record. A predicate that uses only
  Lean's own library, as both answers of `LeanIntentExamples.Answers` do, keeps its meaning while
  the Lean release does; `LeanIntent.Confirmation` refuses a stored answer whose predicate's text,
  everything the predicate reaches printed in full, no answer of the log holds;
* that a project checks its current revision against its stored answers: it does so by declaring a
  value of `Accepted answers` for that revision, and a project that declares none checks nothing.
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-- The two kinds of consequence shown with a record. -/
inductive Consequence.Kind where
  /-- What the record requires or rules out: every model of the record satisfies it. -/
  | entailment
  /-- What the record still allows: some model of the record satisfies it. -/
  | possibility

/-- A consequence of an intent record whose subject has type `W`, as shown with the record. -/
structure Consequence (W : Type u) where
  /-- The name the consequence is read by. -/
  name : String
  /-- Whether it was shown as entailed or as possible. -/
  kind : Consequence.Kind
  /-- The predicate on the subject. -/
  holds : W → Prop

/-- A verdict on a consequence, the owner's own or one made on the owner's behalf. -/
inductive Verdict where
  /-- The consequence is what the owner means. -/
  | confirmed
  /-- The consequence is not what the owner means. -/
  | declined

/-- An answer: a verdict on one consequence, the owner's own or one made on the owner's behalf. -/
structure Answer (W : Type u) where
  /-- The consequence answered. -/
  consequence : Consequence W
  /-- The verdict on it. -/
  verdict : Verdict

/-- The goal the answer `a` sets the revision `r`: for a confirmed entailment, every model of `r`
satisfies the consequence; for a declined entailment, some model fails it; for a confirmed
possibility, some model satisfies it; for a declined possibility, no model satisfies it. -/
def Answer.KeptBy (a : Answer W) (r : IntentRecord W) : Prop :=
  match a.consequence.kind, a.verdict with
  | .entailment, .confirmed => ∀ w, r.Meets w → a.consequence.holds w
  | .entailment, .declined => HasInstance fun w => r.Meets w ∧ ¬ a.consequence.holds w
  | .possibility, .confirmed => HasInstance fun w => r.Meets w ∧ a.consequence.holds w
  | .possibility, .declined => ∀ w, r.Meets w → ¬ a.consequence.holds w

/-- The goals the stored answers set the revision `r`: one for each answer, in order. -/
def kept (r : IntentRecord W) (answers : List (Answer W)) : List Prop :=
  answers.map fun a => a.KeptBy r

/-- The revision `r` keeps every stored answer. -/
def Keeps (r : IntentRecord W) (answers : List (Answer W)) : Prop := Goals (kept r answers)

/-- What keeping the stored answers asks of `r`, written apart from the former. -/
def intendedKeeps (r : IntentRecord W) (answers : List (Answer W)) : Prop :=
  ∀ a ∈ answers, match a with
  | ⟨⟨_, .entailment, c⟩, .confirmed⟩ =>
      ∀ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) → c w
  | ⟨⟨_, .entailment, c⟩, .declined⟩ =>
      ∃ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) ∧ ¬ c w
  | ⟨⟨_, .possibility, c⟩, .confirmed⟩ =>
      ∃ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) ∧ c w
  | ⟨⟨_, .possibility, c⟩, .declined⟩ =>
      ∀ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) → ¬ c w

/-- The former states what keeping the stored answers asks. -/
theorem keeps_correct (r : IntentRecord W) (answers : List (Answer W)) :
    Keeps r answers ↔ intendedKeeps r answers := by
  simp only [Keeps, kept, goals_map, intendedKeeps]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;>
    simp only [Answer.KeptBy, HasInstance, IntentRecord.Meets, IntentRecord.Dom,
      IntentRecord.Props]

/-- `r` keeps the stored answers exactly when it keeps each of them. -/
theorem keeps_iff (r : IntentRecord W) (answers : List (Answer W)) :
    Keeps r answers ↔ ∀ a ∈ answers, a.KeptBy r :=
  goals_map _ _

/-! ## Refusals name the answer they break -/

/-- The opposite answer: the same consequence with the other verdict. -/
def Answer.opposite (a : Answer W) : Answer W where
  consequence := a.consequence
  verdict := match a.verdict with
    | .confirmed => .declined
    | .declined => .confirmed

/-- A revision breaks an answer exactly when it keeps the opposite one: a model that fails a
confirmed entailment, a refutation of a confirmed possibility, a model with a declined possibility,
or a proof that every model still satisfies a declined entailment. -/
theorem Answer.keptBy_opposite (a : Answer W) (r : IntentRecord W) :
    a.opposite.KeptBy r ↔ ¬ a.KeptBy r := by
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;>
    simp only [Answer.opposite, Answer.KeptBy, HasInstance, Classical.not_forall,
      exists_prop, not_exists, not_and, Classical.not_not]

/-- Every refusal names a stored answer that the revision breaks, by the opposite answer it
keeps. -/
theorem not_keeps_iff (r : IntentRecord W) (answers : List (Answer W)) :
    ¬ Keeps r answers ↔ ∃ a ∈ answers, a.opposite.KeptBy r := by
  simp only [keeps_iff, Answer.keptBy_opposite, Classical.not_forall, exists_prop]

/-- A revision that keeps the opposite of a stored answer is refused. -/
theorem not_keeps_of_opposite {r : IntentRecord W} {answers : List (Answer W)} {a : Answer W}
    (ha : a ∈ answers) (h : a.opposite.KeptBy r) : ¬ Keeps r answers :=
  fun hk => (a.keptBy_opposite r).mp h ((keeps_iff r answers).mp hk a ha)

/-- Stored answers that confirm and decline the same consequence refuse every revision, until a
retraction of one resolves the conflict. -/
theorem not_keeps_of_conflict {r : IntentRecord W} {answers : List (Answer W)} {a : Answer W}
    (ha : a ∈ answers) (hb : a.opposite ∈ answers) : ¬ Keeps r answers :=
  fun hk => not_keeps_of_opposite ha ((keeps_iff r answers).mp hk _ hb) hk

/-! ## What a revision may change -/

/-- Whether a revision keeps the stored answers depends only on which subjects meet it: a revision
that renames its clauses or its vocabulary, changes its shape or restates its properties, with the
same models, keeps exactly the answers the original kept. -/
theorem Answer.keptBy_congr (a : Answer W) {r r' : IntentRecord W}
    (h : ∀ w, r.Meets w ↔ r'.Meets w) : a.KeptBy r ↔ a.KeptBy r' := by
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;> simp only [Answer.KeptBy, HasInstance, h]

/-- The stored answers a revision keeps depend only on its models. -/
theorem keeps_congr {r r' : IntentRecord W} (answers : List (Answer W))
    (h : ∀ w, r.Meets w ↔ r'.Meets w) : Keeps r answers ↔ Keeps r' answers := by
  simp only [keeps_iff, Answer.keptBy_congr _ h]

/-! ## Accepted revisions -/

/-- A revision of an intent record accepted under the stored answers `answers`: the record, with a
proof that it keeps every one. A revision that breaks a stored answer is not a value of this type.
-/
structure Accepted (answers : List (Answer W)) where
  /-- The revision. -/
  record : IntentRecord W
  /-- It keeps every stored answer. -/
  keeps : Keeps record answers

/-- An accepted revision keeps every stored answer. -/
theorem Accepted.keptBy {answers : List (Answer W)} (x : Accepted answers) {a : Answer W}
    (ha : a ∈ answers) : a.KeptBy x.record :=
  (keeps_iff _ _).mp x.keeps a ha

/-- A revision is accepted exactly when it keeps each stored answer: the type refuses every
revision that breaks one, and no other. -/
theorem accepted_iff (answers : List (Answer W)) (r : IntentRecord W) :
    (∃ x : Accepted answers, x.record = r) ↔ ∀ a ∈ answers, a.KeptBy r :=
  ⟨fun ⟨x, hx⟩ => hx ▸ fun _ ha => x.keptBy ha, fun h => ⟨⟨r, (keeps_iff r answers).mpr h⟩, rfl⟩⟩

/-- Every model of an accepted revision satisfies each consequence confirmed as entailed. -/
theorem Accepted.entailed {answers : List (Answer W)} (x : Accepted answers) {n : String}
    {c : W → Prop} (ha : ⟨⟨n, .entailment, c⟩, .confirmed⟩ ∈ answers) {w : W}
    (hw : x.record.Meets w) : c w :=
  x.keptBy ha w hw

/-- No model of an accepted revision satisfies a consequence declined as possible. -/
theorem Accepted.excluded {answers : List (Answer W)} (x : Accepted answers) {n : String}
    {c : W → Prop} (ha : ⟨⟨n, .possibility, c⟩, .declined⟩ ∈ answers) {w : W}
    (hw : x.record.Meets w) : ¬ c w :=
  x.keptBy ha w hw

end LeanIntent
