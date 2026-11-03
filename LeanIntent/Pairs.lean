import LeanIntent.Obligations

/-!
# Precondition-postcondition pairs, and the obligation that each admitted input can be served

A property says something for each input. The *input* is whatever the implementation does not
choose: an argument, a state, a world from a class. The *precondition* is what the record demands of
that input, a domain hypothesis or a guard inside the property, `True` where it demands nothing. The
*postcondition* is what the property then asks of the subject at that input. A `Pair W` is those
three for subjects of type `W`: an input type, a precondition on inputs and a postcondition on an
input and a subject. A subject meets the pair when it meets the postcondition at every input the
precondition admits (`Pair.Met`).

A pair is a pair of a record's property when it says exactly what an implementation must prove of
that property: for every subject, the property holds wherever the record's domain hypotheses do
exactly when the subject meets the pair (`IntentRecord.PairOf`, through `Pair.Says`). Every property
has such a pair, whose only input is trivial (`Pair.whole`, `pairOf_whole`). A project states the
finer pairs a property gives, each with the input the property's statement quantifies over, and
proves each a pair of the property.

The obligation `OPair q C`, for a pair `q` and an implementation class `C`, has two goals (`oPair`):

* the precondition admits some input, so a precondition that admits none refutes the obligation,
  whatever the class (`not_oPair_of_admits_nothing`);
* each input the precondition admits has a subject in `C` that meets the postcondition there, so an
  admitted input that no member of `C` serves refutes the obligation (`not_oPair_of_unserved`): the
  precondition is too wide for `C`.

The class `C : W → Prop` is a parameter of every statement here, so the obligation claims no more
than `C` allows. It passes from a class to every wider one (`OPair.mono`), but not in general from a
class to a narrower one (`LeanIntentExamples.Pairs.any_not_blind`), and no pair meets it in the empty
class (`not_oPair_empty`). A class of implementations of another type `A`, read as subjects
by `m : A → W`, is the image `fun w => ∃ a, m a = w`.

A former that computed `True`, a weaker proposition or the obligation for one example only would make
the obligation trivially met, so `oPair_correct` equates what the former states with
`intendedOPair`, written by a direct match on the pair. It uses no definition of the former or of the
helpers it and this module use (`Goals`, `HasInstance`, `Pair.Met`, `Pair.Says`,
`IntentRecord.PairOf`), and it holds for every pair and every class.

What the obligation does not establish:

* That the pair asks for the work it is meant to ask for. The second goal lets the subject depend on
  the input, so a subject that fixes its answer to each input in advance, such as a table or a
  script, can serve every input. Whether a trivial witness of a closed class fixed by the subject's
  type meets a pair is checked by `LeanIntent.TrivialWitnesses`, for the types it covers, not here.
  The pair whose only input is trivial asks one subject of the class to meet the whole property, and
  its obligation gives that of every pair of the property whose precondition admits an input
  (`OPair.of_whole`), but not in general the other way
  (`LeanIntentExamples.Pairs.perWorld_not_whole`).
* That the pair can fail. A pair whose precondition admits an input and whose postcondition every
  subject meets meets the obligation in every class that is not empty; that each property has a
  subject that fails it is O3.
* That the precondition carries the guards on the input. The first goal reads the precondition as
  stated, so a guard written inside the postcondition instead is not checked by it.
* That a project's pair quantifies over what the property quantifies over. `PairOf` checks only that
  the pair says what the property says, so a pair whose input is not one the property speaks of,
  such as one naming a subject, with a postcondition that holds emptily of every other subject, is
  still a pair of it (`pairOf_selfNamed`), and it meets the obligation in a class none of whose
  members fulfils the property (`oPair_selfNamed`). The pair whose only input is trivial is
  unaffected by that choice.
* That one subject meets every pair. That is O2 before running (`O2Run`), and a model of the record
  in `C` serves each admitted input of each pair (`PairOf.served_of_meets`).
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-- A precondition-postcondition pair for subjects of type `W`: what a property says for each input.
-/
structure Pair (W : Type u) where
  /-- What the implementation does not choose: an argument, a state, a world from a class. -/
  Input : Type u
  /-- What the record demands of the input. -/
  pre : Input → Prop
  /-- What the property then asks of the subject at that input. -/
  post : Input → W → Prop

namespace Pair

/-- The subject `w` meets the pair `q`: the postcondition at every input the precondition admits. -/
def Met (q : Pair W) (w : W) : Prop := ∀ x, q.pre x → q.post x w

/-- The pair `q` says exactly the statement `S`: a subject meets `q` exactly when `S` holds of it. -/
def Says (q : Pair W) (S : W → Prop) : Prop := ∀ w, S w ↔ q.Met w

/-- The pair of the property `c` of the record `r` whose only input is trivial: its postcondition is
the property wherever the record's domain hypotheses hold. -/
def whole (r : IntentRecord W) (c : Clause W) : Pair W :=
  ⟨PUnit, fun _ => True, fun _ w => r.Dom w → c.holds w⟩

end Pair

/-- `q` is a pair of the property `c` of the record `r`: `c` is one of the record's properties, and
`q` says exactly what an implementation must prove of it, that it holds wherever the domain
hypotheses do. -/
def IntentRecord.PairOf (r : IntentRecord W) (c : Clause W) (q : Pair W) : Prop :=
  c ∈ r.props ∧ q.Says fun w => r.Dom w → c.holds w

/-! ## The obligation -/

/-- The pair obligation's goals for the pair `q` and the implementation class `C`: an input the
precondition admits, and, for each input the precondition admits, a subject in `C` that meets the
postcondition there. -/
def oPair (q : Pair W) (C : W → Prop) : List Prop :=
  [HasInstance q.pre, ∀ x, q.pre x → HasInstance fun w => C w ∧ q.post x w]

/-- The pair obligation holds of `q` in the class `C`. -/
def OPair (q : Pair W) (C : W → Prop) : Prop := Goals (oPair q C)

/-- What the pair obligation asks, written apart from the former. -/
def intendedOPair : Pair W → (W → Prop) → Prop
  | ⟨_, pre, post⟩, C => (∃ x, pre x) ∧ ∀ x, pre x → ∃ w, C w ∧ post x w

/-- The pair obligation's former states it, for every pair and every class. -/
theorem oPair_correct (q : Pair W) (C : W → Prop) : OPair q C ↔ intendedOPair q C := by
  obtain ⟨Input, pre, post⟩ := q
  simp only [OPair, oPair, Goals, HasInstance, intendedOPair, and_true]

/-- Each goal met gives the obligation. -/
theorem oPair_of {q : Pair W} {C : W → Prop} (hAdmits : ∃ x, q.pre x)
    (hServed : ∀ x, q.pre x → ∃ w, C w ∧ q.post x w) : OPair q C :=
  ⟨hAdmits, hServed, trivial⟩

/-- The obligation gives an input the precondition admits. -/
theorem OPair.admits {q : Pair W} {C : W → Prop} (h : OPair q C) : ∃ x, q.pre x :=
  h.1

/-- The obligation gives, for every input the precondition admits, a subject of the class that
meets the postcondition there. -/
theorem OPair.served {q : Pair W} {C : W → Prop} (h : OPair q C) :
    ∀ x, q.pre x → ∃ w, C w ∧ q.post x w :=
  h.2.1

/-- An admitted input that no subject of the class serves refutes the obligation: the precondition
is too wide for the class. -/
theorem not_oPair_of_unserved {q : Pair W} {C : W → Prop} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, C w → ¬ q.post x w) : ¬ OPair q C := fun hq =>
  let ⟨w, hC, hp⟩ := hq.served x hx
  h w hC hp

/-- A pair whose precondition admits no input refutes the obligation, whatever the class. -/
theorem not_oPair_of_admits_nothing {q : Pair W} (h : ∀ x, ¬ q.pre x) (C : W → Prop) :
    ¬ OPair q C := fun hq =>
  let ⟨x, hx⟩ := hq.admits
  h x hx

/-! ## The implementation class -/

/-- The obligation in a class gives it in every wider class. -/
theorem OPair.mono {q : Pair W} {C C' : W → Prop} (h : OPair q C) (hC : ∀ w, C w → C' w) :
    OPair q C' :=
  oPair_of h.admits fun x hx =>
    let ⟨w, hw, hp⟩ := h.served x hx
    ⟨w, hC w hw, hp⟩

/-- No pair meets the obligation in the empty class. -/
theorem not_oPair_empty (q : Pair W) : ¬ OPair q fun _ => False := fun hq =>
  let ⟨x, hx⟩ := hq.admits
  let ⟨_, hC, _⟩ := hq.served x hx
  hC

/-! ## Pairs of a record's properties -/

/-- Every property of a record has a pair: the one whose only input is trivial. -/
theorem pairOf_whole {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    r.PairOf c (Pair.whole r c) :=
  ⟨hc, fun _ => ⟨fun h _ _ => h, fun h => h PUnit.unit trivial⟩⟩

/-- Every property of a record gives at least one pair. -/
theorem exists_pairOf {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    ∃ q, r.PairOf c q :=
  ⟨_, pairOf_whole hc⟩

/-- A subject meets a pair of a property exactly when the property holds of it wherever the domain
hypotheses do. -/
theorem IntentRecord.PairOf.met_iff {r : IntentRecord W} {c : Clause W} {q : Pair W}
    (hq : r.PairOf c q) (w : W) : q.Met w ↔ (r.Dom w → c.holds w) :=
  (hq.2 w).symm

/-- The obligation of the pair whose only input is trivial: a subject of the class fulfils the
property wherever the domain hypotheses hold. -/
theorem oPair_whole_iff (r : IntentRecord W) (c : Clause W) (C : W → Prop) :
    OPair (Pair.whole r c) C ↔ ∃ w, C w ∧ (r.Dom w → c.holds w) := by
  rw [oPair_correct]
  simp only [Pair.whole, intendedOPair, true_and, forall_const, exists_const]

/-- The obligation of the pair whose only input is trivial gives the obligation of every pair of the
property whose precondition admits an input: one subject of the class that fulfils the property
serves every input of each of its pairs. -/
theorem OPair.of_whole {r : IntentRecord W} {c : Clause W} {q : Pair W} {C : W → Prop}
    (hq : r.PairOf c q) (hAdmits : ∃ x, q.pre x) (h : OPair (Pair.whole r c) C) : OPair q C :=
  let ⟨w, hC, hf⟩ := (oPair_whole_iff r c C).mp h
  oPair_of hAdmits fun x hx => ⟨w, hC, (hq.met_iff w).mpr hf x hx⟩

/-- A model of the record in the class serves every input each pair of its properties admits: O2
before running, with its subject in the class, discharges the second goal of every such pair. -/
theorem IntentRecord.PairOf.served_of_meets {r : IntentRecord W} {c : Clause W} {q : Pair W}
    {C : W → Prop} (hq : r.PairOf c q) {w : W} (hw : r.Meets w) (hC : C w) :
    ∀ x, q.pre x → ∃ w, C w ∧ q.post x w := fun x hx =>
  ⟨w, hC, (hq.met_iff w).mpr (fun _ => hw.2 c hq.1) x hx⟩

/-! ## What a pair's input does not fix -/

/-- A pair of the property `c` of the record `r` whose input names a subject: at the subject `v` it
asks the property only of `v` itself, and holds emptily of every other subject. -/
def Pair.selfNamed (r : IntentRecord W) (c : Clause W) : Pair W :=
  ⟨W, fun _ => True, fun v w => v = w → r.Dom w → c.holds w⟩

/-- `Pair.selfNamed` is a pair of the property, since `PairOf` checks only what a pair says. -/
theorem pairOf_selfNamed {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    r.PairOf c (Pair.selfNamed r c) :=
  ⟨hc, fun w => ⟨fun h _ _ e => e ▸ h, fun h => h w trivial rfl⟩⟩

/-- A pair whose input is not one the property speaks of can meet the obligation in a class none of
whose members fulfils the property: `Pair.selfNamed` meets it in every class with two different
members. The pair whose only input is trivial, which no choice of input affects, fails in such a
class (`oPair_whole_iff`). -/
theorem oPair_selfNamed {r : IntentRecord W} {c : Clause W} {C : W → Prop} {w₁ w₂ : W}
    (h₁ : C w₁) (h₂ : C w₂) (hne : w₁ ≠ w₂) : OPair (Pair.selfNamed r c) C := by
  refine oPair_of ⟨w₁, trivial⟩ fun v _ => ?_
  by_cases hv : v = w₁
  · exact ⟨w₂, h₂, fun e => absurd (hv.symm.trans e) hne⟩
  · exact ⟨w₁, h₁, fun e => absurd e hv⟩

end LeanIntent
