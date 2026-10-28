import LeanIntent.Progress

/-!
# Refinement links from an intent record to an implementation

Below the intent record every link is proved. An implementation of type `A` has a specification
`S : A → Prop`, and a mapping `m : A → W` reads an implementation as the record's subject; the
identity when the two types agree. `S` refines the record when every
implementation meeting `S`, wherever the record's domain hypotheses hold of its subject, has a
subject that meets every property (`Refines`). Specifications may be stacked: a lower specification
refines a higher one under the same domain hypotheses (`RefinesSpec`), and the links compose
(`Refines.comp`).

The link that matters is `fulfils`: from a proof that an implementation meets its specification and
a proof that the specification refines the record, the implementation fulfils the record, for every
implementation and every record. So a proof that the code meets its specification composes into a
proof that it meets the intent.

What the link carries, and what it does not:

* the freedom O5 confirms holds of the subjects of any two implementations meeting the
  specification, not of the implementations themselves (`Refines.determinate`), so concrete
  equality needs a mapping that reflects it;
* a specification is refuted only by a counterexample to the record in the mapping's image
  (`Refines.refutes`); `LeanIntentExamples.Transfer` shows a specification that is neither
  refutable nor determinate refining a record that is both;
* a deliverable that meets its specification under the domain hypotheses supplies the record's
  joint model required before it runs (`Refines.o2Run`).

The domain hypotheses are read only from the record, never from a link, so a fact a link relies on
is one the owner confirmed.
-/

namespace LeanIntent

universe u v w

variable {W : Type u} {A : Sort v} {C : Sort w}

/-- `S`, a specification of implementations of type `A`, refines the intent record `r` through the
mapping `m`: every implementation meeting `S`, wherever the record's domain hypotheses hold of its
subject, has a subject that meets every property of `r`. -/
def Refines (r : IntentRecord W) (m : A → W) (S : A → Prop) : Prop :=
  ∀ a, S a → r.Dom (m a) → r.Props (m a)

/-- `L`, a specification of implementations of type `C`, refines `S` through `n`, under the domain
hypotheses of `r` read at the subject `m (n c)`. -/
def RefinesSpec (r : IntentRecord W) (m : A → W) (S : A → Prop) (n : C → A) (L : C → Prop) :
    Prop :=
  ∀ c, L c → r.Dom (m (n c)) → S (n c)

/-- The refinement link: an implementation proved to meet a specification that refines the record
fulfils the record, for every implementation and every record. -/
theorem fulfils {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S) {impl : A}
    (hS : S impl) : r.Fulfilled (m impl) :=
  hR impl hS

/-- Links compose: a specification that refines one refining the record refines the record. -/
theorem Refines.comp {r : IntentRecord W} {m : A → W} {S : A → Prop} {n : C → A} {L : C → Prop}
    (hS : Refines r m S) (hL : RefinesSpec r m S n L) : Refines r (fun c => m (n c)) L :=
  fun c hc hd => hS (n c) (hL c hc hd) hd

/-- With the identity mapping, a specification refines the record exactly when every subject that
meets it fulfils the record. -/
theorem refines_id_iff {r : IntentRecord W} {S : W → Prop} :
    Refines r (fun w => w) S ↔ ∀ w, S w → r.Fulfilled w :=
  Iff.rfl

/-- The record refines itself: its own properties are a specification of its subject. -/
theorem refines_self (r : IntentRecord W) : Refines r (fun w => w) r.Props :=
  fun _ h _ => h

/-- The freedom O5 confirms transfers to the subjects of implementations meeting a refining
specification, under the domain hypotheses. -/
theorem Refines.determinate {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {R : Freedom W} (h5 : O5 r R) {a b : A} (ha : S a) (hb : S b) (hda : r.Dom (m a))
    (hdb : r.Dom (m b)) : R.relates r (m a) (m b) :=
  h5.relates ⟨hda, hR a ha hda⟩ ⟨hdb, hR b hb hdb⟩

/-- A counterexample to the record in the mapping's image refutes a refining specification. -/
theorem Refines.refutes {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {a : A} (hd : r.Dom (m a)) (hp : ¬ r.Props (m a)) : ¬ S a :=
  fun hs => hp (hR a hs hd)

/-- A deliverable that meets a refining specification under the domain hypotheses supplies the
record's joint model, O2 before it runs. -/
theorem Refines.o2Run {r : IntentRecord W} {m : A → W} {S : A → Prop} (hR : Refines r m S)
    {impl : A} (hS : S impl) (hd : r.Dom (m impl)) : O2Run r :=
  o2Run_of_meets ⟨hd, hR impl hS hd⟩

end LeanIntent
