import LeanIntent.Obligations

/-!
# Progress: the obligations refuse no adequate record

The obligations must not refuse intent that has content. A record passes O1 to O5 whenever its
domain hypotheses have a joint model, each predicate of its vocabulary has an instance, each
property has a non-instance, and no subject that does nothing meets it, its shape being sound (for
a description made of functions, they and its plain values are the whole subject and each function
is free); O5 is then met by the widest freedom, which is shown with the record (`progress`). Before a
deliverable runs, the record's joint model is supplied by the deliverable itself
(`o2Run_of_meets`), so no record is asked for a model before the work that finds one.
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-- O4 holds when the record's shape is sound and no subject that does nothing meets it: a function
meets it by totality, a plain value trivially, and a subject with state or a description made of
functions by the premises. -/
theorem o4_of_idle (r : IntentRecord W) (hs : r.shape.Sound)
    (h : ∀ w, r.shape.Idle w → ¬ r.Meets w) : O4 r := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape with
  | value => trivial
  | function A B => exact (goals_singleton _).mpr fun f x => ⟨f x, rfl⟩
  | step => exact (goals_singleton _).mpr h
  | stepOn => exact (goals_singleton _).mpr h
  | action => exact (goals_singleton _).mpr h
  | actionOn => exact (goals_singleton _).mpr h
  | bundle => exact ⟨hs.1, hs.2, h, trivial⟩

/-- The obligations refuse no record with content: one whose domain hypotheses have a joint model,
whose vocabulary's predicates each have an instance, whose properties each have a non-instance, whose
shape is sound and which no subject that does nothing meets, passes O1 to O5, O5 by the widest
freedom. -/
theorem progress (r : IntentRecord W) (hDom : ∃ w, r.Dom w)
    (hVocab : ∀ p ∈ r.vocab, ∃ a, p.holds a) (hRefutable : ∀ p ∈ r.props, ∃ w, ¬ p.holds w)
    (hShape : r.shape.Sound) (hIdle : ∀ w, r.shape.Idle w → ¬ r.Meets w) :
    (∀ g ∈ o1 r, Nonempty g.1) ∧ O2 r ∧ O3 r ∧ O4 r ∧ O5 r .widest :=
  ⟨o1_wellTyped r, (o2_correct r).mpr ⟨hDom, hVocab⟩, (o3_correct r).mpr hRefutable,
    o4_of_idle r hShape hIdle, o5_widest r⟩

/-- A model of the record, such as a deliverable's subject under the domain hypotheses, meets O2
before running. -/
theorem o2Run_of_meets {r : IntentRecord W} {w : W} (h : r.Meets w) : O2Run r :=
  (goals_singleton _).mpr ⟨w, h⟩

end LeanIntent
