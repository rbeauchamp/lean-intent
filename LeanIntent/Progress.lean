module

public import LeanIntent.Obligations

public section

namespace LeanIntent

universe u

variable {W : Type u}

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

theorem progress (r : IntentRecord W) (hDom : ∃ w, r.Dom w)
    (hVocab : ∀ p ∈ r.vocab, ∃ a, p.holds a) (hRefutable : ∀ p ∈ r.props, ∃ w, ¬ p.holds w)
    (hShape : r.shape.Sound) (hIdle : ∀ w, r.shape.Idle w → ¬ r.Meets w) :
    (∀ g ∈ o1 r, Nonempty g.1) ∧ O2 r ∧ O3 r ∧ O4 r ∧ O5 r .widest :=
  ⟨o1_wellTyped r, (o2_correct r).mpr ⟨hDom, hVocab⟩, (o3_correct r).mpr hRefutable,
    o4_of_idle r hShape hIdle, o5_widest r⟩

theorem o2Run_of_meets {r : IntentRecord W} {w : W} (h : r.Meets w) : O2Run r :=
  (goals_singleton _).mpr ⟨w, h⟩

end LeanIntent
