module

public import LeanIntent.Obligations

public section

namespace LeanIntent

universe u

variable {W : Type u}

structure Pair (W : Type u) where
  Input : Type u
  pre : Input → Prop
  post : Input → W → Prop

namespace Pair

@[expose] def Met (q : Pair W) (w : W) : Prop := ∀ x, q.pre x → q.post x w

@[expose] def Says (q : Pair W) (S : W → Prop) : Prop := ∀ w, S w ↔ q.Met w

@[expose] def whole (r : IntentRecord W) (c : Clause W) : Pair W :=
  ⟨PUnit, fun _ => True, fun _ w => r.Dom w → c.holds w⟩

end Pair

@[expose] def IntentRecord.PairOf (r : IntentRecord W) (c : Clause W) (q : Pair W) : Prop :=
  c ∈ r.props ∧ q.Says fun w => r.Dom w → c.holds w

@[expose] def oPair (q : Pair W) (C : W → Prop) : List Prop :=
  [HasInstance q.pre, ∀ x, q.pre x → HasInstance fun w => C w ∧ q.post x w]

@[expose] def OPair (q : Pair W) (C : W → Prop) : Prop := Goals (oPair q C)

@[expose] def intendedOPair : Pair W → (W → Prop) → Prop
  | ⟨_, pre, post⟩, C => (∃ x, pre x) ∧ ∀ x, pre x → ∃ w, C w ∧ post x w

theorem oPair_correct (q : Pair W) (C : W → Prop) : OPair q C ↔ intendedOPair q C := by
  obtain ⟨Input, pre, post⟩ := q
  simp only [OPair, oPair, Goals, HasInstance, intendedOPair, and_true]

theorem oPair_of {q : Pair W} {C : W → Prop} (hAdmits : ∃ x, q.pre x)
    (hServed : ∀ x, q.pre x → ∃ w, C w ∧ q.post x w) : OPair q C :=
  ⟨hAdmits, hServed, trivial⟩

theorem OPair.admits {q : Pair W} {C : W → Prop} (h : OPair q C) : ∃ x, q.pre x :=
  h.1

theorem OPair.served {q : Pair W} {C : W → Prop} (h : OPair q C) :
    ∀ x, q.pre x → ∃ w, C w ∧ q.post x w :=
  h.2.1

theorem not_oPair_of_unserved {q : Pair W} {C : W → Prop} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, C w → ¬ q.post x w) : ¬ OPair q C := fun hq =>
  let ⟨w, hC, hp⟩ := hq.served x hx
  h w hC hp

theorem not_oPair_of_admits_nothing {q : Pair W} (h : ∀ x, ¬ q.pre x) (C : W → Prop) :
    ¬ OPair q C := fun hq =>
  let ⟨x, hx⟩ := hq.admits
  h x hx

theorem OPair.mono {q : Pair W} {C C' : W → Prop} (h : OPair q C) (hC : ∀ w, C w → C' w) :
    OPair q C' :=
  oPair_of h.admits fun x hx =>
    let ⟨w, hw, hp⟩ := h.served x hx
    ⟨w, hC w hw, hp⟩

theorem not_oPair_empty (q : Pair W) : ¬ OPair q fun _ => False := fun hq =>
  let ⟨x, hx⟩ := hq.admits
  let ⟨_, hC, _⟩ := hq.served x hx
  hC

theorem pairOf_whole {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    r.PairOf c (Pair.whole r c) :=
  ⟨hc, fun _ => ⟨fun h _ _ => h, fun h => h PUnit.unit trivial⟩⟩

theorem exists_pairOf {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    ∃ q, r.PairOf c q :=
  ⟨_, pairOf_whole hc⟩

theorem IntentRecord.PairOf.met_iff {r : IntentRecord W} {c : Clause W} {q : Pair W}
    (hq : r.PairOf c q) (w : W) : q.Met w ↔ (r.Dom w → c.holds w) :=
  (hq.2 w).symm

theorem oPair_whole_iff (r : IntentRecord W) (c : Clause W) (C : W → Prop) :
    OPair (Pair.whole r c) C ↔ ∃ w, C w ∧ (r.Dom w → c.holds w) := by
  rw [oPair_correct]
  simp only [Pair.whole, intendedOPair, true_and, forall_const, exists_const]

theorem OPair.of_whole {r : IntentRecord W} {c : Clause W} {q : Pair W} {C : W → Prop}
    (hq : r.PairOf c q) (hAdmits : ∃ x, q.pre x) (h : OPair (Pair.whole r c) C) : OPair q C :=
  let ⟨w, hC, hf⟩ := (oPair_whole_iff r c C).mp h
  oPair_of hAdmits fun x hx => ⟨w, hC, (hq.met_iff w).mpr hf x hx⟩

theorem IntentRecord.PairOf.served_of_meets {r : IntentRecord W} {c : Clause W} {q : Pair W}
    {C : W → Prop} (hq : r.PairOf c q) {w : W} (hw : r.Meets w) (hC : C w) :
    ∀ x, q.pre x → ∃ w, C w ∧ q.post x w := fun x hx =>
  ⟨w, hC, (hq.met_iff w).mpr (fun _ => hw.2 c hq.1) x hx⟩

@[expose] def Pair.selfNamed (r : IntentRecord W) (c : Clause W) : Pair W :=
  ⟨W, fun _ => True, fun v w => v = w → r.Dom w → c.holds w⟩

theorem pairOf_selfNamed {r : IntentRecord W} {c : Clause W} (hc : c ∈ r.props) :
    r.PairOf c (Pair.selfNamed r c) :=
  ⟨hc, fun w => ⟨fun h _ _ e => e ▸ h, fun h => h w trivial rfl⟩⟩

theorem oPair_selfNamed {r : IntentRecord W} {c : Clause W} {C : W → Prop} {w₁ w₂ : W}
    (h₁ : C w₁) (h₂ : C w₂) (hne : w₁ ≠ w₂) : OPair (Pair.selfNamed r c) C := by
  refine oPair_of ⟨w₁, trivial⟩ fun v _ => ?_
  by_cases hv : v = w₁
  · exact ⟨w₂, h₂, fun e => absurd (hv.symm.trans e) hne⟩
  · exact ⟨w₁, h₁, fun e => absurd e hv⟩

end LeanIntent
