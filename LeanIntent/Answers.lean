module

public import LeanIntent.Obligations

public section

namespace LeanIntent

universe u

variable {W : Type u}

inductive Consequence.Kind where
  | entailment
  | possibility

structure Consequence (W : Type u) where
  name : String
  kind : Consequence.Kind
  holds : W → Prop

inductive Verdict where
  | confirmed
  | declined

structure Answer (W : Type u) where
  consequence : Consequence W
  verdict : Verdict

@[expose] def Answer.KeptBy (a : Answer W) (r : IntentRecord W) : Prop :=
  match a.consequence.kind, a.verdict with
  | .entailment, .confirmed => ∀ w, r.Meets w → a.consequence.holds w
  | .entailment, .declined => HasInstance fun w => r.Meets w ∧ ¬ a.consequence.holds w
  | .possibility, .confirmed => HasInstance fun w => r.Meets w ∧ a.consequence.holds w
  | .possibility, .declined => ∀ w, r.Meets w → ¬ a.consequence.holds w

@[expose] def kept (r : IntentRecord W) (answers : List (Answer W)) : List Prop :=
  answers.map fun a => a.KeptBy r

@[expose] def Keeps (r : IntentRecord W) (answers : List (Answer W)) : Prop := Goals (kept r answers)

@[expose] def intendedKeeps (r : IntentRecord W) (answers : List (Answer W)) : Prop :=
  ∀ a ∈ answers, match a with
  | ⟨⟨_, .entailment, c⟩, .confirmed⟩ =>
      ∀ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) → c w
  | ⟨⟨_, .entailment, c⟩, .declined⟩ =>
      ∃ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) ∧ ¬ c w
  | ⟨⟨_, .possibility, c⟩, .confirmed⟩ =>
      ∃ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) ∧ c w
  | ⟨⟨_, .possibility, c⟩, .declined⟩ =>
      ∀ w, ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w) → ¬ c w

theorem keeps_correct (r : IntentRecord W) (answers : List (Answer W)) :
    Keeps r answers ↔ intendedKeeps r answers := by
  simp only [Keeps, kept, goals_map, intendedKeeps]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;>
    simp only [Answer.KeptBy, HasInstance, IntentRecord.Meets, IntentRecord.Dom,
      IntentRecord.Props]

theorem keeps_iff (r : IntentRecord W) (answers : List (Answer W)) :
    Keeps r answers ↔ ∀ a ∈ answers, a.KeptBy r :=
  goals_map _ _

@[expose] def Answer.opposite (a : Answer W) : Answer W where
  consequence := a.consequence
  verdict := match a.verdict with
    | .confirmed => .declined
    | .declined => .confirmed

theorem Answer.keptBy_opposite (a : Answer W) (r : IntentRecord W) :
    a.opposite.KeptBy r ↔ ¬ a.KeptBy r := by
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;>
    simp only [Answer.opposite, Answer.KeptBy, HasInstance, Classical.not_forall,
      exists_prop, not_exists, not_and, Classical.not_not]

theorem not_keeps_iff (r : IntentRecord W) (answers : List (Answer W)) :
    ¬ Keeps r answers ↔ ∃ a ∈ answers, a.opposite.KeptBy r := by
  simp only [keeps_iff, Answer.keptBy_opposite, Classical.not_forall, exists_prop]

theorem not_keeps_of_opposite {r : IntentRecord W} {answers : List (Answer W)} {a : Answer W}
    (ha : a ∈ answers) (h : a.opposite.KeptBy r) : ¬ Keeps r answers :=
  fun hk => (a.keptBy_opposite r).mp h ((keeps_iff r answers).mp hk a ha)

theorem not_keeps_of_conflict {r : IntentRecord W} {answers : List (Answer W)} {a : Answer W}
    (ha : a ∈ answers) (hb : a.opposite ∈ answers) : ¬ Keeps r answers :=
  fun hk => not_keeps_of_opposite ha ((keeps_iff r answers).mp hk _ hb) hk

theorem Answer.keptBy_congr (a : Answer W) {r r' : IntentRecord W}
    (h : ∀ w, r.Meets w ↔ r'.Meets w) : a.KeptBy r ↔ a.KeptBy r' := by
  obtain ⟨⟨_, kind, c⟩, verdict⟩ := a
  cases kind <;> cases verdict <;> simp only [Answer.KeptBy, HasInstance, h]

theorem keeps_congr {r r' : IntentRecord W} (answers : List (Answer W))
    (h : ∀ w, r.Meets w ↔ r'.Meets w) : Keeps r answers ↔ Keeps r' answers := by
  simp only [keeps_iff, Answer.keptBy_congr _ h]

structure Accepted (answers : List (Answer W)) where
  record : IntentRecord W
  keeps : Keeps record answers

theorem Accepted.keptBy {answers : List (Answer W)} (x : Accepted answers) {a : Answer W}
    (ha : a ∈ answers) : a.KeptBy x.record :=
  (keeps_iff _ _).mp x.keeps a ha

theorem accepted_iff (answers : List (Answer W)) (r : IntentRecord W) :
    (∃ x : Accepted answers, x.record = r) ↔ ∀ a ∈ answers, a.KeptBy r :=
  ⟨fun ⟨x, hx⟩ => hx ▸ fun _ ha => x.keptBy ha, fun h => ⟨⟨r, (keeps_iff r answers).mpr h⟩, rfl⟩⟩

theorem Accepted.entailed {answers : List (Answer W)} (x : Accepted answers) {n : String}
    {c : W → Prop} (ha : ⟨⟨n, .entailment, c⟩, .confirmed⟩ ∈ answers) {w : W}
    (hw : x.record.Meets w) : c w :=
  x.keptBy ha w hw

theorem Accepted.excluded {answers : List (Answer W)} (x : Accepted answers) {n : String}
    {c : W → Prop} (ha : ⟨⟨n, .possibility, c⟩, .declined⟩ ∈ answers) {w : W}
    (hw : x.record.Meets w) : ¬ c w :=
  x.keptBy ha w hw

end LeanIntent
