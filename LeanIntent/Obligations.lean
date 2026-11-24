module

public import LeanIntent.Record

public section

namespace LeanIntent

universe u

variable {W : Type u}

@[expose] def Goals : List Prop → Prop
  | [] => True
  | g :: gs => g ∧ Goals gs

theorem goals_iff : (gs : List Prop) → (Goals gs ↔ ∀ g ∈ gs, g)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | g :: gs => by rw [Goals, List.forall_mem_cons, goals_iff gs]

theorem goals_map {α : Sort _} (f : α → Prop) : (l : List α) → (Goals (l.map f) ↔ ∀ a ∈ l, f a)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | a :: l => by rw [List.map_cons, Goals, List.forall_mem_cons, goals_map f l]

theorem goals_singleton (g : Prop) : Goals [g] ↔ g := by simp [Goals]

@[expose] def HasInstance {α : Sort _} (P : α → Prop) : Prop := ∃ a, P a

@[expose] def HasNonInstance {α : Sort _} (P : α → Prop) : Prop := ∃ a, ¬ P a

@[expose] def Clause.typed (c : Clause W) : (T : Type u) × T := ⟨W → Prop, c.holds⟩

@[expose] def Pred.typed (p : Pred.{u}) : (T : Type u) × T := ⟨p.Arg → Prop, p.holds⟩

@[expose] def o1 (r : IntentRecord W) : List ((T : Type u) × T) :=
  r.dom.map Clause.typed ++ r.props.map Clause.typed ++ r.vocab.map Pred.typed

@[expose] def intendedO1 : IntentRecord W → List ((T : Type u) × T)
  | ⟨_, dom, props, vocab⟩ =>
    dom.map (fun c => ⟨W → Prop, c.holds⟩) ++ props.map (fun c => ⟨W → Prop, c.holds⟩) ++
      vocab.map (fun p => ⟨p.Arg → Prop, p.holds⟩)

theorem o1_correct (r : IntentRecord W) : o1 r = intendedO1 r := by
  cases r; rfl

theorem o1_wellTyped (r : IntentRecord W) : ∀ g ∈ o1 r, Nonempty g.1 :=
  fun g _ => ⟨g.2⟩

@[expose] def o2 (r : IntentRecord W) : List Prop :=
  HasInstance r.Dom :: r.vocab.map fun p => HasInstance p.holds

@[expose] def O2 (r : IntentRecord W) : Prop := Goals (o2 r)

@[expose] def intendedO2 (r : IntentRecord W) : Prop :=
  (∃ w, ∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.vocab, ∃ a, p.holds a

theorem o2_correct (r : IntentRecord W) : O2 r ↔ intendedO2 r := by
  simp only [O2, o2, Goals, goals_map, HasInstance, IntentRecord.Dom, intendedO2]

@[expose] def o2Run (r : IntentRecord W) : List Prop := [HasInstance r.Meets]

@[expose] def O2Run (r : IntentRecord W) : Prop := Goals (o2Run r)

@[expose] def intendedO2Run (r : IntentRecord W) : Prop :=
  ∃ w, (∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w

theorem o2Run_correct (r : IntentRecord W) : O2Run r ↔ intendedO2Run r := by
  simp only [O2Run, o2Run, goals_singleton, HasInstance, IntentRecord.Meets, IntentRecord.Dom,
    IntentRecord.Props, intendedO2Run]

@[expose] def o3 (r : IntentRecord W) : List Prop := r.props.map fun p => HasNonInstance p.holds

@[expose] def O3 (r : IntentRecord W) : Prop := Goals (o3 r)

@[expose] def intendedO3 (r : IntentRecord W) : Prop := ∀ p ∈ r.props, ∃ w, ¬ p.holds w

theorem o3_correct (r : IntentRecord W) : O3 r ↔ intendedO3 r := by
  simp only [O3, o3, goals_map, HasNonInstance, intendedO3]

@[expose] def Member.Ignores (m : Member W) (w : W) : Prop := ∀ x y, m.get w x = m.get w y

@[expose] def Shape.Covers {D : Type u} (data : W → D) (ms : List (Member W)) : Prop :=
  ∀ u v, data u = data v → (∀ m ∈ ms, m.get u = m.get v) → u = v

@[expose] def Shape.Free (ms : List (Member W)) : Prop := ∀ m ∈ ms, ∀ f : m.In → m.Out, ∃ w, m.get w = f

@[expose] def Shape.Sound : {W : Type u} → Shape W → Prop
  | _, .bundle data first rest => Shape.Covers data (first :: rest) ∧ Shape.Free (first :: rest)
  | _, _ => True

@[expose] def Shape.Idle : {W : Type u} → Shape W → W → Prop
  | _, .value _, _ => False
  | _, .function _ _, _ => False
  | _, .step _, f => ∀ s, f s = s
  | _, .stepOn _ _, f => ∀ s i, f s i = s
  | _, .action _ _, f => ∀ s, (f s).2 = s
  | _, .actionOn _ _ _, f => ∀ s i, (f s i).2 = s
  | _, .bundle _ first rest, w => ∃ m ∈ first :: rest, m.Ignores w

@[expose] def Total (A : Type u) (B : A → Type u) : Prop := ∀ f : (x : A) → B x, ∀ x, ∃ y, f x = y

@[expose] def Shape.progress : {W : Type u} → Shape W → (W → Prop) → List Prop
  | _, .value _, _ => []
  | _, .function A B, _ => [Total A B]
  | _, s@(.bundle data first rest), meets =>
    [Shape.Covers data (first :: rest), Shape.Free (first :: rest), ∀ w, s.Idle w → ¬ meets w]
  | _, s, meets => [∀ w, s.Idle w → ¬ meets w]

@[expose] def o4 (r : IntentRecord W) : List Prop := r.shape.progress r.Meets

@[expose] def O4 (r : IntentRecord W) : Prop := Goals (o4 r)

@[expose] def intendedO4At : {W : Type u} → Shape W → IntentRecord W → Prop
  | _, .value _, _ => True
  | _, .function A B, _ => ∀ f : (x : A) → B x, ∀ x, ∃ y, f x = y
  | _, .step S, r => ∀ f : S → S, (∀ s, f s = s) →
      ¬ ((∀ d ∈ r.dom, d.holds f) ∧ ∀ p ∈ r.props, p.holds f)
  | _, .stepOn S I, r => ∀ f : S → I → S, (∀ s i, f s i = s) →
      ¬ ((∀ d ∈ r.dom, d.holds f) ∧ ∀ p ∈ r.props, p.holds f)
  | _, .action S O, r => ∀ f : S → O × S, (∀ s, (f s).2 = s) →
      ¬ ((∀ d ∈ r.dom, d.holds f) ∧ ∀ p ∈ r.props, p.holds f)
  | _, .actionOn S I O, r => ∀ f : S → I → O × S, (∀ s i, (f s i).2 = s) →
      ¬ ((∀ d ∈ r.dom, d.holds f) ∧ ∀ p ∈ r.props, p.holds f)
  | W, .bundle data first rest, r =>
      (∀ u v : W, data u = data v → (∀ m ∈ first :: rest, m.get u = m.get v) → u = v) ∧
      (∀ m ∈ first :: rest, ∀ f : m.In → m.Out, ∃ w, m.get w = f) ∧
      ∀ w : W, (∃ m ∈ first :: rest, ∀ x y, m.get w x = m.get w y) →
        ¬ ((∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w)

@[expose] def intendedO4 (r : IntentRecord W) : Prop := intendedO4At r.shape r

theorem o4_correct (r : IntentRecord W) : O4 r ↔ intendedO4 r := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape <;>
    simp only [O4, o4, Shape.progress, Goals, goals_singleton, Total, Shape.Idle, Shape.Covers,
      Shape.Free, Member.Ignores, IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props,
      intendedO4, intendedO4At, and_true]

theorem o4_eq_nil_iff (r : IntentRecord W) : o4 r = [] ↔ r.shape = .value W := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape <;> simp [o4, Shape.progress]

theorem o4_function {A : Type u} {B : A → Type u} (r : IntentRecord ((x : A) → B x))
    (h : r.shape = .function A B) : O4 r := by
  rw [o4_correct, intendedO4, h]
  exact fun f x => ⟨f x, rfl⟩

theorem not_o4_of_idle {r : IntentRecord W} {w : W} (hIdle : r.shape.Idle w) (hw : r.Meets w) :
    ¬ O4 r := by
  intro h
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape with
  | value => exact hIdle.elim
  | function => exact hIdle.elim
  | step => exact (goals_singleton _).mp h w hIdle hw
  | stepOn => exact (goals_singleton _).mp h w hIdle hw
  | action => exact (goals_singleton _).mp h w hIdle hw
  | actionOn => exact (goals_singleton _).mp h w hIdle hw
  | bundle => exact h.2.2.1 w hIdle hw

theorem Shape.exists_ignores {m : Member W} (hFree : ∀ f : m.In → m.Out, ∃ w, m.get w = f)
    (b : m.Out) : ∃ w, m.Ignores w :=
  let ⟨w, hw⟩ := hFree fun _ => b
  ⟨w, fun x y => by rw [hw]⟩

theorem not_o4_bundle_of_trivial {D : Type u} {data : W → D} {first : Member W}
    {rest : List (Member W)} {vocab : List Pred.{u}} (b : first.Out) :
    ¬ O4 (⟨.bundle data first rest, [], [], vocab⟩ : IntentRecord W) := by
  intro h
  obtain ⟨w, hw⟩ := Shape.exists_ignores (fun f => h.2.1 first (List.mem_cons_self ..) f) b
  exact h.2.2.1 w ⟨first, List.mem_cons_self .., hw⟩
    ⟨(fun _ hd => nomatch hd), fun _ hp => nomatch hp⟩

theorem no_model_of_o4_bundle_subsingleton {D : Type u} {data : W → D} {first : Member W}
    {rest : List (Member W)} {r : IntentRecord W} (hs : r.shape = .bundle data first rest)
    {m : Member W} (hm : m ∈ first :: rest) (hIn : ∀ x y : m.In, x = y) (h : O4 r) (w : W) :
    ¬ r.Meets w := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases hs
  exact h.2.2.1 w ⟨m, hm, fun x y => by rw [hIn x y]⟩

inductive Freedom (W : Type u) where
  | eq
  | widest
  | rel (R : W → W → Prop)

@[expose] def Freedom.relates (r : IntentRecord W) : Freedom W → W → W → Prop
  | .eq, u, v => u = v
  | .widest, u, v => r.Meets u ∧ r.Meets v
  | .rel R, u, v => R u v

@[expose] def o5 (r : IntentRecord W) (R : Freedom W) : List Prop :=
  [∀ u v, r.Meets u → r.Meets v → R.relates r u v]

@[expose] def O5 (r : IntentRecord W) (R : Freedom W) : Prop := Goals (o5 r R)

@[expose] def intendedO5 (r : IntentRecord W) (R : Freedom W) : Prop :=
  ∀ u v, ((∀ d ∈ r.dom, d.holds u) ∧ ∀ p ∈ r.props, p.holds u) →
    ((∀ d ∈ r.dom, d.holds v) ∧ ∀ p ∈ r.props, p.holds v) →
    match R with
    | .eq => u = v
    | .widest => ((∀ d ∈ r.dom, d.holds u) ∧ ∀ p ∈ r.props, p.holds u) ∧
        ((∀ d ∈ r.dom, d.holds v) ∧ ∀ p ∈ r.props, p.holds v)
    | .rel R => R u v

theorem o5_correct (r : IntentRecord W) (R : Freedom W) : O5 r R ↔ intendedO5 r R := by
  cases R <;>
    simp only [O5, o5, goals_singleton, Freedom.relates, IntentRecord.Meets, IntentRecord.Dom,
      IntentRecord.Props, intendedO5]

theorem o5_widest (r : IntentRecord W) : O5 r .widest :=
  (goals_singleton _).mpr fun _ _ hu hv => ⟨hu, hv⟩

theorem O5.relates {r : IntentRecord W} {R : Freedom W} (h : O5 r R) {u v : W} (hu : r.Meets u)
    (hv : r.Meets v) : R.relates r u v :=
  (goals_singleton _).mp h u v hu hv

theorem not_o5_eq {r : IntentRecord W} {u v : W} (hu : r.Meets u) (hv : r.Meets v) (hne : u ≠ v) :
    ¬ O5 r .eq :=
  fun h => hne (h.relates hu hv)

end LeanIntent
