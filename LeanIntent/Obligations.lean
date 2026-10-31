import LeanIntent.Record

/-!
# The adequacy obligations and their goal formers

A specification can be met by code and still miss what its owner meant: it can contradict itself,
say nothing, allow a subject that does nothing, or leave the result open where the owner wanted it
fixed. Each such check is a proposition about the intent record, and this module states each one
for a Lean intent record:

* **O1, well formed**: every statement of the record is a well-typed proposition.
* **O2, satisfiable**: the domain hypotheses have a joint model and each predicate of the
  vocabulary an instance (`O2`), and before a deliverable runs the whole record has a model
  (`O2Run`), so a contradictory record cannot be met vacuously.
* **O3, refutable**: each property has a subject that fails it, so a property nothing fails is
  refused.
* **O4, progress**: for a function, totality; for a subject with state, every subject that leaves
  the state unchanged fails the record; for a description made of functions, every subject in which
  one of them ignores its input fails the record; a plain value is asked nothing.
* **O5, determinate or confirmed freedom**: any two models of the record are equal, or related by
  a stated relation, what the intent leaves unsaid (`Freedom`). The freedom is part of the
  restatement the owner confirms; where it is a fork that changes what they get the owner decides
  it, and otherwise it is a decision made on the owner's behalf.

Each obligation is computed from the record by a *goal former* (`o1` to `o5`, and `o2Run`): one
goal per item it asks about, met by proving their conjunction (`Goals`). A defective former that
computed `True`, a weaker proposition, or the obligation for one example only would make the
obligation trivially met, so each former has a correctness theorem (`o1_correct` to `o5_correct`)
that equates what it states with an intended proposition (`intendedO1` and the rest). Each intended
proposition is written by a direct match on the record and the obligation's definition, and uses no
definition of the formers or of the helpers they use (`Goals`, `HasInstance`, `HasNonInstance`,
`Clause.typed`, `Pred.typed`, `IntentRecord.Dom`, `IntentRecord.Props`, `IntentRecord.Meets`,
`Member.Ignores`, `Shape.Covers`, `Shape.Free`, `Shape.Sound`, `Shape.Idle`, `Shape.progress`,
`Total`, `Freedom.relates`), so a wrong helper makes its
correctness theorem fail. Every theorem quantifies over every record, so it holds of no fixed
example only.

O1's goal is a type, not a proposition: each statement paired with the type it is admitted at.
Lean's kernel checks that pairing when the record is declared, so O1 holds of every record by
construction (`o1_wellTyped`), and `o1_correct` fixes which statements and types `o1` lists.
-/

namespace LeanIntent

universe u

variable {W : Type u}

/-! ## Goals -/

/-- Every goal of the list holds: their conjunction, `True` for none. -/
def Goals : List Prop → Prop
  | [] => True
  | g :: gs => g ∧ Goals gs

theorem goals_iff : (gs : List Prop) → (Goals gs ↔ ∀ g ∈ gs, g)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | g :: gs => by rw [Goals, List.forall_mem_cons, goals_iff gs]

theorem goals_map {α : Sort _} (f : α → Prop) : (l : List α) → (Goals (l.map f) ↔ ∀ a ∈ l, f a)
  | [] => ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | a :: l => by rw [List.map_cons, Goals, List.forall_mem_cons, goals_map f l]

theorem goals_singleton (g : Prop) : Goals [g] ↔ g := by simp [Goals]

/-- `P` has an instance. -/
def HasInstance {α : Sort _} (P : α → Prop) : Prop := ∃ a, P a

/-- `P` has a non-instance. -/
def HasNonInstance {α : Sort _} (P : α → Prop) : Prop := ∃ a, ¬ P a

/-! ## O1, well formed -/

/-- A clause with the type it is admitted at. -/
def Clause.typed (c : Clause W) : (T : Type u) × T := ⟨W → Prop, c.holds⟩

/-- A predicate with the type it is admitted at. -/
def Pred.typed (p : Pred.{u}) : (T : Type u) × T := ⟨p.Arg → Prop, p.holds⟩

/-- O1's goals: every statement of the record, the domain hypotheses, the properties and the
vocabulary in that order, each paired with the type it is admitted at. -/
def o1 (r : IntentRecord W) : List ((T : Type u) × T) :=
  r.dom.map Clause.typed ++ r.props.map Clause.typed ++ r.vocab.map Pred.typed

/-- What O1 asks, written apart from the former. -/
def intendedO1 : IntentRecord W → List ((T : Type u) × T)
  | ⟨_, dom, props, vocab⟩ =>
    dom.map (fun c => ⟨W → Prop, c.holds⟩) ++ props.map (fun c => ⟨W → Prop, c.holds⟩) ++
      vocab.map (fun p => ⟨p.Arg → Prop, p.holds⟩)

/-- O1's former states O1. -/
theorem o1_correct (r : IntentRecord W) : o1 r = intendedO1 r := by
  cases r; rfl

/-- O1 holds of every record: each statement inhabits the type it is admitted at, which Lean's
kernel checked when the record was declared. -/
theorem o1_wellTyped (r : IntentRecord W) : ∀ g ∈ o1 r, Nonempty g.1 :=
  fun g _ => ⟨g.2⟩

/-! ## O2, satisfiable -/

/-- O2's goals when a revision is confirmed: a joint model of the domain hypotheses, then an
instance of each predicate of the vocabulary. The record's own joint model is asked for only
before a deliverable runs (`o2Run`), since it may be the very thing the work is to find. -/
def o2 (r : IntentRecord W) : List Prop :=
  HasInstance r.Dom :: r.vocab.map fun p => HasInstance p.holds

/-- O2 holds of `r`. -/
def O2 (r : IntentRecord W) : Prop := Goals (o2 r)

/-- What O2 asks at confirmation, written apart from the former. -/
def intendedO2 (r : IntentRecord W) : Prop :=
  (∃ w, ∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.vocab, ∃ a, p.holds a

/-- O2's former states O2. -/
theorem o2_correct (r : IntentRecord W) : O2 r ↔ intendedO2 r := by
  simp only [O2, o2, Goals, goals_map, HasInstance, IntentRecord.Dom, intendedO2]

/-- O2's goal before a deliverable runs: a model of the whole record. -/
def o2Run (r : IntentRecord W) : List Prop := [HasInstance r.Meets]

/-- O2 before running holds of `r`. -/
def O2Run (r : IntentRecord W) : Prop := Goals (o2Run r)

/-- What O2 asks before a deliverable runs, written apart from the former. -/
def intendedO2Run (r : IntentRecord W) : Prop :=
  ∃ w, (∀ d ∈ r.dom, d.holds w) ∧ ∀ p ∈ r.props, p.holds w

/-- O2's former before running states it. -/
theorem o2Run_correct (r : IntentRecord W) : O2Run r ↔ intendedO2Run r := by
  simp only [O2Run, o2Run, goals_singleton, HasInstance, IntentRecord.Meets, IntentRecord.Dom,
    IntentRecord.Props, intendedO2Run]

/-! ## O3, refutable -/

/-- O3's goals: a non-instance of each property. -/
def o3 (r : IntentRecord W) : List Prop := r.props.map fun p => HasNonInstance p.holds

/-- O3 holds of `r`. -/
def O3 (r : IntentRecord W) : Prop := Goals (o3 r)

/-- What O3 asks, written apart from the former. -/
def intendedO3 (r : IntentRecord W) : Prop := ∀ p ∈ r.props, ∃ w, ¬ p.holds w

/-- O3's former states O3. -/
theorem o3_correct (r : IntentRecord W) : O3 r ↔ intendedO3 r := by
  simp only [O3, o3, goals_map, HasNonInstance, intendedO3]

/-! ## O4, progress -/

/-- The function `m` of the subject `w` ignores its input: it returns the same for every one. -/
def Member.Ignores (m : Member W) (w : W) : Prop := ∀ x y, m.get w x = m.get w y

/-- The plain values and the functions of a description determine the subject, so no part of it lies
outside them. -/
def Shape.Covers {D : Type u} (data : W → D) (ms : List (Member W)) : Prop :=
  ∀ u v, data u = data v → (∀ m ∈ ms, m.get u = m.get v) → u = v

/-- Each of the functions of a description can be any function of its type, so none is a decoy whose
behaviour is fixed whatever the subject is. -/
def Shape.Free (ms : List (Member W)) : Prop := ∀ m ∈ ms, ∀ f : m.In → m.Out, ∃ w, m.get w = f

/-- What a shape must itself satisfy for O4 to ask what it says: for a description made of functions,
that they and its plain values are the whole subject and that each function is free; nothing of
any other shape. -/
def Shape.Sound : {W : Type u} → Shape W → Prop
  | _, .bundle data first rest => Shape.Covers data (first :: rest) ∧ Shape.Free (first :: rest)
  | _, _ => True

/-- The subjects of a shape that do nothing: for a subject with state, those that leave the state
unchanged on every state and input; for a description made of functions, those in which one of the
functions ignores its input; a plain value or a function has none. -/
def Shape.Idle : {W : Type u} → Shape W → W → Prop
  | _, .value _, _ => False
  | _, .function _ _, _ => False
  | _, .step _, f => ∀ s, f s = s
  | _, .stepOn _ _, f => ∀ s i, f s i = s
  | _, .action _ _, f => ∀ s, (f s).2 = s
  | _, .actionOn _ _ _, f => ∀ s i, (f s i).2 = s
  | _, .bundle _ first rest, w => ∃ m ∈ first :: rest, m.Ignores w

/-- Every function of a Π-type gives every input an output. -/
def Total (A : Type u) (B : A → Type u) : Prop := ∀ f : (x : A) → B x, ∀ x, ∃ y, f x = y

/-- O4's goals for a subject of shape `s` whose models `meets` describes. -/
def Shape.progress : {W : Type u} → Shape W → (W → Prop) → List Prop
  | _, .value _, _ => []
  | _, .function A B, _ => [Total A B]
  | _, s@(.bundle data first rest), meets =>
    [Shape.Covers data (first :: rest), Shape.Free (first :: rest), ∀ w, s.Idle w → ¬ meets w]
  | _, s, meets => [∀ w, s.Idle w → ¬ meets w]

/-- O4's goals: nothing for a plain value; totality for a function, which Lean discharges since
every Lean function is total (`o4_function`); for a subject with state, that every subject leaving
the state unchanged fails the record; and for a description made of functions, that they and its
plain values are the whole subject, that each function can be any function of its type, and that
every subject in which one of them ignores its input fails the record. -/
def o4 (r : IntentRecord W) : List Prop := r.shape.progress r.Meets

/-- O4 holds of `r`. -/
def O4 (r : IntentRecord W) : Prop := Goals (o4 r)

/-- What O4 asks of a record of shape `s`, written apart from the former. -/
def intendedO4At : {W : Type u} → Shape W → IntentRecord W → Prop
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

/-- What O4 asks, written apart from the former. -/
def intendedO4 (r : IntentRecord W) : Prop := intendedO4At r.shape r

/-- O4's former states O4. -/
theorem o4_correct (r : IntentRecord W) : O4 r ↔ intendedO4 r := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape <;>
    simp only [O4, o4, Shape.progress, Goals, goals_singleton, Total, Shape.Idle, Shape.Covers,
      Shape.Free, Member.Ignores, IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props,
      intendedO4, intendedO4At, and_true]

/-- O4 asks nothing exactly of a plain value. -/
theorem o4_eq_nil_iff (r : IntentRecord W) : o4 r = [] ↔ r.shape = .value W := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases shape <;> simp [o4, Shape.progress]

/-- A function meets O4: Lean's functions are total. -/
theorem o4_function {A : Type u} {B : A → Type u} (r : IntentRecord ((x : A) → B x))
    (h : r.shape = .function A B) : O4 r := by
  rw [o4_correct, intendedO4, h]
  exact fun f x => ⟨f x, rfl⟩

/-- A subject that does nothing and meets the record refutes O4: no record that a do-nothing
subject meets has O4. -/
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

/-- A free function of a description, whose results include some value, ignores its input in some
subject: the subject that gives the constant function of that value. -/
theorem Shape.exists_ignores {m : Member W} (hFree : ∀ f : m.In → m.Out, ∃ w, m.get w = f)
    (b : m.Out) : ∃ w, m.Ignores w :=
  let ⟨w, hw⟩ := hFree fun _ => b
  ⟨w, fun x y => by rw [hw]⟩

/-- O4 asks something real of a description made of functions: a record with no hypothesis and no
property, which every subject meets, fails it, wherever the first function can return a value. So
neither an empty list of functions nor a decoy whose behaviour never varies meets O4 vacuously. -/
theorem not_o4_bundle_of_trivial {D : Type u} {data : W → D} {first : Member W}
    {rest : List (Member W)} {vocab : List Pred.{u}} (b : first.Out) :
    ¬ O4 (⟨.bundle data first rest, [], [], vocab⟩ : IntentRecord W) := by
  intro h
  obtain ⟨w, hw⟩ := Shape.exists_ignores (fun f => h.2.1 first (List.mem_cons_self ..) f) b
  exact h.2.2.1 w ⟨first, List.mem_cons_self .., hw⟩
    ⟨(fun _ hd => nomatch hd), fun _ hp => nomatch hp⟩

/-- A function of a description that takes at most one input always ignores it, so O4 and a model of
the record cannot both hold of a record with such a function: a plain value belongs in the
description's `data`. -/
theorem no_model_of_o4_bundle_subsingleton {D : Type u} {data : W → D} {first : Member W}
    {rest : List (Member W)} {r : IntentRecord W} (hs : r.shape = .bundle data first rest)
    {m : Member W} (hm : m ∈ first :: rest) (hIn : ∀ x y : m.In, x = y) (h : O4 r) (w : W) :
    ¬ r.Meets w := by
  obtain ⟨shape, dom, props, vocab⟩ := r
  cases hs
  exact h.2.2.1 w ⟨m, hm, fun x y => by rw [hIn x y]⟩

/-! ## O5, determinate or confirmed freedom -/

/-- The relation O5 asks between two models of a record: equality, the widest freedom, which
relates any two models, or a stated relation, what the intent leaves unsaid. -/
inductive Freedom (W : Type u) where
  | eq
  | widest
  | rel (R : W → W → Prop)

/-- What the freedom relates, for the record `r`. -/
def Freedom.relates (r : IntentRecord W) : Freedom W → W → W → Prop
  | .eq, u, v => u = v
  | .widest, u, v => r.Meets u ∧ r.Meets v
  | .rel R, u, v => R u v

/-- O5's goal: any two models of the record are related by the freedom. -/
def o5 (r : IntentRecord W) (R : Freedom W) : List Prop :=
  [∀ u v, r.Meets u → r.Meets v → R.relates r u v]

/-- O5 holds of `r` with the freedom `R`. -/
def O5 (r : IntentRecord W) (R : Freedom W) : Prop := Goals (o5 r R)

/-- What O5 asks, written apart from the former. -/
def intendedO5 (r : IntentRecord W) (R : Freedom W) : Prop :=
  ∀ u v, ((∀ d ∈ r.dom, d.holds u) ∧ ∀ p ∈ r.props, p.holds u) →
    ((∀ d ∈ r.dom, d.holds v) ∧ ∀ p ∈ r.props, p.holds v) →
    match R with
    | .eq => u = v
    | .widest => ((∀ d ∈ r.dom, d.holds u) ∧ ∀ p ∈ r.props, p.holds u) ∧
        ((∀ d ∈ r.dom, d.holds v) ∧ ∀ p ∈ r.props, p.holds v)
    | .rel R => R u v

/-- O5's former states O5. -/
theorem o5_correct (r : IntentRecord W) (R : Freedom W) : O5 r R ↔ intendedO5 r R := by
  cases R <;>
    simp only [O5, o5, goals_singleton, Freedom.relates, IntentRecord.Meets, IntentRecord.Dom,
      IntentRecord.Props, intendedO5]

/-- O5 never refuses on its own: every record meets it with the widest freedom. What O5 adds is
that the freedom is made explicit, for the owner to decide where it is a fork that changes what they
get, and otherwise to be decided on the owner's behalf. -/
theorem o5_widest (r : IntentRecord W) : O5 r .widest :=
  (goals_singleton _).mpr fun _ _ hu hv => ⟨hu, hv⟩

/-- O5 relates any two models of the record, not only those an example names. -/
theorem O5.relates {r : IntentRecord W} {R : Freedom W} (h : O5 r R) {u v : W} (hu : r.Meets u)
    (hv : r.Meets v) : R.relates r u v :=
  (goals_singleton _).mp h u v hu hv

/-- Two distinct models refute O5 with equality. -/
theorem not_o5_eq {r : IntentRecord W} {u v : W} (hu : r.Meets u) (hv : r.Meets v) (hne : u ≠ v) :
    ¬ O5 r .eq :=
  fun h => hne (h.relates hu hv)

end LeanIntent
