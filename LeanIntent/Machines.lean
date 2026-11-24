module

public import LeanIntent.TrivialWitnesses

public section

namespace LeanIntent

structure Machine (I O : Type) : Type 1 where
  Memory : Type
  initial : Memory
  step : Memory → I → O × Memory

namespace Machine

variable {I O : Type}

@[expose] def memoryAfter (m : Machine I O) (h : List I) : m.Memory :=
  h.foldl (fun s i => (m.step s i).2) m.initial

@[expose] def behaviour (m : Machine I O) (h : List I) (i : I) : O :=
  (m.step (m.memoryAfter h) i).1

theorem memoryAfter_nil (m : Machine I O) : m.memoryAfter [] = m.initial := rfl

theorem memoryAfter_append_singleton (m : Machine I O) (h : List I) (i : I) :
    m.memoryAfter (h ++ [i]) = (m.step (m.memoryAfter h) i).2 := by
  simp only [memoryAfter, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[expose] def ofBehaviour (b : List I → I → O) : Machine I O :=
  ⟨List I, [], fun h i => (b h i, h ++ [i])⟩

theorem memoryAfter_ofBehaviour (b : List I → I → O) (h : List I) :
    (ofBehaviour b).memoryAfter h = h := by
  have go : ∀ (h acc : List I), h.foldl (fun s i => s ++ [i]) acc = acc ++ h := by
    intro h
    induction h with
    | nil => intro acc; simp
    | cons i h ih => intro acc; rw [List.foldl_cons, ih]; simp
  exact (go h []).trans (List.nil_append h)

theorem behaviour_ofBehaviour (b : List I → I → O) : (ofBehaviour b).behaviour = b := by
  funext h i
  simp only [behaviour, memoryAfter_ofBehaviour]
  rfl

@[expose] def clockedScript (s : Nat → O) : Machine I O :=
  ⟨Nat, 0, fun n _ => (s n, n + 1)⟩

theorem memoryAfter_clockedScript (s : Nat → O) (h : List I) :
    (clockedScript s).memoryAfter h = h.length := by
  have go : ∀ (h : List I) (acc : Nat), h.foldl (fun n _ => n + 1) acc = acc + h.length := by
    intro h
    induction h with
    | nil => intro acc; rfl
    | cons i h ih => intro acc; rw [List.foldl_cons, ih, List.length_cons]; omega
  exact (go h 0).trans (Nat.zero_add _)

theorem behaviour_clockedScript (s : Nat → O) :
    (clockedScript s : Machine I O).behaviour = fun h _ => s h.length := by
  funext h i
  simp only [behaviour, memoryAfter_clockedScript]
  rfl

@[expose] def OpenLoop (m : Machine I O) : Prop :=
  ∃ (advance : m.Memory → m.Memory) (choose : m.Memory → O),
    ∀ s i, m.step s i = (choose s, advance s)

@[expose] def FixedInAdvance (m : Machine I O) : Prop :=
  ∃ s : Nat → O, ∀ h i, m.behaviour h i = s h.length

@[expose] def ConstantAction (m : Machine I O) : Prop :=
  ∃ o : O, ∀ h i, m.behaviour h i = o

theorem OpenLoop.fixedInAdvance {m : Machine I O} (hm : m.OpenLoop) : m.FixedInAdvance := by
  obtain ⟨advance, choose, law⟩ := hm
  have shift : ∀ (n : Nat) (a : m.Memory), Nat.repeat advance n (advance a) =
      advance (Nat.repeat advance n a) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; exact congrArg advance (ih a)
  have go : ∀ (h : List I) (acc : m.Memory),
      h.foldl (fun s i => (m.step s i).2) acc = Nat.repeat advance h.length acc := by
    intro h
    induction h with
    | nil => intro acc; rfl
    | cons i h ih => intro acc; rw [List.foldl_cons, law, ih, shift]; rfl
  have drift : ∀ h : List I, m.memoryAfter h = Nat.repeat advance h.length m.initial :=
    fun h => go h m.initial
  exact ⟨fun n => choose (Nat.repeat advance n m.initial), fun h i => by
    rw [behaviour, law, drift]⟩

theorem clockedScript_openLoop (s : Nat → O) : (clockedScript s : Machine I O).OpenLoop :=
  ⟨fun n => Nat.succ (n : Nat), s, fun _ _ => rfl⟩

theorem fixedInAdvance_iff_script (m : Machine I O) :
    m.FixedInAdvance ↔ ∃ s : Nat → O, m.behaviour = (clockedScript s).behaviour := by
  rw [show (∃ s : Nat → O, m.behaviour = (clockedScript s).behaviour) ↔
      ∃ s : Nat → O, m.behaviour = fun h _ => s h.length from
    exists_congr fun s => by rw [behaviour_clockedScript]]
  exact exists_congr fun s => ⟨fun h => funext fun l => funext fun i => h l i,
    fun h l i => congrFun (congrFun h l) i⟩

theorem ConstantAction.fixedInAdvance {m : Machine I O} (hm : m.ConstantAction) :
    m.FixedInAdvance :=
  let ⟨o, h⟩ := hm
  ⟨fun _ => o, h⟩

end Machine

structure MachineIso (W : Type 1) (I O : Type) where
  to : W → Machine I O
  inv : Machine I O → W
  inv_to : ∀ w, inv (to w) = w
  to_inv : ∀ m, to (inv m) = m

@[expose] def MachineIso.refl (I O : Type) : MachineIso (Machine I O) I O :=
  ⟨fun m => m, fun m => m, fun _ => rfl, fun _ => rfl⟩

inductive Machine.Stands : (W : Type 1) → (I O : Type) → MachineIso W I O → Prop
  | self (I O : Type) : Machine.Stands (Machine I O) I O (MachineIso.refl I O)
  | private decl {W : Type 1} {I O : Type} (e : MachineIso W I O) : Machine.Stands W I O e

class CoveredMachine (W : Type 1) where
  In : Type
  Out : Type
  inCode : HasCode In
  outCode : HasCode Out
  iso : MachineIso W In Out
  stands : Machine.Stands W In Out iso

instance {I O : Type} [hi : HasCode I] [ho : HasCode O] : CoveredMachine (Machine I O) :=
  ⟨I, O, hi, ho, .refl I O, .self I O⟩

namespace CoveredMachine

@[expose] def Behaviour (W : Type 1) [m : CoveredMachine W] : Type := List m.In → m.In → m.Out

instance behaviourCovered (W : Type 1) [m : CoveredMachine W] : Covered (Behaviour W) := by
  letI := m.inCode
  letI := m.outCode
  exact inferInstanceAs (Covered (List m.In → m.In → m.Out))

abbrev sig (W : Type 1) [CoveredMachine W] : Sig := (behaviourCovered W).sig

variable {W : Type 1} [m : CoveredMachine W]

@[expose] def machineOf (w : W) : Machine m.In m.Out := m.iso.to w

@[expose] def ofMachine (x : Machine m.In m.Out) : W := m.iso.inv x

@[expose] def behaviourOf (w : W) : Behaviour W := (machineOf w).behaviour

@[expose] def realize (b : Behaviour W) : W := ofMachine (Machine.ofBehaviour b)

theorem machineOf_ofMachine (x : Machine m.In m.Out) : machineOf (ofMachine x : W) = x :=
  m.iso.to_inv x

theorem ofMachine_machineOf (w : W) : ofMachine (machineOf w) = w := m.iso.inv_to w

theorem behaviourOf_ofMachine (x : Machine m.In m.Out) :
    behaviourOf (ofMachine x : W) = x.behaviour := by
  rw [behaviourOf, machineOf_ofMachine]

theorem behaviourOf_realize (b : Behaviour W) : behaviourOf (realize b : W) = b := by
  rw [realize, behaviourOf_ofMachine]
  exact Machine.behaviour_ofBehaviour b

theorem constant_apply {f : Behaviour W} (h : Witness.Constant f) :
    ∃ o : m.Out, ∀ l i, f l i = o := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨m.outCode.iso.inv ((Sig.flat m.outCode.code).inv (Sig.Fn.const _ v _)),
    fun _ _ => rfl⟩

theorem behaviourIso_to (f : Behaviour W) (h : List (m.inCode.code.denote))
    (i : m.inCode.code.denote) :
    (behaviourCovered W).iso.to f h i =
      (Sig.flat m.outCode.code).to
        (m.outCode.iso.to (f (m.inCode.iso.list.inv h) (m.inCode.iso.inv i))) :=
  rfl

theorem blindTo_history_iff (f : Behaviour W) :
    Witness.BlindTo 0 f ↔ ∀ h h' (i : m.In), f h i = f h' i := by
  have hF : ∀ a b : m.Out, (Sig.flat m.outCode.code).to (m.outCode.iso.to a) =
      (Sig.flat m.outCode.code).to (m.outCode.iso.to b) → a = b := fun a b e => by
    have := congrArg (fun y => m.outCode.iso.inv ((Sig.flat m.outCode.code).inv y)) e
    simpa only [Iso.inv_to] using this
  constructor
  · intro hb h h' i
    have e := congrFun (hb (m.inCode.iso.list.to h) (m.inCode.iso.list.to h'))
      (m.inCode.iso.to i)
    simp only [behaviourIso_to, Iso.inv_to] at e
    exact hF _ _ e
  · intro hf x y
    funext i
    show (behaviourCovered W).iso.to f x i = (behaviourCovered W).iso.to f y i
    simp only [behaviourIso_to, hf (m.inCode.iso.list.inv x) (m.inCode.iso.list.inv y)]

theorem blindTo_input_iff (f : Behaviour W) :
    Witness.BlindTo 1 f ↔ ∀ h (i i' : m.In), f h i = f h i' := by
  have hF : ∀ a b : m.Out, (Sig.flat m.outCode.code).to (m.outCode.iso.to a) =
      (Sig.flat m.outCode.code).to (m.outCode.iso.to b) → a = b := fun a b e => by
    have := congrArg (fun y => m.outCode.iso.inv ((Sig.flat m.outCode.code).inv y)) e
    simpa only [Iso.inv_to] using this
  constructor
  · intro hb h i i'
    have e := hb (m.inCode.iso.list.to h) (m.inCode.iso.to i) (m.inCode.iso.to i')
    simp only [behaviourIso_to, Iso.inv_to] at e
    exact hF _ _ e
  · intro hf x y y'
    show (behaviourCovered W).iso.to f x y = (behaviourCovered W).iso.to f x y'
    simp only [behaviourIso_to, hf (m.inCode.iso.list.inv x) (m.inCode.iso.inv y)
      (m.inCode.iso.inv y')]

end CoveredMachine

open CoveredMachine

@[expose] def truthGoals {α : Type _} (P : α → Prop) : List α → List Bool → List Prop
  | [], [] => []
  | x :: xs, true :: bs => P x :: truthGoals P xs bs
  | x :: xs, false :: bs => (¬ P x) :: truthGoals P xs bs
  | _, _ => [False]

theorem goals_truthGoals {α : Type _} (P : α → Prop) : (xs : List α) → (bs : List Bool) →
    (Goals (truthGoals P xs bs) ↔ bs.length = xs.length ∧
      ∀ (i : Nat) (hb : i < bs.length) (hx : i < xs.length), (bs[i] = true ↔ P xs[i]))
  | [], [] => by simp [truthGoals, Goals]
  | [], _ :: _ => by simp [truthGoals, Goals]
  | _ :: _, [] => by simp [truthGoals, Goals]
  | x :: xs, b :: bs => by
      have hv : Goals (truthGoals P (x :: xs) (b :: bs)) ↔
          (b = true ↔ P x) ∧ Goals (truthGoals P xs bs) := by
        cases b <;> simp [truthGoals, Goals]
      rw [hv, goals_truthGoals P xs bs]
      constructor
      · rintro ⟨h0, hlen, hall⟩
        refine ⟨by simp [hlen], fun i hb hx => ?_⟩
        cases i with
        | zero => simpa using h0
        | succ i => simpa using hall i (by simpa using hb) (by simpa using hx)
      · rintro ⟨hlen, hall⟩
        exact ⟨hall 0 (by simp) (by simp), by simpa using hlen,
          fun i hb hx => by simpa using hall (i + 1) (Nat.succ_lt_succ hb) (Nat.succ_lt_succ hx)⟩

@[expose] def truthsTrue {α : Type _} : List α → List Bool → List α
  | x :: xs, true :: bs => x :: truthsTrue xs bs
  | _ :: xs, false :: bs => truthsTrue xs bs
  | _, _ => []

theorem mem_truthsTrue {α : Type _} (P : α → Prop) (y : α) : (xs : List α) → (bs : List Bool) →
    Goals (truthGoals P xs bs) → (y ∈ truthsTrue xs bs ↔ y ∈ xs ∧ P y)
  | [], [], _ => by simp [truthsTrue]
  | [], _ :: _, h => absurd h (by simp [truthGoals, Goals])
  | _ :: _, [], h => absurd h (by simp [truthGoals, Goals])
  | x :: xs, true :: bs, ⟨hv, h⟩ => by
      rw [truthsTrue, List.mem_cons, mem_truthsTrue P y xs bs h, List.mem_cons]
      constructor
      · rintro (rfl | ⟨hy, hp⟩)
        · exact ⟨.inl rfl, hv⟩
        · exact ⟨.inr hy, hp⟩
      · rintro ⟨rfl | hy, hp⟩
        · exact .inl rfl
        · exact .inr ⟨hy, hp⟩
  | x :: xs, false :: bs, ⟨hv, h⟩ => by
      rw [truthsTrue, mem_truthsTrue P y xs bs h, List.mem_cons]
      constructor
      · rintro ⟨hy, hp⟩
        exact ⟨.inr hy, hp⟩
      · rintro ⟨rfl | hy, hp⟩
        · exact absurd hp hv
        · exact ⟨hy, hp⟩

theorem truthsTrue_sublist {α : Type _} : (xs : List α) → (bs : List Bool) →
    List.Sublist (truthsTrue xs bs) xs
  | [], _ => by simp [truthsTrue]
  | _ :: _, [] => by simp [truthsTrue]
  | x :: xs, true :: bs => List.Sublist.cons_cons x (truthsTrue_sublist xs bs)
  | x :: xs, false :: bs => List.Sublist.cons x (truthsTrue_sublist xs bs)

theorem truthsTrue_map {α β : Type _} (f : α → β) : (xs : List α) → (bs : List Bool) →
    (truthsTrue xs bs).map f = truthsTrue (xs.map f) bs
  | [], _ => by simp [truthsTrue]
  | _ :: _, [] => by simp [truthsTrue]
  | x :: xs, true :: bs => by simp [truthsTrue, truthsTrue_map f xs bs]
  | _ :: xs, false :: bs => by simp [truthsTrue, truthsTrue_map f xs bs]

theorem map_getElem_finRange {α : Type _} (xs : List α) :
    (List.finRange xs.length).map (fun i => xs[i]) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem map_getElem_truthsTrue_finRange {α : Type _} (xs : List α) (bs : List Bool) :
    (truthsTrue (List.finRange xs.length) bs).map (fun i => xs[i]) = truthsTrue xs bs := by
  rw [truthsTrue_map, map_getElem_finRange]

theorem find?_eq_some_of_nodup_map {α β : Type _} [BEq β] [LawfulBEq β]
    {l : List α} {key : α → β} (hn : (l.map key).Nodup) {x : α} (hx : x ∈ l) :
    l.find? (fun y => key y == key x) = some x := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : (key a == key x) = false := by
        apply beq_false_of_ne
        intro e
        exact hn.1 ⟨x, hx, e.symm⟩
      simp [hne, ih hn.2 hx]

@[expose] def machineDegenerate (W : Type 1) [CoveredMachine W] : List (Degenerate (sig W)) :=
  degenerate (Behaviour W)

section MachineVerdicts

variable {W : Type 1} [m : CoveredMachine W]

@[expose] def Degenerate.IsMachine (d : Degenerate (sig W)) (w : W) : Prop := d.Is (behaviourOf w)

@[expose] def Degenerate.MeetsMachine (d : Degenerate (sig W)) (r : IntentRecord W) : Prop :=
  ∃ w, d.IsMachine w ∧ r.Meets w

theorem Degenerate.isMachine_congr (d : Degenerate (sig W)) {w w' : W}
    (h : behaviourOf w = behaviourOf w') : d.IsMachine w ↔ d.IsMachine w' := by
  rw [Degenerate.IsMachine, Degenerate.IsMachine, h]

theorem Degenerate.isMachine_inv_iff (d : Degenerate (sig W)) (x : Machine m.In m.Out) :
    d.IsMachine (ofMachine x : W) ↔ d.Is x.behaviour := by
  rw [Degenerate.IsMachine, behaviourOf_ofMachine]

theorem Degenerate.isMachine_realize {d : Degenerate (sig W)} {b : Behaviour W} (h : d.Is b) :
    d.IsMachine (realize b : W) := by
  rw [Degenerate.IsMachine, behaviourOf_realize]
  exact h

@[expose] def machineVerdicts (r : IntentRecord W) (bs : List Bool) : List Prop :=
  truthGoals (fun d : Degenerate (sig W) => d.MeetsMachine r) (machineDegenerate W) bs

@[expose] def MachineVerdicts (r : IntentRecord W) (bs : List Bool) : Prop := Goals (machineVerdicts r bs)

@[expose] def intendedMachineVerdicts (r : IntentRecord W) (bs : List Bool) : Prop :=
  bs.length = (machineDegenerate W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (machineDegenerate W).length),
      (bs[i] = true ↔ ∃ w, (machineDegenerate W)[i].Is (behaviourOf w) ∧
        (∀ x ∈ r.dom, x.holds w) ∧ ∀ p ∈ r.props, p.holds w)

theorem machineVerdicts_correct (r : IntentRecord W) (bs : List Bool) :
    MachineVerdicts r bs ↔ intendedMachineVerdicts r bs := by
  rw [MachineVerdicts, machineVerdicts, goals_truthGoals]
  simp only [intendedMachineVerdicts, Degenerate.MeetsMachine, Degenerate.IsMachine,
    IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props]

@[expose] def machineMetBy (W : Type 1) [CoveredMachine W] (bs : List Bool) : List (Degenerate (sig W)) :=
  truthsTrue (machineDegenerate W) bs

theorem mem_machineMetBy {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs)
    (d : Degenerate (sig W)) : d ∈ machineMetBy W bs ↔ d ∈ machineDegenerate W ∧ d.MeetsMachine r :=
  mem_truthsTrue _ d _ bs h

theorem machineMetBy_eq_nil_iff {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs) :
    machineMetBy W bs = [] ↔ ∀ d ∈ machineDegenerate W, ¬ d.MeetsMachine r := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun d => by rw [mem_machineMetBy h]; exact not_and

theorem not_meets_of_machineMetBy_eq_nil {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) (he : machineMetBy W bs = []) {d : Degenerate (sig W)}
    (hd : d ∈ machineDegenerate W) {w : W} (hw : d.IsMachine w) : ¬ r.Meets w :=
  fun hm => (machineMetBy_eq_nil_iff h).mp he d hd ⟨w, hw, hm⟩

@[expose] def Degenerate.machineLabel {σ : Sig} : Degenerate σ → String
  | .const _ => "the record allows a machine that gives one output whatever its inputs"
  | .proj _ => "the record allows a machine that gives as its output what it was given: its current \
      input, its history of earlier inputs, or, where its output is a function, that function's \
      argument; what a function among them returns; or a part of any of these"
  | .others => "the record allows a machine that gives one output whatever its inputs, at some \
      output other than the empty one"

@[expose] def Degenerate.machineNameAt {σ : Sig} (i : Nat) (d : Degenerate σ) : String :=
  String.ofList
    ('#' :: ((Codec.nat 0 ':' (by decide)).print (i + 1) ++ (' ' :: d.machineLabel.toList)))

theorem Degenerate.machineNameAt_inj {σ : Sig} {i j : Nat} {d₁ d₂ : Degenerate σ}
    (h : d₁.machineNameAt i = d₂.machineNameAt j) : i = j := by
  have hl := congrArg String.toList h
  simp only [machineNameAt, String.toList_ofList, List.cons.injEq, true_and] at hl
  have hp := congrArg (Codec.nat 0 ':' (by decide)).parse hl
  rw [(Codec.nat 0 ':' (by decide)).parse_print, (Codec.nat 0 ':' (by decide)).parse_print] at hp
  exact Nat.succ.inj (congrArg Prod.fst (Option.some.inj hp))

@[expose] def machineConsequence (W : Type 1) [CoveredMachine W]
    (i : Fin (machineDegenerate W).length) : Consequence W :=
  ⟨(machineDegenerate W)[i].machineNameAt i.val, .possibility, (machineDegenerate W)[i].IsMachine⟩

theorem machineConsequence_name_inj {i j : Fin (machineDegenerate W).length}
    (h : (machineConsequence W i).name = (machineConsequence W j).name) : i = j :=
  Fin.ext (Degenerate.machineNameAt_inj h)

theorem machineConsequence_eq_of_name_eq {i j : Fin (machineDegenerate W).length}
    (h : (machineConsequence W i).name = (machineConsequence W j).name) :
    machineConsequence W i = machineConsequence W j :=
  congrArg (machineConsequence W) (machineConsequence_name_inj h)

theorem machineDeclined_keptBy_iff (i : Fin (machineDegenerate W).length) (r : IntentRecord W) :
    (Answer.mk (machineConsequence W i) .declined).KeptBy r ↔
      ¬ (machineDegenerate W)[i].MeetsMachine r := by
  simp only [Answer.KeptBy, machineConsequence, Degenerate.MeetsMachine]
  exact ⟨fun h ⟨w, hi, hm⟩ => h w hm hi, fun h w hm hi => h ⟨w, hi, hm⟩⟩

@[expose] def machinePossibilities {r : IntentRecord W} {bs : List Bool} (_ : MachineVerdicts r bs) :
    List (Consequence W) :=
  (truthsTrue (List.finRange (machineDegenerate W).length) bs).map (machineConsequence W)

theorem mem_machinePossibilities {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs)
    (x : Consequence W) :
    x ∈ machinePossibilities h ↔
      ∃ i : Fin (machineDegenerate W).length,
        (machineDegenerate W)[i].MeetsMachine r ∧ x = machineConsequence W i := by
  have hg : Goals (truthGoals (fun i : Fin (machineDegenerate W).length =>
      (machineDegenerate W)[i].MeetsMachine r) (List.finRange (machineDegenerate W).length) bs) := by
    rw [goals_truthGoals]
    have hm := (goals_truthGoals (fun d : Degenerate (sig W) => d.MeetsMachine r)
      (machineDegenerate W) bs).mp h
    refine ⟨by simpa using hm.1, fun k hb hk => ?_⟩
    have hk' : k < (machineDegenerate W).length := by simpa using hk
    simpa [List.getElem_finRange] using hm.2 k hb hk'
  simp only [machinePossibilities, List.mem_map, mem_truthsTrue _ _ _ bs hg, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨i, hm, e⟩ => ⟨i, hm, e.symm⟩, fun ⟨i, hm, e⟩ => ⟨i, hm, e.symm⟩⟩

theorem machinePossibilities_holdsOf {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) (x : Consequence W) (hx : x ∈ machinePossibilities h) :
    x.kind = .possibility ∧ x.HoldsOf r := by
  obtain ⟨i, ⟨w, hi, hm⟩, rfl⟩ := (mem_machinePossibilities h x).mp hx
  exact ⟨rfl, w, hm, hi⟩

theorem map_holds_machinePossibilities {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) :
    (machinePossibilities h).map Consequence.holds =
      (machineMetBy W bs).map Degenerate.IsMachine := by
  simp only [machinePossibilities, machineMetBy, List.map_map]
  have e : Consequence.holds ∘ machineConsequence W =
      Degenerate.IsMachine ∘ fun i : Fin (machineDegenerate W).length => (machineDegenerate W)[i] := rfl
  rw [e, ← List.map_map, map_getElem_truthsTrue_finRange]

theorem machinePossibilities_names_nodup {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) :
    ((machinePossibilities h).map Consequence.name).Nodup := by
  simp only [machinePossibilities, List.map_map]
  exact List.Pairwise.map (Consequence.name ∘ machineConsequence W)
    (fun _ _ hne heq => hne (machineConsequence_name_inj heq))
    (List.Pairwise.sublist (truthsTrue_sublist _ bs) (List.nodup_finRange _))

theorem find?_machinePossibilities {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) {x : Consequence W} (hx : x ∈ machinePossibilities h) :
    (machinePossibilities h).find? (·.name == x.name) = some x :=
  find?_eq_some_of_nodup_map (machinePossibilities_names_nodup h) hx

theorem find?_map_machinePossibilities {α : Type _} {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) (f : Consequence W → α) (name : α → String)
    (hn : ∀ c, name (f c) = c.name) {x : Consequence W} (hx : x ∈ machinePossibilities h) :
    ((machinePossibilities h).map f).find? (fun a => name a == x.name) = some (f x) := by
  have hnd : (((machinePossibilities h).map f).map name).Nodup := by
    rw [List.map_map]
    have e : name ∘ f = Consequence.name := funext hn
    rw [e]
    exact machinePossibilities_names_nodup h
  have hx' : f x ∈ (machinePossibilities h).map f := List.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hn] using find?_eq_some_of_nodup_map hnd hx'

end MachineVerdicts

inductive MachineWitness (σ : Sig) where
  | behaviour (t : Witness σ)
  | constantAction
  | fixedInAdvance

@[expose] def machineWitnesses (W : Type 1) [CoveredMachine W] : List (MachineWitness (sig W)) :=
  (witnesses (Behaviour W)).map .behaviour ++ [.constantAction, .fixedInAdvance]

section MachineWitnesses

variable {W : Type 1} [m : CoveredMachine W]

@[expose] def MachineWitness.Admits : MachineWitness (sig W) → W → Prop
  | .behaviour .vacuous, _ => True
  | .behaviour .table, w => Witness.Constant (behaviourOf w)
  | .behaviour (.blind i), w => Witness.BlindTo i.val (behaviourOf w)
  | .behaviour (.fixed d), w => d.IsMachine w
  | .behaviour (.timed k), w => Witness.TimedBy k (behaviourOf w)
  | .constantAction, w => (machineOf w).ConstantAction
  | .fixedInAdvance, w => (machineOf w).FixedInAdvance

@[expose] def MachineWitness.Meets (t : MachineWitness (sig W)) (q : Pair W) : Prop :=
  match t with
  | .behaviour .vacuous => ∀ w, q.Met w
  | .behaviour (.fixed d) => ∃ w, d.IsMachine w ∧ q.Met w
  | t => ∀ x, q.pre x → ∃ w, t.Admits w ∧ q.post x w

theorem MachineWitness.admits_congr (t : MachineWitness (sig W)) {w w' : W}
    (h : behaviourOf w = behaviourOf w') : t.Admits w ↔ t.Admits w' := by
  match t with
  | .behaviour .vacuous => exact Iff.rfl
  | .behaviour .table => simp only [MachineWitness.Admits, h]
  | .behaviour (.blind _) => simp only [MachineWitness.Admits, h]
  | .behaviour (.fixed d) => exact d.isMachine_congr h
  | .behaviour (.timed _) => simp only [MachineWitness.Admits, h]
  | .constantAction =>
    simp only [MachineWitness.Admits, Machine.ConstantAction]
    simp only [behaviourOf] at h
    rw [h]
  | .fixedInAdvance =>
    simp only [MachineWitness.Admits, Machine.FixedInAdvance]
    simp only [behaviourOf] at h
    rw [h]

@[expose] def emptyAction : W :=
  ofMachine (Machine.ofBehaviour fun _ _ => m.outCode.iso.inv ((Sig.flat m.outCode.code).inv
    (Sig.Fn.const _ (sig W).out.empty _)))

theorem behaviourOf_emptyAction :
    behaviourOf (emptyAction : W) = Degenerate.constantSubject (sig W).out.empty := by
  rw [emptyAction, behaviourOf_ofMachine, Machine.behaviour_ofBehaviour]
  rfl

theorem constant_emptyAction : Witness.Constant (behaviourOf (emptyAction : W)) :=
  ⟨_, behaviourOf_emptyAction⟩

theorem constantAction_of_constant {w : W} (h : Witness.Constant (behaviourOf w)) :
    (machineOf w).ConstantAction :=
  constant_apply h

theorem MachineWitness.admits_emptyAction (t : MachineWitness (sig W))
    (ht : ∀ d, t ≠ .behaviour (.fixed d)) : t.Admits (emptyAction : W) := by
  match t with
  | .behaviour .vacuous => trivial
  | .behaviour .table => exact constant_emptyAction
  | .behaviour (.blind i) => exact Witness.blindTo_of_constant constant_emptyAction i.val
  | .behaviour (.fixed d) => exact absurd rfl (ht d)
  | .behaviour (.timed k) => exact Witness.timedBy_of_constant constant_emptyAction k
  | .constantAction => exact constantAction_of_constant constant_emptyAction
  | .fixedInAdvance => exact (constantAction_of_constant constant_emptyAction).fixedInAdvance

omit m in
private theorem strategy_of_served' {q : Pair W} {P : W → Prop} {w₀ : W} (h₀ : P w₀)
    (h : ∀ x, q.pre x → ∃ w, P w ∧ q.post x w) :
    ∃ s : q.Input → W, (∀ x, P (s x)) ∧ ∀ x, q.pre x → q.post x (s x) := by
  have hc : ∀ x, ∃ w, P w ∧ (q.pre x → q.post x w) := fun x => by
    by_cases hx : q.pre x
    · obtain ⟨w, hw, hp⟩ := h x hx
      exact ⟨w, hw, fun _ => hp⟩
    · exact ⟨w₀, h₀, fun h' => absurd h' hx⟩
  obtain ⟨s, hs⟩ := Classical.axiomOfChoice hc
  exact ⟨s, fun x => (hs x).1, fun x => (hs x).2⟩

theorem MachineWitness.vacuous_meets_iff (q : Pair W) :
    (MachineWitness.behaviour .vacuous : MachineWitness (sig W)).Meets q ↔
      ∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x) :=
  ⟨fun h s x hx => h (s x) x hx, fun h w x hx => h (fun _ => w) x hx⟩

theorem MachineWitness.fixed_meets_iff (q : Pair W) (d : Degenerate (sig W)) :
    (MachineWitness.behaviour (.fixed d)).Meets q ↔
      ∃ w, d.IsMachine w ∧ ∀ x, q.pre x → q.post x w :=
  Iff.rfl

theorem MachineWitness.meets_iff_strategy (q : Pair W) (t : MachineWitness (sig W))
    (hv : t ≠ .behaviour .vacuous) (hf : ∀ d, t ≠ .behaviour (.fixed d)) :
    t.Meets q ↔ ∃ s : q.Input → W, (∀ x, t.Admits (s x)) ∧ ∀ x, q.pre x → q.post x (s x) := by
  have hm : t.Meets q ↔ ∀ x, q.pre x → ∃ w, t.Admits w ∧ q.post x w := by
    match t with
    | .behaviour .vacuous => exact absurd rfl hv
    | .behaviour (.fixed d) => exact absurd rfl (hf d)
    | .behaviour .table | .behaviour (.blind _) | .behaviour (.timed _) | .constantAction
    | .fixedInAdvance => exact Iff.rfl
  rw [hm]
  exact ⟨strategy_of_served' (t.admits_emptyAction hf), fun ⟨s, hs, h⟩ x hx => ⟨s x, hs x, h x hx⟩⟩

theorem MachineWitness.fixedInAdvance_meets_iff_scripts (q : Pair W) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q ↔
      ∀ x, q.pre x → ∃ s : Nat → m.Out, ∃ w,
        behaviourOf w = (Machine.clockedScript s).behaviour ∧ q.post x w := by
  show (∀ x, q.pre x → ∃ w, (machineOf w).FixedInAdvance ∧ q.post x w) ↔ _
  constructor
  · intro h x hx
    obtain ⟨w, hw, hp⟩ := h x hx
    obtain ⟨s, e⟩ := (Machine.fixedInAdvance_iff_script _).mp hw
    exact ⟨s, w, e, hp⟩
  · intro h x hx
    obtain ⟨s, w, e, hp⟩ := h x hx
    exact ⟨w, (Machine.fixedInAdvance_iff_script _).mpr ⟨s, e⟩, hp⟩

theorem MachineWitness.fixedInAdvance_meets_of_openLoop {q : Pair W}
    (h : ∀ x, q.pre x → ∃ w, (machineOf w).OpenLoop ∧ q.post x w) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, hw.fixedInAdvance, hp⟩

theorem MachineWitness.fixedInAdvance_meets_of_clockedScripts {q : Pair W}
    (sc : q.Input → Nat → m.Out)
    (h : ∀ x, q.pre x → q.post x (ofMachine (Machine.clockedScript (sc x)))) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q :=
  MachineWitness.fixedInAdvance_meets_of_openLoop fun x hx =>
    ⟨_, by rw [machineOf_ofMachine]; exact Machine.clockedScript_openLoop (sc x), h x hx⟩

theorem MachineWitness.constantAction_meets_of_met {q : Pair W} {w : W}
    (hw : (machineOf w).ConstantAction) (h : q.Met w) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q :=
  fun x hx => ⟨w, hw, h x hx⟩

theorem MachineWitness.fixedInAdvance_meets_of_constantAction {q : Pair W}
    (h : (MachineWitness.constantAction : MachineWitness (sig W)).Meets q) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, Machine.ConstantAction.fixedInAdvance hw, hp⟩

theorem MachineWitness.constantAction_meets_of_table {q : Pair W}
    (h : (MachineWitness.behaviour .table : MachineWitness (sig W)).Meets q) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, constantAction_of_constant hw, hp⟩

theorem MachineWitness.constantAction_meets_of_vacuous {q : Pair W}
    (h : (MachineWitness.behaviour .vacuous : MachineWitness (sig W)).Meets q) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q :=
  MachineWitness.constantAction_meets_of_met
    (constantAction_of_constant constant_emptyAction) (h emptyAction)

theorem MachineWitness.not_meets_of_unserved {q : Pair W} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, ¬ q.post x w) : (t : MachineWitness (sig W)) → ¬ t.Meets q
  | .behaviour .vacuous => fun hm => h _ (hm emptyAction x hx)
  | .behaviour (.fixed _) => fun ⟨w, _, hm⟩ => h w (hm x hx)
  | .behaviour .table => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .behaviour (.blind _) => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .behaviour (.timed _) => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .constantAction => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .fixedInAdvance => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp

theorem mem_machineWitnesses_iff (t : MachineWitness (sig W)) :
    t ∈ machineWitnesses W ↔
      t = .behaviour .vacuous ∨ t = .behaviour .table ∨
        (2 ≤ (sig W).args.length ∧ ∃ i, t = .behaviour (.blind i)) ∨
        (∃ d, d ∈ (sig W).degenerate ∧ t = .behaviour (.fixed d)) ∨
        (∃ k, ((∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) ∧
          t = .behaviour (.timed k)) ∨
        t = .constantAction ∨ t = .fixedInAdvance := by
  simp only [machineWitnesses, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro (⟨t', ht', rfl⟩ | h | h)
    · rcases (Sig.mem_witnesses_iff t').mp ht' with
        rfl | rfl | ⟨hn, i, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨k, hk, rfl⟩
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl ⟨hn, i, rfl⟩))
      · exact .inr (.inr (.inr (.inl ⟨d, hd, rfl⟩)))
      · exact .inr (.inr (.inr (.inr (.inl ⟨k, hk, rfl⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))
  · have hw := fun t' => (Sig.mem_witnesses_iff (σ := sig W) t').mpr
    rintro (rfl | rfl | ⟨hn, i, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨k, hk, rfl⟩ | h | h)
    · exact .inl ⟨_, hw _ (.inl rfl), rfl⟩
    · exact .inl ⟨_, hw _ (.inr (.inl rfl)), rfl⟩
    · exact .inl ⟨_, hw _ (.inr (.inr (.inl ⟨hn, i, rfl⟩))), rfl⟩
    · exact .inl ⟨_, hw _ (.inr (.inr (.inr (.inl ⟨d, hd, rfl⟩)))), rfl⟩
    · exact .inl ⟨_, hw _ (.inr (.inr (.inr (.inr ⟨k, hk, rfl⟩)))), rfl⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)

theorem length_machineWitnesses (W : Type 1) [CoveredMachine W] :
    (machineWitnesses W).length = (witnesses (Behaviour W)).length + 2 := by
  simp [machineWitnesses]

theorem MachineWitness.constantAction_mem :
    (MachineWitness.constantAction : MachineWitness (sig W)) ∈ machineWitnesses W :=
  (mem_machineWitnesses_iff _).mpr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))

theorem MachineWitness.fixedInAdvance_mem :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)) ∈ machineWitnesses W :=
  (mem_machineWitnesses_iff _).mpr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))

theorem MachineWitness.vacuous_mem :
    (MachineWitness.behaviour .vacuous : MachineWitness (sig W)) ∈ machineWitnesses W :=
  (mem_machineWitnesses_iff _).mpr (.inl rfl)

theorem machineWitnesses_ne_nil (W : Type 1) [CoveredMachine W] : machineWitnesses W ≠ [] :=
  List.ne_nil_of_mem MachineWitness.vacuous_mem

@[expose] def Pair.MachineMetTrivially (q : Pair W) : Prop :=
  (∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ s : q.Input → W, (∀ x, Witness.Constant (behaviourOf (s x))) ∧
      ∀ x, q.pre x → q.post x (s x)) ∨
    (2 ≤ (sig W).args.length ∧ ∃ i < (sig W).args.length, ∃ s : q.Input → W,
      (∀ x, Witness.BlindTo i (behaviourOf (s x))) ∧ ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ d ∈ degenerate (Behaviour W), ∃ w, d.Is (behaviourOf w) ∧ ∀ x, q.pre x → q.post x w) ∨
    (∃ k : ArgClock (sig W).args, ((∃ xs ys, xs ≠ ys ∧ k.read xs = k.read ys) ∨ k.InClock) ∧
      ∃ s : q.Input → W, (∀ x, Witness.TimedBy k (behaviourOf (s x))) ∧
        ∀ x, q.pre x → q.post x (s x)) ∨
    (∃ s : q.Input → W, (∀ x, (machineOf (s x)).ConstantAction) ∧
      ∀ x, q.pre x → q.post x (s x)) ∨
    ∃ s : q.Input → W, (∀ x, (machineOf (s x)).FixedInAdvance) ∧ ∀ x, q.pre x → q.post x (s x)

theorem machineMetTrivially_iff (q : Pair W) :
    q.MachineMetTrivially ↔ ∃ t ∈ machineWitnesses W, t.Meets q := by
  have st := fun (t : MachineWitness (sig W)) (hv : t ≠ .behaviour .vacuous)
    (hf : ∀ d, t ≠ .behaviour (.fixed d)) => MachineWitness.meets_iff_strategy q t hv hf
  have mem := fun t => (mem_machineWitnesses_iff (W := W) t).mpr
  constructor
  · rintro (h | h | ⟨hn, i, hi, h⟩ | ⟨d, hd, h⟩ | ⟨k, hk, h⟩ | h | h)
    · exact ⟨_, mem _ (.inl rfl), (MachineWitness.vacuous_meets_iff q).mpr h⟩
    · exact ⟨_, mem _ (.inr (.inl rfl)), (st (.behaviour .table) nofun nofun).mpr h⟩
    · exact ⟨_, mem _ (.inr (.inr (.inl ⟨hn, ⟨i, hi⟩, rfl⟩))),
        (st (.behaviour (.blind ⟨i, hi⟩)) nofun nofun).mpr h⟩
    · exact ⟨_, mem _ (.inr (.inr (.inr (.inl ⟨d, hd, rfl⟩)))), h⟩
    · exact ⟨_, mem _ (.inr (.inr (.inr (.inr (.inl ⟨k, hk, rfl⟩))))),
        (st (.behaviour (.timed k)) nofun nofun).mpr h⟩
    · exact ⟨_, MachineWitness.constantAction_mem, (st .constantAction nofun nofun).mpr h⟩
    · exact ⟨_, MachineWitness.fixedInAdvance_mem, (st .fixedInAdvance nofun nofun).mpr h⟩
  · rintro ⟨t, ht, hm⟩
    rcases (mem_machineWitnesses_iff t).mp ht with
      rfl | rfl | ⟨hn, i, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨k, hk, rfl⟩ | rfl | rfl
    · exact .inl ((MachineWitness.vacuous_meets_iff q).mp hm)
    · exact .inr (.inl ((st (.behaviour .table) nofun nofun).mp hm))
    · exact .inr (.inr (.inl ⟨hn, i.val, i.isLt, (st (.behaviour (.blind i)) nofun nofun).mp hm⟩))
    · exact .inr (.inr (.inr (.inl ⟨d, hd, hm⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨k, hk, (st (.behaviour (.timed k)) nofun nofun).mp hm⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ((st .constantAction nofun nofun).mp hm))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr ((st .fixedInAdvance nofun nofun).mp hm))))))

@[expose] def machineWitnessVerdicts (q : Pair W) (bs : List Bool) : List Prop :=
  if (sig W).strayClock then [False]
  else truthGoals (fun t : MachineWitness (sig W) => t.Meets q) (machineWitnesses W) bs

@[expose] def MachineWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  Goals (machineWitnessVerdicts q bs)

@[expose] def intendedMachineWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  (sig W).strayClock = false ∧ bs.length = (machineWitnesses W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (machineWitnesses W).length),
      (bs[i] = true ↔ (machineWitnesses W)[i].Meets q)

theorem machineWitnessVerdicts_correct (q : Pair W) (bs : List Bool) :
    MachineWitnessVerdicts q bs ↔ intendedMachineWitnessVerdicts q bs := by
  rw [MachineWitnessVerdicts, machineWitnessVerdicts, intendedMachineWitnessVerdicts]
  cases h : (sig W).strayClock
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact goals_truthGoals _ _ bs
  · simp [Goals]

theorem not_machineWitnessVerdicts_of_strayClock (h : (sig W).strayClock = true) (q : Pair W)
    (bs : List Bool) : ¬ MachineWitnessVerdicts q bs := by
  rw [machineWitnessVerdicts_correct]
  rintro ⟨hs, _⟩
  rw [h] at hs
  exact Bool.noConfusion hs

theorem machineTimed_mem_of_namedClock {q : Pair W} {bs : List Bool}
    (h : MachineWitnessVerdicts q bs)
    (i : Nat) (hi : i < (sig W).args.length) (o : Ty.NamedClock (sig W).args[i]) :
    ∃ (p : Σ p, Place.Path (.code (sig W).args[i]) p) (r : Place.ArgPath p.1 (sig W).args),
      o.path? = some p ∧ r.From p.2 i ∧ ArgClock.InClock ⟨p.1, r, .value⟩ ∧
        MachineWitness.behaviour (.timed ⟨p.1, r, .value⟩) ∈ machineWitnesses W := by
  obtain ⟨p, r, hp, hr, hk⟩ :=
    Sig.read_of_strayClock_eq_false ((machineWitnessVerdicts_correct q bs).mp h).1 i hi o
  exact ⟨p, r, hp, hr, hk,
    (mem_machineWitnesses_iff _).mpr (.inr (.inr (.inr (.inr (.inl ⟨_, .inr hk, rfl⟩)))))⟩

theorem goals_of_machineWitnessVerdicts {q : Pair W} {bs : List Bool}
    (h : MachineWitnessVerdicts q bs) :
    Goals (truthGoals (fun t : MachineWitness (sig W) => t.Meets q) (machineWitnesses W) bs) := by
  unfold MachineWitnessVerdicts machineWitnessVerdicts at h
  split at h
  · exact absurd h.1 id
  · exact h

@[expose] def machineReported (W : Type 1) [CoveredMachine W] (bs : List Bool) :
    List (MachineWitness (sig W)) :=
  truthsTrue (machineWitnesses W) bs

theorem mem_machineReported {q : Pair W} {bs : List Bool} (h : MachineWitnessVerdicts q bs)
    (t : MachineWitness (sig W)) :
    t ∈ machineReported W bs ↔ t ∈ machineWitnesses W ∧ t.Meets q :=
  mem_truthsTrue _ t _ bs (goals_of_machineWitnessVerdicts h)

theorem machineReported_eq_nil_iff {q : Pair W} {bs : List Bool} (h : MachineWitnessVerdicts q bs) :
    machineReported W bs = [] ↔ ¬ q.MachineMetTrivially := by
  rw [List.eq_nil_iff_forall_not_mem, machineMetTrivially_iff]
  constructor
  · rintro hn ⟨t, ht, hm⟩
    exact hn t ((mem_machineReported h t).mpr ⟨ht, hm⟩)
  · intro hn t ht
    exact hn ⟨t, (mem_machineReported h t).mp ht⟩

end MachineWitnesses

end LeanIntent
