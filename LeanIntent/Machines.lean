module

public import LeanIntent.TrivialWitnesses

/-!
# Subjects that carry their own memory type: machines

The degenerate check and the trivial-witness check cover a subject type through a code (`Ty`), and
every code denotes a type of `Type`. A subject whose values carry a type of their own lives in a
higher universe, so no code denotes it. One such subject is an agent that carries its own memory
type: a value holding a type `Memory`, an initial memory, and a step from a memory and an input to
an output and the next memory. This module covers such subjects, the *machines*, in both checks.

## The class of types covered

A type `W : Type 1` is covered as a machine (`LeanIntent.CoveredMachine`) when Lean's instance
resolution finds, from `W` alone, an input type `In` and an output type `Out`, each covered by a
code (`LeanIntent.HasCode`), and an isomorphism between `W` and the library's own machines from `In`
to `Out` (`LeanIntent.Machine`), with the proof that it is the one the library fixes
(`LeanIntent.Machine.Stands`):

* `Machine I O` itself, through the identity, for every `I` and `O` that have codes;
* a structure a project declares whose fields are a type `M : Type`, then a value of `M` and a step
  `M → I → O × M` in either order, under any names and parameters, with `I` and `O` naming no
  field, through the isomorphism that takes each field to the machine's field of the same role,
  which `deriving LeanIntent.CoveredMachine` writes from the declaration
  (`LeanIntent.MachineDeclared.Handler`), and which the audit of declared types' codes checks
  (`LeanIntent.CodeAudit`).

Every other type in a higher universe has no instance, so Lean reports that it cannot synthesize
`CoveredMachine W` and no verdict about it can be stated: a structure carrying several types or a
type and other fields, a memory in `Type 1` or above, a step without an input or without an output,
and a type-valued function.

## The reading of a subject: its behaviour

A machine's *behaviour* (`Machine.behaviour`) is the output it gives on an input after each history
of earlier inputs: `List I → I → O`, a type the codes cover. Every function of that type is the
behaviour of some machine (`Machine.ofBehaviour`, whose memory is the history), and a machine's
output at each step of a run is its behaviour at the inputs before that step, since its memory then
is the fold of its step over them (`Machine.memoryAfter`); so two machines with the same behaviour
give the same outputs on every sequence of inputs, whatever their memory types. So a subject of `W`
is read as the behaviour of the machine the isomorphism takes it to (`CoveredMachine.behaviourOf`),
and the classes of `W` are the classes of the behaviour type, each member standing for every
subject of `W` whose behaviour that member describes, of any memory type: no member fixes a memory
type, so a record or pair that constrains the memory, such as a bound on its number of values,
meets a member whenever some subject of any memory type with that behaviour meets it
(`Degenerate.isMachine_congr`, `Degenerate.isMachine_inv_iff`, `MachineWitness.admits_congr`).

## The degenerate class

`machineDegenerate W` is the degenerate class of the behaviour type (`LeanIntent.degenerate`):
the machine whose output is one value whatever its inputs, at each value the rule `Ty.Small`
admits, or as one member for the other constants of a type too large to list; and the machine whose
output is what it was given, its current input, its history or a part of either, or, where its
output is a function, that function's argument: a projection. `Degenerate.IsMachine
d w` states that `w` is a subject the member `d` stands for: its behaviour is one `d` stands for.
`MachineVerdicts r bs` states the verdict on each member for a record `r` about `W`, as `Verdicts`
does for a covered type, and `machinePossibilities` reports each member that meets the record.

## The trivial witnesses

`machineWitnesses W` is the class of trivial witnesses of the behaviour type
(`LeanIntent.witnesses`), each member read over `W` through the behaviour, and two members of
machines' own:

* `.constantAction`, at each input, a subject that gives one output whatever its inputs and history,
  fixed for that input in advance: one that ignores its input (`Machine.ConstantAction`);
* `.fixedInAdvance`, at each input, a subject whose output is fixed in advance, a function of the
  number of inputs it has had and of nothing they hold (`Machine.FixedInAdvance`): an open-loop
  agent, whose memory advances and whose output is chosen without reading its input
  (`Machine.OpenLoop`), such as a clocked script, whose memory is a step counter
  (`Machine.clockedScript`).

With `.behaviour .vacuous`, any subject at all, these are the witnesses the method names for an
agent with memory: one whose actions are fixed in advance, one that ignores its input, and the
vacuous witness. The behaviour type's own class holds the script on the history's length only where
the input has two values or more, since where it has one the history's length determines the
arguments and the type alone does not read it as a clock; and its table stands for the subjects
that ignore their input only where the output is no function, since the behaviour type's code
flattens a function in the output into further arguments, which a constant does not read either.
The machines' two members hold those subjects whatever the input and output types are.
`Pair.MachineMetTrivially` states, over strategies and apart from the class, that some trivial
witness meets a pair, and `machineMetTrivially_iff` equates it with some member of the class meeting
it. `MachineWitnessVerdicts q bs` is the check.
-/

public section

namespace LeanIntent

/-! ## Machines -/

/-- A machine from inputs of type `I` to outputs of type `O` that carries its own memory type: an
agent with memory is one, its inputs the percepts and its outputs the actions. -/
structure Machine (I O : Type) : Type 1 where
  /-- Everything the machine retains between inputs. -/
  Memory : Type
  /-- The memory before the first input. -/
  initial : Memory
  /-- One step: the output on an input and the memory kept after it. -/
  step : Memory → I → O × Memory

namespace Machine

variable {I O : Type}

/-- The memory a machine holds after the inputs of `h`, in order. -/
@[expose] def memoryAfter (m : Machine I O) (h : List I) : m.Memory :=
  h.foldl (fun s i => (m.step s i).2) m.initial

/-- The behaviour of a machine: its output on the input `i` after the history `h` of earlier inputs.
-/
@[expose] def behaviour (m : Machine I O) (h : List I) (i : I) : O :=
  (m.step (m.memoryAfter h) i).1

theorem memoryAfter_nil (m : Machine I O) : m.memoryAfter [] = m.initial := rfl

theorem memoryAfter_append_singleton (m : Machine I O) (h : List I) (i : I) :
    m.memoryAfter (h ++ [i]) = (m.step (m.memoryAfter h) i).2 := by
  simp only [memoryAfter, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The machine whose memory is the history of its inputs, and whose output is what `b` gives of
that history and the input. -/
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

/-- Every function of type `List I → I → O` is the behaviour of a machine. -/
theorem behaviour_ofBehaviour (b : List I → I → O) : (ofBehaviour b).behaviour = b := by
  funext h i
  simp only [behaviour, memoryAfter_ofBehaviour]
  rfl

/-- The clocked script that gives `s n` at the `n`-th input, counted from zero: its memory is a step
counter, and it reads no input. -/
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

/-- A clocked script's output at an input is its action for the number of inputs before it. -/
theorem behaviour_clockedScript (s : Nat → O) :
    (clockedScript s : Machine I O).behaviour = fun h _ => s h.length := by
  funext h i
  simp only [behaviour, memoryAfter_clockedScript]
  rfl

/-- An open-loop machine: its output and its next memory are functions of its memory alone, so it
reads no input. -/
@[expose] def OpenLoop (m : Machine I O) : Prop :=
  ∃ (advance : m.Memory → m.Memory) (choose : m.Memory → O),
    ∀ s i, m.step s i = (choose s, advance s)

/-- A machine whose outputs are fixed in advance: its output is a function of the number of inputs
it has had and of nothing they hold. -/
@[expose] def FixedInAdvance (m : Machine I O) : Prop :=
  ∃ s : Nat → O, ∀ h i, m.behaviour h i = s h.length

/-- A machine that gives one output whatever its inputs and history: one that ignores its input. -/
@[expose] def ConstantAction (m : Machine I O) : Prop :=
  ∃ o : O, ∀ h i, m.behaviour h i = o

/-- An open-loop machine's outputs are fixed in advance: its memory after `n` inputs is its initial
memory advanced `n` times, whatever the inputs were. -/
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

/-- A clocked script is open-loop. -/
theorem clockedScript_openLoop (s : Nat → O) : (clockedScript s : Machine I O).OpenLoop :=
  ⟨fun n => Nat.succ (n : Nat), s, fun _ _ => rfl⟩

/-- A machine's outputs are fixed in advance exactly when it behaves as a clocked script. -/
theorem fixedInAdvance_iff_script (m : Machine I O) :
    m.FixedInAdvance ↔ ∃ s : Nat → O, m.behaviour = (clockedScript s).behaviour := by
  rw [show (∃ s : Nat → O, m.behaviour = (clockedScript s).behaviour) ↔
      ∃ s : Nat → O, m.behaviour = fun h _ => s h.length from
    exists_congr fun s => by rw [behaviour_clockedScript]]
  exact exists_congr fun s => ⟨fun h => funext fun l => funext fun i => h l i,
    fun h l i => congrFun (congrFun h l) i⟩

/-- A machine that ignores its input has its outputs fixed in advance. -/
theorem ConstantAction.fixedInAdvance {m : Machine I O} (hm : m.ConstantAction) :
    m.FixedInAdvance :=
  let ⟨o, h⟩ := hm
  ⟨fun _ => o, h⟩

end Machine

/-! ## The types covered as machines -/

/-- An isomorphism between `W` and the machines from `I` to `O`: a map each way, each undoing the
other. -/
structure MachineIso (W : Type 1) (I O : Type) where
  /-- The map to machines. -/
  to : W → Machine I O
  /-- The map back. -/
  inv : Machine I O → W
  inv_to : ∀ w, inv (to w) = w
  to_inv : ∀ m, to (inv m) = m

/-- The identity of the machines from `I` to `O`. -/
@[expose] def MachineIso.refl (I O : Type) : MachineIso (Machine I O) I O :=
  ⟨fun m => m, fun m => m, fun _ => rfl, fun _ => rfl⟩

/-- `e` is the isomorphism through which `W` stands for the machines from `I` to `O`, as the library
fixes it: the identity for the library's own machines, and for a structure a project declares, the
isomorphism its deriving handler writes from the declaration, which takes each field to the
machine's field of the same role. The last constructor, which admits the latter, is private, and the
handler of `LeanIntent.MachineDeclared.Handler` is the only code of the library that applies it. Lean's
privacy binds names only, so that nothing else applies it is decided for a declaration by the audit
of declared types' codes (`LeanIntent.CodeAudit`), and trusted where the audit is not run. -/
inductive Machine.Stands : (W : Type 1) → (I O : Type) → MachineIso W I O → Prop
  | self (I O : Type) : Machine.Stands (Machine I O) I O (MachineIso.refl I O)
  | private decl {W : Type 1} {I O : Type} (e : MachineIso W I O) : Machine.Stands W I O e

/-- The type `W` is covered as a machine: an input type and an output type, each with a code, found
by Lean's instance resolution from `W` alone, with the isomorphism through which `W` stands for the
machines between them and the proof that it is the one the library fixes. A type with no such
instance is not covered, and no verdict about it can be stated. -/
class CoveredMachine (W : Type 1) where
  /-- The type of the inputs. -/
  In : Type
  /-- The type of the outputs. -/
  Out : Type
  /-- The code of the inputs' type. -/
  inCode : HasCode In
  /-- The code of the outputs' type. -/
  outCode : HasCode Out
  /-- The isomorphism through which `W` stands for the machines from `In` to `Out`. -/
  iso : MachineIso W In Out
  /-- The isomorphism is the one the library fixes. -/
  stands : Machine.Stands W In Out iso

/-- The library's own machines are covered through the identity. -/
instance {I O : Type} [hi : HasCode I] [ho : HasCode O] : CoveredMachine (Machine I O) :=
  ⟨I, O, hi, ho, .refl I O, .self I O⟩

/-! ## The reading of a subject -/

namespace CoveredMachine

/-- The behaviours of the subjects of `W`: functions from a history of inputs and an input to an
output. -/
@[expose] def Behaviour (W : Type 1) [m : CoveredMachine W] : Type := List m.In → m.In → m.Out

/-- The behaviour type is covered through the codes of the input and output types, as Lean's
instance resolution covers `List In → In → Out`. -/
instance behaviourCovered (W : Type 1) [m : CoveredMachine W] : Covered (Behaviour W) := by
  letI := m.inCode
  letI := m.outCode
  exact inferInstanceAs (Covered (List m.In → m.In → m.Out))

/-- The code of the behaviour type, of which the classes of `W` are the classes. -/
abbrev sig (W : Type 1) [CoveredMachine W] : Sig := (behaviourCovered W).sig

variable {W : Type 1} [m : CoveredMachine W]

/-- The machine a subject is, through the isomorphism `W`'s coverage fixes. -/
@[expose] def machineOf (w : W) : Machine m.In m.Out := m.iso.to w

/-- The subject of `W` that is the machine `x`. -/
@[expose] def ofMachine (x : Machine m.In m.Out) : W := m.iso.inv x

/-- The behaviour of a subject: that of the machine it is. -/
@[expose] def behaviourOf (w : W) : Behaviour W := (machineOf w).behaviour

/-- A subject whose machine has the history as its memory and the behaviour `b`. -/
@[expose] def realize (b : Behaviour W) : W := ofMachine (Machine.ofBehaviour b)

theorem machineOf_ofMachine (x : Machine m.In m.Out) : machineOf (ofMachine x : W) = x :=
  m.iso.to_inv x

theorem ofMachine_machineOf (w : W) : ofMachine (machineOf w) = w := m.iso.inv_to w

theorem behaviourOf_ofMachine (x : Machine m.In m.Out) :
    behaviourOf (ofMachine x : W) = x.behaviour := by
  rw [behaviourOf, machineOf_ofMachine]

/-- Every behaviour is that of a subject. -/
theorem behaviourOf_realize (b : Behaviour W) : behaviourOf (realize b : W) = b := by
  rw [realize, behaviourOf_ofMachine]
  exact Machine.behaviour_ofBehaviour b

/-- A constant subject of the behaviour type gives one output whatever its history and input. -/
theorem constant_apply {f : Behaviour W} (h : Witness.Constant f) :
    ∃ o : m.Out, ∀ l i, f l i = o := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨m.outCode.iso.inv ((Sig.flat m.outCode.code).inv (Sig.Fn.const _ v _)),
    fun _ _ => rfl⟩

/-- The behaviour type's isomorphism takes a behaviour to the function of its code: each argument
carried back through its own type's isomorphism, and the output forth. -/
theorem behaviourIso_to (f : Behaviour W) (h : List (m.inCode.code.denote))
    (i : m.inCode.code.denote) :
    (behaviourCovered W).iso.to f h i =
      (Sig.flat m.outCode.code).to
        (m.outCode.iso.to (f (m.inCode.iso.list.inv h) (m.inCode.iso.inv i))) :=
  rfl

/-- A behaviour does not read its history, the behaviour type's first argument, exactly when it
gives the same output on an input after every history: the behaviour of a reactive machine. -/
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

/-- A behaviour does not read its current input, the behaviour type's second argument, exactly when
it gives the same output on every input after each history. -/
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

/-! ## Goals stating truth values -/

/-- The goals that `bs` are, in order, the truth values of `P` at the members `xs`: `P x` where the
value is `true` and `¬ P x` where it is `false`, and the goal `False` when the lists differ in
length. -/
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

/-- The members among `xs` whose value in `bs` is `true`. -/
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

/-! ## The degenerate class of a machine type -/

/-- The degenerate subjects of a type covered as a machine, by their descriptions: the class of its
behaviour type. It takes no record, so it is the same for every record about `W`. -/
@[expose] def machineDegenerate (W : Type 1) [CoveredMachine W] : List (Degenerate (sig W)) :=
  degenerate (Behaviour W)

section MachineVerdicts

variable {W : Type 1} [m : CoveredMachine W]

/-- `w` is a subject the description `d` stands for: its behaviour is one `d` stands for. It names
no memory type, so `d` stands for every subject of any memory type that behaves so. -/
@[expose] def Degenerate.IsMachine (d : Degenerate (sig W)) (w : W) : Prop := d.Is (behaviourOf w)

/-- A subject `d` stands for meets the record `r`. -/
@[expose] def Degenerate.MeetsMachine (d : Degenerate (sig W)) (r : IntentRecord W) : Prop :=
  ∃ w, d.IsMachine w ∧ r.Meets w

/-- Two subjects with one behaviour are subjects of the same members, whatever their memory types.
-/
theorem Degenerate.isMachine_congr (d : Degenerate (sig W)) {w w' : W}
    (h : behaviourOf w = behaviourOf w') : d.IsMachine w ↔ d.IsMachine w' := by
  rw [Degenerate.IsMachine, Degenerate.IsMachine, h]

/-- The subject that is the machine `x`, of any memory type, is a subject of `d` exactly when `x`'s
behaviour is one `d` stands for. -/
theorem Degenerate.isMachine_inv_iff (d : Degenerate (sig W)) (x : Machine m.In m.Out) :
    d.IsMachine (ofMachine x : W) ↔ d.Is x.behaviour := by
  rw [Degenerate.IsMachine, behaviourOf_ofMachine]

/-- Every behaviour a member stands for is that of one of `W`'s subjects. -/
theorem Degenerate.isMachine_realize {d : Degenerate (sig W)} {b : Behaviour W} (h : d.Is b) :
    d.IsMachine (realize b : W) := by
  rw [Degenerate.IsMachine, behaviourOf_realize]
  exact h

/-- The degenerate check's goals for a type covered as a machine: that `bs` are, in order, the
verdicts on the members of `machineDegenerate W` for `r`. -/
@[expose] def machineVerdicts (r : IntentRecord W) (bs : List Bool) : List Prop :=
  truthGoals (fun d : Degenerate (sig W) => d.MeetsMachine r) (machineDegenerate W) bs

/-- `bs` are the verdicts, in order, on the degenerate subjects of `W` for `r`. -/
@[expose] def MachineVerdicts (r : IntentRecord W) (bs : List Bool) : Prop := Goals (machineVerdicts r bs)

/-- What the check asks, written apart from its former: one verdict for each member of the class,
`true` exactly when some subject whose behaviour the member at the same position stands for meets
the record. -/
@[expose] def intendedMachineVerdicts (r : IntentRecord W) (bs : List Bool) : Prop :=
  bs.length = (machineDegenerate W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (machineDegenerate W).length),
      (bs[i] = true ↔ ∃ w, (machineDegenerate W)[i].Is (behaviourOf w) ∧
        (∀ x ∈ r.dom, x.holds w) ∧ ∀ p ∈ r.props, p.holds w)

/-- The check's former states it. -/
theorem machineVerdicts_correct (r : IntentRecord W) (bs : List Bool) :
    MachineVerdicts r bs ↔ intendedMachineVerdicts r bs := by
  rw [MachineVerdicts, machineVerdicts, goals_truthGoals]
  simp only [intendedMachineVerdicts, Degenerate.MeetsMachine, Degenerate.IsMachine,
    IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props]

/-- The members of the class of `W` whose verdict in `bs` is that they meet the record. -/
@[expose] def machineMetBy (W : Type 1) [CoveredMachine W] (bs : List Bool) : List (Degenerate (sig W)) :=
  truthsTrue (machineDegenerate W) bs

/-- The members the verdicts report are exactly those a subject of which meets the record. -/
theorem mem_machineMetBy {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs)
    (d : Degenerate (sig W)) : d ∈ machineMetBy W bs ↔ d ∈ machineDegenerate W ∧ d.MeetsMachine r :=
  mem_truthsTrue _ d _ bs h

/-- The verdicts report no member exactly when no subject of any member meets the record. -/
theorem machineMetBy_eq_nil_iff {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs) :
    machineMetBy W bs = [] ↔ ∀ d ∈ machineDegenerate W, ¬ d.MeetsMachine r := by
  rw [List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun d => by rw [mem_machineMetBy h]; exact not_and

/-- Proved verdicts that report nothing refute every subject of every member, of every memory type.
-/
theorem not_meets_of_machineMetBy_eq_nil {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) (he : machineMetBy W bs = []) {d : Degenerate (sig W)}
    (hd : d ∈ machineDegenerate W) {w : W} (hw : d.IsMachine w) : ¬ r.Meets w :=
  fun hm => (machineMetBy_eq_nil_iff h).mp he d hd ⟨w, hw, hm⟩

/-- The name a member's consequence is read by, for a machine: what kind of member it is. -/
@[expose] def Degenerate.machineName {σ : Sig} : Degenerate σ → String
  | .const _ => "the record allows a machine that gives one output whatever its inputs"
  | .proj _ => "the record allows a machine that gives as its output what it was given: its current \
      input, its history of earlier inputs or a part of either, or, where its output is a function, \
      that function's argument"
  | .others => "the record allows a machine that gives one output whatever its inputs, at some \
      output other than the empty one"

/-- The consequence shown for a member: the possibility that the subject is one the member stands
for. -/
@[expose] def Degenerate.machineConsequence (d : Degenerate (sig W)) : Consequence W :=
  ⟨d.machineName, .possibility, d.IsMachine⟩

/-- Declining a member's consequence is kept by exactly the revisions that no subject of the member
meets. -/
theorem Degenerate.machineDeclined_keptBy_iff (d : Degenerate (sig W)) (r : IntentRecord W) :
    (Answer.mk d.machineConsequence .declined).KeptBy r ↔ ¬ d.MeetsMachine r := by
  simp only [Answer.KeptBy, Degenerate.machineConsequence, Degenerate.MeetsMachine]
  exact ⟨fun h ⟨w, hi, hm⟩ => h w hm hi, fun h w hm hi => h ⟨w, hi, hm⟩⟩

/-- The consequences reported: one for each member the proved verdicts `bs` say meets the record, in
order. It takes the proof of the verdicts, so no report exists for verdicts that are not proved. -/
@[expose] def machinePossibilities {r : IntentRecord W} {bs : List Bool} (_ : MachineVerdicts r bs) :
    List (Consequence W) :=
  (machineMetBy W bs).map Degenerate.machineConsequence

/-- Under proved verdicts, the reported consequences are exactly those of the members a subject of
which meets the record. -/
theorem mem_machinePossibilities {r : IntentRecord W} {bs : List Bool} (h : MachineVerdicts r bs)
    (x : Consequence W) :
    x ∈ machinePossibilities h ↔
      ∃ d ∈ machineDegenerate W, d.MeetsMachine r ∧ x = d.machineConsequence := by
  simp only [machinePossibilities, List.mem_map, mem_machineMetBy h]
  exact ⟨fun ⟨d, ⟨hd, hm⟩, e⟩ => ⟨d, hd, hm, e.symm⟩, fun ⟨d, hd, hm, e⟩ => ⟨d, ⟨hd, hm⟩, e.symm⟩⟩

/-- Each reported consequence is a possibility that holds of the record as it is shown. -/
theorem machinePossibilities_holdsOf {r : IntentRecord W} {bs : List Bool}
    (h : MachineVerdicts r bs) (x : Consequence W) (hx : x ∈ machinePossibilities h) :
    x.kind = .possibility ∧ x.HoldsOf r := by
  obtain ⟨d, _, ⟨w, hi, hm⟩, rfl⟩ := (mem_machinePossibilities h x).mp hx
  exact ⟨rfl, w, hm, hi⟩

end MachineVerdicts

/-! ## The trivial witnesses of a machine type -/

/-- A trivial witness of a pair about a type covered as a machine whose behaviour type has the code
`σ`, by its description. -/
inductive MachineWitness (σ : Sig) where
  /-- A member of the behaviour type's class (`LeanIntent.Witness`), read through the behaviour. -/
  | behaviour (t : Witness σ)
  /-- At each input, a subject that gives one output whatever its inputs and history, fixed for that
  input in advance: one that ignores its input. -/
  | constantAction
  /-- At each input, a subject whose outputs are fixed in advance, a function of the number of
  inputs it has had: an open-loop agent, such as a clocked script. -/
  | fixedInAdvance

/-- The trivial witnesses of a pair about the type `W` covered as a machine: the class of its
behaviour type, each member read through the behaviour, then the subjects that ignore their input
and those whose outputs are fixed in advance. It takes no pair, so it is the same for every pair
about `W`, whatever its input type. -/
@[expose] def machineWitnesses (W : Type 1) [CoveredMachine W] : List (MachineWitness (sig W)) :=
  (witnesses (Behaviour W)).map .behaviour ++ [.constantAction, .fixedInAdvance]

section MachineWitnesses

variable {W : Type 1} [m : CoveredMachine W]

/-- The subjects a member offers at an input: for `.behaviour .vacuous`, any subject; for a member
of the behaviour type's class, a subject whose behaviour the member admits (a constant, one that
does not read an argument, one of the degenerate member, one that reads only a clock part); for
`.constantAction`, one that ignores its input; for `.fixedInAdvance`, one whose outputs are fixed in
advance. Each reads the subject only through its behaviour (`MachineWitness.admits_congr`). -/
@[expose] def MachineWitness.Admits : MachineWitness (sig W) → W → Prop
  | .behaviour .vacuous, _ => True
  | .behaviour .table, w => Witness.Constant (behaviourOf w)
  | .behaviour (.blind i), w => Witness.BlindTo i.val (behaviourOf w)
  | .behaviour (.fixed d), w => d.IsMachine w
  | .behaviour (.timed k), w => Witness.TimedBy k (behaviourOf w)
  | .constantAction, w => (machineOf w).ConstantAction
  | .fixedInAdvance, w => (machineOf w).FixedInAdvance

/-- The member `t` meets the pair `q`: for `.behaviour .vacuous`, every subject meets it; for
`.behaviour (.fixed d)`, one subject of `d`, offered at every input, does; and for every other
member, at each input the precondition admits, some subject the member admits meets the
postcondition. -/
@[expose] def MachineWitness.Meets (t : MachineWitness (sig W)) (q : Pair W) : Prop :=
  match t with
  | .behaviour .vacuous => ∀ w, q.Met w
  | .behaviour (.fixed d) => ∃ w, d.IsMachine w ∧ q.Met w
  | t => ∀ x, q.pre x → ∃ w, t.Admits w ∧ q.post x w

/-- Whether a member admits a subject depends on its behaviour alone, so no member fixes a memory
type: a subject of any memory type with the same behaviour is admitted alike. -/
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

/-- The machine that gives the empty output whatever its inputs, which every member admits. -/
@[expose] def emptyAction : W :=
  ofMachine (Machine.ofBehaviour fun _ _ => m.outCode.iso.inv ((Sig.flat m.outCode.code).inv
    (Sig.Fn.const _ (sig W).out.empty _)))

theorem behaviourOf_emptyAction :
    behaviourOf (emptyAction : W) = Degenerate.constantSubject (sig W).out.empty := by
  rw [emptyAction, behaviourOf_ofMachine, Machine.behaviour_ofBehaviour]
  rfl

/-- The machine that gives the empty output whatever its inputs is a constant subject. -/
theorem constant_emptyAction : Witness.Constant (behaviourOf (emptyAction : W)) :=
  ⟨_, behaviourOf_emptyAction⟩

/-- A subject whose behaviour is constant ignores its input. -/
theorem constantAction_of_constant {w : W} (h : Witness.Constant (behaviourOf w)) :
    (machineOf w).ConstantAction :=
  constant_apply h

/-- Every member other than `.behaviour (.fixed d)` admits the machine that gives the empty output
whatever its inputs. -/
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
/-- A choice, at each admitted input, of a subject with the property `P` that meets the
postcondition there is one strategy, which offers `w₀` at every other input. -/
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

/-- `.behaviour .vacuous` meets the pair exactly when every strategy does. -/
theorem MachineWitness.vacuous_meets_iff (q : Pair W) :
    (MachineWitness.behaviour .vacuous : MachineWitness (sig W)).Meets q ↔
      ∀ s : q.Input → W, ∀ x, q.pre x → q.post x (s x) :=
  ⟨fun h s x hx => h (s x) x hx, fun h w x hx => h (fun _ => w) x hx⟩

/-- `.behaviour (.fixed d)` meets the pair exactly when one subject of `d`, offered at every input,
does. -/
theorem MachineWitness.fixed_meets_iff (q : Pair W) (d : Degenerate (sig W)) :
    (MachineWitness.behaviour (.fixed d)).Meets q ↔
      ∃ w, d.IsMachine w ∧ ∀ x, q.pre x → q.post x w :=
  Iff.rfl

/-- Every member other than `.behaviour .vacuous` and `.behaviour (.fixed d)` meets the pair exactly
when some strategy whose every subject it admits does. -/
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

/-! ### The witnesses the method names -/

/-- `.fixedInAdvance` meets the pair exactly when, at each input the precondition admits, some
subject that behaves as a clocked script, of any memory type, meets the postcondition: a table of
clocked scripts, one chosen for each input, read as their behaviours. -/
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

/-- Open-loop agents, one chosen for each input the precondition admits, that meet the postcondition
make `.fixedInAdvance` meet the pair. -/
theorem MachineWitness.fixedInAdvance_meets_of_openLoop {q : Pair W}
    (h : ∀ x, q.pre x → ∃ w, (machineOf w).OpenLoop ∧ q.post x w) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, hw.fixedInAdvance, hp⟩

/-- A table of clocked scripts, the one that gives `sc x n` at the `n`-th input chosen for each
input `x`, that meets the pair makes `.fixedInAdvance` meet it. -/
theorem MachineWitness.fixedInAdvance_meets_of_clockedScripts {q : Pair W}
    (sc : q.Input → Nat → m.Out)
    (h : ∀ x, q.pre x → q.post x (ofMachine (Machine.clockedScript (sc x)))) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q :=
  MachineWitness.fixedInAdvance_meets_of_openLoop fun x hx =>
    ⟨_, by rw [machineOf_ofMachine]; exact Machine.clockedScript_openLoop (sc x), h x hx⟩

/-- One subject that ignores its input and meets the pair makes `.constantAction` meet it. -/
theorem MachineWitness.constantAction_meets_of_met {q : Pair W} {w : W}
    (hw : (machineOf w).ConstantAction) (h : q.Met w) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q :=
  fun x hx => ⟨w, hw, h x hx⟩

/-- Where `.constantAction` meets the pair, so does `.fixedInAdvance`. -/
theorem MachineWitness.fixedInAdvance_meets_of_constantAction {q : Pair W}
    (h : (MachineWitness.constantAction : MachineWitness (sig W)).Meets q) :
    (MachineWitness.fixedInAdvance : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, Machine.ConstantAction.fixedInAdvance hw, hp⟩

/-- Where the behaviour type's table meets the pair, so does `.constantAction`. -/
theorem MachineWitness.constantAction_meets_of_table {q : Pair W}
    (h : (MachineWitness.behaviour .table : MachineWitness (sig W)).Meets q) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q := fun x hx =>
  let ⟨w, hw, hp⟩ := h x hx
  ⟨w, constantAction_of_constant hw, hp⟩

/-- Where every subject meets the pair, `.constantAction` does. -/
theorem MachineWitness.constantAction_meets_of_vacuous {q : Pair W}
    (h : (MachineWitness.behaviour .vacuous : MachineWitness (sig W)).Meets q) :
    (MachineWitness.constantAction : MachineWitness (sig W)).Meets q :=
  MachineWitness.constantAction_meets_of_met
    (constantAction_of_constant constant_emptyAction) (h emptyAction)

/-- No member meets a pair with an admitted input that no subject serves, so none is met by every
pair. -/
theorem MachineWitness.not_meets_of_unserved {q : Pair W} {x : q.Input} (hx : q.pre x)
    (h : ∀ w, ¬ q.post x w) : (t : MachineWitness (sig W)) → ¬ t.Meets q
  | .behaviour .vacuous => fun hm => h _ (hm emptyAction x hx)
  | .behaviour (.fixed _) => fun ⟨w, _, hm⟩ => h w (hm x hx)
  | .behaviour .table => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .behaviour (.blind _) => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .behaviour (.timed _) => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .constantAction => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp
  | .fixedInAdvance => fun hm => let ⟨w, _, hp⟩ := hm x hx; h w hp

/-! ### The class -/

/-- The class, apart from the list that computes it: each member of the behaviour type's class
(`Sig.mem_witnesses_iff` states that class apart from its list), then `.constantAction` and
`.fixedInAdvance`. -/
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

/-- The class has the behaviour type's members and two more. -/
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

/-- No class is empty. -/
theorem machineWitnesses_ne_nil (W : Type 1) [CoveredMachine W] : machineWitnesses W ≠ [] :=
  List.ne_nil_of_mem MachineWitness.vacuous_mem

/-- Some trivial witness meets the pair `q` about a type covered as a machine, stated over
strategies, each the subject offered at every input, and apart from the class: every strategy meets
it; a strategy whose every subject's behaviour is constant does; for a behaviour of at least two
arguments, a strategy whose every subject's behaviour does not read one same argument does; one
subject whose behaviour a member of the behaviour type's degenerate class stands for, offered at
every input, does; for a clock part of the behaviour's arguments whose reading does not determine
them or that is a `LeanIntent.Clock α`, a strategy whose every subject's behaviour reads only it
does; a strategy of subjects that ignore their input does; or a strategy of subjects whose outputs
are fixed in advance does. -/
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

/-- The class lists every trivial witness: some trivial witness meets the pair exactly when some
member of the class does. -/
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

/-! ### Verdicts -/

/-- The trivial-witness check's goals for a type covered as a machine: that `bs` are, in order, the
verdicts on the members of `machineWitnesses W` for the pair `q`; and the goal `False` when an
argument of the behaviour type holds a `LeanIntent.Clock` where no clock part reaches it
(`Sig.strayClock`), a declaration of a clock the class cannot read. -/
@[expose] def machineWitnessVerdicts (q : Pair W) (bs : List Bool) : List Prop :=
  if (sig W).strayClock then [False]
  else truthGoals (fun t : MachineWitness (sig W) => t.Meets q) (machineWitnesses W) bs

/-- `bs` are the verdicts, in order, on the trivial witnesses of `W` for the pair `q`. -/
@[expose] def MachineWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  Goals (machineWitnessVerdicts q bs)

/-- What the check asks, written apart from its former: no argument of the behaviour type holds a
`LeanIntent.Clock` the class cannot read, and one verdict for each member of the class, `true`
exactly when the member at the same position meets the pair. -/
@[expose] def intendedMachineWitnessVerdicts (q : Pair W) (bs : List Bool) : Prop :=
  (sig W).strayClock = false ∧ bs.length = (machineWitnesses W).length ∧
    ∀ (i : Nat) (hb : i < bs.length) (hd : i < (machineWitnesses W).length),
      (bs[i] = true ↔ (machineWitnesses W)[i].Meets q)

/-- The check's former states it. -/
theorem machineWitnessVerdicts_correct (q : Pair W) (bs : List Bool) :
    MachineWitnessVerdicts q bs ↔ intendedMachineWitnessVerdicts q bs := by
  rw [MachineWitnessVerdicts, machineWitnessVerdicts, intendedMachineWitnessVerdicts]
  cases h : (sig W).strayClock
  · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact goals_truthGoals _ _ bs
  · simp [Goals]

/-- No verdict about a type whose behaviour holds a `LeanIntent.Clock` no clock part reaches can be
proved. -/
theorem not_machineWitnessVerdicts_of_strayClock (h : (sig W).strayClock = true) (q : Pair W)
    (bs : List Bool) : ¬ MachineWitnessVerdicts q bs := by
  rw [machineWitnessVerdicts_correct]
  rintro ⟨hs, _⟩
  rw [h] at hs
  exact Bool.noConfusion hs

/-- Proved verdicts are the verdicts, in order, on the members of the class. -/
theorem goals_of_machineWitnessVerdicts {q : Pair W} {bs : List Bool}
    (h : MachineWitnessVerdicts q bs) :
    Goals (truthGoals (fun t : MachineWitness (sig W) => t.Meets q) (machineWitnesses W) bs) := by
  unfold MachineWitnessVerdicts machineWitnessVerdicts at h
  split at h
  · exact absurd h.1 id
  · exact h

/-- The members of the class of `W` whose verdict in `bs` is that they meet the pair. -/
@[expose] def machineReported (W : Type 1) [CoveredMachine W] (bs : List Bool) :
    List (MachineWitness (sig W)) :=
  truthsTrue (machineWitnesses W) bs

/-- Under proved verdicts, the members reported are exactly those that meet the pair. -/
theorem mem_machineReported {q : Pair W} {bs : List Bool} (h : MachineWitnessVerdicts q bs)
    (t : MachineWitness (sig W)) :
    t ∈ machineReported W bs ↔ t ∈ machineWitnesses W ∧ t.Meets q :=
  mem_truthsTrue _ t _ bs (goals_of_machineWitnessVerdicts h)

/-- Under proved verdicts, the report is empty exactly when no trivial witness meets the pair, so a
witness that meets it is never missed. -/
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
