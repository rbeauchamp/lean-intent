module

public import LeanIntent.MachineDeclared

/-!
# An agent that carries its own memory type

A project declares its agent as a structure that carries its own memory type: the memory, the
memory before it sees anything, and a decision from a memory and what it sees to an action and the
next memory, as an agent of a world does. `deriving LeanIntent.CoveredMachine` covers it, so the
degenerate check and the trivial-witness check give verdicts about its records and pairs, though it
lives in `Type 1` and no code denotes it.

The agent's world is a ring of four positions, and all the agent sees is where it is. Its one
action steps forward one position or stays. Its record asks it to be at position `0` after three
steps from every start (`homing`); from each start some number of steps forward, at most three,
gets there, so a goal is feasible from every start, and a clocked script, which reads nothing it
sees and steps forward that many times, reaches it.

* The pair the property gives for each start (`perStart`) is met by the member of agents whose
  actions are fixed in advance, through the clocked script that suits each start, and the check
  reports it (`perStart_witnesses`, `perStart_fixedInAdvance_reported`); so that pair's obligation
  is no evidence that the agent uses what it sees. No agent that takes one action throughout reaches
  `0` from position `2`, which needs two steps forward out of three, so the members of constants and
  of constant actions do not meet it.
* The pair whose only input is trivial, one agent for every start, is met by no agent whose first
  action does not read what it sees, so by no script, constant or agent that reads only its
  history (`whole_witnesses`); the agent that steps forward exactly when it is not at `0`, which
  keeps no memory, meets it, and the members of agents that do not read their history and that read
  only what they see report it.
* The degenerate check refutes both constant agents for `homing` (`homing_verdicts`), and reports
  the agent that never moves for a record asking only that an agent at `0` be at `0` after three
  steps (`stayHome_verdicts`, `stayHome_possibilities`).
* No member fixes a memory type: a pair that also bounds the agent's memory to four values is still
  met by the member of agents whose actions are fixed in advance, through a script whose memory is a
  counter round the ring (`perStartSmall_fixedInAdvance`), where a clocked script's memory, a
  number, has more values than four.

`Position` and `Bool` have codes, so the instance covers `Agent` (`agent_witnesses_length`). The
library's own machines from positions to actions are covered through the identity, and a structure
with a value parameter, whose fields come in another order, is covered by the same handler
(`Indexed`). A structure the module keeps to itself is covered the same way, under private names,
in this module only (`Hidden`, `hidden_machineOf`): it is marked `private`, and a structure of a
`module` file that no `public section` holds, and that is not marked `public`, is private in the
same way.
-/

public section

namespace LeanIntentExamples.Machines

open LeanIntent CoveredMachine

/-- A position on the ring, which is all the agent sees. -/
abbrev Position := Fin 4

/-- An agent, as a project declares it: it carries its own memory type. -/
structure Agent where
  /-- Everything the agent retains between what it sees. -/
  Memory : Type
  /-- The memory before it sees anything. -/
  initial : Memory
  /-- One decision: whether to step forward on seeing a position, and the memory kept after it. -/
  act : Memory → Position → Bool × Memory
  deriving LeanIntent.CoveredMachine

/-- The world's dynamics: stepping forward moves one position round the ring. -/
@[expose] def move (p : Position) (forward : Bool) : Position := if forward then p + 1 else p

/-- The closed loop of the agent and the world from a start: the position and the agent's memory
before each step. -/
@[expose] def loop (a : Agent) (start : Position) : Nat → Position × a.Memory
  | 0 => (start, a.initial)
  | t + 1 =>
    let s := loop a start t
    (move s.1 (a.act s.2 s.1).1, (a.act s.2 s.1).2)

/-- The agent reaches position `0` after three steps from `start`. -/
@[expose] def ReachesFrom (a : Agent) (start : Position) : Prop := (loop a start 3).1 = 0

instance (a : Agent) (start : Position) : Decidable (ReachesFrom a start) :=
  inferInstanceAs (Decidable (_ = _))

/-- A statement about every position holds when it holds at each of the four. -/
theorem forall_position {P : Position → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ s, P s
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

/-- The positions a behaviour visits from a start, with the history of what it saw before each step.
-/
@[expose] def visits (b : List Position → Position → Bool) (start : Position) :
    Nat → Position × List Position
  | 0 => (start, [])
  | t + 1 =>
    let s := visits b start t
    (move s.1 (b s.2 s.1), s.2 ++ [s.1])

/-- The closed loop is the one the agent's behaviour drives: its positions are those the behaviour
visits, and its memory the one the agent holds after what it saw. -/
theorem loop_eq (a : Agent) (start : Position) (t : Nat) :
    loop a start t = ((visits (behaviourOf a) start t).1,
      (machineOf a).memoryAfter (visits (behaviourOf a) start t).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [loop, visits, ih, Machine.memoryAfter_append_singleton]
    rfl

/-- Whether an agent reaches `0` from a start depends on its behaviour alone. -/
theorem reachesFrom_iff (a : Agent) (start : Position) :
    ReachesFrom a start ↔ (visits (behaviourOf a) start 3).1 = 0 := by
  rw [ReachesFrom, loop_eq]

/-- After three steps, a behaviour is where its three actions took it, the first on what it sees at
the start with no history. -/
theorem visits_three (b : List Position → Position → Bool) (start : Position) :
    ∃ a₁ a₂ : Bool, (visits b start 3).1 = move (move (move start (b [] start)) a₁) a₂ :=
  ⟨_, _, rfl⟩

/-- An agent that takes one action throughout does not reach `0` from position `2`. -/
theorem not_reachesFrom_two {a : Agent} {o : Bool} (h : ∀ l i, behaviourOf a l i = o) :
    ¬ ReachesFrom a 2 := by
  rw [reachesFrom_iff, show behaviourOf a = fun _ _ => o from funext fun l => funext (h l)]
  cases o <;> decide

/-- No agent whose first action does not read what it sees reaches `0` both from `0` and from `1`:
from `0` its first step forward leaves it short of the four it would need, and from `1` staying
leaves it more than three steps away. -/
theorem not_both {a : Agent} (h : behaviourOf a [] (0 : Position) = behaviourOf a [] (1 : Position))
    (h0 : ReachesFrom a 0)
    (h1 : ReachesFrom a 1) : False := by
  rw [reachesFrom_iff] at h0 h1
  obtain ⟨a₁, a₂, e₀⟩ := visits_three (behaviourOf a) 0
  obtain ⟨b₁, b₂, e₁⟩ := visits_three (behaviourOf a) 1
  rw [e₀] at h0
  rw [e₁, ← h] at h1
  revert h0 h1
  cases behaviourOf a [] (0 : Position) <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    decide

/-! ## The record and its pairs -/

/-- The property: from every start, the agent is at `0` after three steps. -/
@[expose] def reachesHome : Clause Agent :=
  ⟨"from every start, at position 0 after three steps", fun a => ∀ s, ReachesFrom a s⟩

/-- The record of an agent that gets home from every start. -/
@[expose] def homing : IntentRecord Agent where
  shape := .value _
  dom := []
  props := [reachesHome]
  vocab := []

/-- The pair the property gives for each start. -/
@[expose] def perStart : Pair Agent := ⟨ULift Position, fun _ => True, fun s a => ReachesFrom a s.down⟩

/-- `perStart` is a pair of the property. -/
theorem perStart_pairOf : homing.PairOf reachesHome perStart :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h s _ => h (fun _ hd => nomatch hd) s.down, fun h _ s => h ⟨s⟩ trivial⟩⟩

/-! ## Agents -/

/-- The agent that never moves. -/
@[expose] def stay : Agent := ⟨Unit, (), fun _ _ => (false, ())⟩

/-- The agent that steps forward exactly when it is not at `0`. It keeps no memory. -/
@[expose] def homeward : Agent := ⟨Unit, (), fun _ p => (p != 0, ())⟩

/-- The clocked script that steps forward at its first `k` steps and then stays: its memory is a
step counter, and it reads nothing it sees. -/
@[expose] def counter (k : Nat) : Agent := ⟨Nat, 0, fun n _ => (decide (n < k), n + 1)⟩

/-- The number of steps forward that gets home from a start. -/
@[expose] def needed (s : Position) : Nat := (4 - s.val) % 4

theorem homeward_reaches : ∀ s, ReachesFrom homeward s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

theorem counter_reaches : ∀ s, ReachesFrom (counter (needed s)) s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

theorem not_reachesFrom_stay : ¬ ReachesFrom stay 1 := by decide

/-- `counter k` is the clocked script that steps forward at its first `k` steps. -/
theorem machineOf_counter (k : Nat) :
    machineOf (counter k) = Machine.clockedScript fun n => decide (n < k) := rfl

/-- `counter k` is open-loop: its memory advances and its action is chosen without reading what it
sees. -/
theorem counter_openLoop (k : Nat) : (machineOf (counter k)).OpenLoop := by
  rw [machineOf_counter]
  exact Machine.clockedScript_openLoop _

/-! ## The trivial witnesses -/

/-- The class of the agent's type: any agent, the table of constants, an agent that does not read
its history and one that does not read what it sees now, the agent that always stays and the one
that always steps forward, the scripts on its history, on the history's length and on what it sees
now, then an agent that takes one action throughout and one whose actions are fixed in advance. -/
theorem agent_witnesses_length : (machineWitnesses Agent).length = 11 := by decide

/-- A constant subject of the behaviour type does not reach `0` from position `2`. -/
theorem not_reachesFrom_two_of_constant {a : Agent} (h : Witness.Constant (behaviourOf a)) :
    ¬ ReachesFrom a 2 :=
  let ⟨_, ho⟩ := constant_apply h
  not_reachesFrom_two ho

/-- The per-start pair is met by an agent that does not read its history, by one that does not read
what it sees now, by the scripts on its history, on the history's length and on what it sees now,
and by an agent whose actions are fixed in advance, through the clocked script that suits each
start; not by every agent, by the table, by a constant agent or by one that takes one action
throughout, since none of those reaches `0` from position `2`. -/
theorem perStart_witnesses :
    MachineWitnessVerdicts perStart
      [false, false, true, true, false, false, true, true, true, false, true] := by
  refine ⟨fun h => not_reachesFrom_stay (h stay ⟨1⟩ trivial),
    fun h => ?_,
    fun x _ => ⟨homeward, (blindTo_history_iff _).mpr fun _ _ _ => rfl, homeward_reaches x.down⟩,
    fun x _ => ⟨counter (needed x.down), (blindTo_input_iff _).mpr fun _ _ _ => rfl,
      counter_reaches x.down⟩,
    fun ⟨w, hi, hm⟩ => not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm ⟨2⟩ trivial),
    fun ⟨w, hi, hm⟩ => not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm ⟨2⟩ trivial),
    fun x _ => ⟨counter (needed x.down), fun xs ys e => ?_, counter_reaches x.down⟩,
    fun x _ => ⟨counter (needed x.down), fun xs ys e => ?_, counter_reaches x.down⟩,
    fun x _ => ⟨homeward, fun xs ys e => ?_, homeward_reaches x.down⟩,
    fun h => ?_,
    MachineWitness.fixedInAdvance_meets_of_openLoop fun x _ =>
      ⟨counter (needed x.down), counter_openLoop _, counter_reaches x.down⟩,
    trivial⟩
  · obtain ⟨w, hc, hr⟩ := h ⟨2⟩ trivial
    exact not_reachesFrom_two_of_constant hc hr
  · obtain ⟨h₁, i₁, ⟨⟩⟩ := xs
    obtain ⟨h₂, i₂, ⟨⟩⟩ := ys
    change h₁ = h₂ at e
    subst e
    rfl
  · obtain ⟨h₁, i₁, ⟨⟩⟩ := xs
    obtain ⟨h₂, i₂, ⟨⟩⟩ := ys
    change h₁.length = h₂.length at e
    show (behaviourCovered Agent).iso.to _ h₁ i₁ = (behaviourCovered Agent).iso.to _ h₂ i₂
    rw [behaviourIso_to, behaviourIso_to]
    simp only [behaviourOf, machineOf_counter, Machine.behaviour_clockedScript]
    have len : ∀ l, (HasCode.iso.list.inv l : List Position).length = List.length l :=
      fun l => List.length_map ..
    rw [len, len, e]
  · obtain ⟨h₁, i₁, ⟨⟩⟩ := xs
    obtain ⟨h₂, i₂, ⟨⟩⟩ := ys
    change i₁ = i₂ at e
    subst e
    rfl
  · obtain ⟨w, ⟨o, ho⟩, hr⟩ := h ⟨2⟩ trivial
    exact not_reachesFrom_two ho hr

/-- The check reports, for the per-start pair, the member of agents whose actions are fixed in
advance. -/
theorem perStart_fixedInAdvance_reported :
    MachineWitness.fixedInAdvance ∈ machineReported Agent
      [false, false, true, true, false, false, true, true, true, false, true] :=
  (mem_machineReported perStart_witnesses _).mpr
    ⟨MachineWitness.fixedInAdvance_mem, perStart_witnesses.2.2.2.2.2.2.2.2.2.2.1⟩

/-- No agent whose first action does not read what it sees gets home from every start. -/
theorem not_whole_of_first {a : Agent}
    (h : behaviourOf a [] (0 : Position) = behaviourOf a [] (1 : Position))
    (hr : homing.Dom a → reachesHome.holds a) : False :=
  not_both h (hr (fun _ hd => nomatch hd) 0) (hr (fun _ hd => nomatch hd) 1)

/-- The pair whose only input is trivial is met by the agent that steps forward exactly when it is
not at `0`, which does not read its history and reads only what it sees now; by no agent whose first
action does not read what it sees, so by no script, constant, agent that takes one action throughout
or agent whose actions are fixed in advance; and not by every agent. -/
theorem whole_witnesses :
    MachineWitnessVerdicts (Pair.whole homing reachesHome)
      [false, false, true, false, false, false, false, false, true, false, false] := by
  have dom : homing.Dom stay := fun _ hd => nomatch hd
  refine ⟨fun h => not_reachesFrom_stay (h stay PUnit.unit trivial dom 1),
    fun h => ?_,
    fun _ _ => ⟨homeward, (blindTo_history_iff _).mpr fun _ _ _ => rfl,
      fun _ => homeward_reaches⟩,
    fun h => ?_,
    fun ⟨w, hi, hm⟩ => not_reachesFrom_two_of_constant ⟨_, hi⟩
      (hm PUnit.unit trivial (fun _ hd => nomatch hd) 2),
    fun ⟨w, hi, hm⟩ => not_reachesFrom_two_of_constant ⟨_, hi⟩
      (hm PUnit.unit trivial (fun _ hd => nomatch hd) 2),
    fun h => ?_, fun h => ?_,
    fun _ _ => ⟨homeward, fun xs ys e => ?_, fun _ => homeward_reaches⟩,
    fun h => ?_, fun h => ?_, trivial⟩
  · obtain ⟨w, hc, hr⟩ := h PUnit.unit trivial
    exact not_reachesFrom_two_of_constant hc (hr (fun _ hd => nomatch hd) 2)
  · obtain ⟨w, hb, hr⟩ := h PUnit.unit trivial
    exact not_whole_of_first ((blindTo_input_iff _).mp hb [] (0 : Position) (1 : Position)) hr
  · obtain ⟨w, hk, hr⟩ := h PUnit.unit trivial
    exact not_whole_of_first (hk ([], (0 : Position), ()) ([], (1 : Position), ()) rfl) hr
  · obtain ⟨w, hk, hr⟩ := h PUnit.unit trivial
    exact not_whole_of_first (hk ([], (0 : Position), ()) ([], (1 : Position), ()) rfl) hr
  · obtain ⟨h₁, i₁, ⟨⟩⟩ := xs
    obtain ⟨h₂, i₂, ⟨⟩⟩ := ys
    change i₁ = i₂ at e
    subst e
    rfl
  · obtain ⟨w, ⟨o, ho⟩, hr⟩ := h PUnit.unit trivial
    exact not_reachesFrom_two ho (hr (fun _ hd => nomatch hd) 2)
  · obtain ⟨w, ⟨sc, hs⟩, hr⟩ := h PUnit.unit trivial
    exact not_whole_of_first ((hs [] (0 : Position)).trans (hs [] (1 : Position)).symm) hr

/-! ## No member fixes a memory type -/

/-- The pair for each start that also bounds the agent's memory to four values. -/
@[expose] def perStartSmall : Pair Agent :=
  ⟨ULift Position, fun _ => True,
    fun s a => ReachesFrom a s.down ∧ ∃ f : a.Memory → Fin 4, Function.Injective f⟩

/-- The script that steps forward at its first `k` steps, whose memory is a counter round the ring
of four. -/
@[expose] def ringCounter (k : Nat) : Agent := ⟨Fin 4, 0, fun n _ => (decide (n.val < k), n + 1)⟩

/-- `ringCounter k` is open-loop. -/
theorem ringCounter_openLoop (k : Nat) : (machineOf (ringCounter k)).OpenLoop :=
  ⟨fun (n : Fin 4) => n + 1, fun (n : Fin 4) => decide (n.val < k), fun _ _ => rfl⟩

theorem ringCounter_reaches : ∀ s, ReachesFrom (ringCounter (needed s)) s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

/-- The pair that bounds the memory is met by an agent whose actions are fixed in advance, of
memory `Fin 4`: the member stands for agents of every memory type, so a bound on the memory that the
clocked script, whose memory is a number, does not meet leaves the member met. -/
theorem perStartSmall_fixedInAdvance :
    (MachineWitness.fixedInAdvance : MachineWitness (sig Agent)).Meets perStartSmall :=
  MachineWitness.fixedInAdvance_meets_of_openLoop fun x _ =>
    ⟨ringCounter (needed x.down), ringCounter_openLoop _, ringCounter_reaches x.down,
      fun (n : Fin 4) => n, fun _ _ e => e⟩

/-! ## The degenerate check -/

/-- The degenerate class of the agent's type: the agent that always stays and the one that always
steps forward. -/
theorem agent_degenerate_length : (machineDegenerate Agent).length = 2 := by decide

/-- Neither constant agent gets home from every start: neither reaches `0` from position `2`. -/
theorem homing_verdicts : MachineVerdicts homing [false, false] :=
  ⟨fun ⟨_, hi, hm⟩ =>
      not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm.2 _ (List.mem_singleton_self _) 2),
    fun ⟨_, hi, hm⟩ =>
      not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm.2 _ (List.mem_singleton_self _) 2),
    trivial⟩

/-- The property that an agent at `0` is at `0` after three steps. -/
@[expose] def staysHome : Clause Agent :=
  ⟨"from position 0, at position 0 after three steps", fun a => ReachesFrom a 0⟩

/-- A record that asks only that an agent at `0` be at `0` after three steps. -/
@[expose] def stayHome : IntentRecord Agent where
  shape := .value _
  dom := []
  props := [staysHome]
  vocab := []

/-- The agent that always stays meets it, and the agent that always steps forward does not. -/
theorem stayHome_verdicts : MachineVerdicts stayHome [true, false] :=
  ⟨⟨stay, rfl, (⟨(fun _ hd => nomatch hd), fun p hp => by
      obtain rfl := List.mem_singleton.mp hp
      show ReachesFrom stay 0
      decide⟩ : stayHome.Dom stay ∧ stayHome.Props stay)⟩,
    fun ⟨w, hi, hm⟩ => by
      have h := hm.2 _ (List.mem_singleton_self _)
      rw [show staysHome.holds w = ReachesFrom w 0 from rfl, reachesFrom_iff,
        show behaviourOf w = fun _ _ => true from hi] at h
      exact absurd h (by decide),
    trivial⟩

/-- The check reports the agent that never moves as a possibility the record allows. -/
theorem stayHome_possibilities :
    machinePossibilities stayHome_verdicts =
      [Degenerate.machineConsequence (Degenerate.const false : Degenerate (sig Agent))] :=
  rfl

/-! ## Other types covered -/

/-- The library's own machines from positions to actions are covered through the identity, with the
same class. -/
theorem machine_witnesses_length : (machineWitnesses (Machine Position Bool)).length = 11 := by
  decide

/-- An agent indexed by the number of actions its interface offers, with its fields in another
order. -/
structure Indexed (n : Nat) where
  /-- Everything the agent retains. -/
  Memory : Type
  /-- One decision. -/
  act : Memory → Bool → Fin (n + 1) × Memory
  /-- The memory before it sees anything. -/
  initial : Memory
  deriving LeanIntent.CoveredMachine

/-- Its class has the members of its behaviour type and the two of machines, for every interface. -/
theorem indexed_witnesses_length (n : Nat) :
    (machineWitnesses (Indexed n)).length = (witnesses (Behaviour (Indexed n))).length + 2 :=
  length_machineWitnesses _

/-! ## A structure the module keeps to itself -/

/-- A machine private to this module, as its coverage then is. -/
private structure Hidden where
  /-- Everything it retains. -/
  State : Type
  /-- One step. -/
  next : State → Position → Bool × State
  /-- The state before its first input. -/
  start : State
  deriving LeanIntent.CoveredMachine

/-- The machine a value of the private structure is read as: the one with its fields, each in its
role, whatever their order and names. -/
private theorem hidden_machineOf (h : Hidden) : machineOf h = ⟨h.State, h.start, h.next⟩ := rfl

/-- The private structure has the class of the library's machines between the same types. -/
private theorem hidden_witnesses_length : (machineWitnesses Hidden).length = 11 := by
  decide

end LeanIntentExamples.Machines
