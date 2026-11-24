module

public import LeanIntent.MachineDeclared

public section

namespace LeanIntentExamples.Machines

open LeanIntent CoveredMachine

abbrev Position := Fin 4

structure Agent where
  Memory : Type
  initial : Memory
  act : Memory → Position → Bool × Memory
  deriving LeanIntent.CoveredMachine

@[expose] def move (p : Position) (forward : Bool) : Position := if forward then p + 1 else p

@[expose] def loop (a : Agent) (start : Position) : Nat → Position × a.Memory
  | 0 => (start, a.initial)
  | t + 1 =>
    let s := loop a start t
    (move s.1 (a.act s.2 s.1).1, (a.act s.2 s.1).2)

@[expose] def ReachesFrom (a : Agent) (start : Position) : Prop := (loop a start 3).1 = 0

instance (a : Agent) (start : Position) : Decidable (ReachesFrom a start) :=
  inferInstanceAs (Decidable (_ = _))

theorem forall_position {P : Position → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ s, P s
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

@[expose] def visits (b : List Position → Position → Bool) (start : Position) :
    Nat → Position × List Position
  | 0 => (start, [])
  | t + 1 =>
    let s := visits b start t
    (move s.1 (b s.2 s.1), s.2 ++ [s.1])

theorem loop_eq (a : Agent) (start : Position) (t : Nat) :
    loop a start t = ((visits (behaviourOf a) start t).1,
      (machineOf a).memoryAfter (visits (behaviourOf a) start t).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [loop, visits, ih, Machine.memoryAfter_append_singleton]
    rfl

theorem reachesFrom_iff (a : Agent) (start : Position) :
    ReachesFrom a start ↔ (visits (behaviourOf a) start 3).1 = 0 := by
  rw [ReachesFrom, loop_eq]

theorem visits_three (b : List Position → Position → Bool) (start : Position) :
    ∃ a₁ a₂ : Bool, (visits b start 3).1 = move (move (move start (b [] start)) a₁) a₂ :=
  ⟨_, _, rfl⟩

theorem not_reachesFrom_two {a : Agent} {o : Bool} (h : ∀ l i, behaviourOf a l i = o) :
    ¬ ReachesFrom a 2 := by
  rw [reachesFrom_iff, show behaviourOf a = fun _ _ => o from funext fun l => funext (h l)]
  cases o <;> decide

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

@[expose] def reachesHome : Clause Agent :=
  ⟨"from every start, at position 0 after three steps", fun a => ∀ s, ReachesFrom a s⟩

@[expose] def homing : IntentRecord Agent where
  shape := .value _
  dom := []
  props := [reachesHome]
  vocab := []

@[expose] def perStart : Pair Agent := ⟨ULift Position, fun _ => True, fun s a => ReachesFrom a s.down⟩

theorem perStart_pairOf : homing.PairOf reachesHome perStart :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h s _ => h (fun _ hd => nomatch hd) s.down, fun h _ s => h ⟨s⟩ trivial⟩⟩

@[expose] def stay : Agent := ⟨Unit, (), fun _ _ => (false, ())⟩

@[expose] def homeward : Agent := ⟨Unit, (), fun _ p => (p != 0, ())⟩

@[expose] def counter (k : Nat) : Agent := ⟨Nat, 0, fun n _ => (decide (n < k), n + 1)⟩

@[expose] def needed (s : Position) : Nat := (4 - s.val) % 4

theorem homeward_reaches : ∀ s, ReachesFrom homeward s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

theorem counter_reaches : ∀ s, ReachesFrom (counter (needed s)) s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

theorem not_reachesFrom_stay : ¬ ReachesFrom stay 1 := by decide

theorem machineOf_counter (k : Nat) :
    machineOf (counter k) = Machine.clockedScript fun n => decide (n < k) := rfl

theorem counter_openLoop (k : Nat) : (machineOf (counter k)).OpenLoop := by
  rw [machineOf_counter]
  exact Machine.clockedScript_openLoop _

theorem not_reachesFrom_two_of_constant {a : Agent} (h : Witness.Constant (behaviourOf a)) :
    ¬ ReachesFrom a 2 :=
  let ⟨_, ho⟩ := constant_apply h
  not_reachesFrom_two ho

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

theorem perStart_fixedInAdvance_reported :
    MachineWitness.fixedInAdvance ∈ machineReported Agent
      [false, false, true, true, false, false, true, true, true, false, true] :=
  (mem_machineReported perStart_witnesses _).mpr
    ⟨MachineWitness.fixedInAdvance_mem, perStart_witnesses.2.2.2.2.2.2.2.2.2.2.1⟩

theorem not_whole_of_first {a : Agent}
    (h : behaviourOf a [] (0 : Position) = behaviourOf a [] (1 : Position))
    (hr : homing.Dom a → reachesHome.holds a) : False :=
  not_both h (hr (fun _ hd => nomatch hd) 0) (hr (fun _ hd => nomatch hd) 1)

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

@[expose] def perStartSmall : Pair Agent :=
  ⟨ULift Position, fun _ => True,
    fun s a => ReachesFrom a s.down ∧ ∃ f : a.Memory → Fin 4, Function.Injective f⟩

@[expose] def ringCounter (k : Nat) : Agent := ⟨Fin 4, 0, fun n _ => (decide (n.val < k), n + 1)⟩

theorem ringCounter_openLoop (k : Nat) : (machineOf (ringCounter k)).OpenLoop :=
  ⟨fun (n : Fin 4) => n + 1, fun (n : Fin 4) => decide (n.val < k), fun _ _ => rfl⟩

theorem ringCounter_reaches : ∀ s, ReachesFrom (ringCounter (needed s)) s :=
  forall_position (by decide) (by decide) (by decide) (by decide)

theorem perStartSmall_fixedInAdvance :
    (MachineWitness.fixedInAdvance : MachineWitness (sig Agent)).Meets perStartSmall :=
  MachineWitness.fixedInAdvance_meets_of_openLoop fun x _ =>
    ⟨ringCounter (needed x.down), ringCounter_openLoop _, ringCounter_reaches x.down,
      fun (n : Fin 4) => n, fun _ _ e => e⟩

theorem homing_verdicts : MachineVerdicts homing [false, false] :=
  ⟨fun ⟨_, hi, hm⟩ =>
      not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm.2 _ (List.mem_singleton_self _) 2),
    fun ⟨_, hi, hm⟩ =>
      not_reachesFrom_two_of_constant ⟨_, hi⟩ (hm.2 _ (List.mem_singleton_self _) 2),
    trivial⟩

@[expose] def staysHome : Clause Agent :=
  ⟨"from position 0, at position 0 after three steps", fun a => ReachesFrom a 0⟩

@[expose] def stayHome : IntentRecord Agent where
  shape := .value _
  dom := []
  props := [staysHome]
  vocab := []

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

theorem stayHome_possibilities :
    machinePossibilities stayHome_verdicts =
      [machineConsequence Agent ⟨0, by decide⟩] :=
  rfl

theorem machineOf_machine (x : Machine Position Bool) : machineOf x = x := rfl

structure Indexed (n : Nat) where
  Memory : Type
  act : Memory → Bool → Fin (n + 1) × Memory
  initial : Memory
  deriving LeanIntent.CoveredMachine

theorem indexed_witnesses_length (n : Nat) :
    (machineWitnesses (Indexed n)).length = (witnesses (Behaviour (Indexed n))).length + 2 :=
  length_machineWitnesses _

private structure Hidden where
  State : Type
  next : State → Position → Bool × State
  start : State
  deriving LeanIntent.CoveredMachine

private theorem hidden_machineOf (h : Hidden) : machineOf h = ⟨h.State, h.start, h.next⟩ := rfl

end LeanIntentExamples.Machines
