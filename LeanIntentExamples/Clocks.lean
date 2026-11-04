import LeanIntentExamples.TrivialWitnesses

/-!
# Scripts of timed actions whose clock sits inside an argument or is the only argument

The agents of `LeanIntentExamples.TrivialWitnesses` follow courses of two steps. Here three more
agents follow them, each of a type whose class held no script of timed actions before the clock
parts (`LeanIntent.Clocks`), so that a pair met by a script fixed to each course passed the check.

* An agent that remembers what it has seen, of type `List Bool → Bool`. Its timed script reads only
  the length of its history, a clock part whose reading does not determine the history, so the class
  holds the script on it, last. Each readable course alone is followed by such a script, so the
  per-course pair is reported (`perCourseH_witnesses`, `perCourseH_script_reported`); no script
  follows every readable course, and no member meets the pair whose only input is trivial
  (`wholeCourseH_witnesses`), which the agent that does what it saw last meets.
* An agent that sees a structure holding the time and what it sees, of type `Glance → Bool`. The time
  field is a clock part whose reading does not determine the glance, so the class holds the script on
  it, met by the per-course pair as the projection onto what it sees is
  (`perCourseG_witnesses`).
* A policy that reads only a clock, of type `Clock → Bool`: every such policy is a script, and the
  type says its argument is a clock, so the class holds the script on it, which meets the pair that
  gives each policy one schedule to keep (`perSchedule_witnesses`). The same pair about policies of
  type `Nat → Bool` reports nothing (`perScheduleNat_witnesses`): the number is all a policy reads,
  and the type alone reads it as what the policy sees.

A `LeanIntent.Clock` inside a list, where no clock part reaches, is a declaration the class cannot
read, and no verdict about such a type can be proved (`stray_refused`).
-/

namespace LeanIntentExamples.Clocks

open LeanIntent LeanIntentExamples.TrivialWitnesses

/-! ## An agent with a history -/

/-- An agent that acts on everything it has seen, oldest first. -/
abbrev Historied := List Bool → Bool

/-- What the agent has seen by the step `t` of the course `v`, oldest first. -/
def history (v : Course) (t : Fin 2) : List Bool :=
  if t.val = 0 then [v.sight 0] else [v.sight 0, v.sight 1]

/-- The agent `a` follows the course `v`: at each step, on its history, it takes the action that
step needs. -/
def FollowsH (a : Historied) (v : Course) : Prop := ∀ t, a (history v t) = v.need t

/-- The property that the agent follows every readable course. -/
def followsReadableH : Clause Historied :=
  ⟨"follows every readable course", fun a => ∀ v, Readable v → FollowsH a v⟩

/-- The record of an agent with a history that follows every readable course. -/
def historied : IntentRecord Historied where
  shape := .function _ _
  dom := []
  props := [followsReadableH]
  vocab := [⟨"Readable", Course, Readable⟩,
    ⟨"Follows", Historied × Course, fun p => FollowsH p.1 p.2⟩]

/-- The pair the property gives for each course. -/
def perCourseH : Pair Historied := ⟨Course, Readable, fun v a => FollowsH a v⟩

/-- `perCourseH` is a pair of the property. -/
theorem perCourseH_pairOf : historied.PairOf followsReadableH perCourseH :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

/-- The script that takes, at each length of the history, the action the course `v` needs then. -/
def scriptFor (v : Course) : Historied := fun h => if h.length = 1 then v.need 0 else v.need 1

/-- The per-course pair is met by the script of timed actions on the history's length fixed to each
course, and by no other member: not by every agent, the table or a constant. -/
theorem perCourseH_witnesses : WitnessVerdicts perCourseH [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun v _ => ⟨scriptFor v, fun xs ys e => ?_, fun t => ?_⟩, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) allTrue (fun _ => rfl) 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h zigzag fun _ => rfl
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true (h allFalse (fun _ => rfl) 0).symm
  · show scriptFor v xs.1 = scriptFor v ys.1
    unfold scriptFor
    rw [show xs.1.length = ys.1.length from e]
  · match t with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- The check reports the script on the history's length for the per-course pair. -/
theorem perCourseH_script_reported :
    Witness.timed (.here (.length .bool)) ∈ reported Historied [false, false, false, false, true] :=
  (mem_reported perCourseH_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ⟨([true], ()), ([false], ()),
      fun h => Bool.noConfusion (List.cons.inj (congrArg Prod.fst h)).1, rfl⟩),
      perCourseH_witnesses.2.2.2.2.1⟩

/-- The pair whose only input is trivial is met by no member: no script on the history's length,
table or constant follows every readable course, since at the first step the history `[true]` and
the history `[false]` have one length. -/
theorem wholeCourseH_witnesses :
    WitnessVerdicts (Pair.whole historied followsReadableH) [false, false, false, false, false] := by
  have hNoScript : ¬ (Witness.timed (.here (.length .bool)) :
      Witness (Covered.sig (W := Historied))).Meets (Pair.whole historied followsReadableH) :=
    fun h => by
      obtain ⟨a, hk, hf⟩ := h PUnit.unit trivial
      have hall := hf fun _ hd => nomatch hd
      have e : a [true] = a [false] := hk ([true], ()) ([false], ()) rfl
      have ht : a [true] = true := hall allTrue (fun _ => rfl) 0
      have hf' : a [false] = false := hall allFalse (fun _ => rfl) 0
      exact Bool.false_ne_true (hf'.symm.trans (e.symm.trans ht))
  refine ⟨fun h => ?_, fun h => hNoScript (Witness.timed_meets_of_table _ h),
    fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, hNoScript, trivial⟩
  · exact Bool.false_ne_true
      (h (fun _ => false) PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allFalse (fun _ => rfl) 0).symm

/-- The agent that does what it saw last follows every readable course, so the whole pair passes
the check for a reason no trivial witness gives. -/
theorem lastSeen_follows : followsReadableH.holds fun h => h.getLastD false := by
  intro v hv t
  match t with
  | ⟨0, _⟩ => exact (hv 0).symm
  | ⟨1, _⟩ => exact (hv 1).symm

/-! ## An agent that sees the time -/

/-- What an agent sees at a step: the time, and the bit it sees then. -/
structure Glance where
  /-- The step. -/
  time : Fin 2
  /-- What the agent sees. -/
  sight : Bool
  deriving LeanIntent.HasCode

/-- An agent that acts on a glance. -/
abbrev Glancer := Glance → Bool

/-- The pair that asks, for each readable course, that the agent take at each step the action that
step needs, on the glance it has then. -/
def perCourseG : Pair Glancer :=
  ⟨Course, Readable, fun v a => ∀ t, a ⟨t, v.sight t⟩ = v.need t⟩

/-- The per-course pair is met by the projection onto what the agent sees and by the script on the
time field fixed to each course; not by every agent, the table or a constant. -/
theorem perCourseG_witnesses :
    WitnessVerdicts perCourseG [false, false, false, false, true, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    ⟨_, rfl, fun _ hv t => (hv t).symm⟩,
    fun v _ => ⟨fun g => v.need g.time, fun _ _ e => congrArg v.need (Fin.ext e), fun _ => rfl⟩,
    trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) allTrue (fun _ => rfl) 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h zigzag fun _ => rfl
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true (h allFalse (fun _ => rfl) 0).symm

/-! ## A policy that reads only a clock -/

/-- A policy that acts on the clock alone. -/
abbrev Policy := Clock → Bool

/-- The pair that gives each policy one schedule, the action each of two ticks needs, and asks it to
keep that schedule. -/
def perSchedule : Pair Policy := ⟨Fin 2 → Bool, fun _ => True, fun s a => ∀ t, a ⟨t.val⟩ = s t⟩

/-- Every policy keeps its own schedule, so the script on the clock meets the per-schedule pair, as
no constant, table or every policy does. -/
theorem perSchedule_witnesses :
    WitnessVerdicts perSchedule [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun s _ => ⟨fun c => if c.tick = 0 then s 0 else s 1, fun _ _ e => ?_, fun t => ?_⟩, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) (fun _ => true) trivial 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h (fun t => t.val == 0) trivial
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h (fun _ => true) trivial 0)
  · subst e
    exact Bool.false_ne_true (h (fun _ => false) trivial 0).symm
  · exact congrArg (fun n => if n = 0 then _ else _) e
  · match t with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- The same pair about policies of type `Nat → Bool`: the number is all a policy reads, and the type
alone reads it as what the policy sees, so the class holds no script and reports nothing. -/
theorem perScheduleNat_witnesses :
    WitnessVerdicts (⟨Fin 2 → Bool, fun _ => True, fun s a => ∀ t, a t.val = s t⟩ : Pair (Nat → Bool))
      [false, false, false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) (fun _ => true) trivial 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h (fun t => t.val == 0) trivial
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h (fun _ => true) trivial 0)
  · subst e
    exact Bool.false_ne_true (h (fun _ => false) trivial 0).symm

/-! ## A clock the class cannot read -/

/-- A `LeanIntent.Clock` inside a list, where no clock part reaches, is refused: no verdict about a
pair of agents of type `List Clock → Bool` can be proved. -/
theorem stray_refused (q : Pair (List Clock → Bool)) (bs : List Bool) : ¬ WitnessVerdicts q bs :=
  not_witnessVerdicts_of_strayClock (by decide) q bs

end LeanIntentExamples.Clocks
