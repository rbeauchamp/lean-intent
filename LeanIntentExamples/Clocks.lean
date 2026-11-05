import LeanIntentExamples.TrivialWitnesses
import LeanIntentExamples.WithoutBase

/-!
# Scripts of timed actions whose clock sits inside an argument or is the only argument

The agents of `LeanIntentExamples.TrivialWitnesses` follow courses of two steps. Here more agents
follow them, each of a type whose class held no script of timed actions before the clock parts
(`LeanIntent.Clocks`), so that a pair met by a script fixed to each course passed the check.

* An agent that remembers what it has seen, of type `List Bool → Bool`. Its timed script reads only
  the length of its history, a clock part whose reading does not determine the history, so the class
  holds the script on it, last. Each readable course alone is followed by such a script, so the
  per-course pair is reported (`perCourseH_witnesses`, `perCourseH_script_reported`); no script
  follows every readable course, and no member meets the pair whose only input is trivial
  (`wholeCourseH_witnesses`), which the agent that does what it saw last meets.
* An agent that sees a structure holding the time and what it sees, of type `Glance → Bool`. Neither
  field's value determines the glance, so the class holds the script on each, the time and then what
  the agent sees, both met by the per-course pair as the projection onto what it sees is
  (`perCourseG_witnesses`).
* An agent that sees a view holding a machine time and what it sees, of type `TickView → Bool`. Its
  time is a `UInt64`, whose value does not determine the view, so the class holds the script on it.
  The pair that asks the agent to answer each input bit at time `0` and its negation at time `1`,
  while it sees `false` both times, is met by that script alone, which the check reports
  (`tick_witnesses`, `tick_script_reported`): no constant, projection or script on what it sees
  meets it.
* A policy that reads only a clock, of type `Clock Nat → Bool`: every such policy is a script, and
  the type says its argument is a clock, so the class holds the script on it, which meets the pair
  that gives each policy one schedule to keep (`perSchedule_witnesses`). Its tick, a number that
  also determines the argument, is no `LeanIntent.Clock`, so it adds no member. The same pair about
  policies of type `Nat → Bool` reports nothing (`perScheduleNat_witnesses`): the number is all a
  policy reads, and the type alone reads it as what the policy sees.
* An agent that sees a rose tree of `LeanIntentExamples.WithoutBase`, of type `Rose → Bool`, a
  recursive type nested through a list. Its one constructor's fields are clock parts: the label,
  whose value does not determine the tree, since the children may differ, and the children, read as
  a value and by their number, since `List Rose`, the group's type that holds them, is shaped as a
  list. The pair that asks the agent to answer each input bit at the leaf labelled `0` and its
  negation at the leaf labelled `1` is met by the script on the label alone, which the check reports
  (`rose_witnesses`, `rose_label_reported`).
* An agent that sees a link of `LeanIntentExamples.WithoutBase`, a structure whose one field is an
  option of itself: that field holds all of the link, so the type alone reads it as what the agent
  sees, and nothing inside the option, which has two constructors, is a clock part, so the class
  holds no script (`link_clocks`).

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
    Witness.timed ⟨_, .here (.self _), .length .bool⟩ ∈
      reported Historied [false, false, false, false, true] :=
  (mem_reported perCourseH_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ⟨([true], ()), ([false], ()),
      fun h => Bool.noConfusion (List.cons.inj (congrArg Prod.fst h)).1, rfl⟩),
      perCourseH_witnesses.2.2.2.2.1⟩

/-- The pair whose only input is trivial is met by no member: no script on the history's length,
table or constant follows every readable course, since at the first step the history `[true]` and
the history `[false]` have one length. -/
theorem wholeCourseH_witnesses :
    WitnessVerdicts (Pair.whole historied followsReadableH) [false, false, false, false, false] := by
  have hNoScript : ¬ (Witness.timed ⟨_, .here (.self _), .length .bool⟩ :
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

/-- The per-course pair is met by the projection onto what the agent sees, by the script on the time
field fixed to each course and by the subject that reads only what it sees; not by every agent, the
table or a constant. -/
theorem perCourseG_witnesses :
    WitnessVerdicts perCourseG [false, false, false, false, true, true, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    ⟨_, rfl, fun _ hv t => (hv t).symm⟩,
    fun v _ => ⟨fun g => v.need g.time, fun _ _ e => congrArg v.need e, fun _ => rfl⟩,
    fun _ hv => ⟨fun g => g.sight, fun _ _ e => e, fun t => (hv t).symm⟩,
    trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) allTrue (fun _ => rfl) 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h zigzag fun _ => rfl
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true (h allFalse (fun _ => rfl) 0).symm

/-! ## An agent that sees a machine time -/

/-- What an agent sees at a step: a machine time, and the bit it sees then. -/
structure TickView where
  /-- The time. -/
  time : UInt64
  /-- What the agent sees. -/
  sight : Bool
  deriving LeanIntent.HasCode

/-- The pair that asks, for each input bit `b`, that the agent answer `b` at time `0` and its negation
at time `1`, seeing `false` both times. -/
def tickPair : Pair (TickView → Bool) :=
  ⟨Bool, fun _ => True, fun b a => a ⟨0, false⟩ = b ∧ a ⟨1, false⟩ = !b⟩

/-- The pair is met by the script on the time fixed to each input bit, and by no other member: not
by every agent, the table, a constant, the projection onto what the agent sees or the subject that
reads only what it sees, since the two views differ only in their time. -/
theorem tick_witnesses :
    WitnessVerdicts tickPair [false, false, false, false, false, true, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun b _ => ⟨fun v => if v.time = 0 then b else !b,
      fun _ _ e => congrArg (fun t : UInt64 => if t = 0 then b else !b) e,
      ite_eq_left rfl, ite_eq_right (by decide)⟩,
    fun h => ?_, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) true trivial).1
  · obtain ⟨a, ⟨v, rfl⟩, h0, h1⟩ := h true trivial
    exact Bool.false_ne_true (h1.symm.trans h0)
  · subst e
    exact Bool.false_ne_true (h true trivial).1
  · subst e
    exact Bool.false_ne_true (h false trivial).1.symm
  · subst e
    exact Bool.false_ne_true (h true trivial).1
  · obtain ⟨a, hk, h0, h1⟩ := h true trivial
    have e : a ⟨0, false⟩ = a ⟨1, false⟩ :=
      hk (((0 : UInt64), false, ()), ()) (((1 : UInt64), false, ()), ()) rfl
    exact Bool.false_ne_true (h1.symm.trans (e.symm.trans h0))

/-- The check reports the script on the time for the pair. -/
theorem tick_script_reported :
    Witness.timed ⟨_, .here (.field _ _ (.head _ (.self _))), .value _⟩ ∈
      reported (TickView → Bool) [false, false, false, false, false, true, false] :=
  (mem_reported tick_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ⟨(((0 : UInt64), false, ()), ()), (((0 : UInt64), true, ()), ()),
      fun h => Bool.noConfusion (congrArg (fun p => p.1.2.1) h), rfl⟩),
      tick_witnesses.2.2.2.2.2.1⟩

/-! ## A policy that reads only a clock -/

/-- A policy that acts on the clock alone. -/
abbrev Policy := Clock Nat → Bool

/-- The pair that gives each policy one schedule, the action each of two ticks needs, and asks it to
keep that schedule. -/
def perSchedule : Pair Policy := ⟨Fin 2 → Bool, fun _ => True, fun s a => ∀ t, a ⟨t.val⟩ = s t⟩

/-- Every policy keeps its own schedule, so the script on the clock meets the per-schedule pair, as
no constant, table or every policy does. -/
theorem perSchedule_witnesses :
    WitnessVerdicts perSchedule [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun s _ => ⟨fun c => if c.tick = 0 then s 0 else s 1,
      Witness.timedBy_of_injective ((ArgClock.determines_iff _).mp rfl) _, fun t => ?_⟩, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) (fun _ => true) trivial 0)
  · obtain ⟨a, ⟨b, rfl⟩, hf⟩ := h (fun t => t.val == 0) trivial
    exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))
  · subst e
    exact Bool.false_ne_true (h (fun _ => true) trivial 0)
  · subst e
    exact Bool.false_ne_true (h (fun _ => false) trivial 0).symm
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

/-! ## An agent that sees a rose tree -/

open LeanIntentExamples.WithoutBase in
/-- A rose tree's label. -/
def label : Rose → Nat
  | .node n _ => n

open LeanIntentExamples.WithoutBase in
/-- The pair that asks, for each input bit `b`, that the agent answer `b` at the leaf labelled `0`
and its negation at the leaf labelled `1`. -/
def rosePair : Pair (Rose → Bool) :=
  ⟨Bool, fun _ => True, fun b a => a (.node 0 []) = b ∧ a (.node 1 []) = !b⟩

open LeanIntentExamples.WithoutBase in
/-- The clock part on a rose tree's label: the data of the one constructor of `Rose`, the group's
type `0`, which is not the group's root `List Rose`. -/
abbrev roseLabel : ArgClock (Covered.sig (W := Rose → Bool)).args :=
  ⟨_, .here (.field _ _ (.muAt rfl (.data (by decide) rfl (.head _ (.self _))))), .value _⟩

open LeanIntentExamples.WithoutBase in
/-- The label of a rose tree is what the clock part on it reads of the tree's code. -/
theorem rose_label (x : (HasCode.code Rose).denote) :
    label ((HasCode.iso (α := Rose)).inv x) = roseLabel.read (x, ()) := by
  cases x with
  | node c d k =>
    rcases c with ⟨_ | _, hc⟩
    · rfl
    · simp [Ty.muN, Ty.items, Ty.item] at hc

open LeanIntentExamples.WithoutBase in
/-- The pair is met by the script on the label fixed to each input bit, and by no other member: not
by every agent, the table, a constant, the script on the children or the script on their number,
since the two trees have the same children. -/
theorem rose_witnesses :
    WitnessVerdicts rosePair [false, false, false, false, true, false, false] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun b _ => ⟨fun t => if label t = 0 then b else !b, fun xs ys e => ?_, rfl, rfl⟩,
    fun h => ?_, fun h => ?_, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) true trivial).1
  · obtain ⟨a, ⟨v, rfl⟩, h0, h1⟩ := h true trivial
    exact Bool.false_ne_true (h1.symm.trans h0)
  · subst e
    exact Bool.false_ne_true (h true trivial).1
  · subst e
    exact Bool.false_ne_true (h false trivial).1.symm
  · obtain ⟨x, ⟨⟩⟩ := xs
    obtain ⟨y, ⟨⟩⟩ := ys
    show (if label ((HasCode.iso (α := Rose)).inv x) = 0 then b else !b) =
      (if label ((HasCode.iso (α := Rose)).inv y) = 0 then b else !b)
    rw [rose_label x, rose_label y]
    exact congrArg (fun n : Nat => if n = 0 then b else !b) e
  · obtain ⟨a, hk, h0, h1⟩ := h true trivial
    have e : a (.node 0 []) = a (.node 1 []) :=
      hk ((HasCode.iso (α := Rose)).to (.node 0 []), ())
        ((HasCode.iso (α := Rose)).to (.node 1 []), ()) rfl
    exact Bool.false_ne_true (h1.symm.trans (e.symm.trans h0))
  · obtain ⟨a, hk, h0, h1⟩ := h true trivial
    have e : a (.node 0 []) = a (.node 1 []) :=
      hk ((HasCode.iso (α := Rose)).to (.node 0 []), ())
        ((HasCode.iso (α := Rose)).to (.node 1 []), ()) rfl
    exact Bool.false_ne_true (h1.symm.trans (e.symm.trans h0))

open LeanIntentExamples.WithoutBase in
/-- The check reports the script on the label for the pair. -/
theorem rose_label_reported :
    Witness.timed roseLabel ∈
      reported (Rose → Bool) [false, false, false, false, true, false, false] :=
  (mem_reported rose_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ((ArgClock.determines_eq_false_iff _).mp rfl)),
      rose_witnesses.2.2.2.2.1⟩

open LeanIntentExamples.WithoutBase in
/-- A link's one field, `next`, holds all of the link, so its reading determines the argument and the
type alone reads it as what the agent sees; and `Option Link` has two constructors, so no clock part
reaches inside it. So the class of `Link → Bool` holds no script of timed actions. -/
theorem link_clocks : (Covered.sig (W := Link → Bool)).clocks = [] := rfl

/-! ## A clock the class cannot read -/

/-- A `LeanIntent.Clock` inside a list, where no clock part reaches, is refused: no verdict about a
pair of agents of type `List (Clock Nat) → Bool` can be proved. -/
theorem stray_refused (q : Pair (List (Clock Nat) → Bool)) (bs : List Bool) :
    ¬ WitnessVerdicts q bs :=
  not_witnessVerdicts_of_strayClock (by decide) q bs

end LeanIntentExamples.Clocks
