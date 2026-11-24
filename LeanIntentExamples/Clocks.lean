module

public import LeanIntentExamples.TrivialWitnesses
public import LeanIntentExamples.WithoutBase
import all Init.Prelude

public section

namespace LeanIntentExamples.Clocks

open LeanIntent LeanIntentExamples.TrivialWitnesses

abbrev Historied := List Bool → Bool

@[expose] def history (v : Course) (t : Fin 2) : List Bool :=
  if t.val = 0 then [v.sight 0] else [v.sight 0, v.sight 1]

@[expose] def FollowsH (a : Historied) (v : Course) : Prop := ∀ t, a (history v t) = v.need t

@[expose] def followsReadableH : Clause Historied :=
  ⟨"follows every readable course", fun a => ∀ v, Readable v → FollowsH a v⟩

@[expose] def historied : IntentRecord Historied where
  shape := .function _ _
  dom := []
  props := [followsReadableH]
  vocab := [⟨"Readable", Course, Readable⟩,
    ⟨"Follows", Historied × Course, fun p => FollowsH p.1 p.2⟩]

@[expose] def perCourseH : Pair Historied := ⟨Course, Readable, fun v a => FollowsH a v⟩

theorem perCourseH_pairOf : historied.PairOf followsReadableH perCourseH :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

@[expose] def scriptFor (v : Course) : Historied := fun h => if h.length = 1 then v.need 0 else v.need 1

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

theorem perCourseH_script_reported :
    Witness.timed ⟨.code (.list .bool), .here (.self _), .count (.length .bool)⟩ ∈
      reported Historied [false, false, false, false, true] :=
  (mem_reported perCourseH_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ⟨([true], ()), ([false], ()),
      fun h => Bool.noConfusion (List.cons.inj (congrArg Prod.fst h)).1, rfl⟩),
      perCourseH_witnesses.2.2.2.2.1⟩

theorem wholeCourseH_witnesses :
    WitnessVerdicts (Pair.whole historied followsReadableH) [false, false, false, false, false] := by
  have hNoScript : ¬ (Witness.timed ⟨.code (.list .bool), .here (.self _), .count (.length .bool)⟩ :
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

theorem lastSeen_follows : followsReadableH.holds fun h => h.getLastD false := by
  intro v hv t
  match t with
  | ⟨0, _⟩ => exact (hv 0).symm
  | ⟨1, _⟩ => exact (hv 1).symm

structure Glance where
  time : Fin 2
  sight : Bool
  deriving LeanIntent.HasCode

abbrev Glancer := Glance → Bool

@[expose] def perCourseG : Pair Glancer :=
  ⟨Course, Readable, fun v a => ∀ t, a ⟨t, v.sight t⟩ = v.need t⟩

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

structure TickView where
  time : UInt64
  sight : Bool
  deriving LeanIntent.HasCode

@[expose] def tickPair : Pair (TickView → Bool) :=
  ⟨Bool, fun _ => True, fun b a => a ⟨0, false⟩ = b ∧ a ⟨1, false⟩ = !b⟩

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

theorem tick_script_reported :
    Witness.timed ⟨_, .here (.fields rfl (.step (.decl _ _ _) (.head _ (.self _)))), .value⟩ ∈
      reported (TickView → Bool) [false, false, false, false, false, true, false] :=
  (mem_reported tick_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ⟨(((0 : UInt64), false, ()), ()), (((0 : UInt64), true, ()), ()),
      fun h => Bool.noConfusion (congrArg (fun p => p.1.2.1) h), rfl⟩),
      tick_witnesses.2.2.2.2.2.1⟩

abbrev Policy := Clock Nat → Bool

@[expose] def perSchedule : Pair Policy := ⟨Fin 2 → Bool, fun _ => True, fun s a => ∀ t, a ⟨t.val⟩ = s t⟩

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

open LeanIntentExamples.WithoutBase in
@[expose] def label : Rose → Nat
  | .node n _ => n

open LeanIntentExamples.WithoutBase in
@[expose] def rosePair : Pair (Rose → Bool) :=
  ⟨Bool, fun _ => True, fun b a => a (.node 0 []) = b ∧ a (.node 1 []) = !b⟩

open LeanIntentExamples.WithoutBase in
abbrev roseLabel : ArgClock (Covered.sig (W := Rose → Bool)).args :=
  ⟨_, .here (.fields rfl (.step (.decl _ _ _) (.step (.muAt rfl)
    (.data (by decide) rfl (.head _ (.self _)))))), .value⟩

open LeanIntentExamples.WithoutBase in
theorem rose_label (x : (HasCode.code Rose).denote) :
    label ((HasCode.iso (α := Rose)).inv x) = roseLabel.read (x, ()) := by
  cases x with
  | node c d k =>
    rcases c with ⟨_ | _, hc⟩
    · rfl
    · simp [Ty.muN, Ty.items, Ty.item] at hc

open LeanIntentExamples.WithoutBase in
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
theorem rose_label_reported :
    Witness.timed roseLabel ∈
      reported (Rose → Bool) [false, false, false, false, true, false, false] :=
  (mem_reported rose_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ((ArgClock.determines_eq_false_iff _).mp rfl)),
      rose_witnesses.2.2.2.2.1⟩

open LeanIntentExamples.WithoutBase in
theorem link_clocks : (Covered.sig (W := Link → Bool)).clocks = [] := by rfl

inductive History where
  | nil
  | cons (head : Bool) (tail : History)
  deriving LeanIntent.HasCode

@[expose] def historyPair : Pair (History → Bool) :=
  ⟨Bool, fun _ => True, fun b a => a .nil = b ∧ a (.cons false .nil) = !b⟩

abbrev historyLength : ArgClock (Covered.sig (W := History → Bool)).args :=
  ⟨.code (HasCode.code History), .here (.self _), .count (.treeLength rfl)⟩

theorem history_witnesses :
    WitnessVerdicts historyPair [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    fun b _ => ⟨Witness.script historyLength fun n => if n = 0 then b else !b,
      (Witness.timedBy_iff_script _ _).mpr ⟨_, rfl⟩, rfl, rfl⟩, trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) true trivial).1
  · obtain ⟨a, ⟨v, rfl⟩, h0, h1⟩ := h true trivial
    exact Bool.false_ne_true (h1.symm.trans h0)
  · subst e
    exact Bool.false_ne_true (h true trivial).1
  · subst e
    exact Bool.false_ne_true (h false trivial).1.symm

theorem history_length_reported :
    Witness.timed historyLength ∈ reported (History → Bool) [false, false, false, false, true] :=
  (mem_reported history_witnesses _).mpr
    ⟨Witness.timed_mem (.inl ((ArgClock.determines_eq_false_iff _).mp rfl)),
      history_witnesses.2.2.2.2.1⟩

theorem stray_refused (q : Pair (List (Clock Nat) → Bool)) (bs : List Bool) :
    ¬ WitnessVerdicts q bs :=
  not_witnessVerdicts_of_strayClock (by decide) q bs

end LeanIntentExamples.Clocks
