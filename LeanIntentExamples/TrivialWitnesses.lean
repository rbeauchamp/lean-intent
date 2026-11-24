module

public import LeanIntentExamples.Pairs
public import LeanIntent.TrivialWitnesses

public section

namespace LeanIntentExamples.TrivialWitnesses

open LeanIntent LeanIntentExamples.Pairs

theorem blind_iff_constant (a : Agent) : Blind a ↔ Witness.Constant a :=
  ⟨fun h => ⟨a false, funext fun s => h s false⟩, fun ⟨_, e⟩ _ _ => by subst e; rfl⟩

theorem perWorld_witnesses : WitnessVerdicts perWorld [false, true, false, false, true] := by
  refine ⟨fun h => ?_, ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun v hv => hv.symm⟩,
    trivial⟩
  · exact Bool.false_ne_true (h (fun _ => false) ⟨true, true⟩ rfl)
  · exact ((Witness.oPair_constant_iff perWorld).mp
      (perWorld_blind.mono fun a h => (blind_iff_constant a).mp h)).2
  · subst e
    exact Bool.false_ne_true (h ⟨true, true⟩ rfl)
  · subst e
    exact Bool.false_ne_true (h ⟨false, false⟩ rfl).symm

theorem perWorld_table_reported :
    Witness.table ∈ reported Agent [false, true, false, false, true] :=
  (mem_reported perWorld_witnesses _).mpr ⟨Witness.table_mem, perWorld_witnesses.2.1⟩

theorem whole_witnesses :
    WitnessVerdicts (Pair.whole agent reachesLegible) [false, false, false, false, true] := by
  refine ⟨fun h => ?_, fun h => ?_, fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_,
    ⟨_, rfl, fun _ _ _ _ hv => hv.symm⟩, trivial⟩
  · exact Bool.false_ne_true
      (h (fun _ => false) PUnit.unit trivial (fun _ hd => nomatch hd) ⟨true, true⟩ rfl)
  · exact whole_not_blind
      (OPair.mono ((Witness.oPair_constant_iff _).mpr ⟨⟨PUnit.unit, trivial⟩, h⟩)
        fun a ha => (blind_iff_constant a).mpr ha)
  · subst e
    exact Bool.false_ne_true (h PUnit.unit trivial (fun _ hd => nomatch hd) ⟨true, true⟩ rfl)
  · subst e
    exact Bool.false_ne_true (h PUnit.unit trivial (fun _ hd => nomatch hd) ⟨false, false⟩ rfl).symm

structure Course where
  sight : Fin 2 → Bool
  need : Fin 2 → Bool

abbrev Clocked := Fin 2 → Bool → Bool

@[expose] def Follows (a : Clocked) (v : Course) : Prop := ∀ t, a t (v.sight t) = v.need t

@[expose] def Readable (v : Course) : Prop := ∀ t, v.need t = v.sight t

@[expose] def followsReadable : Clause Clocked :=
  ⟨"follows every readable course", fun a => ∀ v, Readable v → Follows a v⟩

@[expose] def clocked : IntentRecord Clocked where
  shape := .function _ _
  dom := []
  props := [followsReadable]
  vocab := [⟨"Readable", Course, Readable⟩, ⟨"Follows", Clocked × Course, fun p => Follows p.1 p.2⟩]

@[expose] def perCourse : Pair Clocked := ⟨Course, Readable, fun v a => Follows a v⟩

theorem perCourse_pairOf : clocked.PairOf followsReadable perCourse :=
  ⟨List.mem_singleton_self _, fun _ =>
    ⟨fun h v hv => h (fun _ hd => nomatch hd) v hv, fun h _ => h⟩⟩

@[expose] def zigzag : Course := ⟨fun t => t.val == 0, fun t => t.val == 0⟩

@[expose] def allTrue : Course := ⟨fun _ => true, fun _ => true⟩

@[expose] def allFalse : Course := ⟨fun _ => false, fun _ => false⟩

theorem zigzag_not_constant {a : Clocked} (h : Witness.Constant a) : ¬ Follows a zigzag := by
  obtain ⟨v, rfl⟩ := h
  intro hf
  exact Bool.false_ne_true ((hf 1).symm.trans (hf 0))

theorem perCourse_witnesses :
    WitnessVerdicts perCourse [false, false, true, true, false, false, true, true, true] := by
  refine ⟨fun h => ?_, fun h => ?_,
    fun _ hv => ⟨fun _ s => s, fun _ _ => rfl, fun t => (hv t).symm⟩,
    fun v _ => ⟨fun t _ => v.need t, fun _ _ _ => rfl, fun _ => rfl⟩,
    fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun _ hv t => (hv t).symm⟩,
    fun v _ => ⟨fun t _ => v.need t, fun _ _ e => congrArg v.need e, fun _ => rfl⟩,
    fun _ hv => ⟨fun _ s => s, fun _ _ e => e, fun t => (hv t).symm⟩,
    trivial⟩
  · exact Bool.false_ne_true (h (fun _ _ => false) allTrue (fun _ => rfl) 0)
  · obtain ⟨a, ha, hf⟩ := h zigzag fun _ => rfl
    exact zigzag_not_constant ha hf
  · subst e
    exact Bool.false_ne_true (h allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true (h allFalse (fun _ => rfl) 0).symm

theorem timed_not_whole {a : Clocked} (e : a 0 true = a 0 false)
    (h : ∀ v, Readable v → Follows a v) : False := by
  have ht : a 0 true = true := h allTrue (fun _ => rfl) 0
  have hf : a 0 false = false := h allFalse (fun _ => rfl) 0
  exact Bool.false_ne_true (hf.symm.trans (e.symm.trans ht))

theorem wholeCourse_witnesses :
    WitnessVerdicts (Pair.whole clocked followsReadable)
      [false, false, true, false, false, false, true, false, true] := by
  have hNoTimed : ¬ (Witness.blind ⟨1, by decide⟩ : Witness (Covered.sig (W := Clocked))).Meets
      (Pair.whole clocked followsReadable) := fun h => by
    obtain ⟨a, hb, hf⟩ := h PUnit.unit trivial
    exact timed_not_whole (hb (0 : Fin 2) true false) (hf fun _ hd => nomatch hd)
  have hNoScript : ¬ (Witness.timed ⟨_, .here (.self _), .value⟩ :
      Witness (Covered.sig (W := Clocked))).Meets (Pair.whole clocked followsReadable) := fun h => by
    obtain ⟨a, hk, hf⟩ := h PUnit.unit trivial
    exact timed_not_whole (hk ((0 : Fin 2), true, ()) ((0 : Fin 2), false, ()) rfl)
      (hf fun _ hd => nomatch hd)
  refine ⟨fun h => ?_, fun h => hNoTimed (Witness.blind_meets_of_table _ h),
    fun _ _ => ⟨fun _ s => s, fun _ _ => rfl, fun _ v hv t => (hv t).symm⟩, hNoTimed,
    fun ⟨_, e, h⟩ => ?_, fun ⟨_, e, h⟩ => ?_, ⟨_, rfl, fun _ _ _ v hv t => (hv t).symm⟩,
    hNoScript, fun _ _ => ⟨fun _ s => s, fun _ _ e => e, fun _ v hv t => (hv t).symm⟩, trivial⟩
  · exact Bool.false_ne_true
      (h (fun _ _ => false) PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allTrue (fun _ => rfl) 0)
  · subst e
    exact Bool.false_ne_true
      (h PUnit.unit trivial (fun _ hd => nomatch hd) allFalse (fun _ => rfl) 0).symm

end LeanIntentExamples.TrivialWitnesses
