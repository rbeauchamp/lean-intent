module

public import LeanIntent.Explain
public import LeanIntent.Generic
public import LeanIntent.Progress

public section

namespace LeanIntentExamples.DayWorld

open LeanIntent

structure DayWorld (Ctx Act Obs E : Type) where
  length : Nat
  night : Nat → Bool
  cost : Nat → Ctx → Act → E
  sees : Nat → Ctx → Obs

abbrev NightHalf (length start t : Nat) : Prop := (t + start) % length < length / 2

@[expose] def quarter (length start t : Nat) : Nat := (t + start) % length * 4 / length

@[expose] def halves (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"each day has a daytime half and a night half of equal length", fun w =>
    0 < w.length ∧ w.length % 2 = 0 ∧
      ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t⟩

@[expose] def nightCostsMore (Ctx Act Obs E : Type) [LT E] : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"at night every action costs more energy", fun w =>
    ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a⟩

@[expose] def tellsDayFromNight (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always tell day from night", fun w =>
    ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

@[expose] def seesQuarter (Ctx Act Obs E : Type) : Clause (DayWorld Ctx Act Obs E) :=
  ⟨"the agent can always see where in the day it is, at least to a quarter of the day", fun w =>
    ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
      quarter w.length start t = quarter w.length start t'⟩

@[expose] def dayCycle (Ctx Act Obs E : Type) [LT E] : IntentRecord (DayWorld Ctx Act Obs E) where
  shape := .bundle (fun w => w.length) ⟨"night", Nat, Bool, fun w => w.night⟩
    [⟨"cost", Nat × Ctx × Act, E, fun w p => w.cost p.1 p.2.1 p.2.2⟩,
      ⟨"sees", Nat × Ctx, Obs, fun w p => w.sees p.1 p.2⟩]
  dom := []
  props := [halves Ctx Act Obs E, nightCostsMore Ctx Act Obs E, tellsDayFromNight Ctx Act Obs E,
    seesQuarter Ctx Act Obs E]
  vocab := [⟨"night half", Nat × Nat × Nat, fun p => NightHalf p.1 p.2.1 p.2.2⟩,
    ⟨"costs less", E × E, fun p => p.1 < p.2⟩,
    ⟨"in quarter", Nat × Nat × Nat × Nat, fun p => quarter p.1 p.2.1 p.2.2.1 = p.2.2.2⟩]

variable {Ctx Act Obs E : Type} [LT E]

theorem dayCycle_meets {w : DayWorld Ctx Act Obs E} :
    (dayCycle Ctx Act Obs E).Meets w ↔
      (0 < w.length ∧ w.length % 2 = 0 ∧
        ∃ start, ∀ t, w.night t = true ↔ NightHalf w.length start t) ∧
      (∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a) ∧
      (∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t') ∧
      (∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
        quarter w.length start t = quarter w.length start t') := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))))⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

theorem quarter_lt {length : Nat} (hpos : 0 < length) (start t : Nat) :
    quarter length start t < 4 := by
  unfold quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  have := Nat.mod_lt (t + start) hpos
  omega

theorem nightHalf_iff_quarter {length : Nat} (hpos : 0 < length) (heven : length % 2 = 0)
    (start t : Nat) : NightHalf length start t ↔ quarter length start t < 2 := by
  unfold NightHalf quarter
  rw [Nat.div_lt_iff_lt_mul hpos]
  omega

@[expose] def quarterIndex (length start t : Nat) : Fin 4 := ⟨min (quarter length start t) 3, by omega⟩

@[expose] def clockWorld (length start : Nat) (lo hi : E) (sight : Fin 4 → Obs) : DayWorld Ctx Act Obs E where
  length := length
  night t := decide (NightHalf length start t)
  cost t _ _ := if NightHalf length start t then hi else lo
  sees t _ := sight (quarterIndex length start t)

theorem clockWorld_meets {length start : Nat} {lo hi : E} {sight : Fin 4 → Obs}
    (hpos : 0 < length) (heven : length % 2 = 0) (hlt : lo < hi)
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (dayCycle Ctx Act Obs E).Meets (clockWorld length start lo hi sight) := by
  have hq : ∀ t t', sight (quarterIndex length start t) = sight (quarterIndex length start t') →
      quarter length start t = quarter length start t' := by
    intro t t' h
    have h0 := congrArg Fin.val (hsight _ _ h)
    simp only [quarterIndex] at h0
    have h1 := quarter_lt hpos start t
    have h2 := quarter_lt hpos start t'
    omega
  refine dayCycle_meets.mpr ⟨⟨hpos, heven, start, fun t => decide_eq_true_iff⟩,
    fun c a t t' ht ht' => ?_, fun t t' c c' h => ?_, start, fun t t' c c' h => hq t t' h⟩
  · have hn : NightHalf length start t :=
      of_decide_eq_true (show decide (NightHalf length start t) = true from ht)
    have hd : ¬ NightHalf length start t' :=
      of_decide_eq_false (show decide (NightHalf length start t') = false from ht')
    show (if NightHalf length start t' then hi else lo) <
      (if NightHalf length start t then hi else lo)
    rw [ite_eq_right hd, ite_eq_left hn]
    exact hlt
  · show decide (NightHalf length start t) = decide (NightHalf length start t')
    rw [decide_eq_decide, nightHalf_iff_quarter hpos heven, nightHalf_iff_quarter hpos heven,
      hq t t' h]

@[expose] def dayOrNightOnly (lo hi : E) (o₁ o₂ : Obs) : DayWorld Ctx Act Obs E :=
  { clockWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi (fun _ => o₁) with
    sees := fun t _ => if NightHalf 4 0 t then o₁ else o₂ }

theorem dayCycle_refutes_dayOrNightOnly (c : Ctx) (lo hi : E) (o₁ o₂ : Obs) :
    ¬ (dayCycle Ctx Act Obs E).Meets (dayOrNightOnly lo hi o₁ o₂) := by
  intro h
  obtain ⟨-, -, -, s, hs⟩ := dayCycle_meets.mp h
  have n0 : NightHalf 4 0 0 := by decide
  have n1 : NightHalf 4 0 1 := by decide
  have same : (dayOrNightOnly (Ctx := Ctx) (Act := Act) lo hi o₁ o₂).sees 0 c =
      (dayOrNightOnly (Ctx := Ctx) (Act := Act) lo hi o₁ o₂).sees 1 c := by
    show (if NightHalf 4 0 0 then o₁ else o₂) = (if NightHalf 4 0 1 then o₁ else o₂)
    rw [ite_eq_left n0, ite_eq_left n1]
  have := hs 0 1 c c same
  simp only [dayOrNightOnly, clockWorld, quarter] at this
  omega

theorem dayCycle_o2 {lo hi : E} (hlt : lo < hi) (sight : Fin 4 → Obs) :
    O2 (dayCycle Ctx Act Obs E) := by
  refine (o2_correct _).mpr ⟨⟨clockWorld 2 0 lo hi sight, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨(2, 0, 0), show (0 + 0) % 2 < 2 / 2 by decide⟩
  · exact ⟨(lo, hi), hlt⟩
  · exact ⟨(4, 0, 0, 0), show quarter 4 0 0 = 0 by decide⟩

theorem dayCycle_o2Run {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : O2Run (dayCycle Ctx Act Obs E) :=
  o2Run_of_meets (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)

theorem dayCycle_o3 (c : Ctx) (a : Act) {lo hi : E} (hirr : ¬ lo < lo) (sight : Fin 4 → Obs) :
    O3 (dayCycle Ctx Act Obs E) := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [dayCycle, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with length := 0 },
      fun h => Nat.lt_irrefl 0 h.1⟩
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      cost := fun _ _ _ => lo }, fun h => hirr (h c a 0 1 rfl rfl)⟩
  · exact ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      sees := fun _ _ => sight 0 }, fun h => Bool.noConfusion (h 0 1 c c rfl)⟩
  · refine ⟨{ clockWorld (Ctx := Ctx) (Act := Act) 2 0 lo hi sight with
      sees := fun _ _ => sight 0 }, fun ⟨s, hs⟩ => ?_⟩
    have := hs 0 1 c c rfl
    change (0 + s) % 2 * 4 / 2 = (1 + s) % 2 * 4 / 2 at this
    omega

theorem exists_tick {length : Nat} (start k : Nat) (hk : k < length) :
    ∃ t, (t + start) % length = k := by
  refine ⟨k + (length - start % length), ?_⟩
  have hd := Nat.div_add_mod start length
  have hm := Nat.mod_lt start (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
  have e : k + (length - start % length) + start = k + length * (start / length + 1) := by
    rw [Nat.mul_succ]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

omit [LT E] in
theorem exists_night_and_day {w : DayWorld Ctx Act Obs E} (h : (halves Ctx Act Obs E).holds w) :
    ∃ t t', w.night t = true ∧ w.night t' = false := by
  obtain ⟨hpos, heven, s, hs⟩ := h
  obtain ⟨t, ht⟩ := exists_tick (length := w.length) s 0 hpos
  obtain ⟨t', ht'⟩ := exists_tick (length := w.length) s (w.length / 2) (by omega)
  refine ⟨t, t', (hs t).mpr ?_, ?_⟩
  · show (t + s) % w.length < w.length / 2
    omega
  · have : ¬ w.night t' = true := fun hn => by
      have : (t' + s) % w.length < w.length / 2 := (hs t').mp hn
      omega
    simpa using this

theorem dayCycle_o4 (c : Ctx) (a : Act) (e : E) (o : Obs) (hirr : ∀ x : E, ¬ x < x) :
    O4 (dayCycle Ctx Act Obs E) := by
  refine o4_of_idle _ ⟨?_, ?_⟩ ?_
  · rintro ⟨l, n, co, se⟩ ⟨l', n', co', se'⟩ hl h
    have hn := h ⟨"night", Nat, Bool, fun w => w.night⟩ (List.mem_cons_self ..)
    have hc := h ⟨"cost", Nat × Ctx × Act, E, fun w p => w.cost p.1 p.2.1 p.2.2⟩
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hs := h ⟨"sees", Nat × Ctx, Obs, fun w p => w.sees p.1 p.2⟩
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    cases hl
    cases hn
    have hc' : co = co' := funext fun t => funext fun x => funext fun y =>
      congrFun hc (t, x, y)
    have hs' : se = se' := funext fun t => funext fun x => congrFun hs (t, x)
    subst hc' hs'
    rfl
  · intro m hm f
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact ⟨⟨0, f, fun _ _ _ => e, fun _ _ => o⟩, rfl⟩
    · exact ⟨⟨0, fun _ => false, fun t x y => f (t, x, y), fun _ _ => o⟩, rfl⟩
    · exact ⟨⟨0, fun _ => false, fun _ _ _ => e, fun t x => f (t, x)⟩, rfl⟩
  · rintro w ⟨m, hm, hig⟩ hw
    obtain ⟨h1, h2, h3, -⟩ := dayCycle_meets.mp hw
    obtain ⟨t, t', hn, hd⟩ := exists_night_and_day h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · have : w.night t = w.night t' := hig t t'
      rw [hn, hd] at this
      exact Bool.noConfusion this
    · have : w.cost t c a = w.cost t' c a := hig (t, c, a) (t', c, a)
      have hlt := h2 c a t t' hn hd
      rw [this] at hlt
      exact hirr _ hlt
    · have : w.night t = w.night t' := h3 t t' c c (hig (t, c) (t', c))
      rw [hn, hd] at this
      exact Bool.noConfusion this

theorem dayCycle_not_o5_eq {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) : ¬ O5 (dayCycle Ctx Act Obs E) .eq :=
  not_o5_eq (clockWorld_meets (length := 2) (start := 0) (by decide) (by decide) hlt hsight)
    (clockWorld_meets (length := 4) (start := 0) (by decide) (by decide) hlt hsight)
    (fun h => absurd (congrArg DayWorld.length h) (show (2 : Nat) ≠ 4 by decide))

theorem dayCycle_o5_widest : O5 (dayCycle Ctx Act Obs E) .widest := o5_widest _

@[expose] def everyDayAlike : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"every day lasts the same even number of ticks, at least two, placed alike", .entailment,
    fun w => 2 ≤ w.length ∧ w.length % 2 = 0 ∧ ∀ t, w.night (t + w.length) = w.night t⟩

theorem everyDayAlike_holds : (everyDayAlike (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) := by
  intro w hw
  obtain ⟨⟨hpos, heven, s, hs⟩, -, -, -⟩ := dayCycle_meets.mp hw
  refine ⟨by omega, heven, fun t => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [hs, hs]
  show (t + w.length + s) % w.length < _ ↔ (t + s) % w.length < _
  rw [Nat.add_right_comm, Nat.add_mod_right]

@[expose] def nightAlwaysDearer : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"every action costs more at any night moment than at any daytime moment", .entailment,
    fun w => ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a⟩

theorem nightAlwaysDearer_holds : (nightAlwaysDearer (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.1

@[expose] def tellsDayFromNightAlways : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"what the agent sees always tells day from night", .entailment,
    fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'⟩

theorem tellsDayFromNightAlways_holds : (tellsDayFromNightAlways (Ctx := Ctx) (Act := Act)
    (Obs := Obs) (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.2.1

@[expose] def seesQuarterOfDay : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"what the agent sees always tells it which quarter of the day it is in", .entailment,
    fun w => ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' →
      quarter w.length start t = quarter w.length start t'⟩

theorem seesQuarterOfDay_holds : (seesQuarterOfDay (Ctx := Ctx) (Act := Act) (Obs := Obs)
    (E := E)).HoldsOf (dayCycle Ctx Act Obs E) :=
  fun _ hw => (dayCycle_meets.mp hw).2.2.2

@[expose] def longDay : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"a day may last 1000 ticks", .possibility, fun w => w.length = 1000⟩

theorem longDay_holds {lo hi : E} (hlt : lo < hi) {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (longDay (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨clockWorld 1000 0 lo hi sight, clockWorld_meets (by decide) (by decide) hlt hsight, rfl⟩

@[expose] def dayOrNightOnlyWorld (lo hi : E) (o₁ o₂ : Obs) : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"the agent may see only whether it is day or night", .possibility,
    fun w => w = dayOrNightOnly lo hi o₁ o₂⟩

@[expose] def varyingNight (lo hi hi' : E) (sight : Fin 4 → Obs) : DayWorld Ctx Act Obs E :=
  { clockWorld (Ctx := Ctx) (Act := Act) 4 0 lo hi sight with
    cost := fun t _ _ => if NightHalf 4 0 t then (if t % 4 = 0 then hi else hi') else lo }

theorem varyingNight_meets {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j) :
    (dayCycle Ctx Act Obs E).Meets (varyingNight lo hi hi' sight) := by
  have base := dayCycle_meets.mp
    (clockWorld_meets (Ctx := Ctx) (Act := Act) (length := 4) (start := 0) (by decide)
      (by decide) hlt hsight)
  refine dayCycle_meets.mpr ⟨base.1, fun c a t t' ht ht' => ?_, base.2.2.1, base.2.2.2⟩
  have hn : NightHalf 4 0 t := of_decide_eq_true (show decide (NightHalf 4 0 t) = true from ht)
  have hd : ¬ NightHalf 4 0 t' :=
    of_decide_eq_false (show decide (NightHalf 4 0 t') = false from ht')
  show (if NightHalf 4 0 t' then (if t' % 4 = 0 then hi else hi') else lo) <
    (if NightHalf 4 0 t then (if t % 4 = 0 then hi else hi') else lo)
  rw [ite_eq_right hd, ite_eq_left hn]
  split
  · exact hlt
  · exact hlt'

@[expose] def nightCostVaries : Consequence (DayWorld Ctx Act Obs E) :=
  ⟨"an action may cost more at one night moment than at another", .possibility,
    fun w => ∃ c a t t', w.night t = true ∧ w.night t' = true ∧ w.cost t c a ≠ w.cost t' c a⟩

theorem nightCostVaries_holds (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi)
    (hlt' : lo < hi') (hne : hi ≠ hi') {sight : Fin 4 → Obs}
    (hsight : ∀ i j, sight i = sight j → i = j) :
    (nightCostVaries (Ctx := Ctx) (Act := Act) (Obs := Obs) (E := E)).HoldsOf
      (dayCycle Ctx Act Obs E) :=
  ⟨varyingNight lo hi hi' sight, varyingNight_meets hlt hlt' hsight, c, a, 0, 1,
    (by decide : decide (NightHalf 4 0 0) = true), (by decide : decide (NightHalf 4 0 1) = true),
    by
      have h0 : NightHalf 4 0 0 := by decide
      have h1 : NightHalf 4 0 1 := by decide
      have z0 : (0 : Nat) % 4 = 0 := by decide
      have z1 : ¬ (1 : Nat) % 4 = 0 := by decide
      show (if NightHalf 4 0 0 then (if 0 % 4 = 0 then hi else hi') else lo) ≠
        (if NightHalf 4 0 1 then (if 1 % 4 = 0 then hi else hi') else lo)
      rw [ite_eq_left h0, ite_eq_left z0, ite_eq_left h1, ite_eq_right z1]
      exact hne⟩

@[expose] def dayCycleExplained (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    (hne : hi ≠ hi') {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j) :
    Explanation (dayCycle Ctx Act Obs E) where
  shape :=
    { requires := "The subject is a description of a world's day: how many ticks a day lasts, \
        which ticks are night, what each action costs at each tick in each situation, and what \
        the agent sees at each tick in each situation. Time is counted in whole ticks from the \
        start of a run, and one clock serves the whole world."
      rulesOut := "Nothing by itself; it fixes only what the statements below talk about."
      allows := "Any world's situations, actions, sights and energy amounts."
      freedom := "None of its own. It carries no state from one tick to the next, so it is \
        declared a description made of functions, and obligation O4 asks that a world in which \
        any of the three ignores its input fails the record." }
  dom := []
  props := [
    { requires := "A day lasts a fixed, even number of ticks, at least two. The night is one \
        unbroken stretch of exactly half of them and the daytime the other half, and every day \
        is the same."
      rulesOut := "A world with no night or no daytime; a day of an odd number of ticks; a \
        night broken into several stretches; days of different lengths."
      allows := "Any even day length, and a night that starts at any tick of the day."
      freedom := "How long a day is and where in it the night starts." },
    { requires := "For every action and every situation, the action costs strictly more energy \
        at every night tick than at every daytime tick, waiting included."
      rulesOut := "Any action that, in some situation, costs as much or less at some night tick \
        than at some daytime tick."
      allows := "Any amount more at night, and a night cost that changes during the night, as \
        long as it stays above every daytime cost."
      freedom := "How much more the night costs, and whether that extra changes during the \
        night." },
    { requires := "Whatever the agent sees always tells it whether it is day or night."
      rulesOut := "An agent that sees a day moment and a night moment alike."
      allows := "An agent that sees more than that."
      freedom := "How much more it sees." },
    { requires := "Whatever the agent sees always tells it which quarter of the day it is in."
      rulesOut := "An agent that sees only whether it is day or night, in a day longer than \
        two ticks."
      allows := "An agent that sees the quarter, a finer part of the day, or the exact tick."
      freedom := "How much more finely than a quarter the agent sees the time of day." }]
  vocab := [
    { requires := "Tick t is in the night when, counted around a day of the given length from \
        where the night starts, it falls in the first half."
      rulesOut := "Tick 1 in a day of two ticks whose night starts at tick 0."
      allows := "Tick 0 in that day."
      freedom := "None: it is a definition." },
    { requires := "The world's own order on energy amounts."
      rulesOut := "Whatever that order rules out."
      allows := "Whatever that order allows."
      freedom := "None of its own." },
    { requires := "Tick t lies in the given quarter of a day of the given length, counted from \
        the given start."
      rulesOut := "Tick 0 in quarter 1 of a day of four ticks counted from tick 0."
      allows := "Tick 0 in quarter 0 of that day."
      freedom := "None: it is a definition." }]
  restatement := .unconfirmed
  consequences := [
    ⟨everyDayAlike, everyDayAlike_holds,
      { requires := "Every day lasts the same even number of ticks, at least two, and each \
          day's night falls at the same ticks of the day."
        rulesOut := "Days of different lengths."
        allows := "Any one day length shared by all days."
        freedom := "The length itself." }, .unsettled⟩,
    ⟨nightAlwaysDearer, nightAlwaysDearer_holds,
      { requires := "Even the cheapest action costs more at any night moment than at any \
          daytime moment, in the same situation."
        rulesOut := "Any action that is no dearer at some night moment."
        allows := "Any extra amount."
        freedom := "How much more." }, .unsettled⟩,
    ⟨tellsDayFromNightAlways, tellsDayFromNightAlways_holds,
      { requires := "From what it sees, the agent can always tell whether it is day or night."
        rulesOut := "An agent that cannot tell day from night at some moment."
        allows := "An agent that sees more than that."
        freedom := "How much more it sees." }, .unsettled⟩,
    ⟨seesQuarterOfDay, seesQuarterOfDay_holds,
      { requires := "From what it sees, the agent can always tell which quarter of the day it \
          is in."
        rulesOut := "An agent that sees only day or night, in a day longer than two ticks."
        allows := "Seeing a finer part of the day, or the exact tick."
        freedom := "How much finer than a quarter." }, .unsettled⟩,
    ⟨longDay, longDay_holds hlt hsight,
      { requires := "Nothing more: a world whose day lasts 1000 ticks can meet the record."
        rulesOut := "Nothing."
        allows := "Short days and long days alike."
        freedom := "The day's length." }, .unsettled⟩,
    ⟨nightCostVaries, nightCostVaries_holds c a hlt hlt' hne hsight,
      { requires := "Nothing more: an action may cost more at one night moment than at another, \
          as long as every night cost is above every daytime cost."
        rulesOut := "Nothing."
        allows := "A night that is dearer at midnight than at dusk."
        freedom := "Whether the night's extra changes during the night." }, .unsettled⟩]

structure World where
  Ctx : Type
  Act : Type
  Obs : Type
  E : Type
  lt : LT E

@[expose] def family : Family World (fun p => DayWorld p.Ctx p.Act p.Obs p.E) :=
  fun p => @dayCycle p.Ctx p.Act p.Obs p.E p.lt

@[expose] def Good (p : World) : Prop :=
  Nonempty p.Ctx ∧ Nonempty p.Act ∧ (∃ lo hi : p.E, p.lt.lt lo hi) ∧ (∀ x : p.E, ¬ p.lt.lt x x) ∧
    ∃ sight : Fin 4 → p.Obs, ∀ i j, sight i = sight j → i = j

theorem family_o2Run : Family.HoldsWhere family Good fun _ r => O2Run r := by
  rintro p ⟨-, -, ⟨lo, hi, hlt⟩, -, sight, hsight⟩
  exact @dayCycle_o2Run _ _ _ _ p.lt lo hi hlt sight hsight

theorem family_o4 : Family.HoldsWhere family Good fun _ r => O4 r := by
  rintro p ⟨⟨c⟩, ⟨a⟩, ⟨lo, -, -⟩, hirr, sight, -⟩
  exact @dayCycle_o4 _ _ _ _ p.lt c a lo (sight 0) hirr

@[expose] def rep : World := ⟨Unit, Unit, Fin 4, Nat, inferInstance⟩

theorem rep_good : Good rep :=
  ⟨⟨()⟩, ⟨()⟩, ⟨(0 : Nat), (1 : Nat), Nat.zero_lt_one⟩, fun x => Nat.lt_irrefl x, id, fun _ _ h => h⟩

theorem rep_o4 : O4 (family rep) := family_o4.at rep_good

theorem dayCycle_not_o4_without_a_situation : ¬ O4 (dayCycle Empty Unit (Fin 4) Nat) :=
  not_o4_of_idle (w := clockWorld 2 0 0 1 id)
    ⟨⟨"cost", Nat × Empty × Unit, Nat, fun w p => w.cost p.1 p.2.1 p.2.2⟩,
      List.mem_cons_of_mem _ (List.mem_cons_self ..), fun x => nomatch x.2.1⟩
    (clockWorld_meets (by decide) (by decide) (by decide) fun _ _ h => h)

theorem rep_lt : (0 : Nat) < 1 := by decide

theorem rep_lt' : (0 : Nat) < 2 := by decide

theorem rep_ne : (1 : Nat) ≠ 2 := by decide

theorem rep_sight : ∀ i j : Fin 4, id i = id j → i = j := fun _ _ h => h

end LeanIntentExamples.DayWorld
