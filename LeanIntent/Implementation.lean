module

public import LeanIntent.Confirmation
public import LeanIntent.Progress

public section

namespace LeanIntent

universe u

structure Implementation {W : Type u} (d : Deliverable W) where
  subject : W
  meets : d.record.Meets subject

structure AwaitingImplementation {W : Type u} (d : Deliverable W) where
  reason : String
  stated : reason.toList.any (!·.isWhitespace) = true := by decide +kernel

namespace Implementation

section

variable {W : Type u} {d : Deliverable W}

theorem dom (v : Implementation d) : d.record.Dom v.subject := v.meets.1

theorem props (v : Implementation d) : d.record.Props v.subject := v.meets.2

theorem fulfilled (v : Implementation d) : d.record.Fulfilled v.subject := fun _ => v.meets.2

theorem exists_iff {w : W} : (∃ v : Implementation d, v.subject = w) ↔ d.record.Meets w :=
  ⟨fun ⟨v, h⟩ => h ▸ v.meets, fun h => ⟨⟨w, h⟩, rfl⟩⟩

theorem o2Run (v : Implementation d) : O2Run d.record :=
  o2Run_of_meets v.meets

theorem not_idle (v : Implementation d) (h4 : O4 d.record) : ¬ d.record.shape.Idle v.subject :=
  fun hi => not_o4_of_idle hi v.meets h4

theorem relates (v : Implementation d) {R : Freedom W} (h5 : O5 d.record R) {w : W}
    (hw : d.record.Meets w) : R.relates d.record v.subject w :=
  h5.relates v.meets hw

end

structure Constant where
  module : Lean.Name
  name : Lean.Name
  deriving @[expose] DecidableEq, Repr

structure Entry where
  name : Lean.Name
  deliverable : Option Lean.Name
  subject : Option Constant
  deriving @[expose] DecidableEq, Repr

structure AwaitingEntry where
  name : Lean.Name
  deliverable : Option Lean.Name
  reason : String
  deriving @[expose] DecidableEq, Repr

inductive Finding where
  | noDeliverable
  | unimplemented (deliverable : Lean.Name)
  | several (deliverable : Lean.Name) (values : List Lean.Name)
  | untied (value : Lean.Name)
  | notConstant (value : Lean.Name)
  | severalAwaiting (deliverable : Lean.Name) (values : List Lean.Name)
  | awaitingImplemented (deliverable : Lean.Name) (values : List Lean.Name)
  | untiedAwaiting (value : Lean.Name)
  deriving @[expose] DecidableEq, Repr

@[expose] def implementing (vs : List Entry) (d : Lean.Name) : List Entry :=
  vs.filter fun v => v.deliverable == some d

@[expose] def awaitingFor (as : List AwaitingEntry) (d : Lean.Name) : List AwaitingEntry :=
  as.filter fun a => a.deliverable == some d

@[expose] def tiesTo (ds : List Lean.Name) : Option Lean.Name → Bool
  | some d => ds.contains d
  | none => false

@[expose] def Entry.ties (ds : List Lean.Name) (v : Entry) : Bool := tiesTo ds v.deliverable

@[expose] def AwaitingEntry.ties (ds : List Lean.Name) (a : AwaitingEntry) : Bool := tiesTo ds a.deliverable

@[expose] def deliverableFindings (vs : List Entry) (as : List AwaitingEntry) (d : Lean.Name) :
    List Finding :=
  (if (implementing vs d).isEmpty && (awaitingFor as d).isEmpty then [.unimplemented d] else []) ++
    (if 2 ≤ (implementing vs d).length then
      [.several d ((implementing vs d).map (·.name))] else []) ++
    (if 2 ≤ (awaitingFor as d).length then
      [.severalAwaiting d ((awaitingFor as d).map (·.name))] else []) ++
    (if !(implementing vs d).isEmpty && !(awaitingFor as d).isEmpty then
      [.awaitingImplemented d ((awaitingFor as d).map (·.name))] else [])

@[expose] def entryFindings (ds : List Lean.Name) (v : Entry) : List Finding :=
  (if v.ties ds then [] else [.untied v.name]) ++
    (if v.subject.isSome then [] else [.notConstant v.name])

@[expose] def awaitingFindings (ds : List Lean.Name) (a : AwaitingEntry) : List Finding :=
  if a.ties ds then [] else [.untiedAwaiting a.name]

@[expose] def findings (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : List Finding :=
  (if ds.isEmpty then [.noDeliverable] else []) ++ ds.flatMap (deliverableFindings vs as) ++
    vs.flatMap (entryFindings ds) ++ as.flatMap (awaitingFindings ds)

@[expose] def Accounted (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : Prop :=
  ds ≠ [] ∧
    (∀ d ∈ ds,
      (vs.countP (fun v => decide (v.deliverable = some d)) = 1 ∧
          as.countP (fun a => decide (a.deliverable = some d)) = 0) ∨
        (vs.countP (fun v => decide (v.deliverable = some d)) = 0 ∧
          as.countP (fun a => decide (a.deliverable = some d)) = 1)) ∧
    (∀ v ∈ vs, (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true) ∧
    ∀ a ∈ as, ∃ d ∈ ds, a.deliverable = some d

@[expose] def implementationOf (vs : List Entry) (d : Lean.Name) : Option (Lean.Name × Constant) :=
  match implementing vs d with
  | [v] => v.subject.map fun c => (v.name, c)
  | _ => none

@[expose] def awaitedOf (as : List AwaitingEntry) (d : Lean.Name) : Option (Lean.Name × String) :=
  match awaitingFor as d with
  | [a] => some (a.name, a.reason)
  | _ => none

structure Report where
  findings : List Finding
  implementations : List (Lean.Name × Lean.Name × Constant)
  awaiting : List (Lean.Name × Lean.Name × String)
  deriving Repr

@[expose] def report (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : Report :=
  ⟨findings ds vs as, ds.filterMap fun d => (implementationOf vs d).map fun x => (d, x),
    ds.filterMap fun d => (awaitedOf as d).map fun x => (d, x)⟩

section

variable {ds : List Lean.Name} {vs : List Entry} {as : List AwaitingEntry}

theorem mem_implementing {d : Lean.Name} {v : Entry} :
    v ∈ implementing vs d ↔ v ∈ vs ∧ v.deliverable = some d := by
  simp [implementing]

theorem mem_awaitingFor {d : Lean.Name} {a : AwaitingEntry} :
    a ∈ awaitingFor as d ↔ a ∈ as ∧ a.deliverable = some d := by
  simp [awaitingFor]

theorem tiesTo_iff {o : Option Lean.Name} : tiesTo ds o = true ↔ ∃ d ∈ ds, o = some d := by
  cases o <;> simp [tiesTo]

theorem ties_iff {v : Entry} : v.ties ds = true ↔ ∃ d ∈ ds, v.deliverable = some d := tiesTo_iff

theorem AwaitingEntry.ties_iff {a : AwaitingEntry} :
    a.ties ds = true ↔ ∃ d ∈ ds, a.deliverable = some d := tiesTo_iff

theorem length_implementing {d : Lean.Name} :
    (implementing vs d).length = vs.countP (fun v => decide (v.deliverable = some d)) := by
  simp only [implementing, List.countP_eq_length_filter]
  congr 2
  funext v
  exact Bool.eq_iff_iff.mpr (by simp)

theorem length_awaitingFor {d : Lean.Name} :
    (awaitingFor as d).length = as.countP (fun a => decide (a.deliverable = some d)) := by
  simp only [awaitingFor, List.countP_eq_length_filter]
  congr 2
  funext a
  exact Bool.eq_iff_iff.mpr (by simp)

theorem deliverableFindings_eq_nil_iff {d : Lean.Name} :
    deliverableFindings vs as d = [] ↔
      (implementing vs d).length + (awaitingFor as d).length = 1 := by
  unfold deliverableFindings
  generalize implementing vs d = is
  generalize awaitingFor as d = ws
  rcases is with _ | ⟨_, _ | ⟨_, is⟩⟩ <;> rcases ws with _ | ⟨_, _ | ⟨_, ws⟩⟩ <;> simp <;> omega

theorem entryFindings_eq_nil_iff {v : Entry} :
    entryFindings ds v = [] ↔ (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true := by
  unfold entryFindings
  rw [← ties_iff]
  cases v.ties ds <;> cases v.subject.isSome <;> simp

theorem awaitingFindings_eq_nil_iff {a : AwaitingEntry} :
    awaitingFindings ds a = [] ↔ ∃ d ∈ ds, a.deliverable = some d := by
  unfold awaitingFindings
  rw [← AwaitingEntry.ties_iff]
  cases a.ties ds <;> simp

theorem findings_eq_nil_iff : findings ds vs as = [] ↔ Accounted ds vs as := by
  have one : ∀ i w : Nat, i + w = 1 ↔ (i = 1 ∧ w = 0) ∨ (i = 0 ∧ w = 1) := by omega
  unfold findings Accounted
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, deliverableFindings_eq_nil_iff,
    length_implementing, length_awaitingFor, one, entryFindings_eq_nil_iff,
    awaitingFindings_eq_nil_iff]
  cases ds <;> simp [and_assoc]

theorem replace_nil_iff {as₁ as₂ : List AwaitingEntry} {a : AwaitingEntry} {v : Entry}
    (hd : v.deliverable = a.deliverable) (hs : v.subject.isSome = true) :
    findings ds (v :: vs) (as₁ ++ as₂) = [] ↔ findings ds vs (as₁ ++ a :: as₂) = [] := by
  rw [findings_eq_nil_iff, findings_eq_nil_iff]
  unfold Accounted
  simp only [List.countP_cons, List.countP_append, hd, decide_eq_true_eq, List.mem_cons,
    List.mem_append, forall_eq_or_imp, hs, and_true]
  constructor
  · rintro ⟨hne, hcount, ⟨hvt, hv⟩, ha⟩
    refine ⟨hne, fun d hd' => ?_, hv, fun b hb => ?_⟩
    · have := hcount d hd'
      by_cases h : a.deliverable = some d <;> simp only [h, ite_true, ite_false] at this ⊢ <;> omega
    · rcases hb with hb | rfl | hb
      · exact ha b (.inl hb)
      · exact hvt
      · exact ha b (.inr hb)
  · rintro ⟨hne, hcount, hv, ha⟩
    refine ⟨hne, fun d hd' => ?_, ⟨ha a (.inr (.inl rfl)), hv⟩, fun b hb => ?_⟩
    · have := hcount d hd'
      by_cases h : a.deliverable = some d <;> simp only [h, ite_true, ite_false] at this ⊢ <;> omega
    · rcases hb with hb | hb
      · exact ha b (.inl hb)
      · exact ha b (.inr (.inr hb))

@[expose] def Finding.Holds (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) :
    Finding → Prop
  | .noDeliverable => ds = []
  | .unimplemented d =>
    d ∈ ds ∧ (∀ v ∈ vs, v.deliverable ≠ some d) ∧ ∀ a ∈ as, a.deliverable ≠ some d
  | .several d ns => d ∈ ds ∧ ns = (implementing vs d).map (·.name) ∧ 2 ≤ ns.length
  | .untied n => ∃ v ∈ vs, v.name = n ∧ ∀ d ∈ ds, v.deliverable ≠ some d
  | .notConstant n => ∃ v ∈ vs, v.name = n ∧ v.subject = none
  | .severalAwaiting d ns => d ∈ ds ∧ ns = (awaitingFor as d).map (·.name) ∧ 2 ≤ ns.length
  | .awaitingImplemented d ns =>
    d ∈ ds ∧ (∃ v ∈ vs, v.deliverable = some d) ∧ ns = (awaitingFor as d).map (·.name) ∧ ns ≠ []
  | .untiedAwaiting n => ∃ a ∈ as, a.name = n ∧ ∀ d ∈ ds, a.deliverable ≠ some d

theorem deliverableFindings_sound {d : Lean.Name} (hd : d ∈ ds) {f : Finding}
    (hf : f ∈ deliverableFindings vs as d) : f.Holds ds vs as := by
  unfold deliverableFindings at hf
  simp only [List.mem_append] at hf
  rcases hf with ((hf | hf) | hf) | hf <;> split at hf <;> rename_i h <;>
    (try exact absurd hf List.not_mem_nil) <;> rw [List.mem_singleton.mp hf]
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    refine ⟨hd, fun v hv hvd => ?_, fun a ha had => ?_⟩
    · have : v ∈ implementing vs d := mem_implementing.mpr ⟨hv, hvd⟩
      rw [h.1] at this
      exact List.not_mem_nil this
    · have : a ∈ awaitingFor as d := mem_awaitingFor.mpr ⟨ha, had⟩
      rw [h.2] at this
      exact List.not_mem_nil this
  · exact ⟨hd, rfl, by simpa using h⟩
  · exact ⟨hd, rfl, by simpa using h⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h.1
    exact ⟨hd, ⟨v, mem_implementing.mp hv⟩, rfl, by simpa using h.2⟩

theorem entryFindings_sound {v : Entry} (hv : v ∈ vs) {f : Finding} (hf : f ∈ entryFindings ds v) :
    f.Holds ds vs as := by
  unfold entryFindings at hf
  rcases List.mem_append.mp hf with hf | hf
  · split at hf
    · exact absurd hf List.not_mem_nil
    · rename_i hn
      rw [List.mem_singleton.mp hf]
      refine ⟨v, hv, rfl, fun d hd hvd => hn ?_⟩
      exact ties_iff.mpr ⟨d, hd, hvd⟩
  · split at hf
    · exact absurd hf List.not_mem_nil
    · rename_i hn
      rw [List.mem_singleton.mp hf]
      exact ⟨v, hv, rfl, by simpa using hn⟩

theorem awaitingFindings_sound {a : AwaitingEntry} (ha : a ∈ as) {f : Finding}
    (hf : f ∈ awaitingFindings ds a) : f.Holds ds vs as := by
  unfold awaitingFindings at hf
  split at hf
  · exact absurd hf List.not_mem_nil
  · rename_i hn
    rw [List.mem_singleton.mp hf]
    exact ⟨a, ha, rfl, fun d hd had => hn (AwaitingEntry.ties_iff.mpr ⟨d, hd, had⟩)⟩

theorem findings_sound {f : Finding} (hf : f ∈ findings ds vs as) : f.Holds ds vs as := by
  unfold findings at hf
  simp only [List.mem_append, List.mem_flatMap] at hf
  rcases hf with ((hf | ⟨d, hd, hf⟩) | ⟨v, hv, hf⟩) | ⟨a, ha, hf⟩
  · split at hf
    · rename_i h
      rw [List.mem_singleton.mp hf]
      exact List.isEmpty_iff.mp h
    · exact absurd hf List.not_mem_nil
  · exact deliverableFindings_sound hd hf
  · exact entryFindings_sound hv hf
  · exact awaitingFindings_sound ha hf

theorem implementationOf_eq_some_iff {d n : Lean.Name} {c : Constant} :
    implementationOf vs d = some (n, c) ↔
      ∃ v, implementing vs d = [v] ∧ v.name = n ∧ v.subject = some c := by
  unfold implementationOf
  match implementing vs d with
  | [] => simp
  | [v] =>
    simp only [Option.map_eq_some_iff, Prod.mk.injEq, List.cons.injEq, and_true, exists_eq_left']
    constructor
    · rintro ⟨a, hs, rfl, rfl⟩
      exact ⟨rfl, hs⟩
    · rintro ⟨rfl, hs⟩
      exact ⟨c, hs, rfl, rfl⟩
  | _ :: _ :: _ => simp

theorem mem_implementations {d n : Lean.Name} {c : Constant} :
    (d, n, c) ∈ (report ds vs as).implementations ↔
      d ∈ ds ∧ ∃ v, implementing vs d = [v] ∧ v.name = n ∧ v.subject = some c := by
  rw [← implementationOf_eq_some_iff]
  simp only [report, List.mem_filterMap]
  constructor
  · rintro ⟨d', hd', hx⟩
    cases h : implementationOf vs d' with
    | none => simp [h] at hx
    | some x =>
      simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hd', h⟩
  · rintro ⟨hd, h⟩
    exact ⟨d, hd, by simp [h]⟩

theorem awaitedOf_eq_some_iff {d n : Lean.Name} {r : String} :
    awaitedOf as d = some (n, r) ↔ ∃ a, awaitingFor as d = [a] ∧ a.name = n ∧ a.reason = r := by
  unfold awaitedOf
  match awaitingFor as d with
  | [] => simp
  | [a] => simp [eq_comm]
  | _ :: _ :: _ => simp

theorem mem_awaiting {d n : Lean.Name} {r : String} :
    (d, n, r) ∈ (report ds vs as).awaiting ↔
      d ∈ ds ∧ ∃ a, awaitingFor as d = [a] ∧ a.name = n ∧ a.reason = r := by
  rw [← awaitedOf_eq_some_iff]
  simp only [report, List.mem_filterMap]
  constructor
  · rintro ⟨d', hd', hx⟩
    cases h : awaitedOf as d' with
    | none => simp [h] at hx
    | some x =>
      simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hd', h⟩
  · rintro ⟨hd, h⟩
    exact ⟨d, hd, by simp [h]⟩

theorem listed_of_nil (h : findings ds vs as = []) {d : Lean.Name} (hd : d ∈ ds) :
    (∃ v c, v ∈ vs ∧ v.deliverable = some d ∧ v.subject = some c ∧
        (d, v.name, c) ∈ (report ds vs as).implementations ∧ ∀ a ∈ as, a.deliverable ≠ some d) ∨
      ∃ a ∈ as, a.deliverable = some d ∧ (d, a.name, a.reason) ∈ (report ds vs as).awaiting ∧
        ∀ v ∈ vs, v.deliverable ≠ some d := by
  unfold findings at h
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  have hone := deliverableFindings_eq_nil_iff.mp (h.1.1.2 d hd)
  have hall := fun v hv => entryFindings_eq_nil_iff.mp (h.1.2 v hv)
  rcases Nat.add_eq_one_iff.mp hone with ⟨hi, hw⟩ | ⟨hi, hw⟩
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hw
    have hmem : a ∈ awaitingFor as d := by rw [ha]; exact List.mem_singleton_self a
    obtain ⟨has, had⟩ := mem_awaitingFor.mp hmem
    refine .inr ⟨a, has, had, mem_awaiting.mpr ⟨hd, a, ha, rfl, rfl⟩, ?_⟩
    intro v hv hvd
    have : v ∈ implementing vs d := mem_implementing.mpr ⟨hv, hvd⟩
    rw [List.length_eq_zero_iff.mp hi] at this
    exact List.not_mem_nil this
  · obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hi
    have hmem : v ∈ implementing vs d := by rw [hv]; exact List.mem_singleton_self v
    obtain ⟨hvs, hvd⟩ := mem_implementing.mp hmem
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hall v hvs).2
    refine .inl ⟨v, c, hvs, hvd, hc, mem_implementations.mpr ⟨hd, v, hv, rfl, hc⟩, ?_⟩
    intro a ha had
    have : a ∈ awaitingFor as d := mem_awaitingFor.mpr ⟨ha, had⟩
    rw [List.length_eq_zero_iff.mp hw] at this
    exact List.not_mem_nil this

end

end Implementation

end LeanIntent
