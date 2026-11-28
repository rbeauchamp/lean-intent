module

public import LeanIntent.Implementation

public section

namespace LeanIntent

universe u

structure Proof where
  {statement : Prop}
  proof : statement

inductive O2RunProof {W : Type u} (r : IntentRecord W) where
  | proved (proof : O2Run r)
  | deferred (reason : String)
      (stated : reason.toList.any (!·.isWhitespace) = true := by decide +kernel)

inductive ComparisonDirection {W : Type u} (r₁ r₂ : IntentRecord W) where
  | implies (proof : ∀ w, r₁.Meets w → r₂.Meets w)
  | separates (witness : W) (proof : r₁.Meets witness ∧ ¬ r₂.Meets witness)
  | unproved (reason : String)
      (stated : reason.toList.any (!·.isWhitespace) = true := by decide +kernel)

@[expose] def ComparisonDirection.isProved {W : Type u} {r₁ r₂ : IntentRecord W} :
    ComparisonDirection r₁ r₂ → Bool
  | .implies _ => true
  | .separates _ _ => true
  | .unproved _ _ => false

inductive BlindComparison {W : Type u} (r : IntentRecord W) where
  | records (blind : IntentRecord W)
      (forward : ComparisonDirection r blind)
      (backward : ComparisonDirection blind r)
      (hasProof : forward.isProved || backward.isProved = true := by rfl)
  | cases (theorems : List Proof)
      (nonempty : theorems ≠ [] := by simp)
      (reason : String)
      (stated : reason.toList.any (!·.isWhitespace) = true := by decide +kernel)

structure Required {W : Type u} (d : Deliverable W) where
  o2 : O2 d.record
  o2Run : O2RunProof d.record
  o3 : O3 d.record
  o4 : O4 d.record
  freedom : Freedom W
  o5 : O5 d.record freedom
  comparison : BlindComparison d.record
  additional : List Proof := []

namespace Required

open Implementation (Constant)

structure DeliverableEntry where
  module : Lean.Name
  name : Lean.Name
  record : Option Lean.Name := none
  deriving @[expose] DecidableEq, Repr

structure ImplEntry where
  module : Lean.Name
  name : Lean.Name
  deliverable : Option Lean.Name := none
  deriving @[expose] DecidableEq, Repr

inductive Cited where
  | thm (c : Constant)
  | other (c : Constant)
  | term
  deriving @[expose] DecidableEq, Repr

inductive O2RunEntry where
  | proved (proof : Cited)
  | deferred (reason : String)
  deriving @[expose] DecidableEq, Repr

inductive DirectionEntry where
  | proved (proof : Cited)
  | unproved (reason : String)
  deriving @[expose] DecidableEq, Repr

inductive ComparisonEntry where
  | records (blind : Option Constant) (forward backward : DirectionEntry)
  | cases (theorems : List Cited) (reason : String)
  deriving @[expose] DecidableEq, Repr

structure Entry where
  name : Lean.Name
  module : Lean.Name
  deliverable : Option Lean.Name
  o2 : Cited
  o2Run : O2RunEntry
  o3 : Cited
  o4 : Cited
  o5 : Cited
  comparison : ComparisonEntry
  additional : List Cited := []
  deriving @[expose] DecidableEq, Repr

@[expose] def O2RunEntry.cited : O2RunEntry → List Cited
  | .proved c => [c]
  | .deferred _ => []

@[expose] def DirectionEntry.cited : DirectionEntry → List Cited
  | .proved c => [c]
  | .unproved _ => []

@[expose] def ComparisonEntry.cited : ComparisonEntry → List Cited
  | .records _ fwd bwd => fwd.cited ++ bwd.cited
  | .cases ts _ => ts

@[expose] def Entry.allCited (r : Entry) : List Cited :=
  [r.o2] ++ r.o2Run.cited ++ [r.o3, r.o4, r.o5] ++ r.comparison.cited ++ r.additional

inductive Finding where
  | deliverableUnbuilt (deliverable module : Lean.Name)
  | implementationUnbuilt (value module : Lean.Name)
  | undeclared (deliverable : Lean.Name)
  | several (deliverable : Lean.Name) (values : List Lean.Name)
  | requiredUnbuilt (value module : Lean.Name)
  | untied (value : Lean.Name)
  | o2RunDeferred (value deliverable : Lean.Name)
  | blindNotConstant (value : Lean.Name)
  | blindUnbuilt (value blind module : Lean.Name)
  | selfComparison (value record : Lean.Name)
  | noComparisonProof (value : Lean.Name)
  | notConstant (value : Lean.Name)
  | notTheorem (value constant module : Lean.Name)
  | unbuilt (value cited module : Lean.Name)
  deriving @[expose] DecidableEq, Repr

@[expose] def entriesFor (rs : List Entry) (d : Lean.Name) : List Entry :=
  rs.filter fun r => r.deliverable == some d

@[expose] def deliverableFindings (built : List Lean.Name) (rs : List Entry) (d : DeliverableEntry) :
    List Finding :=
  let matching := entriesFor rs d.name
  (if built.contains d.module then [] else [.deliverableUnbuilt d.name d.module]) ++
    (if matching.isEmpty then [.undeclared d.name] else []) ++
    (if 2 ≤ matching.length then [.several d.name (matching.map (·.name))] else [])

@[expose] def implementationFindings (built : List Lean.Name) (v : ImplEntry) : List Finding :=
  if built.contains v.module then [] else [.implementationUnbuilt v.name v.module]

@[expose] def citedFindings (built : List Lean.Name) (r : Lean.Name) : Cited → List Finding
  | .thm c => if built.contains c.module then [] else [.unbuilt r c.name c.module]
  | .other c => [.notTheorem r c.name c.module]
  | .term => [.notConstant r]

@[expose] def o2RunFindings (vs : List ImplEntry) (r : Entry) : List Finding :=
  match r.o2Run, r.deliverable with
  | .deferred _, some d =>
    if vs.any (·.deliverable == some d) then [.o2RunDeferred r.name d] else []
  | _, _ => []

@[expose] def comparisonFindings (built : List Lean.Name) (ds : List DeliverableEntry) (r : Entry) :
    List Finding :=
  match r.comparison with
  | .records blind fwd bwd =>
    let blindErrs := match blind with
      | none => [.blindNotConstant r.name]
      | some b =>
        (if built.contains b.module then [] else [.blindUnbuilt r.name b.name b.module]) ++
          if ds.any (fun d => some d.name == r.deliverable && d.record == some b.name) then
            [.selfComparison r.name b.name]
          else []
    let proofErrs :=
      if fwd.cited.isEmpty && bwd.cited.isEmpty then [.noComparisonProof r.name] else []
    blindErrs ++ proofErrs
  | .cases ts _ =>
    if ts.isEmpty then [.noComparisonProof r.name] else []

@[expose] def entryFindings (built : List Lean.Name) (ds : List DeliverableEntry)
    (vs : List ImplEntry) (r : Entry) : List Finding :=
  (if built.contains r.module then [] else [.requiredUnbuilt r.name r.module]) ++
    (if ds.any (some ·.name == r.deliverable) then [] else [.untied r.name]) ++
    o2RunFindings vs r ++
    comparisonFindings built ds r ++
    r.allCited.flatMap (citedFindings built r.name)

@[expose] def declaredFindings (built : List Lean.Name) (ds : List DeliverableEntry)
    (vs : List ImplEntry) (rs : List Entry) : List Finding :=
  ds.flatMap (deliverableFindings built rs) ++ vs.flatMap (implementationFindings built) ++
    rs.flatMap (entryFindings built ds vs)

@[expose] def findings (built : List Lean.Name) (ds : List DeliverableEntry) (vs : List ImplEntry)
    (rs : List Entry) : List Finding :=
  if rs = [] then [] else declaredFindings built ds vs rs

@[expose] def ComparisonEntry.Valid (built : List Lean.Name) (ds : List DeliverableEntry)
    (r : Entry) : ComparisonEntry → Prop
  | .records blind fwd bwd =>
    (∃ b, blind = some b ∧ b.module ∈ built ∧
      ∀ d ∈ ds, r.deliverable = some d.name → d.record ≠ some b.name) ∧
      ((∃ c, fwd = .proved c) ∨ ∃ c, bwd = .proved c)
  | .cases ts _ => ts ≠ []

@[expose] def Located (built : List Lean.Name) (ds : List DeliverableEntry) (vs : List ImplEntry)
    (rs : List Entry) : Prop :=
  rs = [] ∨
    (∀ d ∈ ds, d.module ∈ built) ∧ (∀ v ∈ vs, v.module ∈ built) ∧
      (∀ r ∈ rs, r.module ∈ built) ∧
      (∀ d ∈ ds, rs.countP (fun r => decide (r.deliverable = some d.name)) = 1) ∧
      (∀ r ∈ rs, ∃ d ∈ ds, r.deliverable = some d.name) ∧
      (∀ r ∈ rs, ∀ reason d, r.o2Run = .deferred reason → r.deliverable = some d →
        ∀ v ∈ vs, v.deliverable ≠ some d) ∧
      (∀ r ∈ rs, r.comparison.Valid built ds r) ∧
      ∀ r ∈ rs, ∀ t ∈ r.allCited, ∃ c, t = .thm c ∧ c.module ∈ built

structure Report where
  findings : List Finding
  theorems : List (Lean.Name × Constant)
  deferredO2Run : List (Lean.Name × String)
  unprovedComparisons : List (Lean.Name × String × String)
  casesComparisons : List (Lean.Name × String)
  deriving Repr

@[expose] def theoremsOf (r : Entry) : List (Lean.Name × Constant) :=
  r.allCited.filterMap fun
    | .thm c => some (r.name, c)
    | _ => none

@[expose] def deferredOf (r : Entry) : Option (Lean.Name × String) :=
  match r.o2Run with
  | .deferred reason => some (r.name, reason)
  | .proved _ => none

@[expose] def unprovedOf (r : Entry) : List (Lean.Name × String × String) :=
  match r.comparison with
  | .records _ fwd bwd =>
    (match fwd with | .unproved reason => [(r.name, "forward", reason)] | .proved _ => []) ++
      (match bwd with | .unproved reason => [(r.name, "backward", reason)] | .proved _ => [])
  | .cases _ _ => []

@[expose] def casesOf (r : Entry) : Option (Lean.Name × String) :=
  match r.comparison with
  | .cases _ reason => some (r.name, reason)
  | .records _ _ _ => none

@[expose] def report (built : List Lean.Name) (ds : List DeliverableEntry) (vs : List ImplEntry)
    (rs : List Entry) : Report :=
  ⟨findings built ds vs rs, rs.flatMap theoremsOf, rs.filterMap deferredOf,
    rs.flatMap unprovedOf, rs.filterMap casesOf⟩

section

variable {built : List Lean.Name} {ds : List DeliverableEntry} {vs : List ImplEntry}
  {rs : List Entry}

theorem mem_entriesFor {d : Lean.Name} {r : Entry} :
    r ∈ entriesFor rs d ↔ r ∈ rs ∧ r.deliverable = some d := by
  simp [entriesFor]

theorem length_entriesFor {d : Lean.Name} :
    (entriesFor rs d).length = rs.countP (fun r => decide (r.deliverable = some d)) := by
  simp only [entriesFor, List.countP_eq_length_filter]
  congr 2
  funext r
  exact Bool.eq_iff_iff.mpr (by simp)

theorem deliverableFindings_eq_nil_iff {d : DeliverableEntry} :
    deliverableFindings built rs d = [] ↔
      d.module ∈ built ∧ rs.countP (fun r => decide (r.deliverable = some d.name)) = 1 := by
  unfold deliverableFindings
  rw [← length_entriesFor]
  generalize entriesFor rs d.name = ms
  by_cases hb : d.module ∈ built <;> cases ms with
  | nil => simp [hb]
  | cons _ rest =>
    cases rest with
    | nil => simp [hb]
    | cons _ _ => simp [hb]

theorem implementationFindings_eq_nil_iff {v : ImplEntry} :
    implementationFindings built v = [] ↔ v.module ∈ built := by
  unfold implementationFindings
  by_cases hb : v.module ∈ built <;> simp_all

theorem citedFindings_eq_nil_iff {r : Lean.Name} {t : Cited} :
    citedFindings built r t = [] ↔ ∃ c, t = .thm c ∧ c.module ∈ built := by
  cases t with
  | thm c => by_cases hb : c.module ∈ built <;> simp_all [citedFindings]
  | other c => simp [citedFindings]
  | term => simp [citedFindings]

theorem o2RunFindings_eq_nil_iff {r : Entry} :
    o2RunFindings vs r = [] ↔
      ∀ reason d, r.o2Run = .deferred reason → r.deliverable = some d →
        ∀ v ∈ vs, v.deliverable ≠ some d := by
  unfold o2RunFindings
  cases ho : r.o2Run with
  | proved _ => simp
  | deferred reason =>
    cases hd : r.deliverable with
    | none => simp
    | some d =>
      by_cases hv : ∃ v ∈ vs, v.deliverable = some d
      · have hany : vs.any (·.deliverable == some d) = true := by
          obtain ⟨v, hvm, hvd⟩ := hv
          exact List.any_eq_true.mpr ⟨v, hvm, by simp [hvd]⟩
        simp only [hany, ↓reduceIte, reduceCtorEq, false_iff]
        intro h
        obtain ⟨v, hvm, hvd⟩ := hv
        exact h reason d rfl rfl v hvm hvd
      · have hany : vs.any (·.deliverable == some d) = false :=
          Bool.eq_false_iff.mpr fun h => hv <| by
            obtain ⟨v, hvm, hvd⟩ := List.any_eq_true.mp h
            exact ⟨v, hvm, beq_iff_eq.mp hvd⟩
        simp only [hany, Bool.false_eq_true, ↓reduceIte, true_iff]
        intro _ _ _ heq v hvm hvd
        cases heq
        exact hv ⟨v, hvm, hvd⟩

theorem direction_cited_isEmpty_iff {dir : DirectionEntry} :
    dir.cited.isEmpty = true ↔ ¬ ∃ c, dir = .proved c := by
  cases dir <;> simp [DirectionEntry.cited]

theorem comparisonFindings_eq_nil_iff {r : Entry} :
    comparisonFindings built ds r = [] ↔ r.comparison.Valid built ds r := by
  unfold comparisonFindings ComparisonEntry.Valid
  cases hc : r.comparison with
  | cases ts reason =>
    simp only [List.isEmpty_iff]
    by_cases ht : ts = [] <;> simp [ht]
  | records blind fwd bwd =>
    simp only [List.append_eq_nil_iff]
    have hp : (if (fwd.cited.isEmpty && bwd.cited.isEmpty) = true then [Finding.noComparisonProof r.name]
        else []) = [] ↔ ((∃ c, fwd = .proved c) ∨ ∃ c, bwd = .proved c) := by
      cases fwd <;> cases bwd <;> simp [DirectionEntry.cited]
    rw [hp]
    refine and_congr_left fun _ => ?_
    cases blind with
    | none => simp
    | some b =>
      simp only [List.append_eq_nil_iff, Option.some.injEq, exists_eq_left']
      have hm : (if built.contains b.module then [] else [Finding.blindUnbuilt r.name b.name b.module]) =
          [] ↔ b.module ∈ built := by
        by_cases hb : b.module ∈ built <;> simp_all
      have hs : (if ds.any (fun d => some d.name == r.deliverable && d.record == some b.name) then
          [Finding.selfComparison r.name b.name] else []) = [] ↔
          ∀ d ∈ ds, r.deliverable = some d.name → d.record ≠ some b.name := by
        by_cases hself : ∃ d ∈ ds, r.deliverable = some d.name ∧ d.record = some b.name
        · have hany : ds.any (fun d => some d.name == r.deliverable && d.record == some b.name) = true := by
            obtain ⟨d, hdm, hrd, hdr⟩ := hself
            exact List.any_eq_true.mpr ⟨d, hdm, by simp [hrd, hdr]⟩
          simp only [hany, ↓reduceIte, reduceCtorEq, false_iff]
          intro h
          obtain ⟨d, hdm, hrd, hdr⟩ := hself
          exact h d hdm hrd hdr
        · have hany : ds.any (fun d => some d.name == r.deliverable && d.record == some b.name) = false :=
            Bool.eq_false_iff.mpr fun h => hself <| by
              obtain ⟨d, hdm, ha⟩ := List.any_eq_true.mp h
              simp only [Bool.and_eq_true, beq_iff_eq] at ha
              exact ⟨d, hdm, ha.1.symm, ha.2⟩
          simp only [hany, Bool.false_eq_true, ↓reduceIte, true_iff]
          intro d hdm hrd hdr
          exact hself ⟨d, hdm, hrd, hdr⟩
      rw [hm, hs]

theorem entryFindings_eq_nil_iff {r : Entry} :
    entryFindings built ds vs r = [] ↔
      r.module ∈ built ∧ (∃ d ∈ ds, r.deliverable = some d.name) ∧
        (∀ reason d, r.o2Run = .deferred reason → r.deliverable = some d →
          ∀ v ∈ vs, v.deliverable ≠ some d) ∧
        r.comparison.Valid built ds r ∧
        ∀ t ∈ r.allCited, ∃ c, t = .thm c ∧ c.module ∈ built := by
  unfold entryFindings
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, citedFindings_eq_nil_iff,
    o2RunFindings_eq_nil_iff, comparisonFindings_eq_nil_iff]
  have hm : (if built.contains r.module then [] else [Finding.requiredUnbuilt r.name r.module]) =
      [] ↔ r.module ∈ built := by
    by_cases hb : r.module ∈ built <;> simp_all
  have hd : (if ds.any (some ·.name == r.deliverable) then [] else [Finding.untied r.name]) = [] ↔
      ∃ d ∈ ds, r.deliverable = some d.name := by
    by_cases hd : ∃ d ∈ ds, r.deliverable = some d.name
    · have : ds.any (some ·.name == r.deliverable) = true := by
        obtain ⟨d, hd, he⟩ := hd
        exact List.any_eq_true.mpr ⟨d, hd, by simp [he]⟩
      simp [this, hd]
    · have : ds.any (some ·.name == r.deliverable) = false := by
        refine Bool.eq_false_iff.mpr fun h => hd ?_
        obtain ⟨d, hd, he⟩ := List.any_eq_true.mp h
        exact ⟨d, hd, (beq_iff_eq.mp he).symm⟩
      simp [this, hd]
  rw [hm, hd, and_assoc, and_assoc, and_assoc]

theorem findings_eq_nil_iff : findings built ds vs rs = [] ↔ Located built ds vs rs := by
  unfold findings Located
  by_cases hne : rs = []
  · simp [hne]
  simp only [hne, ↓reduceIte, false_or]
  unfold declaredFindings
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, deliverableFindings_eq_nil_iff,
    implementationFindings_eq_nil_iff, entryFindings_eq_nil_iff]
  constructor
  · rintro ⟨⟨hd, hv⟩, hr⟩
    exact ⟨fun d h => (hd d h).1, hv, fun r h => (hr r h).1, fun d h => (hd d h).2,
      fun r h => (hr r h).2.1, fun r h => (hr r h).2.2.1, fun r h => (hr r h).2.2.2.1,
      fun r h => (hr r h).2.2.2.2⟩
  · rintro ⟨hdb, hv, hrb, hdr, hrd, hdef, hcmp, hrt⟩
    exact ⟨⟨fun d h => ⟨hdb d h, hdr d h⟩, hv⟩,
      fun r h => ⟨hrb r h, hrd r h, hdef r h, hcmp r h, hrt r h⟩⟩

theorem findings_nothing : findings built ds vs [] = [] := by
  simp [findings]

theorem undeclared_mem {d : DeliverableEntry} (hne : rs ≠ []) (hd : d ∈ ds)
    (hr : ∀ r ∈ rs, r.deliverable ≠ some d.name) :
    Finding.undeclared d.name ∈ findings built ds vs rs := by
  have hempty : entriesFor rs d.name = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun r h =>
      let ⟨hrm, hrd⟩ := mem_entriesFor.mp h
      hr r hrm hrd
  unfold findings declaredFindings
  simp only [hne, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨d, hd, by simp [deliverableFindings, hempty]⟩))

theorem several_mem {d : DeliverableEntry} (hd : d ∈ ds)
    (h2 : 2 ≤ (entriesFor rs d.name).length) :
    Finding.several d.name ((entriesFor rs d.name).map (·.name)) ∈ findings built ds vs rs := by
  have hne : rs ≠ [] := by
    intro hnil
    subst hnil
    simp [entriesFor] at h2
  unfold findings declaredFindings
  simp only [hne, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨d, hd, by simp [deliverableFindings, h2]⟩))

theorem requiredUnbuilt_mem {r : Entry} (hr : r ∈ rs) (hb : r.module ∉ built) :
    Finding.requiredUnbuilt r.name r.module ∈ findings built ds vs rs := by
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (by simp [hb]))))

theorem unbuilt_mem {r : Entry} {c : Constant} (hr : r ∈ rs) (ht : .thm c ∈ r.allCited)
    (hb : c.module ∉ built) : Finding.unbuilt r.name c.name c.module ∈ findings built ds vs rs := by
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ht, by simp [citedFindings, hb]⟩)

theorem o2RunDeferred_mem {r : Entry} {reason : String} {d : Lean.Name} {v : ImplEntry}
    (hr : r ∈ rs) (ho : r.o2Run = .deferred reason) (hd : r.deliverable = some d)
    (hv : v ∈ vs) (hvd : v.deliverable = some d) :
    Finding.o2RunDeferred r.name d ∈ findings built ds vs rs := by
  have hany : vs.any (·.deliverable == some d) = true :=
    List.any_eq_true.mpr ⟨v, hv, by simp [hvd]⟩
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (by simp [o2RunFindings, ho, hd, hany])))

theorem selfComparison_mem {r : Entry} {d : DeliverableEntry} {b : Constant}
    {fwd bwd : DirectionEntry} (hr : r ∈ rs) (hd : d ∈ ds) (hrd : r.deliverable = some d.name)
    (hdr : d.record = some b.name) (hc : r.comparison = .records (some b) fwd bwd) :
    Finding.selfComparison r.name b.name ∈ findings built ds vs rs := by
  have hany : ds.any (fun d' => some d'.name == r.deliverable && d'.record == some b.name) = true :=
    List.any_eq_true.mpr ⟨d, hd, by simp [hrd, hdr]⟩
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_left _ (List.mem_append_right _
    (by simp [comparisonFindings, hc, hany]))

theorem blindUnbuilt_mem {r : Entry} {b : Constant} {fwd bwd : DirectionEntry} (hr : r ∈ rs)
    (hc : r.comparison = .records (some b) fwd bwd) (hb : b.module ∉ built) :
    Finding.blindUnbuilt r.name b.name b.module ∈ findings built ds vs rs := by
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_left _ (List.mem_append_right _
    (by simp [comparisonFindings, hc, hb]))

@[expose] def Finding.Holds (built : List Lean.Name) (ds : List DeliverableEntry)
    (vs : List ImplEntry) (rs : List Entry) : Finding → Prop
  | .deliverableUnbuilt d m => (∃ x ∈ ds, x.name = d ∧ x.module = m) ∧ m ∉ built
  | .implementationUnbuilt v m => (∃ x ∈ vs, x.name = v ∧ x.module = m) ∧ m ∉ built
  | .undeclared d => rs ≠ [] ∧ (∃ x ∈ ds, x.name = d) ∧ ∀ r ∈ rs, r.deliverable ≠ some d
  | .several d ns =>
    (∃ x ∈ ds, x.name = d) ∧ ns = (entriesFor rs d).map (·.name) ∧ 2 ≤ ns.length
  | .requiredUnbuilt n m => ∃ r ∈ rs, r.name = n ∧ r.module = m ∧ m ∉ built
  | .untied n => ∃ r ∈ rs, r.name = n ∧ ∀ d ∈ ds, r.deliverable ≠ some d.name
  | .o2RunDeferred n d =>
    ∃ r ∈ rs, r.name = n ∧ r.deliverable = some d ∧ (∃ reason, r.o2Run = .deferred reason) ∧
      ∃ v ∈ vs, v.deliverable = some d
  | .blindNotConstant n =>
    ∃ r ∈ rs, r.name = n ∧ ∃ fwd bwd, r.comparison = .records none fwd bwd
  | .blindUnbuilt n b m =>
    ∃ r ∈ rs, r.name = n ∧ (∃ fwd bwd, r.comparison = .records (some ⟨m, b⟩) fwd bwd) ∧ m ∉ built
  | .selfComparison n recName =>
    ∃ r ∈ rs, r.name = n ∧ (∃ b fwd bwd, r.comparison = .records (some b) fwd bwd ∧ b.name = recName) ∧
      ∃ d ∈ ds, r.deliverable = some d.name ∧ d.record = some recName
  | .noComparisonProof n =>
    ∃ r ∈ rs, r.name = n ∧
      ((∃ blind r1 r2, r.comparison = .records blind (.unproved r1) (.unproved r2)) ∨
        ∃ reason, r.comparison = .cases [] reason)
  | .notConstant n => ∃ r ∈ rs, r.name = n ∧ .term ∈ r.allCited
  | .notTheorem n c m => ∃ r ∈ rs, r.name = n ∧ .other ⟨m, c⟩ ∈ r.allCited
  | .unbuilt n c m => ∃ r ∈ rs, r.name = n ∧ .thm ⟨m, c⟩ ∈ r.allCited ∧ m ∉ built

theorem comparisonFindings_sound {r : Entry} (hr : r ∈ rs) {f : Finding}
    (hf : f ∈ comparisonFindings built ds r) : f.Holds built ds vs rs := by
  unfold comparisonFindings at hf
  cases hc : r.comparison with
  | cases ts reason =>
    rw [hc] at hf
    simp only at hf
    split at hf
    · rename_i ht
      rw [List.mem_singleton.mp hf]
      exact ⟨r, hr, rfl, .inr ⟨reason, List.isEmpty_iff.mp ht ▸ hc⟩⟩
    · exact absurd hf List.not_mem_nil
  | records blind fwd bwd =>
    rw [hc] at hf
    simp only [List.mem_append] at hf
    rcases hf with hf | hf
    · cases blind with
      | none =>
        rw [List.mem_singleton.mp hf]
        exact ⟨r, hr, rfl, fwd, bwd, hc⟩
      | some b =>
        simp only [List.mem_append] at hf
        rcases hf with hf | hf
        · split at hf
          · exact absurd hf List.not_mem_nil
          · rename_i h
            rw [List.mem_singleton.mp hf]
            exact ⟨r, hr, rfl, ⟨fwd, bwd, hc⟩, by simpa using h⟩
        · split at hf
          · rename_i h
            rw [List.mem_singleton.mp hf]
            obtain ⟨d, hdm, ha⟩ := List.any_eq_true.mp h
            simp only [Bool.and_eq_true, beq_iff_eq] at ha
            exact ⟨r, hr, rfl, ⟨b, fwd, bwd, hc, rfl⟩, d, hdm, ha.1.symm, ha.2⟩
          · exact absurd hf List.not_mem_nil
    · split at hf
      · rename_i h
        rw [List.mem_singleton.mp hf]
        simp only [Bool.and_eq_true] at h
        cases fwd with
        | proved _ => simp [DirectionEntry.cited] at h
        | unproved r1 =>
          cases bwd with
          | proved _ => simp [DirectionEntry.cited] at h
          | unproved r2 =>
            exact ⟨r, hr, rfl, .inl ⟨blind, r1, r2, hc⟩⟩
      · exact absurd hf List.not_mem_nil

theorem findings_sound {f : Finding} (hf : f ∈ findings built ds vs rs) :
    f.Holds built ds vs rs := by
  unfold findings at hf
  split at hf
  · exact absurd hf List.not_mem_nil
  rename_i hne
  unfold declaredFindings at hf
  simp only [List.mem_append, List.mem_flatMap] at hf
  rcases hf with (⟨d, hd, hf⟩ | ⟨v, hv, hf⟩) | ⟨r, hr, hf⟩
  · unfold deliverableFindings at hf
    simp only [List.mem_append] at hf
    rcases hf with (hf | hf) | hf <;> split at hf <;> rename_i h <;>
      (try exact absurd hf List.not_mem_nil) <;> rw [List.mem_singleton.mp hf]
    · exact ⟨⟨d, hd, rfl, rfl⟩, by simpa using h⟩
    · refine ⟨hne, ⟨d, hd, rfl⟩, fun r hr hdl => ?_⟩
      have hmem : r ∈ entriesFor rs d.name := mem_entriesFor.mpr ⟨hr, hdl⟩
      rw [List.isEmpty_iff.mp h] at hmem
      exact List.not_mem_nil hmem
    · exact ⟨⟨d, hd, rfl⟩, rfl, by simpa using h⟩
  · unfold implementationFindings at hf
    split at hf <;> rename_i h
    · exact absurd hf List.not_mem_nil
    · rw [List.mem_singleton.mp hf]
      exact ⟨⟨v, hv, rfl, rfl⟩, by simpa using h⟩
  · unfold entryFindings at hf
    simp only [List.mem_append] at hf
    rcases hf with (((hf | hf) | hf) | hf) | hf
    · split at hf <;> rename_i h
      · exact absurd hf List.not_mem_nil
      · rw [List.mem_singleton.mp hf]
        exact ⟨r, hr, rfl, rfl, by simpa using h⟩
    · split at hf <;> rename_i h
      · exact absurd hf List.not_mem_nil
      · rw [List.mem_singleton.mp hf]
        refine ⟨r, hr, rfl, fun d hd he => h ?_⟩
        exact List.any_eq_true.mpr ⟨d, hd, by simp [he]⟩
    · unfold o2RunFindings at hf
      cases ho : r.o2Run with
      | proved _ => simp [ho] at hf
      | deferred reason =>
        cases hd : r.deliverable with
        | none => simp [ho, hd] at hf
        | some d =>
          simp only [ho, hd] at hf
          split at hf
          · rename_i h
            rw [List.mem_singleton.mp hf]
            obtain ⟨v, hvm, hvd⟩ := List.any_eq_true.mp h
            exact ⟨r, hr, rfl, hd, ⟨reason, ho⟩, v, hvm, beq_iff_eq.mp hvd⟩
          · exact absurd hf List.not_mem_nil
    · exact comparisonFindings_sound hr hf
    · obtain ⟨t, ht, hf⟩ := List.mem_flatMap.mp hf
      cases t with
      | thm c =>
        simp only [citedFindings] at hf
        split at hf <;> rename_i h
        · exact absurd hf List.not_mem_nil
        · rw [List.mem_singleton.mp hf]
          exact ⟨r, hr, rfl, ht, by simpa using h⟩
      | other c =>
        rw [List.mem_singleton.mp hf]
        exact ⟨r, hr, rfl, ht⟩
      | term =>
        rw [List.mem_singleton.mp hf]
        exact ⟨r, hr, rfl, ht⟩

theorem mem_theorems {n : Lean.Name} {c : Constant} :
    (n, c) ∈ (report built ds vs rs).theorems ↔ ∃ r ∈ rs, r.name = n ∧ .thm c ∈ r.allCited := by
  simp only [report, theoremsOf, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, t, ht, he⟩
    cases t <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨r, hr, rfl, ht⟩
  · rintro ⟨r, hr, rfl, ht⟩
    exact ⟨r, hr, .thm c, ht, rfl⟩

theorem mem_deferredO2Run {n : Lean.Name} {reason : String} :
    (n, reason) ∈ (report built ds vs rs).deferredO2Run ↔
      ∃ r ∈ rs, r.name = n ∧ r.o2Run = .deferred reason := by
  simp only [report, deferredOf, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, he⟩
    cases ho : r.o2Run with
    | proved _ => simp [ho] at he
    | deferred rsn =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨r, hr, rfl, ho⟩
  · rintro ⟨r, hr, rfl, ho⟩
    exact ⟨r, hr, by simp [ho]⟩

theorem mem_unprovedComparisons {n : Lean.Name} {dir reason : String} :
    (n, dir, reason) ∈ (report built ds vs rs).unprovedComparisons ↔
      ∃ r ∈ rs, r.name = n ∧ ∃ blind fwd bwd, r.comparison = .records blind fwd bwd ∧
        ((dir = "forward" ∧ fwd = .unproved reason) ∨
          (dir = "backward" ∧ bwd = .unproved reason)) := by
  simp only [report, unprovedOf, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, he⟩
    cases hc : r.comparison with
    | cases _ _ => simp [hc] at he
    | records blind fwd bwd =>
      simp only [hc, List.mem_append] at he
      rcases he with he | he
      · cases fwd with
        | proved _ => exact absurd he List.not_mem_nil
        | unproved rsn =>
          simp only [List.mem_singleton, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ⟨r, hr, rfl, blind, .unproved reason, bwd, hc, .inl ⟨rfl, rfl⟩⟩
      · cases bwd with
        | proved _ => exact absurd he List.not_mem_nil
        | unproved rsn =>
          simp only [List.mem_singleton, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ⟨r, hr, rfl, blind, fwd, .unproved reason, hc, .inr ⟨rfl, rfl⟩⟩
  · rintro ⟨r, hr, rfl, blind, fwd, bwd, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨r, hr, by simp [hc]⟩
    · exact ⟨r, hr, by simp [hc]⟩

theorem mem_casesComparisons {n : Lean.Name} {reason : String} :
    (n, reason) ∈ (report built ds vs rs).casesComparisons ↔
      ∃ r ∈ rs, r.name = n ∧ ∃ ts, r.comparison = .cases ts reason := by
  simp only [report, casesOf, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, he⟩
    cases hc : r.comparison with
    | records _ _ _ => simp [hc] at he
    | cases ts rsn =>
      simp only [hc, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨r, hr, rfl, ts, hc⟩
  · rintro ⟨r, hr, rfl, ts, hc⟩
    exact ⟨r, hr, by simp [hc]⟩

end

@[expose] def Finding.message : Finding → String
  | .deliverableUnbuilt d m =>
    s!"the deliverable {d}, which holds the proof that its record keeps its answers, is declared in \
      the module {m}, which the project's build does not list: declare it in a module of a library \
      the proof check builds, or, where another package declares it and the proof check builds \
      {m}, give {m} among the modules the build lists"
  | .implementationUnbuilt v m =>
    s!"{v}, which holds the proof that an implementation meets its deliverable's record, is \
      declared in the module {m}, which the project's build does not list: declare it in a module \
      of a library the proof check builds, or, where another package declares it and the proof \
      check builds {m}, give {m} among the modules the build lists"
  | .undeclared d =>
    s!"the deliverable {d} has no value of `LeanIntent.Required` naming its obligations and blind \
      comparison, and a value of `LeanIntent.Required` is read, the project's own or another \
      package's, so every deliverable read must be named: declare one value of \
      `LeanIntent.Required {d}`, in a module of a library the proof check builds, carrying its \
      typed `O2`, `O2Run`, `O3`, `O4`, `O5`, blind comparison, and any additional required theorems"
  | .several d ns =>
    s!"the deliverable {d} has several values of `LeanIntent.Required` ({ns}): combine them into \
      one value of `LeanIntent.Required {d}` so one declaration carries its obligations, blind \
      comparison, and additional theorems"
  | .requiredUnbuilt n m =>
    s!"{n}, which names theorems the intent-first procedure requires, is declared in the module \
      {m}, which the project's build does not list, so the proof check does not check its proofs: \
      declare it in a module of a library the proof check builds, or, where another package \
      declares it and the proof check builds {m}, give {m} among the modules the build lists, \
      after which the project must name each of its own deliverables too"
  | .untied n =>
    s!"the type of {n} names no deliverable of the project: declare it as \
      `LeanIntent.Required d` for a deliverable `d` that a module read declares"
  | .o2RunDeferred n d =>
    s!"{n} leaves `O2Run` deferred for the deliverable {d}, which already has an implementation: \
      prove `O2Run` (for example via `LeanIntent.Implementation.o2Run` on its `Implementation` \
      value) and replace `.deferred` with `.proved`"
  | .blindNotConstant n =>
    s!"{n} gives a blind formalization record that is not a declared constant: declare the blind \
      record in a module the proof check builds and pass its constant name"
  | .blindUnbuilt n b m =>
    s!"{n} compares against the blind record {b}, declared in the module {m}, which the project's \
      build does not list: move {b} into a module of a library the proof check builds, or have \
      that library build {m}"
  | .selfComparison n recName =>
    s!"{n} compares the deliverable's record {recName} against itself: pass the independent blind \
      formalization record declared in its own module instead"
  | .noComparisonProof n =>
    s!"{n} provides no comparison theorem against the blind formalization: prove at least one \
      comparison direction (`.implies` or `.separates`) or list at least one case verdict theorem \
      under `.cases`"
  | .notConstant n =>
    s!"{n} gives a proof that is not a theorem's name: declare each required proof as a `theorem` \
      and pass its name (or `⟨name⟩` / `⟨@name⟩` in lists)"
  | .notTheorem n c m =>
    s!"{n} names {c}, which the module {m}, recorded as declaring it, does not declare as a \
      theorem: declare what it proves with `theorem`, and name that; a theorem of that name in \
      another module does not stand for it, so prove it in {m} or remove the declaration there"
  | .unbuilt n c m =>
    s!"{n} names the theorem {c}, declared in the module {m}, which the project's build does not \
      list, so the proof check does not check it: move {c} into a module of a library the proof \
      check builds, or have that library build {m}, for example by naming it in the library's \
      globs, or, where another package declares {c} and the proof check builds {m}, give {m} \
      among the modules the build lists"

end Required

end LeanIntent
