module

public import LeanIntent.Implementation

public section

namespace LeanIntent

universe u

structure Proof where
  {statement : Prop}
  proof : statement

structure Required {W : Type u} (d : Deliverable W) where
  theorems : List Proof
  nonempty : theorems ≠ [] := by simp

namespace Required

open Implementation (Constant)

inductive Cited where
  | thm (c : Constant)
  | other (c : Constant)
  | term
  deriving @[expose] DecidableEq, Repr

structure Entry where
  name : Lean.Name
  module : Lean.Name
  deliverable : Option Lean.Name
  theorems : List Cited
  deriving @[expose] DecidableEq, Repr

inductive Finding where
  | deliverableUnbuilt (deliverable module : Lean.Name)
  | implementationUnbuilt (value module : Lean.Name)
  | undeclared (deliverable : Lean.Name)
  | requiredUnbuilt (value module : Lean.Name)
  | untied (value : Lean.Name)
  | notConstant (value : Lean.Name)
  | notTheorem (value constant module : Lean.Name)
  | unbuilt (value cited module : Lean.Name)
  deriving @[expose] DecidableEq, Repr

@[expose] def deliverableFindings (built : List Lean.Name) (rs : List Entry) (d : Constant) :
    List Finding :=
  (if built.contains d.module then [] else [.deliverableUnbuilt d.name d.module]) ++
    if rs.any (·.deliverable == some d.name) then [] else [.undeclared d.name]

@[expose] def implementationFindings (built : List Lean.Name) (v : Constant) : List Finding :=
  if built.contains v.module then [] else [.implementationUnbuilt v.name v.module]

@[expose] def citedFindings (built : List Lean.Name) (r : Lean.Name) : Cited → List Finding
  | .thm c => if built.contains c.module then [] else [.unbuilt r c.name c.module]
  | .other c => [.notTheorem r c.name c.module]
  | .term => [.notConstant r]

@[expose] def entryFindings (built : List Lean.Name) (ds : List Constant) (r : Entry) :
    List Finding :=
  (if built.contains r.module then [] else [.requiredUnbuilt r.name r.module]) ++
    (if ds.any (some ·.name == r.deliverable) then [] else [.untied r.name]) ++
    r.theorems.flatMap (citedFindings built r.name)

@[expose] def declaredFindings (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) :
    List Finding :=
  ds.flatMap (deliverableFindings built rs) ++ vs.flatMap (implementationFindings built) ++
    rs.flatMap (entryFindings built ds)

@[expose] def findings (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) :
    List Finding :=
  if rs = [] then [] else declaredFindings built ds vs rs

@[expose] def Located (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) : Prop :=
  rs = [] ∨
    (∀ d ∈ ds, d.module ∈ built) ∧ (∀ v ∈ vs, v.module ∈ built) ∧
      (∀ r ∈ rs, r.module ∈ built) ∧
      (∀ d ∈ ds, ∃ r ∈ rs, r.deliverable = some d.name) ∧
      (∀ r ∈ rs, ∃ d ∈ ds, r.deliverable = some d.name) ∧
      ∀ r ∈ rs, ∀ t ∈ r.theorems, ∃ c, t = .thm c ∧ c.module ∈ built

structure Report where
  findings : List Finding
  theorems : List (Lean.Name × Constant)
  deriving Repr

@[expose] def theoremsOf (r : Entry) : List (Lean.Name × Constant) :=
  r.theorems.filterMap fun
    | .thm c => some (r.name, c)
    | _ => none

@[expose] def report (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) : Report :=
  ⟨findings built ds vs rs, rs.flatMap theoremsOf⟩

section

variable {built : List Lean.Name} {ds vs : List Constant} {rs : List Entry}

theorem deliverableFindings_eq_nil_iff {d : Constant} :
    deliverableFindings built rs d = [] ↔
      d.module ∈ built ∧ ∃ r ∈ rs, r.deliverable = some d.name := by
  unfold deliverableFindings
  by_cases hb : d.module ∈ built <;> by_cases hr : ∃ r ∈ rs, r.deliverable = some d.name <;>
    simp_all

theorem implementationFindings_eq_nil_iff {v : Constant} :
    implementationFindings built v = [] ↔ v.module ∈ built := by
  unfold implementationFindings
  by_cases hb : v.module ∈ built <;> simp_all

theorem citedFindings_eq_nil_iff {r : Lean.Name} {t : Cited} :
    citedFindings built r t = [] ↔ ∃ c, t = .thm c ∧ c.module ∈ built := by
  cases t with
  | thm c => by_cases hb : c.module ∈ built <;> simp_all [citedFindings]
  | other c => simp [citedFindings]
  | term => simp [citedFindings]

theorem entryFindings_eq_nil_iff {r : Entry} :
    entryFindings built ds r = [] ↔
      r.module ∈ built ∧ (∃ d ∈ ds, r.deliverable = some d.name) ∧
        ∀ t ∈ r.theorems, ∃ c, t = .thm c ∧ c.module ∈ built := by
  unfold entryFindings
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, citedFindings_eq_nil_iff]
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
  rw [hm, hd, and_assoc]

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
      fun r h => (hr r h).2.1, fun r h => (hr r h).2.2⟩
  · rintro ⟨hdb, hv, hrb, hdr, hrd, hrt⟩
    exact ⟨⟨fun d h => ⟨hdb d h, hdr d h⟩, hv⟩, fun r h => ⟨hrb r h, hrd r h, hrt r h⟩⟩

theorem findings_nothing : findings built ds vs [] = [] := by
  simp [findings]

theorem undeclared_mem {d : Constant} (hne : rs ≠ []) (hd : d ∈ ds)
    (hr : ∀ r ∈ rs, r.deliverable ≠ some d.name) :
    Finding.undeclared d.name ∈ findings built ds vs rs := by
  have : rs.any (·.deliverable == some d.name) = false :=
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨r, hr', he⟩ := List.any_eq_true.mp h
      exact hr r hr' (beq_iff_eq.mp he)
  unfold findings declaredFindings
  simp only [hne, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨d, hd, by simp [deliverableFindings, this]⟩))

theorem requiredUnbuilt_mem {r : Entry} (hr : r ∈ rs) (hb : r.module ∉ built) :
    Finding.requiredUnbuilt r.name r.module ∈ findings built ds vs rs := by
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_left _ (List.mem_append_left _ (by simp [hb]))

theorem unbuilt_mem {r : Entry} {c : Constant} (hr : r ∈ rs) (ht : .thm c ∈ r.theorems)
    (hb : c.module ∉ built) : Finding.unbuilt r.name c.name c.module ∈ findings built ds vs rs := by
  unfold findings declaredFindings
  simp only [List.ne_nil_of_mem hr, ↓reduceIte]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ht, by simp [citedFindings, hb]⟩)

@[expose] def Finding.Holds (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) :
    Finding → Prop
  | .deliverableUnbuilt d m => ⟨m, d⟩ ∈ ds ∧ m ∉ built
  | .implementationUnbuilt v m => ⟨m, v⟩ ∈ vs ∧ m ∉ built
  | .undeclared d => rs ≠ [] ∧ (∃ c ∈ ds, c.name = d) ∧ ∀ r ∈ rs, r.deliverable ≠ some d
  | .requiredUnbuilt n m => ∃ r ∈ rs, r.name = n ∧ r.module = m ∧ m ∉ built
  | .untied n => ∃ r ∈ rs, r.name = n ∧ ∀ d ∈ ds, r.deliverable ≠ some d.name
  | .notConstant n => ∃ r ∈ rs, r.name = n ∧ .term ∈ r.theorems
  | .notTheorem n c m => ∃ r ∈ rs, r.name = n ∧ .other ⟨m, c⟩ ∈ r.theorems
  | .unbuilt n c m => ∃ r ∈ rs, r.name = n ∧ .thm ⟨m, c⟩ ∈ r.theorems ∧ m ∉ built

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
    rcases List.mem_append.mp hf with hf | hf <;> split at hf <;> rename_i h <;>
      (try exact absurd hf List.not_mem_nil) <;> rw [List.mem_singleton.mp hf]
    · exact ⟨hd, by simpa using h⟩
    · refine ⟨hne, ⟨d, hd, rfl⟩, fun r hr he => h ?_⟩
      exact List.any_eq_true.mpr ⟨r, hr, by simp [he]⟩
  · unfold implementationFindings at hf
    split at hf <;> rename_i h
    · exact absurd hf List.not_mem_nil
    · rw [List.mem_singleton.mp hf]
      exact ⟨hv, by simpa using h⟩
  · unfold entryFindings at hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · split at hf <;> rename_i h
        · exact absurd hf List.not_mem_nil
        · rw [List.mem_singleton.mp hf]
          exact ⟨r, hr, rfl, rfl, by simpa using h⟩
      · split at hf <;> rename_i h
        · exact absurd hf List.not_mem_nil
        · rw [List.mem_singleton.mp hf]
          refine ⟨r, hr, rfl, fun d hd he => h ?_⟩
          exact List.any_eq_true.mpr ⟨d, hd, by simp [he]⟩
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
    (n, c) ∈ (report built ds vs rs).theorems ↔ ∃ r ∈ rs, r.name = n ∧ .thm c ∈ r.theorems := by
  simp only [report, theoremsOf, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, t, ht, he⟩
    cases t <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨r, hr, rfl, ht⟩
  · rintro ⟨r, hr, rfl, ht⟩
    exact ⟨r, hr, .thm c, ht, rfl⟩

end

@[expose] def Finding.message : Finding → String
  | .deliverableUnbuilt d m =>
    s!"the deliverable {d}, which holds the proof that its record keeps its answers, is declared in \
      the module {m}, which the project's build does not list: declare it in a module of a library \
      the proof check builds, or, where another package declares it and the proof check builds \
      {m}, give {m} among the modules the build lists"
  | .implementationUnbuilt v m =>
    s!"{v}, which holds the proof that an implementation fulfils its deliverable's record, is \
      declared in the module {m}, which the project's build does not list: declare it in a module \
      of a library the proof check builds, or, where another package declares it and the proof \
      check builds {m}, give {m} among the modules the build lists"
  | .undeclared d =>
    s!"the deliverable {d} names none of the theorems the intent-first procedure requires of it, \
      and a value of `LeanIntent.Required` is read, the project's own or another package's, so \
      every deliverable read must be named: declare a value of `LeanIntent.Required {d}`, in a \
      module of a library the proof check builds, that lists each of them by its name, its \
      obligations and the theorems comparing it with the blind formalization among them"
  | .requiredUnbuilt n m =>
    s!"{n}, which names theorems the intent-first procedure requires, is declared in the module \
      {m}, which the project's build does not list, so the proof check does not check that what \
      it lists are proofs: declare it in a module of a library the proof check builds, or, where \
      another package declares it and the proof check builds {m}, give {m} among the modules the \
      build lists, after which the project must name each of its own deliverables too"
  | .untied n =>
    s!"the type of {n} names no deliverable of the project: declare it as \
      `LeanIntent.Required d` for a deliverable `d` that a module read declares"
  | .notConstant n =>
    s!"{n} lists a proof that is not a theorem's name: list each theorem as `⟨name⟩`, or \
      `⟨@name⟩` where its first arguments are implicit"
  | .notTheorem n c m =>
    s!"{n} lists {c}, which the module {m}, recorded as declaring it, does not declare as a \
      theorem: declare what it proves with `theorem`, and list that; a theorem of that name in \
      another module does not stand for it, so prove it in {m} or remove the declaration there"
  | .unbuilt n c m =>
    s!"{n} lists the theorem {c}, declared in the module {m}, which the project's build does not \
      list, so the proof check does not check it: move {c} into a module of a library the proof \
      check builds, or have that library build {m}, for example by naming it in the library's \
      globs, or, where another package declares {c} and the proof check builds {m}, give {m} \
      among the modules the build lists"

end Required

end LeanIntent
