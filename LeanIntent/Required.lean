import LeanIntent.Implementation

/-!
# The theorems the intent-first procedure requires, in modules the proof check builds

The intent-first procedure has a project prove theorems it then relies on: the record's adequacy
obligations, the comparison between a second model's blind formalization and the record, the
answers a deliverable keeps, and the proof that its implementation fulfils the record. A theorem is
checked only where the project's proof check, the check it runs on every change to establish its
proofs, builds the module that declares it: a theorem in a file that nothing builds, or that is not
committed, is checked by nothing, however finished the step that asked for it reads. This module
adds the value that names those theorems and the decision that refuses a project whose theorems lie
outside the modules its build lists.

* **A project names the theorems it relies on.** A value of `Required d` lists, for the deliverable
  `d`, theorems the procedure requires of it, each by its proof (`Proof`), which a project writes as
  the theorem's name; Lean checks, when the value is declared, that each entry is a proof, resolving
  each name to a constant the value's module declares or imports. A deliverable may have several
  such values, one in each module that holds some of its theorems; each lists at least one theorem
  (`Required.nonempty`), so a value naming nothing is no value of the type.
* **The answers a deliverable keeps, and the proof that an implementation fulfils its record, are
  read where they are held.** A deliverable (`LeanIntent.Deliverable`) holds the proof that its
  record keeps its answers, and a value of `LeanIntent.Implementation d` the proof that its subject
  fulfils the record; each proof is checked where the module that declares the value is built.
* **The decision** (`findings`) reads the modules the project's build lists (`built`), the
  deliverables and the values of `Implementation d` by the module that declares each, and, for each
  value of `Required d`, the deliverable its type names and what it lists, as
  `LeanIntent.Required.Read` computes them from the build. It finds nothing exactly when every
  deliverable and every implementation value is declared in a module the build lists, every
  deliverable has a value of `Required` naming it, every such value names a deliverable of the
  project, and everything such a value lists is a theorem declared in a module the build lists
  (`findings_eq_nil_iff`, whose statement `Located` shares no definition with the decision). Each
  finding holds and names what it is about (`findings_sound`), and `Finding.message` says, for each,
  what the project declares or moves to clear it.
* **A project that declares nothing keeps its verdict.** With no deliverable, no implementation and
  no value of `Required`, the decision finds nothing, whatever the build lists (`findings_nothing`).

The decisions this module makes, each on the owner's behalf:

* **Every deliverable names its theorems.** A deliverable no value of `Required` names is refused,
  naming it and saying what to declare: the procedure requires its obligations and its comparison
  before the deliverable is confirmed, and a theorem nothing names is a theorem no check finds.
* **A theorem is listed as a constant Lean records as a theorem, and nothing else.** A term that is
  not a constant, such as an application of a theorem to arguments, names no declaration whose
  module can be read, and is refused naming the value; a constant that is not a theorem, such as a
  definition or an axiom, is refused naming it.
* **Where a theorem lies is the module Lean's environment records as declaring it**, compared with
  the module names the build lists, never the theorem's name: a name a file the build does not list
  also declares cannot pass for the theorem, since one environment holds one declaration of a name.

What this module does not establish: that a listed theorem states what the procedure asks of it,
which review reads; that its proof rests only on axioms the project accepts, which a project's own
gate audits, as it audits its other proofs; that Lean's kernel checked it, which the option
`debug.skipKernelTC` skips; that every theorem the procedure requires is listed, since a theorem no
value lists is not read; and that the module names given as the build's are those the project's
proof check builds, which the gate reads from Lake (`LeanIntent.Required.Read.queryModules`).
-/

namespace LeanIntent

universe u

/-- **A theorem a project proves**, by its proof: a proof of the proposition `statement`. A project
writes one as `⟨name⟩`, or `⟨@name⟩` where the theorem's first arguments are implicit, so that the
proof it holds is the theorem's constant. -/
structure Proof where
  /-- The proposition the theorem states. -/
  {statement : Prop}
  /-- Its proof. -/
  proof : statement

/-- **Theorems the intent-first procedure requires of the deliverable `d`**, each by its proof: its
obligations, its comparison with a second model's blind formalization, and every other theorem the
procedure has the project prove about it. A project declares at least one for each deliverable, in a
module its proof check builds that imports the deliverable and the theorems it lists. -/
structure Required {W : Type u} (d : Deliverable W) where
  /-- The theorems, each by its proof. -/
  theorems : List Proof
  /-- The list names at least one theorem. The default proof has `simp` prove it of a list written
  out. -/
  nonempty : theorems ≠ [] := by simp

namespace Required

open Implementation (Constant)

/-! ## The decision -/

/-- What a value of `Required d` lists, one entry of its list, as the build shows it. -/
inductive Cited where
  /-- A constant Lean's environment records as a theorem, by the module that declares it and its
  name. -/
  | thm (c : Constant)
  /-- A constant that is not a theorem, by its module and its name. -/
  | other (c : Constant)
  /-- A term that is not a constant. -/
  | term
  deriving DecidableEq, Repr

/-- A value of a `Required` type that a project declares, as the build shows it. -/
structure Entry where
  /-- The constant of that type. -/
  name : Lean.Name
  /-- The deliverable its type names, where that is a constant. -/
  deliverable : Option Lean.Name
  /-- What it lists. -/
  theorems : List Cited
  deriving DecidableEq, Repr

/-- What is wrong with where a project's required theorems lie. -/
inductive Finding where
  /-- This deliverable, which holds the proof that its record keeps its answers, is declared in this
  module, which the build does not list. -/
  | deliverableUnbuilt (deliverable module : Lean.Name)
  /-- This value, which holds the proof that its subject fulfils its deliverable's record, is
  declared in this module, which the build does not list. -/
  | implementationUnbuilt (value module : Lean.Name)
  /-- No value of `Required` names this deliverable. -/
  | undeclared (deliverable : Lean.Name)
  /-- The type of this value of `Required` names no deliverable of the project. -/
  | untied (value : Lean.Name)
  /-- This value of `Required` lists a term that is not a constant. -/
  | notConstant (value : Lean.Name)
  /-- This value of `Required` lists this constant, which is not a theorem. -/
  | notTheorem (value constant : Lean.Name)
  /-- This value of `Required` lists this theorem, declared in this module, which the build does
  not list. -/
  | unbuilt (value cited module : Lean.Name)
  deriving DecidableEq, Repr

/-- What is wrong with the deliverable `d`, given the modules `built` and the entries `rs`. -/
def deliverableFindings (built : List Lean.Name) (rs : List Entry) (d : Constant) : List Finding :=
  (if built.contains d.module then [] else [.deliverableUnbuilt d.name d.module]) ++
    if rs.any (·.deliverable == some d.name) then [] else [.undeclared d.name]

/-- What is wrong with the value `v` recording an implementation, given the modules `built`. -/
def implementationFindings (built : List Lean.Name) (v : Constant) : List Finding :=
  if built.contains v.module then [] else [.implementationUnbuilt v.name v.module]

/-- What is wrong with one entry the value `r` lists, given the modules `built`. -/
def citedFindings (built : List Lean.Name) (r : Lean.Name) : Cited → List Finding
  | .thm c => if built.contains c.module then [] else [.unbuilt r c.name c.module]
  | .other c => [.notTheorem r c.name]
  | .term => [.notConstant r]

/-- What is wrong with the entry `r`, given the modules `built` and the deliverables `ds`. -/
def entryFindings (built : List Lean.Name) (ds : List Constant) (r : Entry) : List Finding :=
  (if ds.any (some ·.name == r.deliverable) then [] else [.untied r.name]) ++
    r.theorems.flatMap (citedFindings built r.name)

/-- **The decision**: what is wrong with where the theorems lie, given the modules `built` the
build lists, the deliverables `ds` and the values `vs` recording implementations, each by the module
that declares it, and the entries `rs` of the values of `Required`. -/
def findings (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) : List Finding :=
  ds.flatMap (deliverableFindings built rs) ++ vs.flatMap (implementationFindings built) ++
    rs.flatMap (entryFindings built ds)

/-- **Every required theorem lies in a module the build lists**: each deliverable and each value
recording an implementation is declared in such a module; each deliverable is named by an entry;
each entry names a deliverable; and everything each entry lists is a theorem declared in such a
module. It is stated over the lists alone, with no definition the decision uses. -/
def Located (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) : Prop :=
  (∀ d ∈ ds, d.module ∈ built) ∧ (∀ v ∈ vs, v.module ∈ built) ∧
    (∀ d ∈ ds, ∃ r ∈ rs, r.deliverable = some d.name) ∧
    (∀ r ∈ rs, ∃ d ∈ ds, r.deliverable = some d.name) ∧
    ∀ r ∈ rs, ∀ t ∈ r.theorems, ∃ c, t = .thm c ∧ c.module ∈ built

/-- What a gate reads: the findings, and each theorem the values list, with the value listing it
and the theorem by the module that declares it. -/
structure Report where
  /-- What is wrong: empty exactly when every required theorem lies in a module the build lists
  (`findings_eq_nil_iff`). -/
  findings : List Finding
  /-- Each theorem an entry lists, with that entry's value (`mem_theorems`). -/
  theorems : List (Lean.Name × Constant)
  deriving Repr

/-- The theorems among what `r` lists, each with `r`'s value. -/
def theoremsOf (r : Entry) : List (Lean.Name × Constant) :=
  r.theorems.filterMap fun
    | .thm c => some (r.name, c)
    | _ => none

/-- **What a gate reads**, given the modules the build lists, the deliverables, the values recording
implementations and the entries of the values of `Required`. -/
def report (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) : Report :=
  ⟨findings built ds vs rs, rs.flatMap theoremsOf⟩

/-! ## What the decision decides -/

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
      (∃ d ∈ ds, r.deliverable = some d.name) ∧
        ∀ t ∈ r.theorems, ∃ c, t = .thm c ∧ c.module ∈ built := by
  unfold entryFindings
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, citedFindings_eq_nil_iff]
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

/-- **The decision finds nothing exactly when every required theorem lies in a module the build
lists** (`Located`): for every list of module names and every list of deliverables, values and
entries. -/
theorem findings_eq_nil_iff : findings built ds vs rs = [] ↔ Located built ds vs rs := by
  unfold findings Located
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, deliverableFindings_eq_nil_iff,
    implementationFindings_eq_nil_iff, entryFindings_eq_nil_iff]
  constructor
  · rintro ⟨⟨hd, hv⟩, hr⟩
    exact ⟨fun d h => (hd d h).1, hv, fun d h => (hd d h).2, fun r h => (hr r h).1,
      fun r h => (hr r h).2⟩
  · rintro ⟨hdb, hv, hdr, hrd, hrt⟩
    exact ⟨⟨fun d h => ⟨hdb d h, hdr d h⟩, hv⟩, fun r h => ⟨hrd r h, hrt r h⟩⟩

/-- **A project that declares nothing keeps its verdict**: with no deliverable, no value recording
an implementation and no value of `Required`, the decision finds nothing, whatever the build lists. -/
theorem findings_nothing : findings built [] [] [] = [] := rfl

/-- A deliverable no entry names is refused, naming it, whatever else the project declares. -/
theorem undeclared_mem {d : Constant} (hd : d ∈ ds) (hr : ∀ r ∈ rs, r.deliverable ≠ some d.name) :
    Finding.undeclared d.name ∈ findings built ds vs rs := by
  have : rs.any (·.deliverable == some d.name) = false :=
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨r, hr', he⟩ := List.any_eq_true.mp h
      exact hr r hr' (beq_iff_eq.mp he)
  unfold findings
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨d, hd, by simp [deliverableFindings, this]⟩))

/-- A theorem an entry lists, declared in a module the build does not list, is refused, naming the
entry's value, the theorem and that module. -/
theorem unbuilt_mem {r : Entry} {c : Constant} (hr : r ∈ rs) (ht : .thm c ∈ r.theorems)
    (hb : c.module ∉ built) : Finding.unbuilt r.name c.name c.module ∈ findings built ds vs rs := by
  unfold findings
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  unfold entryFindings
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, ht, by simp [citedFindings, hb]⟩)

/-! ## What a finding says -/

/-- What the finding `f` states of the modules `built`, the deliverables `ds`, the values `vs` and
the entries `rs`. -/
def Finding.Holds (built : List Lean.Name) (ds vs : List Constant) (rs : List Entry) :
    Finding → Prop
  | .deliverableUnbuilt d m => ⟨m, d⟩ ∈ ds ∧ m ∉ built
  | .implementationUnbuilt v m => ⟨m, v⟩ ∈ vs ∧ m ∉ built
  | .undeclared d => (∃ c ∈ ds, c.name = d) ∧ ∀ r ∈ rs, r.deliverable ≠ some d
  | .untied n => ∃ r ∈ rs, r.name = n ∧ ∀ d ∈ ds, r.deliverable ≠ some d.name
  | .notConstant n => ∃ r ∈ rs, r.name = n ∧ .term ∈ r.theorems
  | .notTheorem n c => ∃ r ∈ rs, r.name = n ∧ ∃ m, .other ⟨m, c⟩ ∈ r.theorems
  | .unbuilt n c m => ∃ r ∈ rs, r.name = n ∧ .thm ⟨m, c⟩ ∈ r.theorems ∧ m ∉ built

/-- **Each finding holds**, and names the deliverable, value, theorem or module it is about. -/
theorem findings_sound {f : Finding} (hf : f ∈ findings built ds vs rs) :
    f.Holds built ds vs rs := by
  unfold findings at hf
  simp only [List.mem_append, List.mem_flatMap] at hf
  rcases hf with (⟨d, hd, hf⟩ | ⟨v, hv, hf⟩) | ⟨r, hr, hf⟩
  · unfold deliverableFindings at hf
    rcases List.mem_append.mp hf with hf | hf <;> split at hf <;> rename_i h <;>
      (try exact absurd hf List.not_mem_nil) <;> rw [List.mem_singleton.mp hf]
    · exact ⟨hd, by simpa using h⟩
    · refine ⟨⟨d, hd, rfl⟩, fun r hr he => h ?_⟩
      exact List.any_eq_true.mpr ⟨r, hr, by simp [he]⟩
  · unfold implementationFindings at hf
    split at hf <;> rename_i h
    · exact absurd hf List.not_mem_nil
    · rw [List.mem_singleton.mp hf]
      exact ⟨hv, by simpa using h⟩
  · unfold entryFindings at hf
    rcases List.mem_append.mp hf with hf | hf
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
        exact ⟨r, hr, rfl, c.module, ht⟩
      | term =>
        rw [List.mem_singleton.mp hf]
        exact ⟨r, hr, rfl, ht⟩

/-- **The report lists a theorem with a value exactly when** that value's entry lists it as a
theorem. -/
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

/-! ## What a refusal says -/

/-- **What the finding `f` says**, in plain words, with what the project declares or moves to clear
it. -/
def Finding.message : Finding → String
  | .deliverableUnbuilt d m =>
    s!"the deliverable {d}, which holds the proof that its record keeps its answers, is declared in \
      the module {m}, which the project's build does not list: declare it in a module of a library \
      the proof check builds"
  | .implementationUnbuilt v m =>
    s!"{v}, which holds the proof that an implementation fulfils its deliverable's record, is \
      declared in the module {m}, which the project's build does not list: declare it in a module \
      of a library the proof check builds"
  | .undeclared d =>
    s!"the deliverable {d} names none of the theorems the intent-first procedure requires of it: \
      declare a value of `LeanIntent.Required {d}`, in a module of a library the proof check \
      builds, that lists each of them by its name, its obligations and the theorems comparing it \
      with the blind formalization among them"
  | .untied n =>
    s!"the type of {n} names no deliverable of the project: declare it as \
      `LeanIntent.Required d` for a deliverable `d` that the modules read declare"
  | .notConstant n =>
    s!"{n} lists a proof that is not a theorem's name: list each theorem as `⟨name⟩`, or \
      `⟨@name⟩` where its first arguments are implicit"
  | .notTheorem n c =>
    s!"{n} lists {c}, which is not a theorem: declare what it proves with `theorem`, and list that"
  | .unbuilt n c m =>
    s!"{n} lists the theorem {c}, declared in the module {m}, which the project's build does not \
      list, so the proof check does not check it: move {c} into a module of a library the proof \
      check builds, or have that library build {m}, for example by naming it in the library's \
      globs"

end Required

end LeanIntent
