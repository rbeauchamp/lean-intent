import LeanIntent.Confirmation

/-!
# The implementation of a deliverable

A proof that an implementation fulfils its intent record binds the code only when what the project
declares names that code. A deliverable (`LeanIntent.Deliverable`) holds a record, its explanation
and the answers it keeps, which its owner confirms before any implementation exists, and names no
implementation. This module adds the value that does, declared once the implementation exists: an
`Implementation d` holds the constant that implements the deliverable `d`, as the record's subject,
and the proof that it fulfils the record (`IntentRecord.Fulfilled`).

* **The proof is of the recorded constant, by its type.** The field `fulfils` has the type
  `d.record.Fulfilled subject`, and Lean's kernel checks every declaration, so a value is accepted
  only when its proof proves that proposition of the subject it records. A theorem that another
  constant fulfils the record is a proof of it only where the two constants are definitionally
  equal, so that the proposition is the same one; anywhere else Lean refuses the declaration, naming
  the proof and both propositions, and the project does not build. So a subject can be recorded
  exactly when it fulfils the record (`exists_iff`), and the fulfilment a gate reads is of the
  constant recorded.
* **It is tied to the owners' log through the deliverable.** A value names its deliverable in its
  type, the deliverable names its record, and the answers of the project's owners' log name that
  record and its revision (`LeanIntent.Confirmation`).
* **Nothing of it enters a revision's text.** The texts an answer holds are computed from the
  deliverable's explanation and what its meaning reaches (`LeanIntent.Render.revisionText`,
  `LeanIntent.Render.consequenceText`), and a value of `Implementation d` is declared after `d`,
  which its type names, so nothing `d` holds refers to it. Recording the implementation, or replacing
  it with another, changes no answer's text, and the confirmations stand. Renaming a constant still
  changes the text of every revision whose meaning reaches it, as it always has; a record's meaning
  reaches no declaration of its implementation where cone exclusion (`LeanIntent.Cone`) accepts it
  against that implementation.
* **The decision** (`findings`) reads, for each value of a project, the deliverable its type names
  and the constant its subject is (`Entry`), as `LeanIntent.Implementation.Read` computes them from
  the build. It finds nothing exactly when the project declares a deliverable, each deliverable has
  exactly one value recording its implementation, and each value names one of the project's
  deliverables and records a constant (`findings_eq_nil_iff`). Each finding holds and names the
  deliverable or value it is about (`findings_sound`), and the report lists each deliverable with the
  value that records its implementation and that constant's module and name
  (`mem_implementations`).

The decisions this module makes, each on the owner's behalf:

* **One implementation for each deliverable.** A deliverable with no value is refused, naming it,
  since nothing then says which code fulfils it; one with several is refused, naming them, since the
  project's declarations would then not tell which of the programs is the deliverable's. A project
  with two programs for one record declares two deliverables.
* **One constant may implement several deliverables.** Each value's proof is of its own
  deliverable's record, so a theorem about one record discharges no other, and a program may be what
  two contracts are about.
* **The subject is a constant.** A term, such as `fun l => sort l` or a polymorphic function applied
  to the record's types, names no constant a reader can find, and is refused, naming the value: the
  project records a definition of it instead.
* **A value whose type names no deliverable of the project is refused**, naming it: a term in place
  of a constant, or a deliverable that the modules read do not declare, ties it to nothing the log
  is tied to.

What this module does not establish: that the recorded constant is what a program runs, such as an
executable's entry point calling it, or that its compiled code computes its definition, which
`implemented_by` and `extern` replace; that the proof rests only on axioms the project accepts, which
`#print axioms` lists of a value and a project's own gate audits, as it audits its other proofs; that
Lean's kernel checked each value, which the option `debug.skipKernelTC` skips; and that the entries
are those of the build, which `LeanIntent.Implementation.Read` reads through Lean.
-/

namespace LeanIntent

universe u

/-- **An implementation of the deliverable `d`**: the constant that implements it, as the subject of
its record, and the proof that it fulfils the record. A project declares one for each deliverable
once its implementation exists, in a module that imports the deliverable and the implementation. -/
structure Implementation {W : Type u} (d : Deliverable W) where
  /-- The implementation: the constant the record's subject is. -/
  subject : W
  /-- It fulfils the deliverable's record. -/
  fulfils : d.record.Fulfilled subject

namespace Implementation

section

variable {W : Type u} {d : Deliverable W}

/-- What a value records fulfils the deliverable's record. -/
theorem fulfilled (v : Implementation d) : d.record.Fulfilled v.subject := v.fulfils

/-- **A subject can be recorded as the implementation of `d` exactly when it fulfils the record**:
no value records a subject that does not, so a proof about another subject is no proof of it. -/
theorem exists_iff {w : W} : (∃ v : Implementation d, v.subject = w) ↔ d.record.Fulfilled w :=
  ⟨fun ⟨v, h⟩ => h ▸ v.fulfils, fun h => ⟨⟨w, h⟩, rfl⟩⟩

/-- Wherever the record's domain hypotheses hold of the implementation, it meets the record. -/
theorem meets (v : Implementation d) (hd : d.record.Dom v.subject) : d.record.Meets v.subject :=
  IntentRecord.meets_of_fulfilled v.fulfils hd

end

/-! ## The decision -/

/-- A constant, by the module that declares it and its name. -/
structure Constant where
  /-- The module that declares it. -/
  module : Lean.Name
  /-- Its name. -/
  name : Lean.Name
  deriving DecidableEq, Repr

/-- A value of an `Implementation` type that a project declares, as the build shows it. -/
structure Entry where
  /-- The constant of that type. -/
  name : Lean.Name
  /-- The deliverable its type names, where that is a constant. -/
  deliverable : Option Lean.Name
  /-- The constant its subject is, where it is one. -/
  subject : Option Constant
  deriving DecidableEq, Repr

/-- What is wrong with a project's implementations. -/
inductive Finding where
  /-- The project declares no deliverable. -/
  | noDeliverable
  /-- No value records the implementation of this deliverable. -/
  | unimplemented (deliverable : Lean.Name)
  /-- These values all record the implementation of this deliverable. -/
  | several (deliverable : Lean.Name) (values : List Lean.Name)
  /-- The type of this value names no deliverable of the project. -/
  | untied (value : Lean.Name)
  /-- The subject this value records is not a constant. -/
  | notConstant (value : Lean.Name)
  deriving DecidableEq, Repr

/-- The entries among `vs` that record the implementation of the deliverable `d`. -/
def implementing (vs : List Entry) (d : Lean.Name) : List Entry :=
  vs.filter fun v => v.deliverable == some d

/-- The entry `v` names one of the deliverables `ds`. -/
def Entry.ties (ds : List Lean.Name) (v : Entry) : Bool :=
  match v.deliverable with
  | some d => ds.contains d
  | none => false

/-- What is wrong with the deliverable `d`, given the entries `vs`. -/
def deliverableFindings (vs : List Entry) (d : Lean.Name) : List Finding :=
  match implementing vs d with
  | [] => [.unimplemented d]
  | [_] => []
  | ws => [.several d (ws.map (·.name))]

/-- What is wrong with the entry `v`, given the deliverables `ds`. -/
def entryFindings (ds : List Lean.Name) (v : Entry) : List Finding :=
  (if v.ties ds then [] else [.untied v.name]) ++
    (if v.subject.isSome then [] else [.notConstant v.name])

/-- **The decision**: everything wrong with the implementations the entries `vs` record of the
deliverables `ds`. -/
def findings (ds : List Lean.Name) (vs : List Entry) : List Finding :=
  (if ds.isEmpty then [.noDeliverable] else []) ++ ds.flatMap (deliverableFindings vs) ++
    vs.flatMap (entryFindings ds)

/-- **The deliverables `ds` are implemented** as the entries `vs` record: there is at least one
deliverable, each has exactly one entry recording its implementation, and each entry names one of
them and records a constant. -/
def Implemented (ds : List Lean.Name) (vs : List Entry) : Prop :=
  ds ≠ [] ∧ (∀ d ∈ ds, ∃ v, implementing vs d = [v]) ∧
    ∀ v ∈ vs, (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true

/-- The value that records the implementation of the deliverable `d`, and the constant it records,
where exactly one entry does and records a constant. -/
def implementationOf (vs : List Entry) (d : Lean.Name) : Option (Lean.Name × Constant) :=
  match implementing vs d with
  | [v] => v.subject.map fun c => (v.name, c)
  | _ => none

/-- Everything a gate reads of a project's implementations. -/
structure Report where
  /-- What is wrong: empty exactly when the deliverables are implemented (`findings_eq_nil_iff`). -/
  findings : List Finding
  /-- Each deliverable whose implementation exactly one value records, with that value and the
  constant it records (`mem_implementations`). -/
  implementations : List (Lean.Name × Lean.Name × Constant)
  deriving Repr

/-- **What a gate reads**, given the project's deliverables and the entries of its values. -/
def report (ds : List Lean.Name) (vs : List Entry) : Report :=
  ⟨findings ds vs, ds.filterMap fun d => (implementationOf vs d).map fun x => (d, x)⟩

/-! ## What the decision decides -/

section

variable {ds : List Lean.Name} {vs : List Entry}

theorem mem_implementing {d : Lean.Name} {v : Entry} :
    v ∈ implementing vs d ↔ v ∈ vs ∧ v.deliverable = some d := by
  simp [implementing]

theorem ties_iff {v : Entry} : v.ties ds = true ↔ ∃ d ∈ ds, v.deliverable = some d := by
  unfold Entry.ties
  cases v.deliverable <;> simp

theorem deliverableFindings_eq_nil_iff {d : Lean.Name} :
    deliverableFindings vs d = [] ↔ ∃ v, implementing vs d = [v] := by
  unfold deliverableFindings
  match implementing vs d with
  | [] => simp
  | [v] => simp
  | _ :: _ :: _ => simp

theorem entryFindings_eq_nil_iff {v : Entry} :
    entryFindings ds v = [] ↔ (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true := by
  unfold entryFindings
  rw [← ties_iff]
  cases v.ties ds <;> cases v.subject.isSome <;> simp

/-- **The decision finds nothing exactly when the deliverables are implemented.** -/
theorem findings_eq_nil_iff : findings ds vs = [] ↔ Implemented ds vs := by
  unfold findings Implemented
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, deliverableFindings_eq_nil_iff,
    entryFindings_eq_nil_iff]
  cases ds <;> simp

/-! ## What a finding says -/

/-- What the finding `f` states of the deliverables `ds` and the entries `vs`. -/
def Finding.Holds (ds : List Lean.Name) (vs : List Entry) : Finding → Prop
  | .noDeliverable => ds = []
  | .unimplemented d => d ∈ ds ∧ ∀ v ∈ vs, v.deliverable ≠ some d
  | .several d ns => d ∈ ds ∧ ns = (implementing vs d).map (·.name) ∧ 2 ≤ ns.length
  | .untied n => ∃ v ∈ vs, v.name = n ∧ ∀ d ∈ ds, v.deliverable ≠ some d
  | .notConstant n => ∃ v ∈ vs, v.name = n ∧ v.subject = none

theorem deliverableFindings_sound {d : Lean.Name} (hd : d ∈ ds) {f : Finding}
    (hf : f ∈ deliverableFindings vs d) : f.Holds ds vs := by
  unfold deliverableFindings at hf
  match h : implementing vs d, hf with
  | [], hf =>
    rw [List.mem_singleton.mp hf]
    refine ⟨hd, fun v hv hvd => ?_⟩
    have : v ∈ implementing vs d := mem_implementing.mpr ⟨hv, hvd⟩
    rw [h] at this
    exact List.not_mem_nil this
  | [_], hf => exact absurd hf List.not_mem_nil
  | a :: b :: rest, hf =>
    rw [List.mem_singleton.mp hf]
    exact ⟨hd, by rw [h], by simp⟩

theorem entryFindings_sound {v : Entry} (hv : v ∈ vs) {f : Finding} (hf : f ∈ entryFindings ds v) :
    f.Holds ds vs := by
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

/-- **Each finding holds**, and names the deliverable or the value it is about. -/
theorem findings_sound {f : Finding} (hf : f ∈ findings ds vs) : f.Holds ds vs := by
  unfold findings at hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · split at hf
      · rename_i h
        rw [List.mem_singleton.mp hf]
        exact List.isEmpty_iff.mp h
      · exact absurd hf List.not_mem_nil
    · obtain ⟨d, hd, hf⟩ := List.mem_flatMap.mp hf
      exact deliverableFindings_sound hd hf
  · obtain ⟨v, hv, hf⟩ := List.mem_flatMap.mp hf
    exact entryFindings_sound hv hf

/-! ## What the report lists -/

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

/-- **The report lists a deliverable with a value and a constant exactly when** that value is the one
entry recording the deliverable's implementation, and that constant its subject. -/
theorem mem_implementations {d n : Lean.Name} {c : Constant} :
    (d, n, c) ∈ (report ds vs).implementations ↔
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

/-- Where the decision finds nothing, the report lists every deliverable, with the value that records
its implementation and the constant that value records. -/
theorem implementations_of_nil (h : findings ds vs = []) {d : Lean.Name} (hd : d ∈ ds) :
    ∃ v c, v ∈ vs ∧ v.deliverable = some d ∧ v.subject = some c ∧
      (d, v.name, c) ∈ (report ds vs).implementations := by
  obtain ⟨_, hone, hall⟩ := findings_eq_nil_iff.mp h
  obtain ⟨v, hv⟩ := hone d hd
  have hmem : v ∈ implementing vs d := by rw [hv]; exact List.mem_singleton_self v
  obtain ⟨hvs, hvd⟩ := mem_implementing.mp hmem
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hall v hvs).2
  exact ⟨v, c, hvs, hvd, hc, mem_implementations.mpr ⟨hd, v, hv, rfl, hc⟩⟩

end

end Implementation

end LeanIntent
