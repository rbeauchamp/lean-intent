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
* **A deliverable may await its implementation.** Its owner confirms its record before any
  implementation exists, so for a while a deliverable is deliberately unimplemented. A value of
  `AwaitingImplementation d` declares that state of the deliverable `d`, with the reason, such as
  the issue that tracks the work, whose text cannot be blank (`AwaitingImplementation.stated`). It
  is declared after `d` too, so nothing of it enters a revision's text either, and the project
  retires it by replacing it with a value of `Implementation d`, which leaves the decision's verdict
  as it was (`replace_nil_iff`).
* **The decision** (`findings`) reads, for each value of a project, the deliverable its type names
  and either the constant its subject is (`Entry`) or the reason it awaits one (`AwaitingEntry`), as
  `LeanIntent.Implementation.Read` computes them from the build. It finds nothing exactly when the
  project declares a deliverable, each deliverable has exactly one value recording its
  implementation or exactly one value declaring it awaiting one, and not both, each value names one
  of the project's deliverables, and each implementation records a constant (`findings_eq_nil_iff`,
  whose statement `Accounted` shares no definition with the decision). Each finding holds and names
  the deliverable or value it is about (`findings_sound`), and the report lists each deliverable
  with the value that records its implementation and that constant's module and name
  (`mem_implementations`), or with the value that declares it awaiting one and its reason
  (`mem_awaiting`).

The decisions this module makes, each on the owner's behalf:

* **One implementation for each deliverable, or one declaration that it awaits one.** A deliverable
  with neither is refused, naming it, since nothing then says which code fulfils it or that none is
  meant to yet; one with several implementations is refused, naming them, since the project's
  declarations would then not tell which of the programs is the deliverable's; and one with several
  declarations that it awaits an implementation, or with an implementation and such a declaration,
  is refused, naming those declarations, since a declaration left in place after the implementation
  exists says something false of the project. A project with two programs for one record declares
  two deliverables.
* **A declaration that a deliverable awaits its implementation names its reason.** A blank reason
  is no value of `AwaitingImplementation d`, whose field `stated` proves the reason is not blank,
  which is false of a blank one; the decision does not read the reason, and the report gives it.
* **One constant may implement several deliverables.** Each value's proof is of its own
  deliverable's record, so a theorem about one record discharges no other, and a program may be what
  two contracts are about.
* **The subject is a constant.** A term, such as `fun l => sort l` or a polymorphic function applied
  to the record's types, names no constant a reader can find, and is refused, naming the value: the
  project records a definition of it instead.
* **A value whose type names no deliverable of the project is refused**, naming it, whether it
  records an implementation or declares one awaited: a term in place of a constant, or a deliverable
  that the modules read do not declare, ties it to nothing the log is tied to.

What this module does not establish: that the recorded constant is what a program runs, such as an
executable's entry point calling it, or that its compiled code computes its definition, which
`implemented_by` and `extern` replace; that the proof rests only on axioms the project accepts, which
`#print axioms` lists of a value and a project's own gate audits, as it audits its other proofs; that
Lean's kernel checked each value, which the option `debug.skipKernelTC` skips; that the entries are
those of the build, which `LeanIntent.Implementation.Read` reads through Lean; and that work on a
deliverable declared awaiting its implementation goes on, or for how long it may wait: the
declaration is accepted for as long as it stands, and its reason is what a reader sees of it.
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

/-- **The deliverable `d` awaits its implementation**, for the reason given, such as the address of
the issue that tracks the work. A project declares one for a deliverable whose record is confirmed
before its implementation exists, in a module that imports the deliverable, and replaces it with a
value of `Implementation d` once the implementation exists. -/
structure AwaitingImplementation {W : Type u} (d : Deliverable W) where
  /-- Why the implementation is awaited, or where its work is tracked. -/
  reason : String
  /-- The reason is not blank: it holds a character that is not whitespace. The default proof,
  `decide +kernel`, has Lean's kernel decide it of the reason written. -/
  stated : reason.toList.any (!·.isWhitespace) = true := by decide +kernel

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

/-- A value of an `AwaitingImplementation` type that a project declares, as the build shows it. -/
structure AwaitingEntry where
  /-- The constant of that type. -/
  name : Lean.Name
  /-- The deliverable its type names, where that is a constant. -/
  deliverable : Option Lean.Name
  /-- The reason it gives. -/
  reason : String
  deriving DecidableEq, Repr

/-- What is wrong with a project's implementations. -/
inductive Finding where
  /-- The project declares no deliverable. -/
  | noDeliverable
  /-- No value records the implementation of this deliverable, and none declares that it awaits
  one. -/
  | unimplemented (deliverable : Lean.Name)
  /-- These values all record the implementation of this deliverable. -/
  | several (deliverable : Lean.Name) (values : List Lean.Name)
  /-- The type of this value names no deliverable of the project. -/
  | untied (value : Lean.Name)
  /-- The subject this value records is not a constant. -/
  | notConstant (value : Lean.Name)
  /-- These values all declare that this deliverable awaits its implementation. -/
  | severalAwaiting (deliverable : Lean.Name) (values : List Lean.Name)
  /-- A value records the implementation of this deliverable, and these values declare that it
  awaits one. -/
  | awaitingImplemented (deliverable : Lean.Name) (values : List Lean.Name)
  /-- The type of this value, which declares a deliverable awaiting its implementation, names no
  deliverable of the project. -/
  | untiedAwaiting (value : Lean.Name)
  deriving DecidableEq, Repr

/-- The entries among `vs` that record the implementation of the deliverable `d`. -/
def implementing (vs : List Entry) (d : Lean.Name) : List Entry :=
  vs.filter fun v => v.deliverable == some d

/-- The entries among `as` that declare that the deliverable `d` awaits its implementation. -/
def awaitingFor (as : List AwaitingEntry) (d : Lean.Name) : List AwaitingEntry :=
  as.filter fun a => a.deliverable == some d

/-- The deliverable `o` names, where it names one, is one of the deliverables `ds`. -/
def tiesTo (ds : List Lean.Name) : Option Lean.Name → Bool
  | some d => ds.contains d
  | none => false

/-- The entry `v` names one of the deliverables `ds`. -/
def Entry.ties (ds : List Lean.Name) (v : Entry) : Bool := tiesTo ds v.deliverable

/-- The entry `a` names one of the deliverables `ds`. -/
def AwaitingEntry.ties (ds : List Lean.Name) (a : AwaitingEntry) : Bool := tiesTo ds a.deliverable

/-- What is wrong with the deliverable `d`, given the entries `vs` and `as`. -/
def deliverableFindings (vs : List Entry) (as : List AwaitingEntry) (d : Lean.Name) :
    List Finding :=
  (if (implementing vs d).isEmpty && (awaitingFor as d).isEmpty then [.unimplemented d] else []) ++
    (if 2 ≤ (implementing vs d).length then
      [.several d ((implementing vs d).map (·.name))] else []) ++
    (if 2 ≤ (awaitingFor as d).length then
      [.severalAwaiting d ((awaitingFor as d).map (·.name))] else []) ++
    (if !(implementing vs d).isEmpty && !(awaitingFor as d).isEmpty then
      [.awaitingImplemented d ((awaitingFor as d).map (·.name))] else [])

/-- What is wrong with the entry `v`, given the deliverables `ds`. -/
def entryFindings (ds : List Lean.Name) (v : Entry) : List Finding :=
  (if v.ties ds then [] else [.untied v.name]) ++
    (if v.subject.isSome then [] else [.notConstant v.name])

/-- What is wrong with the entry `a`, given the deliverables `ds`. -/
def awaitingFindings (ds : List Lean.Name) (a : AwaitingEntry) : List Finding :=
  if a.ties ds then [] else [.untiedAwaiting a.name]

/-- **The decision**: everything wrong with the implementations the entries `vs` record, and the
entries `as` declare awaited, of the deliverables `ds`. -/
def findings (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : List Finding :=
  (if ds.isEmpty then [.noDeliverable] else []) ++ ds.flatMap (deliverableFindings vs as) ++
    vs.flatMap (entryFindings ds) ++ as.flatMap (awaitingFindings ds)

/-- **Every deliverable of `ds` is accounted for** by the entries `vs`, which record
implementations, and `as`, which declare implementations awaited: there is at least one deliverable;
each has exactly one implementation and no declaration that it awaits one, or no implementation and
exactly one such declaration; each entry names one of the deliverables; and each implementation
records a constant. It is stated over the lists alone, with no definition the decision uses. -/
def Accounted (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : Prop :=
  ds ≠ [] ∧
    (∀ d ∈ ds,
      (vs.countP (fun v => decide (v.deliverable = some d)) = 1 ∧
          as.countP (fun a => decide (a.deliverable = some d)) = 0) ∨
        (vs.countP (fun v => decide (v.deliverable = some d)) = 0 ∧
          as.countP (fun a => decide (a.deliverable = some d)) = 1)) ∧
    (∀ v ∈ vs, (∃ d ∈ ds, v.deliverable = some d) ∧ v.subject.isSome = true) ∧
    ∀ a ∈ as, ∃ d ∈ ds, a.deliverable = some d

/-- The value that records the implementation of the deliverable `d`, and the constant it records,
where exactly one entry does and records a constant. -/
def implementationOf (vs : List Entry) (d : Lean.Name) : Option (Lean.Name × Constant) :=
  match implementing vs d with
  | [v] => v.subject.map fun c => (v.name, c)
  | _ => none

/-- The value that declares that the deliverable `d` awaits its implementation, and the reason it
gives, where exactly one entry declares it. -/
def awaitedOf (as : List AwaitingEntry) (d : Lean.Name) : Option (Lean.Name × String) :=
  match awaitingFor as d with
  | [a] => some (a.name, a.reason)
  | _ => none

/-- Everything a gate reads of a project's implementations. -/
structure Report where
  /-- What is wrong: empty exactly when every deliverable is accounted for
  (`findings_eq_nil_iff`). -/
  findings : List Finding
  /-- Each deliverable whose implementation exactly one value records, with that value and the
  constant it records (`mem_implementations`). -/
  implementations : List (Lean.Name × Lean.Name × Constant)
  /-- Each deliverable that exactly one value declares awaiting its implementation, with that value
  and the reason it gives (`mem_awaiting`). -/
  awaiting : List (Lean.Name × Lean.Name × String)
  deriving Repr

/-- **What a gate reads**, given the project's deliverables and the entries of its values. -/
def report (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) : Report :=
  ⟨findings ds vs as, ds.filterMap fun d => (implementationOf vs d).map fun x => (d, x),
    ds.filterMap fun d => (awaitedOf as d).map fun x => (d, x)⟩

/-! ## What the decision decides -/

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

/-- The entries recording the implementation of `d` are those whose deliverable is `d`. -/
theorem length_implementing {d : Lean.Name} :
    (implementing vs d).length = vs.countP (fun v => decide (v.deliverable = some d)) := by
  simp only [implementing, List.countP_eq_length_filter]
  congr 2
  funext v
  exact Bool.eq_iff_iff.mpr (by simp)

/-- The entries declaring `d` awaited are those whose deliverable is `d`. -/
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

/-- **The decision finds nothing exactly when every deliverable is accounted for**: there is a
deliverable, each has exactly one implementation or exactly one declaration that it awaits one, and
not both, each entry names one of the deliverables, and each implementation records a constant. -/
theorem findings_eq_nil_iff : findings ds vs as = [] ↔ Accounted ds vs as := by
  have one : ∀ i w : Nat, i + w = 1 ↔ (i = 1 ∧ w = 0) ∨ (i = 0 ∧ w = 1) := by omega
  unfold findings Accounted
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, deliverableFindings_eq_nil_iff,
    length_implementing, length_awaitingFor, one, entryFindings_eq_nil_iff,
    awaitingFindings_eq_nil_iff]
  cases ds <;> simp [and_assoc]

/-- **Replacing a declaration that a deliverable awaits its implementation with a value recording
it** leaves the decision's verdict as it was: given an implementation `v` naming the deliverable the
awaiting entry `a` names, and recording a constant, the decision finds nothing with `v` in place of
`a` exactly when it finds nothing with `a`. -/
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

/-! ## What a finding says -/

/-- What the finding `f` states of the deliverables `ds` and the entries `vs` and `as`. -/
def Finding.Holds (ds : List Lean.Name) (vs : List Entry) (as : List AwaitingEntry) :
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

/-- **Each finding holds**, and names the deliverable or the value it is about. -/
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

/-- **The report lists a deliverable with a value and a reason exactly when** that value is the one
entry declaring that the deliverable awaits its implementation, and that reason the one it gives. -/
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

/-- Where the decision finds nothing, the report lists every deliverable either with the value that
records its implementation and the constant that value records, no value declaring it awaited, or
with the value that declares it awaiting its implementation and the reason given, no value recording
one. -/
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
