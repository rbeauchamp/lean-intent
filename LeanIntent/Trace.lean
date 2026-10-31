import LeanIntent.Statement

/-!
# Tracing an answer's authority back to a declared owner

An answer counts only when a declared owner gave it, or a party acting under a delegation that
traces back to one, within the scope of every delegation on the way. This module decides that, for
each answer of a project's log, from the statements of the owners' log (`LeanIntent.Statement`):
the owners declaration in force, and the delegations, answers, retractions and revocations.

Every statement records who made it (`Authority`): a principal acting as an owner, or acting under
the delegation it names. So an answer names the one chain its authority rests on: the delegation it
acts under, the delegation that one was granted under, and so on, until a principal acting as an
owner. The decision follows that chain and nothing else.

* **The specification** (`Chain`): an authority traces back, for an act on a record, when it is a
  declared owner acting as owner, or it acts under a delegation whose `Link` holds and whose grantor's
  authority traces back in turn. The link at a principal `p` acting under the delegation with id `d`
  holds when the one statement of the project with id `d` is a delegation to `p`, no statement
  of the log revokes it (`revokes`), its scope allows the act (`allows`), and it may be passed on
  when its delegate passed it on. An answer is accepted (`Accepted`) when it is the one statement of
  the project with its id, its authority traces back for what it does, and no retraction whose own
  authority traces back retracts it (`Retracted`). A chain is a sequence of links that ends at a
  declared owner (`chain_iff_leads`), and, being finite, never returns to a link it has passed
  (`Chain.no_cycle`).
* **The decision** (`check`): walks the chain from the answer, testing each link in turn, and
  refuses at the first that fails. It visits each id of the log at most once, so it stops on every
  input and refuses a chain that returns to a link it has passed.
* **What it decides** (`check_eq_ok_iff`): it accepts exactly the accepted answers, for every log,
  every owners declaration and every statement. **What a refusal says** (`check_eq_error`): it names
  the answer, and either that the answer is not the one statement of its id, or not an answer, or
  the first link that breaks, with every link before it holding (`Leads`) and the test that link
  fails (`Fails`), or the retraction that retracts it. A link that breaks breaks every chain through
  it (`Fails.not_chain`).
* **Monotonicity, where it holds**: a statement added with an id no statement of the log has, that
  is no revocation, keeps every chain (`Chain.append_fresh`); a statement added that is no
  delegation makes no chain (`Chain.of_append`), so a revocation only removes authority; and a
  retraction added with a fresh id accepts no answer the log refused
  (`Accepted.of_append_retractions`).

The decisions this module makes, each a reading of the statements' meaning:

* A retraction is an act like an answer: it takes effect only when its author's authority traces
  back, for retracting an answer on the answer's record, which a delegation allows only when it lets
  its delegate retract.
* A revocation takes effect when the principal who granted the delegation, or a declared owner acting
  as owner, made it. It takes effect in every chain that passes through the delegation, whatever the
  dates: an answer or retraction made under a revoked delegation, before or after the revocation,
  does not count.
* Only statements of the project count. A reference to an id that no statement of the project
  has, or that more than one has, is a broken link; an answer whose id another statement of the
  project shares is refused, so no retraction is ambiguous.
* Record names are compared exactly; a delegation that names records covers only those names.

Acceptance is not monotone everywhere: a revocation can restore an answer, by voiding a retraction
made under the revoked delegation; a delegation added can make such a retraction count; and an owners
declaration with more owners can make a revocation count.

What it does not decide: which owners declaration is in force, which the caller gives
(`LeanIntent.Confirmation` gives the log's one declaration, and refuses a log with several, since
only signatures could settle which is in force, lean-intent #19); whether a statement's author made
it, which review of the change that commits it checks, and a signature too, for a project that
signs; whether the log given holds every statement the project has committed, which the caller
gathers, since a log missing a revocation or a retraction can accept an answer the whole log
refuses; and the dates, sources and keys of statements, which it does not read.
-/

namespace LeanIntent

namespace Trace

/-- What a statement does that needs authority. -/
inductive Act.Kind where
  /-- Confirm a consequence. -/
  | confirm
  /-- Decline a consequence. -/
  | decline
  /-- Retract an answer. -/
  | retract
  deriving DecidableEq

/-- An act on one intent record, named as statements name it. -/
structure Act where
  /-- What is done. -/
  kind : Act.Kind
  /-- The intent record's name. -/
  record : String
  deriving DecidableEq

/-- The act of an answer: it confirms or declines, as its verdict says, a consequence of its
record. -/
def Act.ofAnswer (a : Statement.Answer) : Act :=
  ⟨match a.verdict with | .confirmed => .confirm | .declined => .decline, a.record⟩

/-- The scope `s` allows the act: it covers the act's record, every record or that name exactly,
and lets its delegate do that kind of act. -/
def allows (s : Scope) (act : Act) : Bool :=
  (match s.records with | .all => true | .only names => names.contains act.record) &&
    (match act.kind with | .confirm => s.confirm | .decline => s.decline | .retract => s.retract)

/-- Why a link breaks. -/
inductive Broken where
  /-- A principal acting as owner is not a declared owner. -/
  | notOwner
  /-- No statement of the project has the delegation's id. -/
  | unknown
  /-- More than one statement of the project has the delegation's id. -/
  | ambiguous
  /-- The statement with the delegation's id is not a delegation. -/
  | notDelegation
  /-- The principal acting under the delegation is not its delegate. -/
  | notDelegate
  /-- The statement with the id given revokes the delegation. -/
  | revoked (revocation : Ident)
  /-- The delegation's scope does not allow the act. -/
  | outOfScope
  /-- The delegation was passed on, though it may not be. -/
  | notPassable
  /-- Following the chain from the delegation's grantor leads back to this link. -/
  | cycle
  deriving DecidableEq

section

variable (project : Ident) (owners : Statement.Owners) (log : List Statement)

/-- The statements of the project in the log with the id `d`, in the log's order. -/
def named (d : Ident) : List Statement :=
  log.filter fun s => s.project == project && s.id == d

/-- The one statement of the project with the id `d`, or `none` when none or more than one has
it. -/
def find (d : Ident) : Option Statement :=
  match named project log d with
  | [s] => some s
  | _ => none

/-- `o` is a declared owner. -/
def isOwner (o : Ident) : Bool :=
  (owners.principals.map Principal.name).contains o

/-- The statement `r` revokes the delegation of the project with the id `d`, granted by `g`: it is
a revocation of the project naming `d`, made by `g`'s principal or by a declared owner acting as
owner. -/
def revokes (d : Ident) (g : Authority) (r : Statement) : Bool :=
  r.project == project && match r.body with
    | .revocation v => v.delegation == d &&
        (v.author.principal == g.principal ||
          (v.author.delegation == none && isOwner owners v.author.principal))
    | _ => false

/-- The link at the principal `p` acting under the delegation with the id `d` holds for the act
`act`, its authority passed on when `passed`: the one statement of the project with the id `d`
states the delegation `del`, whose delegate is `p`, which no statement of the log revokes, whose
scope allows the act, and which may be passed on if it is. It leads to `del.delegator`, who granted
it. -/
def Link (act : Act) (passed : Bool) (p d : Ident) (del : Statement.Delegation) : Prop :=
  (∃ s, find project log d = some s ∧ s.body = .delegation del) ∧ del.delegate.name = p ∧
    (∀ r ∈ log, revokes project owners d del.delegator r = false) ∧ allows del.scope act = true ∧
    (passed = true → del.mayPassOn = true)

/-- **The specification.** `Chain act passed a`: the authority `a` traces back to a declared owner
for the act `act`, within the scope of every delegation on the way. It is passed on when `passed`,
that is, used to grant a delegation, so the delegation it acts under must allow that. -/
inductive Chain (act : Act) : Bool → Authority → Prop where
  /-- A declared owner, acting as owner. -/
  | owner {passed : Bool} {o : Ident} : isOwner owners o = true → Chain act passed ⟨o, none⟩
  /-- A principal acting under a delegation whose link holds, granted by an authority that traces
  back, passed on. -/
  | link {passed : Bool} {p d : Ident} {del : Statement.Delegation} :
      Link project owners log act passed p d del → Chain act true del.delegator →
      Chain act passed ⟨p, some d⟩

/-- `Leads act passed a passed' b`: following the chain from `a`, every link holds until `b`. -/
inductive Leads (act : Act) : Bool → Authority → Bool → Authority → Prop where
  /-- No link. -/
  | refl {passed : Bool} {a : Authority} : Leads act passed a passed a
  /-- A link that holds, then the links from its grantor. -/
  | link {passed passed' : Bool} {p d : Ident} {del : Statement.Delegation} {b : Authority} :
      Link project owners log act passed p d del → Leads act true del.delegator passed' b →
      Leads act passed ⟨p, some d⟩ passed' b

/-- `Fails act passed a why`: the link at `a` breaks for the reason `why`. -/
inductive Fails (act : Act) : Bool → Authority → Broken → Prop where
  /-- A principal acting as owner is not a declared owner. -/
  | notOwner {passed : Bool} {o : Ident} :
      isOwner owners o = false → Fails act passed ⟨o, none⟩ .notOwner
  /-- No statement of the project has the id `d`. -/
  | unknown {passed : Bool} {p d : Ident} :
      named project log d = [] → Fails act passed ⟨p, some d⟩ .unknown
  /-- More than one statement of the project has the id `d`. -/
  | ambiguous {passed : Bool} {p d : Ident} {s t : Statement} {rest : List Statement} :
      named project log d = s :: t :: rest → Fails act passed ⟨p, some d⟩ .ambiguous
  /-- The statement with the id `d` is not a delegation. -/
  | notDelegation {passed : Bool} {p d : Ident} {s : Statement} :
      find project log d = some s → (∀ del, s.body ≠ .delegation del) →
      Fails act passed ⟨p, some d⟩ .notDelegation
  /-- The delegation's delegate is not `p`. -/
  | notDelegate {passed : Bool} {p d : Ident} {s : Statement} {del : Statement.Delegation} :
      find project log d = some s → s.body = .delegation del → del.delegate.name ≠ p →
      Fails act passed ⟨p, some d⟩ .notDelegate
  /-- The statement `r` of the log revokes the delegation. -/
  | revoked {passed : Bool} {p d : Ident} {s r : Statement} {del : Statement.Delegation} :
      find project log d = some s → s.body = .delegation del → r ∈ log →
      revokes project owners d del.delegator r = true → Fails act passed ⟨p, some d⟩ (.revoked r.id)
  /-- The delegation's scope does not allow the act. -/
  | outOfScope {passed : Bool} {p d : Ident} {s : Statement} {del : Statement.Delegation} :
      find project log d = some s → s.body = .delegation del → allows del.scope act = false →
      Fails act passed ⟨p, some d⟩ .outOfScope
  /-- The authority is passed on, and the delegation may not be. -/
  | notPassable {passed : Bool} {p d : Ident} {s : Statement} {del : Statement.Delegation} :
      find project log d = some s → s.body = .delegation del → passed = true →
      del.mayPassOn = false → Fails act passed ⟨p, some d⟩ .notPassable
  /-- The link holds, and links that all hold lead from its grantor back to it. -/
  | cycle {passed passed' : Bool} {p d : Ident} {del : Statement.Delegation} :
      Link project owners log act passed p d del →
      Leads project owners log act true del.delegator passed' ⟨p, some d⟩ →
      Fails act passed ⟨p, some d⟩ .cycle

/-- The author of `r` when it is a retraction of the project of the answer with the id `answer`. -/
def retractionOf (answer : Ident) (r : Statement) : Option Authority :=
  if r.project = project then
    match r.body with
    | .retraction t => if t.answer = answer then some t.author else none
    | _ => none
  else none

/-- The answer `s`, which states `a`, is retracted: a statement of the log retracts it with
authority that traces back for retracting an answer on its record. -/
def Retracted (s : Statement) (a : Statement.Answer) : Prop :=
  ∃ r ∈ log, ∃ t, retractionOf project s.id r = some t ∧
    Chain project owners log ⟨.retract, a.record⟩ false t

/-- **The answer `s` is accepted**: it is the one statement of the project with its id, and an
answer whose authority traces back for what it does and which no retraction retracts. -/
def Accepted (s : Statement) : Prop :=
  find project log s.id = some s ∧ ∃ a, s.body = .answer a ∧
    Chain project owners log (.ofAnswer a) false a.author ∧ ¬ Retracted project owners log s a

/-! ## The decision -/

/-- The link at `p` acting under the delegation with the id `d`, tested in `Link`'s order: the
grantor when it holds, the first test it fails when not. -/
def link (act : Act) (passed : Bool) (p d : Ident) : Except Broken Authority :=
  match named project log d with
  | [] => .error .unknown
  | _ :: _ :: _ => .error .ambiguous
  | [s] =>
    match s.body with
    | .delegation del =>
      if del.delegate.name ≠ p then .error .notDelegate
      else
        match log.find? (revokes project owners d del.delegator) with
        | some r => .error (.revoked r.id)
        | none =>
          if allows del.scope act = false then .error .outOfScope
          else if passed = true ∧ del.mayPassOn = false then .error .notPassable
          else .ok del.delegator
    | _ => .error .notDelegation

/-- The walk up the chain from `a`, refusing at the first link that breaks. `rest` holds the ids of
the log the walk has not passed, so a link whose id it has passed closes a cycle, and `fuel` is at
least the length of `rest`, so the walk stops. -/
def walk (act : Act) : Nat → List Ident → Bool → Authority → Except (Authority × Broken) Unit
  | _, _, _, ⟨o, none⟩ => if isOwner owners o then .ok () else .error (⟨o, none⟩, .notOwner)
  | fuel, rest, passed, ⟨p, some d⟩ =>
    match link project owners log act passed p d with
    | .error why => .error (⟨p, some d⟩, why)
    | .ok g =>
      match fuel with
      | 0 => .error (⟨p, some d⟩, .cycle)
      | n + 1 =>
        if d ∈ rest then walk act n (rest.filter (· != d)) true g
        else .error (⟨p, some d⟩, .cycle)

/-- Whether the authority `a` traces back for the act `act`, and the first link that breaks when it
does not: the walk from `a` with no id of the log passed. -/
def trace (act : Act) (a : Authority) : Except (Authority × Broken) Unit :=
  walk project owners log act log.length (log.map Statement.id) false a

/-- `trace` as a `Bool`. -/
def traces (act : Act) (a : Authority) : Bool :=
  match trace project owners log act a with
  | .ok _ => true
  | .error _ => false

/-- The first statement of the log that retracts the answer with the id `answer`, on the record
`record`, with authority that traces back. -/
def retractedBy (answer : Ident) (record : String) : Option Statement :=
  log.find? fun r =>
    match retractionOf project answer r with
    | some t => traces project owners log ⟨.retract, record⟩ t
    | none => false

end

/-- Why an answer is refused. -/
inductive Reason where
  /-- It is not the one statement of the project with its id. -/
  | notOne
  /-- It is not an answer. -/
  | notAnswer
  /-- Its chain breaks at the link of the authority `link`, for the reason `why`. -/
  | broken (link : Authority) (why : Broken)
  /-- The statement with the id given retracts it. -/
  | retracted (retraction : Ident)
  deriving DecidableEq

/-- A refusal: the answer refused, by its id, and why. -/
structure Refusal where
  /-- The answer's id. -/
  answer : Ident
  /-- Why it is refused. -/
  reason : Reason
  deriving DecidableEq

section

variable (project : Ident) (owners : Statement.Owners) (log : List Statement)

/-- **The decision** on the statement `s`, given the project, its owners declaration and its log:
`.ok ()` when it accepts it, and the refusal when it does not. -/
def check (s : Statement) : Except Refusal Unit :=
  if find project log s.id ≠ some s then .error ⟨s.id, .notOne⟩
  else
    match s.body with
    | .answer a =>
      match trace project owners log (.ofAnswer a) a.author with
      | .error (b, why) => .error ⟨s.id, .broken b why⟩
      | .ok () =>
        match retractedBy project owners log s.id a.record with
        | some r => .error ⟨s.id, .retracted r.id⟩
        | none => .ok ()
    | _ => .error ⟨s.id, .notAnswer⟩

/-- Every answer of the project in the log, in the log's order, with the decision on it. -/
def checkLog : List (Statement × Except Refusal Unit) :=
  (log.filter fun s => s.project == project && (s.body matches .answer _)).map
    fun s => (s, check project owners log s)

/-- What the reason `r` for refusing the statement `s` states. -/
def Reason.Holds (s : Statement) : Reason → Prop
  | .notOne => find project log s.id ≠ some s
  | .notAnswer => ∀ a, s.body ≠ .answer a
  | .broken b why => ∃ a, s.body = .answer a ∧ ∃ x,
      Leads project owners log (.ofAnswer a) false a.author x b ∧
      Fails project owners log (.ofAnswer a) x b why
  | .retracted i => ∃ a, s.body = .answer a ∧
      Chain project owners log (.ofAnswer a) false a.author ∧
      ∃ r ∈ log, r.id = i ∧ ∃ t, retractionOf project s.id r = some t ∧
        Chain project owners log ⟨.retract, a.record⟩ false t

/-- The authority `a` acts under the delegation of the project that `g` granted: a step up the
chain, with none of the link's tests. -/
def Step (a g : Authority) : Prop :=
  ∃ p d s del, a = ⟨p, some d⟩ ∧ find project log d = some s ∧ s.body = .delegation del ∧
    del.delegator = g

/-- `Reach a b`: steps up the chain lead from `a` to `b`. -/
inductive Reach : Authority → Authority → Prop where
  /-- No step. -/
  | refl {a : Authority} : Reach a a
  /-- A step, then steps. -/
  | step {a b c : Authority} : Step project log a b → Reach b c → Reach a c

/-- Each id of the log that the walk has passed, those not in `rest`, is the id of a link that
held, from whose grantor the walk led to `a`. -/
def Visited (act : Act) (rest : List Ident) (passed : Bool) (a : Authority) : Prop :=
  ∀ d ∈ log.map Statement.id, d ∉ rest → ∃ q y del, Link project owners log act y q d del ∧
    Leads project owners log act true del.delegator passed a

end

/-! ## Links, chains and cycles -/

section Proofs

variable {project : Ident} {owners : Statement.Owners} {log : List Statement}

theorem mem_named {d : Ident} {s : Statement} :
    s ∈ named project log d ↔ s ∈ log ∧ s.project = project ∧ s.id = d := by
  simp [named]

theorem find_eq_some {d : Ident} {s : Statement} :
    find project log d = some s ↔ named project log d = [s] := by
  unfold find
  split <;> simp_all

theorem find_mem {d : Ident} {s : Statement} (h : find project log d = some s) :
    s ∈ log ∧ s.project = project ∧ s.id = d :=
  mem_named.mp (by rw [find_eq_some.mp h]; exact List.mem_singleton_self s)

/-- Two links at the same delegation's id lead to the same delegation. -/
theorem Link.unique {act act' : Act} {passed passed' : Bool} {p p' d : Ident}
    {del del' : Statement.Delegation} (h : Link project owners log act passed p d del)
    (h' : Link project owners log act' passed' p' d del') : del = del' := by
  obtain ⟨⟨s, hs, hb⟩, -⟩ := h
  obtain ⟨⟨s', hs', hb'⟩, -⟩ := h'
  rw [hs] at hs'
  cases hs'
  rw [hb] at hb'
  cases hb'
  rfl

theorem Link.step {act : Act} {passed : Bool} {p d : Ident} {del : Statement.Delegation}
    (h : Link project owners log act passed p d del) :
    Step project log ⟨p, some d⟩ del.delegator := by
  obtain ⟨⟨s, hs, hb⟩, -⟩ := h
  exact ⟨p, d, s, del, rfl, hs, hb, rfl⟩

theorem Step.unique {a g g' : Authority} (h : Step project log a g) (h' : Step project log a g') :
    g = g' := by
  obtain ⟨p, d, s, del, rfl, hs, hb, rfl⟩ := h
  obtain ⟨p', d', s', del', ha, hs', hb', rfl⟩ := h'
  cases ha
  rw [hs] at hs'
  cases hs'
  rw [hb] at hb'
  cases hb'
  rfl

theorem Reach.tail {a b c : Authority} (h : Reach project log a b) (hs : Step project log b c) :
    Reach project log a c := by
  induction h with
  | refl => exact .step hs .refl
  | step h₁ _ ih => exact .step h₁ (ih hs)

/-- A step from `a` to `g` and steps back from `g` to `a` put `g` on a cycle. -/
theorem Reach.cycle {a g : Authority} (hr : Reach project log g a) (hs : Step project log a g) :
    ∃ g', Step project log g g' ∧ Reach project log g' g := by
  cases hr with
  | refl => exact ⟨_, hs, .refl⟩
  | step h₁ h₂ => exact ⟨_, h₁, h₂.tail hs⟩

theorem Leads.reach {act : Act} {x y : Bool} {a b : Authority}
    (h : Leads project owners log act x a y b) : Reach project log a b := by
  induction h with
  | refl => exact .refl
  | link hl _ ih => exact .step hl.step ih

theorem Leads.tail {act : Act} {x y : Bool} {a : Authority} {p d : Ident}
    {del : Statement.Delegation} (h : Leads project owners log act x a y ⟨p, some d⟩)
    (hl : Link project owners log act y p d del) :
    Leads project owners log act x a true del.delegator := by
  generalize hb : (⟨p, some d⟩ : Authority) = b at h
  revert hl
  induction h with
  | refl => intro hl; subst hb; exact .link hl .refl
  | link h₀ _ ih => intro hl; exact .link h₀ (ih hb hl)

/-- **A chain has no cycle.** No authority that traces back steps to an authority from which steps
lead back to it. -/
theorem Chain.no_cycle {act : Act} {x : Bool} {a g : Authority}
    (h : Chain project owners log act x a) (hs : Step project log a g)
    (hr : Reach project log g a) : False := by
  induction h generalizing g with
  | owner =>
    obtain ⟨_, _, _, _, h, -⟩ := hs
    cases h
  | link hl _ ih =>
    obtain ⟨g', h₁, h₂⟩ := hr.cycle hs
    have hg := hs.unique hl.step
    subst hg
    exact ih h₁ h₂

/-- A chain from `a` continues along every link that leads from `a`. -/
theorem Leads.chain {act : Act} {x y : Bool} {a b : Authority}
    (h : Leads project owners log act x a y b) (hc : Chain project owners log act x a) :
    Chain project owners log act y b := by
  induction h with
  | refl => exact hc
  | link hl _ ih =>
    cases hc with
    | link hl' hc' =>
      have := hl.unique hl'
      subst this
      exact ih hc'

/-- Links that lead from `a` to an authority that traces back make `a` trace back. -/
theorem Leads.chain_of {act : Act} {x y : Bool} {a b : Authority}
    (h : Leads project owners log act x a y b) (hc : Chain project owners log act y b) :
    Chain project owners log act x a := by
  induction h with
  | refl => exact hc
  | link hl _ ih => exact .link hl (ih hc)

/-- **A chain is a sequence of links that ends at a declared owner.** The authority `a` traces back
exactly when links that all hold lead from it to a declared owner acting as owner. -/
theorem chain_iff_leads {act : Act} {x : Bool} {a : Authority} :
    Chain project owners log act x a ↔
      ∃ y o, Leads project owners log act x a y ⟨o, none⟩ ∧ isOwner owners o = true := by
  constructor
  · intro h
    induction h with
    | owner ho => exact ⟨_, _, .refl, ho⟩
    | link hl _ ih =>
      obtain ⟨y, o, hle, ho⟩ := ih
      exact ⟨y, o, .link hl hle, ho⟩
  · rintro ⟨y, o, hle, ho⟩
    exact hle.chain_of (.owner ho)

/-- **A link that breaks breaks every chain through it**: no authority whose links lead to it traces
back. -/
theorem Fails.not_chain {act : Act} {x : Bool} {b : Authority} {why : Broken}
    (hf : Fails project owners log act x b why) : ¬ Chain project owners log act x b := by
  intro hc
  cases hf with
  | notOwner h =>
    cases hc with
    | owner h' => rw [h] at h'; cases h'
  | unknown h =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s, hs, -⟩, -⟩ := hl
      rw [find_eq_some, h] at hs
      cases hs
  | ambiguous h =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s, hs, -⟩, -⟩ := hl
      rw [find_eq_some, h] at hs
      cases hs
  | notDelegation hs hb =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s', hs', hb'⟩, -⟩ := hl
      rw [hs] at hs'
      cases hs'
      exact hb _ hb'
  | notDelegate hs hb hp =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s', hs', hb'⟩, hp', -⟩ := hl
      rw [hs] at hs'
      cases hs'
      rw [hb] at hb'
      cases hb'
      exact hp hp'
  | revoked hs hb hr hrev =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s', hs', hb'⟩, -, hno, -⟩ := hl
      rw [hs] at hs'
      cases hs'
      rw [hb] at hb'
      cases hb'
      rw [hno _ hr] at hrev
      cases hrev
  | outOfScope hs hb ha =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s', hs', hb'⟩, -, -, ha', -⟩ := hl
      rw [hs] at hs'
      cases hs'
      rw [hb] at hb'
      cases hb'
      rw [ha] at ha'
      cases ha'
  | notPassable hs hb hp hm =>
    cases hc with
    | link hl _ =>
      obtain ⟨⟨s', hs', hb'⟩, -, -, -, hm'⟩ := hl
      rw [hs] at hs'
      cases hs'
      rw [hb] at hb'
      cases hb'
      rw [hm' hp] at hm
      cases hm
  | cycle hl hle => exact hc.no_cycle hl.step hle.reach

/-- Every link before a link that breaks holds, so the authority they lead from does not trace
back. -/
theorem Leads.not_chain {act : Act} {x y : Bool} {a b : Authority} {why : Broken}
    (hle : Leads project owners log act x a y b) (hf : Fails project owners log act y b why) :
    ¬ Chain project owners log act x a :=
  fun hc => hf.not_chain (hle.chain hc)

/-! ## What the decision decides -/

theorem link_of_Link {act : Act} {passed : Bool} {p d : Ident} {del : Statement.Delegation}
    (h : Link project owners log act passed p d del) :
    link project owners log act passed p d = .ok del.delegator := by
  obtain ⟨⟨s, hs, hb⟩, hp, hr, ha, hpass⟩ := h
  have hf : log.find? (revokes project owners d del.delegator) = none :=
    List.find?_eq_none.mpr fun r hr' => by simp [hr r hr']
  rw [find_eq_some] at hs
  unfold link
  rw [hs]
  simp only [hb, hp, ne_eq, not_true_eq_false, ↓reduceIte, hf, ha]
  cases passed <;> cases hm : del.mayPassOn <;> simp_all

theorem Link_of_link {act : Act} {passed : Bool} {p d : Ident} {g : Authority}
    (h : link project owners log act passed p d = .ok g) :
    ∃ del, Link project owners log act passed p d del ∧ g = del.delegator := by
  unfold link at h
  split at h
  · cases h
  · cases h
  · rename_i s hs
    split at h
    · rename_i del hb
      split at h
      · cases h
      · rename_i hp
        split at h
        · cases h
        · rename_i hf
          split at h
          · cases h
          · rename_i ha
            split at h
            · cases h
            · rename_i hpass
              cases h
              refine ⟨del, ⟨⟨s, find_eq_some.mpr hs, hb⟩, ?_, ?_, ?_, ?_⟩, rfl⟩
              · simpa using hp
              · intro r hr
                simpa using List.find?_eq_none.mp hf r hr
              · simpa using ha
              · intro hp'
                simpa [hp'] using hpass
    · cases h

theorem fails_of_link {act : Act} {passed : Bool} {p d : Ident} {why : Broken}
    (h : link project owners log act passed p d = .error why) :
    Fails project owners log act passed ⟨p, some d⟩ why := by
  unfold link at h
  split at h
  · rename_i hn
    cases h
    exact .unknown hn
  · rename_i hn
    cases h
    exact .ambiguous hn
  · rename_i s hs
    have hs' := find_eq_some.mpr hs
    split at h
    · rename_i del hb
      split at h
      · rename_i hp
        cases h
        exact .notDelegate hs' hb hp
      · split at h
        · rename_i r hf
          cases h
          exact .revoked hs' hb (List.mem_of_find?_eq_some hf) (List.find?_some hf)
        · split at h
          · rename_i ha
            cases h
            exact .outOfScope hs' hb ha
          · split at h
            · rename_i hpass
              cases h
              exact .notPassable hs' hb hpass.1 hpass.2
            · cases h
    · rename_i hb
      cases h
      exact .notDelegation hs' fun del h => hb del h

theorem walk_sound {act : Act} {fuel : Nat} {rest : List Ident} {passed : Bool} {a : Authority}
    (h : walk project owners log act fuel rest passed a = .ok ()) :
    Chain project owners log act passed a := by
  induction fuel generalizing rest passed a with
  | zero =>
    obtain ⟨o, _ | d⟩ := a
    · simp only [walk] at h
      split at h
      · exact .owner ‹_›
      · cases h
    · simp only [walk] at h
      split at h <;> cases h
  | succ n ih =>
    obtain ⟨o, _ | d⟩ := a
    · simp only [walk] at h
      split at h
      · exact .owner ‹_›
      · cases h
    · simp only [walk] at h
      split at h
      · cases h
      · rename_i g hg
        split at h
        · obtain ⟨del, hl, rfl⟩ := Link_of_link hg
          exact .link hl (ih h)
        · cases h

theorem Visited.next {act : Act} {rest : List Ident} {passed : Bool} {p d : Ident}
    {del : Statement.Delegation}
    (hv : Visited project owners log act rest passed ⟨p, some d⟩)
    (hl : Link project owners log act passed p d del) :
    Visited project owners log act (rest.filter (· != d)) true del.delegator := by
  intro d' hd' hn
  by_cases he : d' = d
  · subst he
    exact ⟨p, passed, del, hl, .refl⟩
  · have : d' ∉ rest := fun hm => hn (List.mem_filter.mpr ⟨hm, by simpa using he⟩)
    obtain ⟨q, y, del', hl', hle⟩ := hv d' hd' this
    exact ⟨q, y, del', hl', hle.tail hl⟩

/-- A link whose id the walk has passed closes a cycle: links lead from its grantor back to it. -/
theorem Visited.cycle {act : Act} {rest : List Ident} {passed : Bool} {p d : Ident}
    {del : Statement.Delegation}
    (hv : Visited project owners log act rest passed ⟨p, some d⟩)
    (hl : Link project owners log act passed p d del) (hd : d ∉ rest) :
    Leads project owners log act true del.delegator passed ⟨p, some d⟩ := by
  have hmem : d ∈ log.map Statement.id := by
    obtain ⟨⟨s, hs, -⟩, -⟩ := hl
    obtain ⟨hsl, -, rfl⟩ := find_mem hs
    exact List.mem_map_of_mem hsl
  obtain ⟨q, y, del', hl', hle⟩ := hv d hmem hd
  rw [hl.unique hl']
  exact hle

theorem length_filter_lt {d : Ident} {rest : List Ident} (hd : d ∈ rest) :
    (rest.filter (· != d)).length < rest.length :=
  List.length_filter_lt_length_iff_exists.mpr ⟨d, hd, by simp⟩

theorem walk_complete {act : Act} {passed : Bool} {a : Authority}
    (hc : Chain project owners log act passed a) :
    ∀ {fuel : Nat} {rest : List Ident}, rest.length ≤ fuel →
      Visited project owners log act rest passed a →
      walk project owners log act fuel rest passed a = .ok () := by
  induction hc with
  | owner ho =>
    intro fuel rest _ _
    simp [walk, ho]
  | @link passed p d del hl hc ih =>
    intro fuel rest hlen hv
    have hd : d ∈ rest := by
      by_cases hd : d ∈ rest
      · exact hd
      · exact absurd (hv.cycle hl hd).reach fun hr => (Chain.link hl hc).no_cycle hl.step hr
    cases fuel with
    | zero =>
      rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)] at hd
      cases hd
    | succ n =>
      simp only [walk, link_of_Link hl, hd, ↓reduceIte]
      exact ih (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (length_filter_lt hd) hlen)) (hv.next hl)

theorem walk_error {act : Act} {fuel : Nat} {rest : List Ident} {passed : Bool}
    {a b : Authority} {why : Broken} (hlen : rest.length ≤ fuel)
    (hv : Visited project owners log act rest passed a)
    (h : walk project owners log act fuel rest passed a = .error (b, why)) :
    ∃ x, Leads project owners log act passed a x b ∧ Fails project owners log act x b why := by
  induction fuel generalizing rest passed a with
  | zero =>
    obtain ⟨o, _ | d⟩ := a
    · simp only [walk] at h
      split at h
      · cases h
      · rename_i ho
        cases h
        exact ⟨passed, .refl, .notOwner (by simpa using ho)⟩
    · simp only [walk] at h
      split at h
      · rename_i why' hw
        cases h
        exact ⟨passed, .refl, fails_of_link hw⟩
      · rename_i g hg
        cases h
        obtain ⟨del, hl, rfl⟩ := Link_of_link hg
        have hd : d ∉ rest := by
          rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
          exact List.not_mem_nil
        exact ⟨passed, .refl, .cycle hl (hv.cycle hl hd)⟩
  | succ n ih =>
    obtain ⟨o, _ | d⟩ := a
    · simp only [walk] at h
      split at h
      · cases h
      · rename_i ho
        cases h
        exact ⟨passed, .refl, .notOwner (by simpa using ho)⟩
    · simp only [walk] at h
      split at h
      · rename_i why' hw
        cases h
        exact ⟨passed, .refl, fails_of_link hw⟩
      · rename_i g hg
        obtain ⟨del, hl, rfl⟩ := Link_of_link hg
        split at h
        · rename_i hd
          obtain ⟨x, hle, hf⟩ := ih
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (length_filter_lt hd) hlen)) (hv.next hl) h
          exact ⟨x, .link hl hle, hf⟩
        · rename_i hd
          cases h
          exact ⟨passed, .refl, .cycle hl (hv.cycle hl hd)⟩

theorem visited_start {act : Act} {passed : Bool} {a : Authority} :
    Visited project owners log act (log.map Statement.id) passed a :=
  fun _ hd hn => absurd hd hn

/-- `trace` accepts exactly the authorities that trace back. -/
theorem trace_eq_ok_iff {act : Act} {a : Authority} :
    trace project owners log act a = .ok () ↔ Chain project owners log act false a :=
  ⟨walk_sound, fun h => walk_complete h (by simp) visited_start⟩

/-- `trace` names the first link that breaks: every link before it holds. -/
theorem trace_eq_error {act : Act} {a b : Authority} {why : Broken}
    (h : trace project owners log act a = .error (b, why)) :
    ∃ x, Leads project owners log act false a x b ∧ Fails project owners log act x b why :=
  walk_error (by simp) visited_start h

theorem traces_iff {act : Act} {a : Authority} :
    traces project owners log act a = true ↔ Chain project owners log act false a := by
  rw [← trace_eq_ok_iff]
  unfold traces
  split <;> simp_all

theorem retractedBy_eq_none_iff {answer : Ident} {record : String} :
    retractedBy project owners log answer record = none ↔
      ¬ ∃ r ∈ log, ∃ t, retractionOf project answer r = some t ∧
        Chain project owners log ⟨.retract, record⟩ false t := by
  simp only [retractedBy, List.find?_eq_none]
  constructor
  · rintro h ⟨r, hr, t, ht, hc⟩
    have := h r hr
    rw [ht] at this
    exact this (traces_iff.mpr hc)
  · intro h r hr hp
    apply h
    cases ht : retractionOf project answer r with
    | none => rw [ht] at hp; cases hp
    | some t =>
      rw [ht] at hp
      exact ⟨r, hr, t, ht, traces_iff.mp hp⟩

theorem retractedBy_eq_some {answer : Ident} {record : String} {r : Statement}
    (h : retractedBy project owners log answer record = some r) :
    r ∈ log ∧ ∃ t, retractionOf project answer r = some t ∧
      Chain project owners log ⟨.retract, record⟩ false t := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  cases ht : retractionOf project answer r with
  | none => rw [ht] at hp; cases hp
  | some t =>
    rw [ht] at hp
    exact ⟨t, rfl, traces_iff.mp hp⟩

/-- **What the decision decides.** For every project, owners declaration, log and statement, it
accepts the statement exactly when the statement is an accepted answer: the one statement of the
project with its id, an answer whose authority traces back to a declared owner within the scope of
every delegation on the way, passed on only where each may be, and which no retraction with such
authority retracts. -/
theorem check_eq_ok_iff {s : Statement} :
    check project owners log s = .ok () ↔ Accepted project owners log s := by
  unfold check Accepted Retracted
  by_cases hf : find project log s.id = some s
  · simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
    cases hb : s.body with
    | answer a =>
      simp only [Statement.Body.answer.injEq, exists_eq_left']
      cases ht : trace project owners log (.ofAnswer a) a.author with
      | error e =>
        obtain ⟨b, why⟩ := e
        simp only [reduceCtorEq, false_iff, not_and]
        intro hc
        rw [trace_eq_ok_iff.mpr hc] at ht
        cases ht
      | ok u =>
        have hc := trace_eq_ok_iff.mp ht
        cases hr : retractedBy project owners log s.id a.record with
        | none => simp [hc, retractedBy_eq_none_iff.mp hr]
        | some r =>
          obtain ⟨hmem, t, hrt, hct⟩ := retractedBy_eq_some hr
          simp only [reduceCtorEq, false_iff, not_and, Classical.not_not]
          exact fun _ => ⟨r, hmem, t, hrt, hct⟩
    | _ => simp
  · simp [hf]

/-- **What a refusal says.** Every refusal names the answer refused, and its reason holds: the
statement is not the one statement of the project with its id, or not an answer; or the first link
of its chain that breaks, every link before it holding, and the test it fails; or a retraction that
retracts it with authority that traces back. -/
theorem check_eq_error {s : Statement} {r : Refusal}
    (h : check project owners log s = .error r) :
    r.answer = s.id ∧ r.reason.Holds project owners log s := by
  unfold check at h
  split at h
  · rename_i hf
    cases h
    exact ⟨rfl, hf⟩
  · split at h
    · rename_i a hb
      split at h
      · rename_i b why ht
        cases h
        exact ⟨rfl, a, hb, trace_eq_error ht⟩
      · rename_i ht
        split at h
        · rename_i r' hr
          cases h
          obtain ⟨hmem, t, hrt, hct⟩ := retractedBy_eq_some hr
          exact ⟨rfl, a, hb, trace_eq_ok_iff.mp ht, r', hmem, rfl, t, hrt, hct⟩
        · cases h
    · rename_i hb
      cases h
      exact ⟨rfl, fun a h => hb a h⟩

/-- `checkLog` decides every answer of the project in the log, and nothing else. -/
theorem mem_checkLog {s : Statement} {d : Except Refusal Unit} :
    (s, d) ∈ checkLog project owners log ↔
      s ∈ log ∧ s.project = project ∧ (∃ a, s.body = .answer a) ∧
        d = check project owners log s := by
  simp only [checkLog, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨s', ⟨hs', hp, hb⟩, rfl, rfl⟩
    refine ⟨hs', hp, ?_, rfl⟩
    revert hb
    cases s'.body <;> simp
  · rintro ⟨hs, hp, ⟨a, hb⟩, rfl⟩
    exact ⟨s, ⟨hs, hp, by simp [hb]⟩, rfl, rfl⟩

/-! ## Monotonicity, where it holds -/

/-- **A statement that is no revocation, added with a fresh id, keeps every chain.** Delegations,
answers, retractions and owners declarations added to the log, none with an id a statement of the
log has, take no authority away. -/
theorem Chain.append_fresh {act : Act} {x : Bool} {a : Authority} {more : List Statement}
    (hfresh : ∀ t ∈ more, t.project = project → t.id ∉ log.map Statement.id)
    (hrev : ∀ t ∈ more, ∀ v, t.body ≠ .revocation v)
    (h : Chain project owners log act x a) : Chain project owners (log ++ more) act x a := by
  induction h with
  | owner ho => exact .owner ho
  | @link passed p d del hl _ ih =>
    obtain ⟨⟨s, hs, hb⟩, hp, hr, ha, hpass⟩ := hl
    refine .link ⟨⟨s, ?_, hb⟩, hp, ?_, ha, hpass⟩ ih
    · have hmore : named project more d = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
        obtain ⟨htm, htp, hti⟩ := mem_named.mp ht
        obtain ⟨hsl, -, hsid⟩ := find_mem hs
        exact hfresh t htm htp (List.mem_map.mpr ⟨s, hsl, hsid.trans hti.symm⟩)
      rw [find_eq_some] at hs ⊢
      simp only [named, List.filter_append] at hs hmore ⊢
      rw [hs, hmore]
      rfl
    · intro r hr'
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact hr r hr'
      · unfold revokes
        cases hrb : r.body with
        | revocation v => exact absurd hrb (hrev r hr' v)
        | _ => simp

/-- **A statement that is no delegation makes no chain.** A chain in the log with statements added,
none a delegation, is a chain in the log: revocations, retractions, answers and owners declarations
grant no authority, and a revocation only removes it. -/
theorem Chain.of_append {act : Act} {x : Bool} {a : Authority} {more : List Statement}
    (hdel : ∀ t ∈ more, ∀ del, t.body ≠ .delegation del)
    (h : Chain project owners (log ++ more) act x a) : Chain project owners log act x a := by
  induction h with
  | owner ho => exact .owner ho
  | link hl _ ih =>
    obtain ⟨⟨s, hs, hb⟩, hp, hr, ha, hpass⟩ := hl
    refine .link ⟨⟨s, ?_, hb⟩, hp, fun r hr' => hr r (List.mem_append_left _ hr'), ha, hpass⟩ ih
    rw [find_eq_some] at hs ⊢
    simp only [named, List.filter_append] at hs ⊢
    rcases List.append_eq_singleton_iff.mp hs with ⟨-, hm⟩ | ⟨hl', -⟩
    · have : s ∈ [s] := List.mem_singleton_self s
      rw [← hm] at this
      exact absurd hb (hdel s (List.mem_filter.mp this).1 _)
    · exact hl'

/-- **A retraction added with a fresh id accepts no answer the log refused.** -/
theorem Accepted.of_append_retractions {s : Statement} {more : List Statement}
    (hret : ∀ t ∈ more, ∃ r, t.body = .retraction r)
    (hfresh : ∀ t ∈ more, t.project = project → t.id ∉ log.map Statement.id)
    (h : Accepted project owners (log ++ more) s) : Accepted project owners log s := by
  obtain ⟨hf, a, hb, hc, hnr⟩ := h
  have hdel : ∀ t ∈ more, ∀ del, t.body ≠ .delegation del := fun t ht del he => by
    obtain ⟨r, hr⟩ := hret t ht
    rw [hr] at he
    cases he
  have hrev : ∀ t ∈ more, ∀ v, t.body ≠ .revocation v := fun t ht v he => by
    obtain ⟨r, hr⟩ := hret t ht
    rw [hr] at he
    cases he
  refine ⟨?_, a, hb, hc.of_append hdel, ?_⟩
  · rw [find_eq_some] at hf ⊢
    simp only [named, List.filter_append] at hf ⊢
    rcases List.append_eq_singleton_iff.mp hf with ⟨-, hm⟩ | ⟨hl', -⟩
    · have hs : s ∈ [s] := List.mem_singleton_self s
      rw [← hm] at hs
      obtain ⟨r, hr⟩ := hret s (List.mem_filter.mp hs).1
      rw [hr] at hb
      cases hb
    · exact hl'
  · rintro ⟨r, hr, t, ht, hct⟩
    exact hnr ⟨r, List.mem_append_left _ hr, t, ht, hct.append_fresh hfresh hrev⟩

end Proofs

end Trace

end LeanIntent
