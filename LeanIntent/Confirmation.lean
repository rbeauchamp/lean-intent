import LeanIntent.Explain
import LeanIntent.Trace

/-!
# The check that a project's deliverables are confirmed

A consequence counts as confirmed only when a declared owner confirmed it, or a party acting under
a delegation that traces back to one; an agent marking its own specification confirmed would remove
the one check no proof replaces. A project keeps its statements in its owners' log (`OwnersLog`) and
declares each deliverable (`Deliverable`): a record, its explanation, with who settled each thing
(`Restatement`, `Settled`), the answers it keeps, with who gave each (`Attributed`), and the proof
that the record keeps them. Those values are ones a project writes. This module decides, from them
and the log and nothing a caller chooses, whether they agree and the current revision of every
deliverable is confirmed, and says why when it is not.

* **The owners** are read from the log (`Declares`): it holds exactly one owners declaration, which
  names at least one principal, every statement of the log belongs to that declaration's project, and
  no two statements share an id (`Confirmed.nodup`). So no caller supplies who the owners are, and a
  log with no owner declared passes nothing.
* **An answer counts** (`Counts`) exactly when `LeanIntent.Trace` accepts it, by the owners so
  declared, which is exactly when it traces back to a declared owner within the scope of every
  delegation on the way (`counts_iff`, `Trace.check_eq_ok_iff`), for every log and statement. So the
  check accepts every confirmation that traces back and refuses every other. Separately, each answer
  that counts must record its source, so one that records none is a finding of the log.
* **A revision** (`Revision`) is what the current build shows: the record's name, the text of its
  rendering with no word of who settled what, the recorded standing of its restatement, the
  consequences shown with their statuses, and the answers kept, each consequence with the text of
  its predicate's whole meaning. An answer answers a question of the revision (`answersNow`) only
  when it names that exact text, so an answer for an older revision answers nothing, and a
  definition changed under an unchanged name changes the text.
* **A revision is confirmed** (`Revision.Confirmed`) when:
  - its plain restatement (`restatement`) has an answer that counts and confirms it at this revision,
    by the owner its `Restatement` names, or, where it records none, by a delegate and no owner; and
    none that counts declines it. Every revision asks this, so one that shows no consequence, or
    whose every consequence is derived, still needs that confirmation;
  - each consequence shown has a status that holds (`Settles`): answered and confirmed, by the
    answerer it names, at this revision; or derived, which the type allows only where the restatement
    stands as an owner's, with no answer at this revision. A fork, or a consequence not settled, does
    not pass, and neither does one an answer that counts declines;
  - each answer it keeps is backed by an answer that counts, by the answerer it names, at any
    revision, with the same text and verdict; and each answer that counts on its record, but a
    restatement, is one it keeps. So a deliverable cannot quietly drop a requirement: an answer stops
    being one only when someone with authority retracts it.
* **Each status agrees with the answers it keeps** (`Revision.Agrees`): one that records an answer
  names one of them, by the same answerer with the same verdict, and one recorded as derived, which
  says no one answered it, names no consequence one of them answers.
* **The decision** (`findings`) lists everything wrong, and is empty exactly when the deliverables
  are confirmed (`findings_eq_nil_iff`); each finding states what holds (`findings_sound`).
* **The standing the log gives** (`standing`, `checked`): a status printed from these reads a
  confirmation only where the log holds one of this revision, so a record revised after its owner
  confirmed it stops printing as confirmed, whatever value it still holds (`standing_of_older`).

A status is a field of a consequence the explanation shows, so a status of a consequence the revision
no longer has does not exist; an answer in the log to such a consequence still counts, and must be
kept or retracted.

The decisions this module makes, each on the owner's behalf:

* A refused answer does not count, and is reported (`Report.decisions`), but it does not stop the
  deliverable being confirmed by answers that do count. A check that failed on any refused answer
  would refuse answers that trace back, and would let any bad entry hold a project's confirmations.
* Authority is read as the log now stands, whatever the dates. **A delegation revoked or removed, or
  an owner removed from the declaration, after an answer was recorded**, takes the answer's authority
  with it: it stops counting, and the check refuses until someone with authority answers again. A
  date is what its author wrote, so a rule that kept an answer because of its date would let the date
  keep an authority the project has withdrawn; refusing costs one answer given again.
* **Of several owners, one confirming is enough**, as `Trace` reads every owner's authority alike; a
  project that wants more says so by its own review, or by signatures (lean-intent #19).
* A declined consequence of the current revision stops the deliverable, since each consequence shown
  holds of it by proof: the record must change.
* A log with several owners declarations is refused, and owners change by a reviewed edit of the one
  declaration. A declaration names no author, and only signatures (lean-intent #19) could settle
  which of several is in force.
* **A log that repeats a statement's id is refused**, naming each id it repeats. `Trace` refuses an
  answer whose id another statement shares, and breaks a link to a delegation whose id another
  shares, so an unrelated statement could otherwise make an answer refuse and so drop out of what is
  checked: an owner's decline would no longer stop the deliverable, with no retraction by anyone with
  authority. Refusing costs one id renamed.

What this module does not establish: that a statement's author made it, which review of the change
that commits it checks, and a dishonest agent could invent an answer, which the history would show;
that a consequence recorded as derived truly follows from the restatement, so an agent could record
a real fork as derived, which the committed history shows; that the texts of a `Revision` are those
of the current build, which `LeanIntent.Confirmation.Read` computes from Lean's environment; and that
a rendering's text determines its meaning, which `LeanIntent.Render` lists as what it trusts.
-/

namespace LeanIntent

universe u

/-- A deliverable a project declares: an intent record, its explanation, the answers it keeps with
who gave each, and the proof that the record keeps them. The constants of this type are the
project's deliverables, so a revision that breaks a kept answer is no value of it. -/
structure Deliverable (W : Type u) where
  /-- The current revision of the record. -/
  record : IntentRecord W
  /-- Its explanation, whose consequences are those to settle. -/
  explanation : Explanation record
  /-- The answers it keeps: every answer of the log that counts on this record, but a restatement. -/
  answers : List (Attributed W)
  /-- The record keeps them. -/
  keeps : Keeps record (answers.map (·.answer))

/-- A project's owners' log: the text of each statement, as `Statement.print` writes it. The constant
of this type is what the project commits, in a Lean module of its own, so that a check reads the same
text from the finished build. -/
structure OwnersLog where
  /-- The text of each statement. -/
  statements : List String

/-- What a source says. -/
def Source.text : Source → String
  | .words t | .reference t => t

/-- A source that says something. -/
def Source.recorded (s : Source) : Bool :=
  s.text.toList.any (!·.isWhitespace)

namespace Confirmation

/-- A question a revision asks: a consequence, with the text of its predicate's meaning. -/
structure Question where
  /-- The consequence's name. -/
  consequence : String
  /-- Whether it is shown as entailed or as possible. -/
  kind : Consequence.Kind
  /-- The text of what its predicate means (`LeanIntent.Render.consequenceText`). -/
  predicate : String
  deriving DecidableEq

/-- The question every revision asks: whether its rendering, as it stands, is the plain restatement
of the owner's intent. Its predicate is this fixed text, which no consequence's text is. -/
def restatement : Question :=
  ⟨"the record's plain restatement", .entailment, "the record, as its revision prints it"⟩

/-- A deliverable's current revision, as the build shows it. -/
structure Revision where
  /-- The record's name. -/
  record : String
  /-- The text of its rendering, saying nothing of who settled what
  (`LeanIntent.Render.revisionText`). -/
  text : String
  /-- The standing the explanation records for its restatement. -/
  standing : Restatement
  /-- The consequences its explanation shows, each with the status it records. -/
  shown : List (Question × Settled standing)
  /-- The answers it keeps, each with who it records as giving it. -/
  kept : List (Question × Verdict × Answerer)

/-- The answer `a` is to the question `q`. -/
def Question.names (q : Question) (a : Statement.Answer) : Bool :=
  a.consequence == q.consequence && a.kind == q.kind && a.predicate == q.predicate

/-- The answer `a` answers the question `q` of the revision `rev`: it names the record, the
revision's exact text and the question. An answer to an older revision does not. -/
def Revision.answersNow (rev : Revision) (q : Question) (a : Statement.Answer) : Bool :=
  a.record == rev.record && a.revision == rev.text && q.names a

/-- The answer `a` backs a kept answer to `q` with the verdict `v`, of the revision `rev`: it names
the record and the question, with the same text and verdict, at any revision. -/
def Revision.backs (rev : Revision) (q : Question) (v : Verdict) (a : Statement.Answer) : Bool :=
  a.record == rev.record && q.names a && a.verdict == v

/-- The answerer the statement `s`, stating the answer `a`, shows: its author, for the reason its
source gives. -/
def answererOf (s : Statement) (a : Statement.Answer) : Answerer :=
  a.author.answerer s.source.text

/-- The owners declarations of a log. -/
def declarations (log : List Statement) : List (Statement × Statement.Owners) :=
  log.filterMap fun s => match s.body with | .owners o => some (s, o) | _ => none

/-- The log `log` declares the owners `o` of the project `p`: exactly one declaration, which names at
least one principal, every statement of the log is of that project, and no two share an id. -/
def Declares (log : List Statement) (p : Ident) (o : Statement.Owners) : Prop :=
  (∃ s, declarations log = [(s, o)] ∧ s.project = p) ∧ o.principals ≠ [] ∧
    (∀ s ∈ log, s.project = p) ∧ (log.map (·.id)).Nodup

section

variable (p : Ident) (o : Statement.Owners) (log : List Statement)

/-- **The statement `s` counts**: `Trace` accepts it, so it is an answer whose authority traces back
to a declared owner and which no retraction with authority retracts. -/
def Counts (s : Statement) : Prop := Trace.Accepted p o log s

/-- `Counts`, decided. -/
def counts (s : Statement) : Bool :=
  match Trace.check p o log s with | .ok _ => true | .error _ => false

/-- An answer that counts meets `test`, which reads the statement and its answer. -/
def AnswerWhere (test : Statement → Statement.Answer → Prop) : Prop :=
  ∃ s ∈ log, Counts p o log s ∧ ∃ a, s.body = .answer a ∧ test s a

/-- The status `x` of the question `q` holds of the revision `rev`: answered and confirmed, by the
answerer it names, at this revision; or derived, with no answer at this revision. A status that
declines, a fork and a consequence not settled do not pass. -/
def Revision.Settles (rev : Revision) (q : Question) {s : Restatement} : Settled s → Prop
  | .answered ans .confirmed => AnswerWhere p o log fun t a =>
      rev.answersNow q a = true ∧ a.verdict = .confirmed ∧ answererOf t a = ans
  | .derived => ¬ AnswerWhere p o log fun _ a => rev.answersNow q a = true
  | _ => False

/-- The recorded standing `s` of the restatement of the revision `rev` holds: a confirmation of this
revision by the owner it names; or, where it names none, by a delegate, and by no owner. -/
def Revision.Stands (rev : Revision) : Restatement → Prop
  | .confirmed n => AnswerWhere p o log fun _ a =>
      rev.answersNow restatement a = true ∧ a.verdict = .confirmed ∧ a.author = ⟨n, none⟩
  | .unconfirmed =>
      (AnswerWhere p o log fun _ a =>
        rev.answersNow restatement a = true ∧ a.verdict = .confirmed) ∧
      ¬ AnswerWhere p o log fun _ a =>
        rev.answersNow restatement a = true ∧ a.verdict = .confirmed ∧ a.author.delegation = none

/-- The status `x` of the question `q` agrees with the answers the revision `rev` keeps: an answer it
records is one of them, and one it records as derived, which says no one answered it, is one none of
them answers. -/
def Revision.Agrees (rev : Revision) (q : Question) {s : Restatement} : Settled s → Prop
  | .answered ans v => (q, v, ans) ∈ rev.kept
  | .derived => ∀ k ∈ rev.kept, k.1 ≠ q
  | _ => True

/-- **The revision `rev` is confirmed.** Its restatement stands as recorded, and each consequence
shown is settled as recorded, with no answer that counts declining either at this revision; each
answer it keeps is backed by an answer that counts, by the answerer it names; each answer that counts
on its record, but a restatement, is one it keeps; and each status agrees with the answers it keeps. -/
def Revision.Confirmed (rev : Revision) : Prop :=
  rev.Stands p o log rev.standing ∧
  (¬ AnswerWhere p o log fun _ a =>
    rev.answersNow restatement a = true ∧ a.verdict = .declined) ∧
  (∀ x ∈ rev.shown, rev.Settles p o log x.1 x.2 ∧
    ¬ AnswerWhere p o log fun _ a => rev.answersNow x.1 a = true ∧ a.verdict = .declined) ∧
  (∀ k ∈ rev.kept, AnswerWhere p o log fun t a =>
    rev.backs k.1 k.2.1 a = true ∧ answererOf t a = k.2.2) ∧
  (∀ s ∈ log, Counts p o log s → ∀ a, s.body = .answer a → a.record = rev.record →
    restatement.names a = false → ∃ k ∈ rev.kept, rev.backs k.1 k.2.1 a = true) ∧
  (∀ x ∈ rev.shown, rev.Agrees x.1 x.2)

end

/-- **The deliverables are confirmed**: the log declares the project's owners, there is at least one
deliverable, each answer that counts records its source, and the current revision of each deliverable
is confirmed. -/
def Confirmed (log : List Statement) (revs : List Revision) : Prop :=
  ∃ p o, Declares log p o ∧ revs ≠ [] ∧ (∀ s ∈ log, Counts p o log s → s.source.recorded = true) ∧
    ∀ rev ∈ revs, rev.Confirmed p o log

/-- What is wrong with a project's confirmations. -/
inductive Finding where
  /-- The project has no owners' log. -/
  | noLog
  /-- The project has several owners' logs, named. -/
  | severalLogs (names : List String)
  /-- The statement at this position of the log is not a text `Statement.print` writes. -/
  | unreadable (index : Nat)
  /-- The log declares no owner. -/
  | noOwners
  /-- The log holds several owners declarations, named. -/
  | severalOwners (ids : List Ident)
  /-- The statement named belongs to another project than the owners declaration. -/
  | foreign (id : Ident)
  /-- More than one statement of the log has this id. -/
  | repeated (id : Ident)
  /-- The project declares no deliverable. -/
  | noDeliverable
  /-- This answer counts and records no source. -/
  | sourceless (answer : Ident)
  /-- The recorded confirmation or answer does not hold at the current revision. The statements
  `older` answer this question at other text; the statements `refused` name the current text and do
  not count. -/
  | unanswered (record consequence : String) (older : List Ident) (refused : List Ident)
  /-- Answers that count decline this question at the current revision. -/
  | declined (record consequence : String) (answers : List Ident)
  /-- The explanation records no owner's confirmation of the restatement, and these answers that
  count are one, of the current revision. -/
  | ownerUnrecorded (record : String) (answers : List Ident)
  /-- A status of this consequence says what the log does not: that an answer declined it, or, for a
  derived one, that no one answered it, where these answers do. -/
  | statusDisagrees (record consequence : String) (answers : List Ident)
  /-- This consequence is a fork for the owner to decide. -/
  | fork (record consequence : String)
  /-- No answer that counts backs this kept answer, by the answerer it names; the statements `stale`
  name its consequence with another text, verdict or answerer, or do not count. -/
  | unbacked (record consequence : String) (stale : List Ident)
  /-- This answer counts on the record, and the deliverable does not keep it. -/
  | unkept (record : String) (answer : Ident)
  /-- This consequence's status says what the answers the deliverable keeps do not: it names an answer
  none of them is, or says no one answered it where one of them does. -/
  | keptDisagrees (record consequence : String)
  /-- This value of the project says who settled something, and no deliverable holds it, so nothing
  here asks whether the log agrees. -/
  | undeclared (name : String)
  deriving DecidableEq

section

variable (p : Ident) (o : Statement.Owners) (log : List Statement)

/-- The statements of the log whose answer meets `test`, with the answer. -/
def answersWhere (test : Statement.Answer → Bool) : List (Statement × Statement.Answer) :=
  log.filterMap fun s => match s.body with
    | .answer a => if test a then some (s, a) else none
    | _ => none

/-- The answers that count and answer `q` of the revision `rev`. -/
def countedNow (rev : Revision) (q : Question) : List (Statement × Statement.Answer) :=
  (answersWhere log (rev.answersNow q)).filter fun x => counts p o log x.1

/-- The ids of a list of statements with their answers. -/
def idsOf (l : List (Statement × Statement.Answer)) : List Ident := l.map (·.1.id)

/-- That the question `q` of the revision `rev` has no answer that holds. -/
def unansweredFinding (rev : Revision) (q : Question) : Finding :=
  .unanswered rev.record q.consequence
    (idsOf (answersWhere log fun a =>
      a.record == rev.record && a.consequence == q.consequence && !rev.answersNow q a))
    (idsOf ((answersWhere log (rev.answersNow q)).filter fun x => !counts p o log x.1))

/-- The answers among `c` that decline. -/
def decliners (c : List (Statement × Statement.Answer)) : List (Statement × Statement.Answer) :=
  c.filter fun x => x.2.verdict == .declined

/-- What is wrong with the restatement of the revision `rev`, given its recorded standing `s`. -/
def restatementFindings (rev : Revision) (s : Restatement) : List Finding :=
  let c := countedNow p o log rev restatement
  let d := decliners c
  let owners := c.filter fun x => x.2.verdict == .confirmed && x.2.author.delegation == none
  if d.isEmpty then
    match s with
    | .confirmed n =>
      if c.any (fun x => x.2.verdict == .confirmed && x.2.author == ⟨n, none⟩) then []
      else [unansweredFinding p o log rev restatement]
    | .unconfirmed =>
      if owners.isEmpty then
        if c.any fun x => x.2.verdict == .confirmed then []
        else [unansweredFinding p o log rev restatement]
      else [.ownerUnrecorded rev.record (idsOf owners)]
  else [.declined rev.record restatement.consequence (idsOf d)]

/-- What is wrong with the status `x` of the question `q` of the revision `rev`. -/
def statusFindings (rev : Revision) (q : Question) {s : Restatement} (x : Settled s) :
    List Finding :=
  let c := countedNow p o log rev q
  let d := decliners c
  if d.isEmpty then
    match x with
    | .answered ans .confirmed =>
      if c.any (fun y => y.2.verdict == .confirmed && answererOf y.1 y.2 == ans) then []
      else [unansweredFinding p o log rev q]
    | .answered _ .declined => [.statusDisagrees rev.record q.consequence []]
    | .derived =>
      if c.isEmpty then [] else [.statusDisagrees rev.record q.consequence (idsOf c)]
    | .fork => [.fork rev.record q.consequence]
    | .unsettled => [unansweredFinding p o log rev q]
  else [.declined rev.record q.consequence (idsOf d)]

/-- What is wrong with the kept answer `k` of the revision `rev`. -/
def keptFindings (rev : Revision) (k : Question × Verdict × Answerer) : List Finding :=
  if ((answersWhere log (rev.backs k.1 k.2.1)).filter fun x => counts p o log x.1).any
      (fun x => answererOf x.1 x.2 == k.2.2) then []
  else
    [.unbacked rev.record k.1.consequence (idsOf (answersWhere log fun a =>
      a.record == rev.record && a.consequence == k.1.consequence))]

/-- What is wrong with the answers that count on the record of the revision `rev`: those it does not
keep. -/
def unkeptFindings (rev : Revision) : List Finding :=
  ((answersWhere log fun a => a.record == rev.record && !restatement.names a &&
      !rev.kept.any fun k => rev.backs k.1 k.2.1 a).filter fun x => counts p o log x.1).map
    fun x => .unkept rev.record x.1.id

/-- The answers of the log that count and record no source. -/
def sourcelessFindings : List Finding :=
  ((log.filter fun s => counts p o log s).filter fun s => !s.source.recorded).map
    fun s => .sourceless s.id

/-- What is wrong with the status `x` of the question `q` of the revision `rev`, against the answers
it keeps. -/
def agreeFindings (rev : Revision) (q : Question) {s : Restatement} : Settled s → List Finding
  | .answered ans v =>
    if (q, v, ans) ∈ rev.kept then [] else [.keptDisagrees rev.record q.consequence]
  | .derived => if ∀ k ∈ rev.kept, k.1 ≠ q then [] else [.keptDisagrees rev.record q.consequence]
  | _ => []

/-- What is wrong with the revision `rev`. -/
def revisionFindings (rev : Revision) : List Finding :=
  restatementFindings p o log rev rev.standing ++
    rev.shown.flatMap (fun x => statusFindings p o log rev x.1 x.2) ++
    rev.kept.flatMap (keptFindings p o log rev) ++ unkeptFindings p o log rev ++
    rev.shown.flatMap (fun x => agreeFindings rev x.1 x.2)

end

/-- A finding for each id more than one statement of the log has, once. -/
def repeatedFindings (log : List Statement) : List Finding :=
  let ids := log.map (·.id)
  ((ids.filter fun i => 2 ≤ ids.count i).eraseDups).map .repeated

/-- The owners in force: the project and the declaration, or what is wrong with the log. -/
def inForce (log : List Statement) : Except (List Finding) (Ident × Statement.Owners) :=
  match declarations log with
  | [] => .error (.noOwners :: repeatedFindings log)
  | [(s, o)] =>
    let refused :=
      (log.filter fun t => t.project != s.project).map (fun t => Finding.foreign t.id) ++
        repeatedFindings log
    if o.principals.isEmpty then .error (.noOwners :: refused)
    else if refused.isEmpty then .ok (s.project, o)
    else .error refused
  | ds => .error (.severalOwners (ds.map (·.1.id)) :: repeatedFindings log)

/-- **The decision**: everything wrong with the project's confirmations. -/
def findings (log : List Statement) (revs : List Revision) : List Finding :=
  match inForce log with
  | .error fs => fs
  | .ok (p, o) =>
    if revs.isEmpty then [.noDeliverable]
    else sourcelessFindings p o log ++ revs.flatMap (revisionFindings p o log)

/-! ## Reading the log -/

/-- The statements of a log's texts, or `none` when `Statement.parse` refuses one. -/
def parseAll : List String → Option (List Statement)
  | [] => some []
  | t :: ts => (Statement.parse t).bind fun s => (parseAll ts).map (s :: ·)

/-- A finding for each text `Statement.parse` refuses, by its position, counted from `n`. -/
def unreadableFrom (n : Nat) : List String → List Finding
  | [] => []
  | t :: ts =>
    (if (Statement.parse t).isNone then [.unreadable n] else []) ++ unreadableFrom (n + 1) ts

/-- The statements of a log's texts, or the positions of those `Statement.parse` refuses. A log with
a text it refuses is refused whole: the text could be a revocation. -/
def parseLog (texts : List String) : Except (List Finding) (List Statement) :=
  match parseAll texts with
  | some log => .ok log
  | none => .error (unreadableFrom 0 texts)

/-! ## What a checker reads -/

/-- The origins of a log, each with whether its adoption traces back to a declared owner, as
confirming a consequence of its record would. -/
def origins (p : Ident) (o : Statement.Owners) (log : List Statement) :
    List (Statement × Statement.Origin × Bool) :=
  log.filterMap fun s => match s.body with
    | .origin x => some (s, x, Trace.traces p o log ⟨.confirm, x.record⟩ x.author)
    | _ => none

/-- A log's statements of what an external tool did, or of what is open, for a consequence. -/
def tools (log : List Statement) : List (Statement × Statement.ToolBasis) :=
  log.filterMap fun s => match s.body with | .tool t => some (s, t) | _ => none

/-- Everything a checker reads of a project's confirmations. -/
structure Report where
  /-- What is wrong: of `report`, empty exactly when the deliverables are confirmed
  (`report_findings`), and of what `LeanIntent.Confirmation.Read.check` returns, also only when no
  value saying who settled something stands outside them (`Report.withUndeclared_findings`). -/
  findings : List Finding
  /-- Each answer of the project, with `Trace`'s decision on it. -/
  decisions : List (Statement × Except Trace.Refusal Unit)
  /-- The answers that count. One whose author acts under a delegation is a decision made on the
  owner's behalf; one whose author acts as owner is a declared owner's (`Counts.as_owner`). -/
  counted : List (Statement × Statement.Answer)
  /-- The origins of the records' sources. -/
  origins : List (Statement × Statement.Origin × Bool)
  /-- What external tools did for consequences, or what is open. -/
  tools : List (Statement × Statement.ToolBasis)

/-- **What a checker reads**, given the texts of the log and the current revisions. -/
def report (texts : List String) (revs : List Revision) : Report :=
  match parseLog texts with
  | .error fs => ⟨fs, [], [], [], []⟩
  | .ok log =>
    match inForce log with
    | .error fs => ⟨fs, [], [], [], tools log⟩
    | .ok (p, o) =>
      ⟨findings log revs, Trace.checkLog p o log,
        (answersWhere log fun _ => true).filter fun x => counts p o log x.1,
        origins p o log, tools log⟩

/-- The report `r`, with a finding for each value named that says who settled something and that no
deliverable holds. -/
def Report.withUndeclared (r : Report) (names : List String) : Report :=
  { r with findings := names.map Finding.undeclared ++ r.findings }

/-- Those findings stop the report passing, and nothing else changes what it finds. -/
theorem Report.withUndeclared_findings {r : Report} {names : List String} :
    (r.withUndeclared names).findings = [] ↔ names = [] ∧ r.findings = [] := by
  simp [withUndeclared]

/-! ## The standing the log gives -/

section

variable (p : Ident) (o : Statement.Owners) (log : List Statement)

/-- The standing the log gives the restatement of the revision `rev`: an owner's confirmation of this
revision that counts, or none. -/
def logStanding (rev : Revision) : Restatement :=
  match (countedNow p o log rev restatement).find? (fun x =>
      x.2.verdict == .confirmed && x.2.author.delegation == none) with
  | some x => .confirmed x.2.author.principal
  | none => .unconfirmed

/-- A consequence derived from the standing `t`, where it allows one. -/
def derivedAt : (t : Restatement) → Settled t
  | .confirmed _ => .derived
  | .unconfirmed => .unsettled

/-- The status `x` of the question `q` of the revision `rev`, as the log holds it: an answer stays
only when the log holds it at this revision, and a derived one only with no answer and an owner's
confirmation of this revision. What is printed from this says nothing the log does not hold. -/
def checked (rev : Revision) (q : Question) {s : Restatement} (x : Settled s) :
    Settled (logStanding p o log rev) :=
  match x with
  | .answered ans v =>
    if (countedNow p o log rev q).any (fun y => y.2.verdict == v && answererOf y.1 y.2 == ans) then
      .answered ans v
    else .unsettled
  | .derived => if (countedNow p o log rev q).isEmpty then derivedAt _ else .unsettled
  | .fork => .fork
  | .unsettled => .unsettled

end

/-! ## What the decision decides -/

section Proofs

variable {p : Ident} {o : Statement.Owners} {log : List Statement}

theorem counts_iff {s : Statement} : counts p o log s = true ↔ Counts p o log s := by
  unfold counts Counts
  rw [← Trace.check_eq_ok_iff]
  cases Trace.check p o log s <;> simp

theorem mem_answersWhere {test : Statement.Answer → Bool} {s : Statement} {a : Statement.Answer} :
    (s, a) ∈ answersWhere log test ↔ s ∈ log ∧ s.body = .answer a ∧ test a = true := by
  simp only [answersWhere, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, h⟩
    cases hb : t.body with
    | answer b =>
      simp only [hb] at h
      split at h
      · cases h
        exact ⟨ht, hb, ‹_›⟩
      · cases h
    | _ => simp [hb] at h
  · rintro ⟨hs, hb, ht⟩
    exact ⟨s, hs, by simp [hb, ht]⟩

theorem mem_counted {test : Statement.Answer → Bool} {s : Statement} {a : Statement.Answer} :
    (s, a) ∈ (answersWhere log test).filter (fun x => counts p o log x.1) ↔
      s ∈ log ∧ s.body = .answer a ∧ test a = true ∧ Counts p o log s := by
  simp only [List.mem_filter, mem_answersWhere, counts_iff, and_assoc]

/-- An answer that counts and meets `T` exists exactly when the search the decision makes finds one. -/
theorem any_counted {test : Statement.Answer → Bool} {v : Statement → Statement.Answer → Bool}
    {T : Statement → Statement.Answer → Prop} (hT : ∀ s a, v s a = true ↔ T s a) :
    (((answersWhere log test).filter fun x => counts p o log x.1).any fun x => v x.1 x.2) = true ↔
      AnswerWhere p o log fun s a => test a = true ∧ T s a := by
  simp only [List.any_eq_true, Prod.exists, mem_counted, hT, AnswerWhere]
  constructor
  · rintro ⟨s, a, ⟨hs, hb, ht, hc⟩, hv⟩
    exact ⟨s, hs, hc, a, hb, ht, hv⟩
  · rintro ⟨s, hs, hc, a, hb, ht, hv⟩
    exact ⟨s, a, ⟨hs, hb, ht, hc⟩, hv⟩

theorem decliners_isEmpty {rev : Revision} {q : Question} :
    (decliners (countedNow p o log rev q)).isEmpty = true ↔
      ¬ AnswerWhere p o log fun _ a => rev.answersNow q a = true ∧ a.verdict = .declined := by
  have h := any_counted (p := p) (o := o) (log := log) (test := rev.answersNow q)
    (v := fun _ a => a.verdict == .declined) (T := fun _ a => a.verdict = .declined)
    (fun _ _ => by simp)
  rw [← h]
  simp only [decliners, countedNow, List.isEmpty_iff, List.filter_eq_nil_iff, List.any_eq_true,
    not_exists, not_and, Bool.not_eq_true]

theorem restatementFindings_eq_nil_iff {rev : Revision} {s : Restatement} :
    restatementFindings p o log rev s = [] ↔
      rev.Stands p o log s ∧
        ¬ AnswerWhere p o log fun _ a =>
          rev.answersNow restatement a = true ∧ a.verdict = .declined := by
  have hDec := decliners_isEmpty (p := p) (o := o) (log := log) (rev := rev) (q := restatement)
  have hyes := any_counted (p := p) (o := o) (log := log) (test := rev.answersNow restatement)
    (v := fun _ a => a.verdict == .confirmed) (T := fun _ a => a.verdict = .confirmed)
    (fun _ _ => by simp)
  have howner := any_counted (p := p) (o := o) (log := log) (test := rev.answersNow restatement)
    (v := fun _ a => a.verdict == .confirmed && a.author.delegation == none)
    (T := fun _ a => a.verdict = .confirmed ∧ a.author.delegation = none)
    (fun _ _ => by simp)
  unfold restatementFindings
  simp only []
  split
  · rename_i hE
    have hnd := hDec.mp hE
    cases s with
    | confirmed n =>
      have hn := any_counted (p := p) (o := o) (log := log) (test := rev.answersNow restatement)
        (v := fun _ a => a.verdict == .confirmed && a.author == ⟨n, none⟩)
        (T := fun _ a => a.verdict = .confirmed ∧ a.author = ⟨n, none⟩) (fun _ _ => by simp)
      simp only [Revision.Stands]
      split
      · rename_i h
        exact ⟨fun _ => ⟨hn.mp h, hnd⟩, fun _ => rfl⟩
      · rename_i h
        exact ⟨fun h' => (by cases h'), fun h' => absurd (hn.mpr h'.1) h⟩
    | unconfirmed =>
      simp only [Revision.Stands]
      split
      · rename_i he
        have hno : ¬ AnswerWhere p o log fun _ a => rev.answersNow restatement a = true ∧
            a.verdict = .confirmed ∧ a.author.delegation = none := by
          intro hw
          obtain ⟨t, ht, hc, a, hb, hnow, hv, hdl⟩ := hw
          have hm : (t, a) ∈ (countedNow p o log rev restatement).filter fun x =>
              x.2.verdict == .confirmed && x.2.author.delegation == none :=
            List.mem_filter.mpr ⟨mem_counted.mpr ⟨ht, hb, hnow, hc⟩, by simp [hv, hdl]⟩
          rw [List.isEmpty_iff.mp he] at hm
          cases hm
        split
        · rename_i h
          exact ⟨fun _ => ⟨⟨hyes.mp h, hno⟩, hnd⟩, fun _ => rfl⟩
        · rename_i h
          exact ⟨fun h' => (by cases h'), fun h' => absurd (hyes.mpr h'.1.1) h⟩
      · rename_i he
        refine ⟨fun h' => (by cases h'), fun h' => ?_⟩
        exfalso
        apply he
        rw [List.isEmpty_iff, List.filter_eq_nil_iff]
        intro x hx
        cases hv : (x.2.verdict == .confirmed && x.2.author.delegation == none)
        · simp
        · exfalso
          obtain ⟨t, a⟩ := x
          obtain ⟨ht, hb, hnow, hc⟩ := mem_counted.mp hx
          simp only [Bool.and_eq_true, beq_iff_eq] at hv
          exact h'.1.2 ⟨t, ht, hc, a, hb, hnow, hv.1, hv.2⟩
  · rename_i hE
    have hD : AnswerWhere p o log fun _ a =>
        rev.answersNow restatement a = true ∧ a.verdict = .declined :=
      Classical.byContradiction fun h => hE (hDec.mpr h)
    exact ⟨fun h => (by cases h), fun h => absurd hD h.2⟩

theorem statusFindings_eq_nil_iff {rev : Revision} {q : Question} {s : Restatement}
    {x : Settled s} :
    statusFindings p o log rev q x = [] ↔
      rev.Settles p o log q x ∧
        ¬ AnswerWhere p o log fun _ a => rev.answersNow q a = true ∧ a.verdict = .declined := by
  have hDec := decliners_isEmpty (p := p) (o := o) (log := log) (rev := rev) (q := q)
  unfold statusFindings
  simp only []
  split
  · rename_i hE
    have hnd := hDec.mp hE
    cases x with
    | answered ans v =>
      cases v with
      | confirmed =>
        have hn := any_counted (p := p) (o := o) (log := log) (test := rev.answersNow q)
          (v := fun t a => a.verdict == .confirmed && answererOf t a == ans)
          (T := fun t a => a.verdict = .confirmed ∧ answererOf t a = ans) (fun _ _ => by simp)
        simp only [Revision.Settles]
        split
        · rename_i h
          exact ⟨fun _ => ⟨hn.mp h, hnd⟩, fun _ => rfl⟩
        · rename_i h
          exact ⟨fun h' => (by cases h'), fun h' => absurd (hn.mpr h'.1) h⟩
      | declined =>
        simp [Revision.Settles]
    | derived =>
      simp only [Revision.Settles]
      split
      · rename_i he
        refine ⟨fun _ => ⟨?_, hnd⟩, fun _ => rfl⟩
        rintro ⟨t, ht, hc, a, hb, hnow⟩
        have hm : (t, a) ∈ countedNow p o log rev q := mem_counted.mpr ⟨ht, hb, hnow, hc⟩
        rw [List.isEmpty_iff.mp he] at hm
        cases hm
      · rename_i he
        refine ⟨fun h' => (by cases h'), fun h' => ?_⟩
        exfalso
        apply he
        rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
        rintro ⟨t, a⟩ hm
        obtain ⟨ht, hb, hnow, hc⟩ := mem_counted.mp hm
        exact h'.1 ⟨t, ht, hc, a, hb, hnow⟩
    | fork => simp [Revision.Settles]
    | unsettled => simp [Revision.Settles]
  · rename_i hE
    have hD : AnswerWhere p o log fun _ a => rev.answersNow q a = true ∧ a.verdict = .declined :=
      Classical.byContradiction fun h => hE (hDec.mpr h)
    exact ⟨fun h => (by cases h), fun h => absurd hD h.2⟩

theorem keptFindings_eq_nil_iff {rev : Revision} {k : Question × Verdict × Answerer} :
    keptFindings p o log rev k = [] ↔
      AnswerWhere p o log fun t a => rev.backs k.1 k.2.1 a = true ∧ answererOf t a = k.2.2 := by
  have h := any_counted (p := p) (o := o) (log := log) (test := rev.backs k.1 k.2.1)
    (v := fun t a => answererOf t a == k.2.2) (T := fun t a => answererOf t a = k.2.2)
    (fun _ _ => by simp)
  unfold keptFindings
  split
  · rename_i hc
    exact ⟨fun _ => h.mp hc, fun _ => rfl⟩
  · rename_i hc
    exact ⟨fun h' => (by cases h'), fun hx => absurd (h.mpr hx) hc⟩

theorem unkeptFindings_eq_nil_iff {rev : Revision} :
    unkeptFindings p o log rev = [] ↔
      ∀ s ∈ log, Counts p o log s → ∀ a, s.body = .answer a → a.record = rev.record →
        restatement.names a = false → ∃ k ∈ rev.kept, rev.backs k.1 k.2.1 a = true := by
  unfold unkeptFindings
  rw [List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h s hs hc a hb hr hn
    apply Classical.byContradiction
    intro hk
    refine h (s, a) (mem_counted.mpr ⟨hs, hb, ?_, hc⟩)
    have hany : (rev.kept.any fun k => rev.backs k.1 k.2.1 a) = false := by
      rw [Bool.eq_false_iff]
      intro ha
      obtain ⟨k, hk', hb'⟩ := List.any_eq_true.mp ha
      exact hk ⟨k, hk', hb'⟩
    simp [hr, hn, hany]
  · rintro h ⟨s, a⟩ hm
    obtain ⟨hs, hb, ht, hc⟩ := mem_counted.mp hm
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.eq_false_iff] at ht
    obtain ⟨k, hk, hb'⟩ := h s hs hc a hb ht.1.1 (by simpa using ht.1.2)
    exact ht.2 (List.any_eq_true.mpr ⟨k, hk, hb'⟩)

theorem sourcelessFindings_eq_nil_iff :
    sourcelessFindings p o log = [] ↔ ∀ s ∈ log, Counts p o log s → s.source.recorded = true := by
  unfold sourcelessFindings
  rw [List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h s hs hc
    cases hr : s.source.recorded with
    | true => rfl
    | false =>
      exact absurd (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hs, counts_iff.mpr hc⟩, by simp [hr]⟩)
        (h s)
  · intro h s hm
    obtain ⟨hs, hr⟩ := List.mem_filter.mp hm
    obtain ⟨hl, hc⟩ := List.mem_filter.mp hs
    simp [h s hl (counts_iff.mp hc)] at hr

theorem agreeFindings_eq_nil_iff {rev : Revision} {q : Question} {s : Restatement}
    {x : Settled s} : agreeFindings rev q x = [] ↔ rev.Agrees q x := by
  cases x with
  | fork | unsettled => simp [agreeFindings, Revision.Agrees]
  | _ =>
    simp only [agreeFindings, Revision.Agrees]
    split
    · rename_i h
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rename_i h
      exact ⟨fun h' => (by cases h'), fun h' => absurd h' h⟩

theorem revisionFindings_eq_nil_iff {rev : Revision} :
    revisionFindings p o log rev = [] ↔ rev.Confirmed p o log := by
  unfold revisionFindings Revision.Confirmed
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, restatementFindings_eq_nil_iff,
    statusFindings_eq_nil_iff, keptFindings_eq_nil_iff, unkeptFindings_eq_nil_iff,
    agreeFindings_eq_nil_iff, and_assoc]

/-- A declaration's project and owners are the log's. -/
theorem Declares.unique {p' : Ident} {o' : Statement.Owners} (h : Declares log p o)
    (h' : Declares log p' o') : p = p' ∧ o = o' := by
  obtain ⟨⟨s, hs, hp⟩, -⟩ := h
  obtain ⟨⟨s', hs', hp'⟩, -⟩ := h'
  rw [hs] at hs'
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  exact ⟨hp.symm.trans hp', rfl⟩

theorem foreign_isEmpty {q : Ident} :
    ((log.filter fun t => t.project != q).map fun t => Finding.foreign t.id).isEmpty = true ↔
      ∀ t ∈ log, t.project = q := by
  simp only [List.isEmpty_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, bne_iff_ne, ne_eq,
    Decidable.not_not]

/-- `repeatedFindings` names exactly the ids more than one statement of the log has. -/
theorem mem_repeatedFindings {f : Finding} :
    f ∈ repeatedFindings log ↔ ∃ i, f = .repeated i ∧ 2 ≤ (log.map (·.id)).count i := by
  simp only [repeatedFindings, List.mem_map, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨-, hc⟩, rfl⟩
    exact ⟨i, rfl, hc⟩
  · rintro ⟨i, rfl, hc⟩
    exact ⟨i, ⟨List.mem_map.mp (List.count_pos_iff.mp (Nat.lt_of_lt_of_le Nat.two_pos hc)), hc⟩, rfl⟩

theorem repeatedFindings_eq_nil_iff : repeatedFindings log = [] ↔ (log.map (·.id)).Nodup := by
  rw [List.eq_nil_iff_forall_not_mem, List.nodup_iff_count]
  constructor
  · intro h i
    have := h (.repeated i)
    rw [mem_repeatedFindings] at this
    apply Classical.byContradiction
    intro hc
    exact this ⟨i, rfl, by omega⟩
  · intro h f hf
    obtain ⟨i, -, hc⟩ := mem_repeatedFindings.mp hf
    have := h i
    omega

theorem refused_isEmpty {q : Ident} :
    ((log.filter fun t => t.project != q).map (fun t => Finding.foreign t.id) ++
        repeatedFindings log).isEmpty = true ↔
      (∀ t ∈ log, t.project = q) ∧ (log.map (·.id)).Nodup := by
  rw [List.isEmpty_iff, List.append_eq_nil_iff, ← List.isEmpty_iff, foreign_isEmpty,
    repeatedFindings_eq_nil_iff]

theorem inForce_eq_ok_iff : inForce log = .ok (p, o) ↔ Declares log p o := by
  unfold inForce Declares
  rcases hd : declarations log with _ | ⟨⟨s, o'⟩, _ | ⟨d, ds⟩⟩
  · simp
  · have hex : (∃ t, [(s, o')] = [(t, o)] ∧ t.project = p) ↔ o' = o ∧ s.project = p := by
      constructor
      · rintro ⟨t, h, ht⟩
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, ht⟩
      · rintro ⟨rfl, ht⟩
        exact ⟨s, rfl, ht⟩
    rw [hex]
    simp only []
    split
    · rename_i he
      refine ⟨fun h => (by cases h), ?_⟩
      rintro ⟨⟨rfl, -⟩, hn, -⟩
      exact absurd (List.isEmpty_iff.mp he) hn
    · rename_i he
      have he' : o'.principals ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      split
      · rename_i hf
        obtain ⟨hall, hnd⟩ := refused_isEmpty.mp hf
        constructor
        · intro h
          cases h
          exact ⟨⟨rfl, rfl⟩, he', hall, hnd⟩
        · rintro ⟨⟨rfl, rfl⟩, -, -⟩
          rfl
      · rename_i hf
        refine ⟨fun h => (by cases h), ?_⟩
        rintro ⟨⟨rfl, rfl⟩, -, h⟩
        exact absurd (refused_isEmpty.mpr h) hf
  · simp

/-- Every refusal of `inForce` says something. -/
theorem inForce_error_ne_nil {fs : List Finding} (h : inForce log = .error fs) : fs ≠ [] := by
  unfold inForce at h
  rcases hd : declarations log with _ | ⟨⟨s, o'⟩, _ | ⟨d, ds⟩⟩
  · simp only [hd] at h
    cases h
    simp
  · simp only [hd] at h
    split at h
    · cases h
      simp
    · split at h
      · cases h
      · rename_i hn
        cases h
        exact fun he => hn (by simp only [he]; rfl)
  · simp only [hd] at h
    cases h
    simp

/-- **What the decision decides.** For every log and every list of revisions, it finds nothing
exactly when the deliverables are confirmed. -/
theorem findings_eq_nil_iff {revs : List Revision} :
    findings log revs = [] ↔ Confirmed log revs := by
  unfold findings Confirmed
  cases h : inForce log with
  | error fs =>
    simp only [inForce_error_ne_nil h, false_iff, not_exists, not_and]
    intro p o hd
    rw [inForce_eq_ok_iff.mpr hd] at h
    cases h
  | ok x =>
    obtain ⟨p, o⟩ := x
    have hd := inForce_eq_ok_iff.mp h
    simp only []
    split
    · rename_i he
      have he' : revs = [] := List.isEmpty_iff.mp he
      subst he'
      exact ⟨fun h => (by cases h), fun ⟨_, _, _, hn, _⟩ => absurd rfl hn⟩
    · rename_i he
      have he' : revs ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, revisionFindings_eq_nil_iff,
        sourcelessFindings_eq_nil_iff]
      constructor
      · exact fun hr => ⟨p, o, hd, he', hr.1, hr.2⟩
      · rintro ⟨p', o', hd', -, hs, hr⟩
        obtain ⟨rfl, rfl⟩ := hd.unique hd'
        exact ⟨hs, hr⟩

/-! ## What a finding says -/

/-- What the finding `f`, about the revision `rev`, says of the log and of `rev`. -/
def Finding.Names (p : Ident) (o : Statement.Owners) (log : List Statement) (rev : Revision) :
    Finding → Prop
  | .unanswered r c older refused => r = rev.record ∧
      (∀ i ∈ older, ∃ s ∈ log, s.id = i ∧ ∃ a, s.body = .answer a ∧ a.record = r ∧
        a.consequence = c) ∧
      (∀ i ∈ refused, ∃ s ∈ log, s.id = i ∧ ¬ Counts p o log s ∧ ∃ a, s.body = .answer a ∧
        a.record = r ∧ a.revision = rev.text ∧ a.consequence = c)
  | .declined r c ids => r = rev.record ∧ ids ≠ [] ∧
      ∀ i ∈ ids, ∃ s ∈ log, s.id = i ∧ Counts p o log s ∧ ∃ a, s.body = .answer a ∧ a.record = r ∧
        a.revision = rev.text ∧ a.consequence = c ∧ a.verdict = .declined
  | .ownerUnrecorded r ids => r = rev.record ∧ ids ≠ [] ∧
      ∀ i ∈ ids, ∃ s ∈ log, s.id = i ∧ Counts p o log s ∧ ∃ a, s.body = .answer a ∧
        rev.answersNow restatement a = true ∧ a.verdict = .confirmed ∧ a.author.delegation = none
  | .statusDisagrees r c ids => r = rev.record ∧
      ∀ i ∈ ids, ∃ s ∈ log, s.id = i ∧ Counts p o log s ∧ ∃ a, s.body = .answer a ∧ a.record = r ∧
        a.revision = rev.text ∧ a.consequence = c
  | .fork r c => r = rev.record ∧ ∃ x ∈ rev.shown, x.1.consequence = c ∧ x.2.claim = .fork
  | .unbacked r c stale => r = rev.record ∧ ∃ k ∈ rev.kept, k.1.consequence = c ∧
      (¬ AnswerWhere p o log fun t a => rev.backs k.1 k.2.1 a = true ∧ answererOf t a = k.2.2) ∧
      ∀ i ∈ stale, ∃ s ∈ log, s.id = i ∧ ∃ a, s.body = .answer a ∧ a.record = r ∧ a.consequence = c
  | .unkept r i => r = rev.record ∧ ∃ s ∈ log, s.id = i ∧ Counts p o log s ∧
      ∃ a, s.body = .answer a ∧ a.record = r ∧ restatement.names a = false ∧
        ¬ ∃ k ∈ rev.kept, rev.backs k.1 k.2.1 a = true
  | .keptDisagrees r c => r = rev.record ∧ ∃ x ∈ rev.shown, x.1.consequence = c ∧
      ¬ rev.Agrees x.1 x.2
  | _ => False

/-- What the finding `f` states of the log `log` and the revisions `revs`: about the log, what is
wrong with it, and about a revision, that it is not confirmed and what the finding names. -/
def Finding.Holds (log : List Statement) (revs : List Revision) : Finding → Prop
  | .noOwners => ¬ ∃ p o, Declares log p o
  | .severalOwners ids => ids = (declarations log).map (·.1.id) ∧ 2 ≤ ids.length
  | .foreign id => (¬ ∃ p o, Declares log p o) ∧ ∃ s ∈ log, s.id = id ∧
      ∃ d ∈ declarations log, s.project ≠ d.1.project
  | .repeated id => (¬ ∃ p o, Declares log p o) ∧ 2 ≤ (log.map (·.id)).count id
  | .noDeliverable => revs = []
  | .sourceless id => ∃ p o, Declares log p o ∧ ∃ s ∈ log, s.id = id ∧ Counts p o log s ∧
      s.source.recorded = false
  | f => ∃ p o, Declares log p o ∧ ∃ rev ∈ revs, ¬ rev.Confirmed p o log ∧ f.Names p o log rev

theorem not_declares_of_error {fs : List Finding} (h : inForce log = .error fs) :
    ¬ ∃ p o, Declares log p o := by
  rintro ⟨p, o, hd⟩
  rw [inForce_eq_ok_iff.mpr hd] at h
  cases h

theorem inForce_error_sound {revs : List Revision} {fs : List Finding} {f : Finding}
    (h : inForce log = .error fs) (hf : f ∈ fs) : f.Holds log revs := by
  have nd := not_declares_of_error h
  have hrep : ∀ {g : Finding}, g ∈ repeatedFindings log → g.Holds log revs := by
    intro g hg
    obtain ⟨i, rfl, hc⟩ := mem_repeatedFindings.mp hg
    exact ⟨nd, hc⟩
  unfold inForce at h
  rcases hd : declarations log with _ | ⟨⟨s, o'⟩, _ | ⟨d, ds⟩⟩
  · simp only [hd] at h
    cases h
    rcases List.mem_cons.mp hf with rfl | hf
    · exact nd
    · exact hrep hf
  · have hmem : ∀ {g : Finding},
        g ∈ ((log.filter fun t => t.project != s.project).map fun t => Finding.foreign t.id) ++
          repeatedFindings log →
        g.Holds log revs := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
        obtain ⟨htl, hne⟩ := List.mem_filter.mp ht
        refine ⟨nd, t, htl, rfl, (s, o'), by simp [hd], ?_⟩
        simpa using hne
      · exact hrep hg
    simp only [hd] at h
    split at h
    · cases h
      rcases List.mem_cons.mp hf with rfl | hf
      · exact nd
      · exact hmem hf
    · split at h
      · cases h
      · cases h
        exact hmem hf
  · simp only [hd] at h
    cases h
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by simp [hd], by simp⟩
    · exact hrep hf

/-- **A refusal names each id the log repeats**, whatever else is wrong with it. -/
theorem findings_of_repeated {revs : List Revision} {i : Ident}
    (hc : 2 ≤ (log.map (·.id)).count i) : Finding.repeated i ∈ findings log revs := by
  have hm : Finding.repeated i ∈ repeatedFindings log := mem_repeatedFindings.mpr ⟨i, rfl, hc⟩
  have hnd : ¬ (log.map (·.id)).Nodup := fun h => by
    rw [repeatedFindings_eq_nil_iff.mpr h] at hm
    cases hm
  unfold findings
  cases h : inForce log with
  | ok x => exact absurd (inForce_eq_ok_iff.mp h).2.2.2 hnd
  | error fs =>
    simp only []
    unfold inForce at h
    rcases hd : declarations log with _ | ⟨⟨s, o'⟩, _ | ⟨d, ds⟩⟩
    · simp only [hd] at h
      cases h
      exact List.mem_cons_of_mem _ hm
    · simp only [hd] at h
      split at h
      · cases h
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)
      · split at h
        · cases h
        · cases h
          exact List.mem_append_right _ hm
    · simp only [hd] at h
      cases h
      exact List.mem_cons_of_mem _ hm

theorem unansweredFinding_names {rev : Revision} {q : Question} :
    (unansweredFinding p o log rev q).Names p o log rev := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    obtain ⟨⟨s, a⟩, hm, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hs, hb, ht⟩ := mem_answersWhere.mp hm
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨s, hs, rfl, a, hb, ht.1.1, ht.1.2⟩
  · intro i hi
    obtain ⟨⟨s, a⟩, hm, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hm, hc⟩ := List.mem_filter.mp hm
    obtain ⟨hs, hb, ht⟩ := mem_answersWhere.mp hm
    simp only [Revision.answersNow, Question.names, Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨s, hs, rfl, fun h => by simp [counts_iff.mpr h] at hc, a, hb, ht.1.1, ht.1.2, ht.2.1.1⟩

theorem declinedFinding_names {rev : Revision} {q : Question}
    (hne : (decliners (countedNow p o log rev q)).isEmpty ≠ true) :
    (Finding.declined rev.record q.consequence
      (idsOf (decliners (countedNow p o log rev q)))).Names p o log rev := by
  refine ⟨rfl, fun he => hne ?_, ?_⟩
  · rw [List.isEmpty_iff]
    exact List.map_eq_nil_iff.mp he
  · intro i hi
    obtain ⟨⟨s, a⟩, hm, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hm, hv⟩ := List.mem_filter.mp hm
    obtain ⟨hs, hb, ht, hc⟩ := mem_counted.mp hm
    simp only [Revision.answersNow, Question.names, Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨s, hs, rfl, hc, a, hb, ht.1.1, ht.1.2, ht.2.1.1, by simpa using hv⟩

theorem restatementFindings_names {rev : Revision} {s : Restatement} {f : Finding}
    (hf : f ∈ restatementFindings p o log rev s) : f.Names p o log rev := by
  unfold restatementFindings at hf
  simp only [] at hf
  split at hf
  · cases s with
    | confirmed n =>
      simp only [] at hf
      split at hf
      · cases hf
      · simp only [List.mem_singleton] at hf
        subst hf
        exact unansweredFinding_names
    | unconfirmed =>
      simp only [] at hf
      split at hf
      · split at hf
        · cases hf
        · simp only [List.mem_singleton] at hf
          subst hf
          exact unansweredFinding_names
      · rename_i he
        simp only [List.mem_singleton] at hf
        subst hf
        refine ⟨rfl, fun hi => he ?_, ?_⟩
        · rw [List.isEmpty_iff]
          exact List.map_eq_nil_iff.mp hi
        · intro i hi
          obtain ⟨⟨t, a⟩, hm, rfl⟩ := List.mem_map.mp hi
          obtain ⟨hm, hv⟩ := List.mem_filter.mp hm
          obtain ⟨ht, hb, hnow, hc⟩ := mem_counted.mp hm
          simp only [Bool.and_eq_true, beq_iff_eq] at hv
          exact ⟨t, ht, rfl, hc, a, hb, hnow, hv.1, hv.2⟩
  · rename_i hne
    simp only [List.mem_singleton] at hf
    subst hf
    exact declinedFinding_names hne

/-- What the status findings of a status say, a fork apart. -/
theorem statusFindings_names {rev : Revision} {q : Question} {s : Restatement} {x : Settled s}
    {f : Finding} (hf : f ∈ statusFindings p o log rev q x) :
    (x.claim = .fork ∧ f = .fork rev.record q.consequence) ∨ f.Names p o log rev := by
  unfold statusFindings at hf
  simp only [] at hf
  split at hf
  · cases x with
    | answered ans v =>
      cases v with
      | confirmed =>
        simp only [] at hf
        split at hf
        · cases hf
        · simp only [List.mem_singleton] at hf
          subst hf
          exact .inr unansweredFinding_names
      | declined =>
        simp only [List.mem_singleton] at hf
        subst hf
        exact .inr ⟨rfl, fun _ h => by cases h⟩
    | derived =>
      simp only [] at hf
      split at hf
      · cases hf
      · simp only [List.mem_singleton] at hf
        subst hf
        refine .inr ⟨rfl, ?_⟩
        intro i hi
        obtain ⟨⟨t, a⟩, hm, rfl⟩ := List.mem_map.mp hi
        obtain ⟨ht, hb, hnow, hc⟩ := mem_counted.mp hm
        simp only [Revision.answersNow, Question.names, Bool.and_eq_true, beq_iff_eq] at hnow
        exact ⟨t, ht, rfl, hc, a, hb, hnow.1.1, hnow.1.2, hnow.2.1.1⟩
    | fork =>
      simp only [List.mem_singleton] at hf
      subst hf
      exact .inl ⟨rfl, rfl⟩
    | unsettled =>
      simp only [List.mem_singleton] at hf
      subst hf
      exact .inr unansweredFinding_names
  · rename_i hne
    simp only [List.mem_singleton] at hf
    subst hf
    exact .inr (declinedFinding_names hne)

theorem keptFindings_names {rev : Revision} {k : Question × Verdict × Answerer} {f : Finding}
    (hk : k ∈ rev.kept) (hf : f ∈ keptFindings p o log rev k) : f.Names p o log rev := by
  have hnil := keptFindings_eq_nil_iff (p := p) (o := o) (log := log) (rev := rev) (k := k)
  have hno : ¬ AnswerWhere p o log fun t a => rev.backs k.1 k.2.1 a = true ∧
      answererOf t a = k.2.2 := by
    intro h
    rw [hnil.mpr h] at hf
    cases hf
  unfold keptFindings at hf
  split at hf
  · cases hf
  · simp only [List.mem_singleton] at hf
    subst hf
    refine ⟨rfl, k, hk, rfl, hno, ?_⟩
    intro i hi
    obtain ⟨⟨s, a⟩, hm, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hs, hb, ht⟩ := mem_answersWhere.mp hm
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨s, hs, rfl, a, hb, ht.1, ht.2⟩

theorem unkeptFindings_names {rev : Revision} {f : Finding}
    (hf : f ∈ unkeptFindings p o log rev) : f.Names p o log rev := by
  unfold unkeptFindings at hf
  obtain ⟨⟨s, a⟩, hm, rfl⟩ := List.mem_map.mp hf
  obtain ⟨hs, hb, ht, hc⟩ := mem_counted.mp hm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.eq_false_iff] at ht
  refine ⟨rfl, s, hs, rfl, hc, a, hb, ht.1.1, by simpa using ht.1.2, ?_⟩
  rintro ⟨k, hk, hb'⟩
  exact ht.2 (List.any_eq_true.mpr ⟨k, hk, hb'⟩)

theorem mem_agreeFindings {rev : Revision} {q : Question} {s : Restatement} {x : Settled s}
    {f : Finding} (hf : f ∈ agreeFindings rev q x) :
    f = .keptDisagrees rev.record q.consequence := by
  cases x with
  | fork | unsettled => cases hf
  | _ =>
    simp only [agreeFindings] at hf
    split at hf
    · cases hf
    · exact List.mem_singleton.mp hf

theorem agreeFindings_names {rev : Revision} {x : Question × Settled rev.standing} {f : Finding}
    (hx : x ∈ rev.shown) (hf : f ∈ agreeFindings rev x.1 x.2) : f.Names p o log rev := by
  have hne : ¬ rev.Agrees x.1 x.2 := fun h => by
    rw [agreeFindings_eq_nil_iff.mpr h] at hf
    cases hf
  rw [mem_agreeFindings hf]
  exact ⟨rfl, x, hx, rfl, hne⟩

theorem revisionFindings_names {rev : Revision} {f : Finding}
    (hf : f ∈ revisionFindings p o log rev) : f.Names p o log rev := by
  unfold revisionFindings at hf
  simp only [List.mem_append, List.mem_flatMap] at hf
  rcases hf with (((hf | ⟨x, hx, hf⟩) | ⟨k, hk, hf⟩) | hf) | ⟨x, hx, hf⟩
  · exact restatementFindings_names hf
  · rcases statusFindings_names hf with ⟨hc, rfl⟩ | h
    · exact ⟨rfl, x, hx, rfl, hc⟩
    · exact h
  · exact keptFindings_names hk hf
  · exact unkeptFindings_names hf
  · exact agreeFindings_names hx hf

/-- **What a finding says.** Everything the decision finds holds of the log and the revisions. -/
theorem findings_sound {revs : List Revision} {f : Finding} (hf : f ∈ findings log revs) :
    f.Holds log revs := by
  unfold findings at hf
  cases h : inForce log with
  | error fs =>
    simp only [h] at hf
    exact inForce_error_sound h hf
  | ok x =>
    obtain ⟨p, o⟩ := x
    have hd := inForce_eq_ok_iff.mp h
    simp only [h] at hf
    split at hf
    · rename_i he
      simp only [List.mem_singleton] at hf
      subst hf
      exact List.isEmpty_iff.mp he
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
        obtain ⟨hs, hr⟩ := List.mem_filter.mp hs
        obtain ⟨hl, hc⟩ := List.mem_filter.mp hs
        exact ⟨p, o, hd, s, hl, rfl, counts_iff.mp hc, by simpa using hr⟩
      obtain ⟨rev, hr, hf⟩ := List.mem_flatMap.mp hf
      have hn := revisionFindings_names hf
      have hnc : ¬ rev.Confirmed p o log := fun hc => by
        rw [revisionFindings_eq_nil_iff.mpr hc] at hf
        cases hf
      cases f with
      | noLog | severalLogs _ | unreadable _ | noOwners | severalOwners _ | foreign _ | repeated _
      | noDeliverable | sourceless _ | undeclared _ => exact hn.elim
      | _ => exact ⟨p, o, hd, rev, hr, hnc, hn⟩

/-! ## What is refused, and who answered -/

/-- **An answer given as an owner is a declared owner's.** An agent that is not one cannot record an
answer that counts without a delegation: a decision made on the owner's behalf is recorded as one. -/
theorem Counts.as_owner {s : Statement} {a : Statement.Answer} (h : Counts p o log s)
    (hb : s.body = .answer a) (hd : a.author.delegation = none) :
    Trace.isOwner o a.author.principal = true := by
  obtain ⟨-, a', hb', hc, -⟩ := h
  rw [hb] at hb'
  cases hb'
  generalize a.author = au at hc hd ⊢
  obtain ⟨q, d⟩ := au
  obtain rfl : d = none := hd
  cases hc with
  | owner ho => exact ho

/-- **An answer given under a delegation cites one that covers it**: the one statement of the project
with that id is a delegation to its author, whose scope allows the answer, and whose grantor's
authority traces back to a declared owner. -/
theorem Counts.under_delegation {s : Statement} {a : Statement.Answer} {d : Ident}
    (h : Counts p o log s) (hb : s.body = .answer a) (hd : a.author.delegation = some d) :
    ∃ del, Trace.Link p o log (.ofAnswer a) false a.author.principal d del ∧
      Trace.allows del.scope (.ofAnswer a) = true ∧
      Trace.Chain p o log (.ofAnswer a) true del.delegator := by
  obtain ⟨-, a', hb', hc, -⟩ := h
  rw [hb] at hb'
  cases hb'
  generalize a.author = au at hc hd ⊢
  obtain ⟨q, d'⟩ := au
  obtain rfl : d' = some d := hd
  cases hc with
  | link hl hg => exact ⟨_, hl, hl.2.2.2.1, hg⟩

/-- **An answer that counts and records no source stops the deliverables being confirmed**, so each
answer that counts says where it came from. -/
theorem not_confirmed_of_sourceless {revs : List Revision} {s : Statement} (hs : s ∈ log)
    (hsrc : s.source.recorded = false) (hc : ∀ p o, Declares log p o → Counts p o log s) :
    ¬ Confirmed log revs := by
  rintro ⟨p, o, hd, -, hr, -⟩
  rw [hr s hs (hc p o hd)] at hsrc
  cases hsrc

/-- A log that declares no owner confirms nothing. -/
theorem not_confirmed_of_no_declaration {revs : List Revision} (h : declarations log = []) :
    ¬ Confirmed log revs := by
  rintro ⟨_, _, ⟨⟨s, hs, -⟩, -⟩, -⟩
  rw [h] at hs
  cases hs

/-- **No confirmed log repeats an id**, so no statement can make an answer of it refuse by sharing the
answer's id, or the id of a delegation it cites. -/
theorem Confirmed.nodup {revs : List Revision} (h : Confirmed log revs) :
    (log.map (·.id)).Nodup := by
  obtain ⟨_, _, ⟨-, -, -, hn⟩, -⟩ := h
  exact hn

/-- A project with no deliverable has nothing confirmed. -/
theorem not_confirmed_nil : ¬ Confirmed log [] := by
  rintro ⟨_, _, -, h, -⟩
  exact h rfl

/-- A status that holds is an answer at this revision or a derived one, which is only possible where
the standing is an owner's. -/
theorem Revision.settles_cases {rev : Revision} {q : Question} {s : Restatement} {x : Settled s}
    (h : rev.Settles p o log q x) :
    (AnswerWhere p o log fun _ a => rev.answersNow q a = true ∧ a.verdict = .confirmed) ∨
      ∃ n, s = .confirmed n := by
  cases x with
  | answered ans v =>
    cases v with
    | confirmed =>
      obtain ⟨t, ht, hc, a, hb, hnow, hv, -⟩ := h
      exact .inl ⟨t, ht, hc, a, hb, hnow, hv⟩
    | declined => exact h.elim
  | derived => exact .inr ⟨_, rfl⟩
  | fork | unsettled => exact h.elim

/-- **The restatement of a confirmed revision is confirmed at that revision**, when its standing
names an owner, by that owner, whose answer counts. -/
theorem Revision.Confirmed.owner {rev : Revision} {n : Ident} (h : rev.Confirmed p o log)
    (hn : rev.standing = .confirmed n) :
    ∃ s ∈ log, Counts p o log s ∧ ∃ a, s.body = .answer a ∧ a.record = rev.record ∧
      a.revision = rev.text ∧ restatement.names a = true ∧ a.verdict = .confirmed ∧
        a.author = ⟨n, none⟩ := by
  have hs := h.1
  rw [hn] at hs
  obtain ⟨s, hsl, hc, a, hb, hnow, hv, ha⟩ := hs
  simp only [Revision.answersNow, Bool.and_eq_true, beq_iff_eq] at hnow
  exact ⟨s, hsl, hc, a, hb, hnow.1.1, hnow.1.2, hnow.2, hv, ha⟩

/-- **Every consequence of the current revision has an answer naming that revision, or a derived
status resting on an owner's confirmation of that revision's restatement.** So a confirmation of an
earlier revision never carries a derived status forward. -/
theorem Confirmed.settled {revs : List Revision} {rev : Revision} {x : Question × Settled rev.standing}
    (h : Confirmed log revs) (hr : rev ∈ revs) (hx : x ∈ rev.shown) :
    ∃ p o, Declares log p o ∧
      ((∃ s ∈ log, Counts p o log s ∧ ∃ a, s.body = .answer a ∧ rev.answersNow x.1 a = true ∧
          a.revision = rev.text ∧ a.verdict = .confirmed) ∨
        ∃ n, rev.standing = .confirmed n ∧ Trace.isOwner o n = true ∧
          ∃ s ∈ log, Counts p o log s ∧ ∃ a, s.body = .answer a ∧ a.record = rev.record ∧
            a.revision = rev.text ∧ restatement.names a = true ∧ a.verdict = .confirmed ∧
              a.author = ⟨n, none⟩) := by
  obtain ⟨p, o, hd, -, -, hc⟩ := h
  have hrc := hc rev hr
  refine ⟨p, o, hd, ?_⟩
  rcases Revision.settles_cases (hrc.2.2.1 x hx).1 with ⟨s, hs, hcs, a, hb, hnow, hv⟩ | ⟨n, hn⟩
  · refine .inl ⟨s, hs, hcs, a, hb, hnow, ?_, hv⟩
    simp only [Revision.answersNow, Bool.and_eq_true, beq_iff_eq] at hnow
    exact hnow.1.2
  · obtain ⟨s, hs, hcs, a, hb, hrec, htext, hnames, hv, ha⟩ := hrc.owner hn
    have hown := Counts.as_owner hcs hb (by simp [ha])
    rw [ha] at hown
    exact .inr ⟨n, hn, hown, s, hs, hcs, a, hb, hrec, htext, hnames, hv, ha⟩

/-- **The plain restatement of a confirmed revision has an answer that counts and names it**, so no
deliverable passes with an empty or absent confirmation, whatever it shows. -/
theorem Confirmed.restated {revs : List Revision} {rev : Revision} (h : Confirmed log revs)
    (hr : rev ∈ revs) :
    ∃ p o, Declares log p o ∧ ∃ s ∈ log, Counts p o log s ∧ ∃ a, s.body = .answer a ∧
      a.record = rev.record ∧ a.revision = rev.text ∧ restatement.names a = true ∧
        a.verdict = .confirmed := by
  obtain ⟨p, o, hd, -, -, hc⟩ := h
  refine ⟨p, o, hd, ?_⟩
  have hs := (hc rev hr).1
  have : AnswerWhere p o log fun _ a =>
      rev.answersNow restatement a = true ∧ a.verdict = .confirmed := by
    cases hst : rev.standing with
    | confirmed n =>
      rw [hst] at hs
      obtain ⟨s, hsl, hcs, a, hb, hnow, hv, -⟩ := hs
      exact ⟨s, hsl, hcs, a, hb, hnow, hv⟩
    | unconfirmed =>
      rw [hst] at hs
      exact hs.1
  obtain ⟨s, hs, hcs, a, hb, hnow, hv⟩ := this
  simp only [Revision.answersNow, Bool.and_eq_true, beq_iff_eq] at hnow
  exact ⟨s, hs, hcs, a, hb, hnow.1.1, hnow.1.2, hnow.2, hv⟩

/-- **A status agrees with the answers kept.** Of a confirmed revision, each consequence shown with an
answer has that answer among those it keeps, by that answerer with that verdict, and each recorded as
derived has none among them. -/
theorem Confirmed.agrees {revs : List Revision} {rev : Revision} {x : Question × Settled rev.standing}
    (h : Confirmed log revs) (hr : rev ∈ revs) (hx : x ∈ rev.shown) : rev.Agrees x.1 x.2 := by
  obtain ⟨p, o, -, -, -, hc⟩ := h
  exact (hc rev hr).2.2.2.2.2 x hx

/-- **An answer to an older revision does not count**: a log none of whose answers names the
revision's text does not confirm it. -/
theorem not_confirmed_of_older {revs : List Revision} {rev : Revision} (hr : rev ∈ revs)
    (h : ∀ s ∈ log, ∀ a, s.body = .answer a → a.revision ≠ rev.text) : ¬ Confirmed log revs := by
  intro hc
  obtain ⟨_, _, -, s, hs, -, a, hb, -, hv, -⟩ := hc.restated hr
  exact h s hs a hb hv

/-- **A kept answer whose meaning has changed is refused**: when no answer of the log has the text a
kept answer's predicate now has, the deliverable is not confirmed. -/
theorem not_confirmed_of_changed {revs : List Revision} {rev : Revision}
    {k : Question × Verdict × Answerer} (hr : rev ∈ revs) (hk : k ∈ rev.kept)
    (h : ∀ s ∈ log, ∀ a, s.body = .answer a → a.predicate ≠ k.1.predicate) :
    ¬ Confirmed log revs := by
  rintro ⟨p, o, -, -, -, hc⟩
  obtain ⟨s, hs, -, a, hb, ht, -⟩ := (hc rev hr).2.2.2.1 k hk
  simp only [Revision.backs, Question.names, Bool.and_eq_true, beq_iff_eq] at ht
  exact h s hs a hb ht.1.2.2

/-- **An answer dropped from those a deliverable keeps is refused**, while it counts. -/
theorem not_confirmed_of_dropped {revs : List Revision} {rev : Revision}
    {s : Statement} {a : Statement.Answer} (hr : rev ∈ revs) (hs : s ∈ log)
    (hb : s.body = .answer a) (hrec : a.record = rev.record) (hn : restatement.names a = false)
    (hk : ¬ ∃ k ∈ rev.kept, rev.backs k.1 k.2.1 a = true)
    (hcounts : ∀ p o, Declares log p o → Counts p o log s) : ¬ Confirmed log revs := by
  rintro ⟨p, o, hd, -, -, hc⟩
  exact hk ((hc rev hr).2.2.2.2.1 s hs (hcounts p o hd) a hb hrec hn)

/-! ## The standing the log gives, proved -/

/-- **The log gives a confirmation only where an owner's answer that counts confirms this revision.**
Since `Restatement.words` says confirmed exactly when the standing is (`says_confirmed_iff`), what is
printed from this says so only then. -/
theorem logStanding_eq_confirmed {rev : Revision} {n : Ident}
    (h : logStanding p o log rev = .confirmed n) :
    AnswerWhere p o log fun _ a => rev.answersNow restatement a = true ∧ a.verdict = .confirmed ∧
      a.author = ⟨n, none⟩ := by
  unfold logStanding at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨t, a⟩ := x
    obtain ⟨ht, hb, hnow, hc⟩ := mem_counted.mp (List.mem_of_find?_eq_some hx)
    have hv := List.find?_some hx
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    refine ⟨t, ht, hc, a, hb, hnow, hv.1, ?_⟩
    rcases ha : a.author with ⟨q, d⟩
    simp only [ha] at hv ⊢
    simp [hv.2]
  · cases h

/-- **A record revised after its owner confirmed it stops printing as confirmed**: where no answer of
the log names the revision's text, the log gives no owner's confirmation. -/
theorem logStanding_of_older {rev : Revision}
    (h : ∀ s ∈ log, ∀ a, s.body = .answer a → a.revision ≠ rev.text) :
    logStanding p o log rev = .unconfirmed := by
  cases hl : logStanding p o log rev with
  | unconfirmed => rfl
  | confirmed n =>
    obtain ⟨s, hs, -, a, hb, hnow, -⟩ := logStanding_eq_confirmed hl
    simp only [Revision.answersNow, Bool.and_eq_true, beq_iff_eq] at hnow
    exact absurd hnow.1.2 (h s hs a hb)

/-- **A checked answer is one the log holds**, at this revision, by that answerer, with that verdict.
-/
theorem checked_eq_answered {rev : Revision} {q : Question} {s : Restatement} {x : Settled s}
    {ans : Answerer} {v : Verdict}
    (h : checked p o log rev q x = .answered ans v) :
    AnswerWhere p o log fun t a => rev.answersNow q a = true ∧ a.verdict = v ∧
      answererOf t a = ans := by
  unfold checked at h
  cases x with
  | answered ans' v' =>
    simp only [] at h
    split at h
    · rename_i hany
      cases h
      exact (any_counted (p := p) (o := o) (log := log) (test := rev.answersNow q)
        (v := fun t a => a.verdict == v && answererOf t a == ans)
        (T := fun t a => a.verdict = v ∧ answererOf t a = ans) (fun _ _ => by simp)).mp hany
    · cases h
  | derived =>
    simp only [] at h
    split at h
    · revert h
      generalize logStanding p o log rev = t
      cases t <;> simp [derivedAt]
    · cases h
  | fork => cases h
  | unsettled => cases h

/-- A checked status claims derived only where the log gives an owner's confirmation of this
revision. -/
theorem checked_derived {rev : Revision} {q : Question} {s : Restatement} {x : Settled s}
    (h : (checked p o log rev q x).claim = .derived) :
    ∃ n, logStanding p o log rev = .confirmed n :=
  Settled.says_derived_confirmed _ ((Settled.says_iff _ _).mpr h)

/-! ## Reading the log -/

theorem parseAll_eq_some_iff {texts : List String} {log : List Statement} :
    parseAll texts = some log ↔ texts = log.map Statement.print := by
  induction texts generalizing log with
  | nil =>
    cases log <;> simp [parseAll]
  | cons t ts ih =>
    simp only [parseAll, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    constructor
    · rintro ⟨s, hs, l, hl, rfl⟩
      simp [(Statement.parse_eq_some_iff _ _).mp hs, ih.mp hl]
    · intro h
      cases log with
      | nil => cases h
      | cons s l =>
        simp only [List.map_cons, List.cons.injEq] at h
        exact ⟨s, (Statement.parse_eq_some_iff _ _).mpr h.1.symm, l, ih.mpr h.2, rfl⟩

theorem unreadableFrom_ne_nil {n : Nat} {texts : List String} (h : parseAll texts = none) :
    unreadableFrom n texts ≠ [] := by
  induction texts generalizing n with
  | nil => simp [parseAll] at h
  | cons t ts ih =>
    simp only [unreadableFrom]
    cases hp : Statement.parse t with
    | none => simp
    | some s =>
      have hts : parseAll ts = none := by
        simp only [parseAll, hp, Option.bind_some, Option.map_eq_none_iff] at h
        exact h
      simpa using ih hts

/-- A position `unreadableFrom` reports holds a text `Statement.parse` refuses. -/
theorem unreadableFrom_sound {n : Nat} {texts : List String} {f : Finding}
    (h : f ∈ unreadableFrom n texts) :
    ∃ i t, f = .unreadable (n + i) ∧ texts[i]? = some t ∧ Statement.parse t = none := by
  induction texts generalizing n with
  | nil => cases h
  | cons t ts ih =>
    simp only [unreadableFrom, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hp
        simp only [List.mem_singleton] at h
        exact ⟨0, t, by simpa using h, rfl, by simpa using hp⟩
      · cases h
    · obtain ⟨i, t', rfl, hi, hp⟩ := ih h
      exact ⟨i + 1, t', by simp [Nat.add_assoc, Nat.add_comm 1], by simpa using hi, hp⟩

/-- **`parseLog` reads exactly the printed logs**, each as the statements printed. -/
theorem parseLog_eq_ok_iff {texts : List String} {log : List Statement} :
    parseLog texts = .ok log ↔ texts = log.map Statement.print := by
  rw [← parseAll_eq_some_iff]
  unfold parseLog
  cases parseAll texts <;> simp

/-- The findings of the report on a log that reads are the decision's. -/
theorem report_findings_of_ok {texts : List String} {revs : List Revision}
    (hp : parseLog texts = .ok log) : (report texts revs).findings = findings log revs := by
  unfold report
  rw [hp]
  simp only []
  cases hi : inForce log with
  | error fs => simp [findings, hi]
  | ok x => rfl

/-- **What a checker reads says what it must.** The findings of a report are empty exactly when the
log's texts are the printed texts of statements that confirm the revisions. -/
theorem report_findings {texts : List String} {revs : List Revision} :
    (report texts revs).findings = [] ↔
      ∃ log, texts = log.map Statement.print ∧ Confirmed log revs := by
  cases hp : parseLog texts with
  | error fs =>
    have hne : fs ≠ [] := by
      unfold parseLog at hp
      split at hp
      · cases hp
      · rename_i hn
        cases hp
        exact unreadableFrom_ne_nil hn
    have hr : (report texts revs).findings = fs := by
      unfold report
      rw [hp]
    rw [hr]
    simp only [hne, false_iff, not_exists, not_and]
    intro log hl
    rw [parseLog_eq_ok_iff.mpr hl] at hp
    cases hp
  | ok log =>
    have hl := parseLog_eq_ok_iff.mp hp
    rw [report_findings_of_ok hp, findings_eq_nil_iff]
    constructor
    · exact fun h => ⟨log, hl, h⟩
    · rintro ⟨l, hl', h⟩
      have : l = log := Except.ok.inj ((parseLog_eq_ok_iff.mpr hl').symm.trans hp)
      exact this ▸ h

/-- **Each answer's decision is `Trace`'s**, for the owners the log declares: a report holds it for
each answer of the project, and nothing else, so it accepts a confirmation exactly when its authority
traces back to a declared owner within the scope of each delegation on the way
(`Trace.check_eq_ok_iff`). -/
theorem report_decisions {texts : List String} {revs : List Revision} {s : Statement}
    {d : Except Trace.Refusal Unit} (hp : parseLog texts = .ok log) (hd : Declares log p o) :
    (s, d) ∈ (report texts revs).decisions ↔
      s ∈ log ∧ s.project = p ∧ (∃ a, s.body = .answer a) ∧ d = Trace.check p o log s := by
  have hi := inForce_eq_ok_iff.mpr hd
  unfold report
  rw [hp]
  simp only [hi]
  exact Trace.mem_checkLog

/-- A report's counted answers are exactly the answers of the log that count. -/
theorem report_counted {texts : List String} {revs : List Revision} {s : Statement}
    {a : Statement.Answer} (hp : parseLog texts = .ok log) (hd : Declares log p o) :
    (s, a) ∈ (report texts revs).counted ↔
      s ∈ log ∧ s.body = .answer a ∧ Counts p o log s := by
  have hi := inForce_eq_ok_iff.mpr hd
  unfold report
  rw [hp]
  simp only [hi]
  rw [mem_counted]
  simp

end Proofs

end Confirmation

end LeanIntent
