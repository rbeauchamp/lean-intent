import LeanIntent

/-!
# Tracing answers back to the owner

The owner of the project, `richard`, delegates the sorting record to an assistant, `claude`, who
may confirm, decline and retract answers for it, and pass that on. Under that delegation, `claude`
lets a reviewer, `codex`, confirm consequences of any record, without passing it on, and `codex`
passes it on to `gemini` all the same. Each answer below is decided by `Trace.check`, and the
decisions show what the specification admits and what it refuses:

* the owner's answer, and `codex`'s confirmation of the sorting record through two links, are
  accepted (`byOwner_accepted`, `byReviewer_accepted`), so the specification is met by genuine
  delegation, not only by the owner;
* `codex` declining is refused at its own link, whose scope lets it only confirm
  (`reviewerDeclines_refused`); `codex` confirming for another record is refused at `claude`'s link,
  the first that does not cover that record, though `codex`'s own covers every record
  (`otherRecord_refused`);
* `gemini`'s answer is refused at `codex`'s link, which may not be passed on (`byHelper_refused`), and
  an answer by a principal who calls itself an owner is refused at that claim (`forged_refused`);
* once `claude` revokes the delegation it granted `codex`, `codex`'s confirmation is refused at that
  link, by the revocation (`byReviewer_revoked`); once `claude` retracts the owner's answer, which
  its delegation lets it do for the sorting record, that answer is refused, by the retraction
  (`byOwner_retracted`);
* two delegations, each granted under the other, form a cycle, and an answer under either is
  refused at the link where the chain returns (`looping_refused`).
-/

namespace LeanIntentExamples.Trace

open LeanIntent LeanIntent.Trace

deriving instance DecidableEq for Except

/-- The project. -/
def project : Ident := .of "lean-intent"

/-- Its owners declaration: `richard` alone. -/
def owners : Statement.Owners := ⟨[⟨.of "richard", []⟩], none⟩

/-- A statement of the project, on 2026-10-28. -/
def mk (id : Ident) (body : Statement.Body) : Statement :=
  { project, id, date := ⟨2026, 10, 28, by decide⟩, source := .words "As agreed.", body }

/-- `richard`, as owner, lets `claude` confirm, decline and retract for the sorting record, and pass
that on. -/
def assistant : Statement := mk (.of "assistant") <| .delegation
  { delegator := ⟨.of "richard", none⟩
    delegate := ⟨.of "claude", []⟩
    scope := ⟨.only ["LeanIntentExamples.sorting"], true, true, true⟩
    mayPassOn := true }

/-- `claude`, under `assistant`, lets `codex` confirm for every record, and not pass that on. -/
def reviewer : Statement := mk (.of "reviewer") <| .delegation
  { delegator := ⟨.of "claude", some (.of "assistant")⟩
    delegate := ⟨.of "codex", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := false }

/-- `codex`, under `reviewer`, lets `gemini` confirm for every record. -/
def helper : Statement := mk (.of "helper") <| .delegation
  { delegator := ⟨.of "codex", some (.of "reviewer")⟩
    delegate := ⟨.of "gemini", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := false }

/-- An answer to the possibility of returning the empty list for every input, shown for the second
revision of `record`. -/
def answer (id : Ident) (author : Authority) (record : String) (verdict : Verdict) : Statement :=
  mk id <| .answer
    { author, record, revision := "2", consequence := "returning the empty list for every input",
      kind := .possibility, predicate := "fun f => f = fun _ => []", verdict }

/-- The owner declines it. -/
def byOwner : Statement :=
  answer (.of "by-owner") ⟨.of "richard", none⟩ "LeanIntentExamples.sorting" .declined

/-- `codex`, under `reviewer`, confirms it. -/
def byReviewer : Statement :=
  answer (.of "by-reviewer") ⟨.of "codex", some (.of "reviewer")⟩ "LeanIntentExamples.sorting"
    .confirmed

/-- `codex`, under `reviewer`, declines it. -/
def reviewerDeclines : Statement :=
  answer (.of "reviewer-declines") ⟨.of "codex", some (.of "reviewer")⟩
    "LeanIntentExamples.sorting" .declined

/-- `codex`, under `reviewer`, confirms a consequence of the counter record. -/
def otherRecord : Statement :=
  answer (.of "other-record") ⟨.of "codex", some (.of "reviewer")⟩ "LeanIntentExamples.counter"
    .confirmed

/-- `gemini`, under `helper`, confirms it. -/
def byHelper : Statement :=
  answer (.of "by-helper") ⟨.of "gemini", some (.of "helper")⟩ "LeanIntentExamples.sorting"
    .confirmed

/-- `mallory`, calling itself an owner, confirms it. -/
def forged : Statement :=
  answer (.of "forged") ⟨.of "mallory", none⟩ "LeanIntentExamples.sorting" .confirmed

/-- The project's log. -/
def log : List Statement :=
  [assistant, reviewer, helper, byOwner, byReviewer, reviewerDeclines, otherRecord, byHelper,
    forged]

theorem byOwner_accepted : Accepted project owners log byOwner :=
  check_eq_ok_iff.mp (by decide +kernel)

theorem byReviewer_accepted : Accepted project owners log byReviewer :=
  check_eq_ok_iff.mp (by decide +kernel)

theorem reviewerDeclines_refused :
    check project owners log reviewerDeclines =
      .error ⟨.of "reviewer-declines", .broken ⟨.of "codex", some (.of "reviewer")⟩ .outOfScope⟩ := by
  decide +kernel

theorem otherRecord_refused :
    check project owners log otherRecord =
      .error ⟨.of "other-record", .broken ⟨.of "claude", some (.of "assistant")⟩ .outOfScope⟩ := by
  decide +kernel

theorem byHelper_refused :
    check project owners log byHelper =
      .error ⟨.of "by-helper", .broken ⟨.of "codex", some (.of "reviewer")⟩ .notPassable⟩ := by
  decide +kernel

theorem forged_refused :
    check project owners log forged =
      .error ⟨.of "forged", .broken ⟨.of "mallory", none⟩ .notOwner⟩ := by
  decide +kernel

/-- `claude`, under `assistant`, revokes `reviewer`, which it granted. -/
def revokeReviewer : Statement :=
  mk (.of "revoke-reviewer") <| .revocation ⟨⟨.of "claude", some (.of "assistant")⟩, .of "reviewer"⟩

theorem byReviewer_revoked :
    check project owners (log ++ [revokeReviewer]) byReviewer =
      .error ⟨.of "by-reviewer",
        .broken ⟨.of "codex", some (.of "reviewer")⟩ (.revoked (.of "revoke-reviewer"))⟩ := by
  decide +kernel

/-- `claude`, under `assistant`, retracts the owner's answer. -/
def retractOwner : Statement :=
  mk (.of "retract-owner") <| .retraction ⟨⟨.of "claude", some (.of "assistant")⟩, .of "by-owner"⟩

theorem byOwner_retracted :
    check project owners (log ++ [retractOwner]) byOwner =
      .error ⟨.of "by-owner", .retracted (.of "retract-owner")⟩ := by
  decide +kernel

/-- `x`, under `loop-b`, lets `y` confirm for every record and pass that on. -/
def loopA : Statement := mk (.of "loop-a") <| .delegation
  { delegator := ⟨.of "x", some (.of "loop-b")⟩
    delegate := ⟨.of "y", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := true }

/-- `y`, under `loop-a`, lets `x` confirm for every record and pass that on. -/
def loopB : Statement := mk (.of "loop-b") <| .delegation
  { delegator := ⟨.of "y", some (.of "loop-a")⟩
    delegate := ⟨.of "x", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := true }

/-- `y`, under `loop-a`, confirms it. -/
def looping : Statement :=
  answer (.of "looping") ⟨.of "y", some (.of "loop-a")⟩ "LeanIntentExamples.sorting" .confirmed

theorem looping_refused :
    check project owners [loopA, loopB, looping] looping =
      .error ⟨.of "looping", .broken ⟨.of "y", some (.of "loop-a")⟩ .cycle⟩ := by
  decide +kernel

end LeanIntentExamples.Trace
