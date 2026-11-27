module

public import LeanIntent.Trace

public section

namespace LeanIntentExamples.Trace

open LeanIntent LeanIntent.Trace

deriving instance @[expose] DecidableEq for Except

@[expose] def project : Ident := .of "lean-intent"

@[expose] def owners : Statement.Owners := ⟨[⟨.of "richard", []⟩], none⟩

@[expose] def mk (id : Ident) (body : Statement.Body) : Statement :=
  { project, id, date := ⟨2026, 10, 28, by decide⟩, source := .words "As agreed.", body }

@[expose] def assistant : Statement := mk (.of "assistant") <| .delegation
  { delegator := ⟨.of "richard", none⟩
    delegate := ⟨.of "agent", []⟩
    scope := ⟨.only ["LeanIntentExamples.sorting"], true, true, true⟩
    mayPassOn := true }

@[expose] def reviewer : Statement := mk (.of "reviewer") <| .delegation
  { delegator := ⟨.of "agent", some (.of "assistant")⟩
    delegate := ⟨.of "auditor", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := false }

@[expose] def helper : Statement := mk (.of "helper") <| .delegation
  { delegator := ⟨.of "auditor", some (.of "reviewer")⟩
    delegate := ⟨.of "worker", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := false }

@[expose] def answer (id : Ident) (author : Authority) (record : String) (verdict : Verdict) : Statement :=
  mk id <| .answer
    { author, record, revision := "2", consequence := "returning the empty list for every input",
      kind := .possibility, predicate := "fun f => f = fun _ => []", verdict }

@[expose] def byOwner : Statement :=
  answer (.of "by-owner") ⟨.of "richard", none⟩ "LeanIntentExamples.sorting" .declined

@[expose] def byReviewer : Statement :=
  answer (.of "by-reviewer") ⟨.of "auditor", some (.of "reviewer")⟩ "LeanIntentExamples.sorting"
    .confirmed

@[expose] def reviewerDeclines : Statement :=
  answer (.of "reviewer-declines") ⟨.of "auditor", some (.of "reviewer")⟩
    "LeanIntentExamples.sorting" .declined

@[expose] def otherRecord : Statement :=
  answer (.of "other-record") ⟨.of "auditor", some (.of "reviewer")⟩ "LeanIntentExamples.counter"
    .confirmed

@[expose] def byHelper : Statement :=
  answer (.of "by-helper") ⟨.of "worker", some (.of "helper")⟩ "LeanIntentExamples.sorting"
    .confirmed

@[expose] def forged : Statement :=
  answer (.of "forged") ⟨.of "mallory", none⟩ "LeanIntentExamples.sorting" .confirmed

@[expose] def log : List Statement :=
  [assistant, reviewer, helper, byOwner, byReviewer, reviewerDeclines, otherRecord, byHelper,
    forged]

theorem byOwner_accepted : Accepted project owners log byOwner :=
  check_eq_ok_iff.mp (by decide +kernel)

theorem byReviewer_accepted : Accepted project owners log byReviewer :=
  check_eq_ok_iff.mp (by decide +kernel)

theorem reviewerDeclines_refused :
    check project owners log reviewerDeclines =
      .error ⟨.of "reviewer-declines", .broken ⟨.of "auditor", some (.of "reviewer")⟩ .outOfScope⟩ := by
  decide +kernel

theorem otherRecord_refused :
    check project owners log otherRecord =
      .error ⟨.of "other-record", .broken ⟨.of "agent", some (.of "assistant")⟩ .outOfScope⟩ := by
  decide +kernel

theorem byHelper_refused :
    check project owners log byHelper =
      .error ⟨.of "by-helper", .broken ⟨.of "auditor", some (.of "reviewer")⟩ .notPassable⟩ := by
  decide +kernel

theorem forged_refused :
    check project owners log forged =
      .error ⟨.of "forged", .broken ⟨.of "mallory", none⟩ .notOwner⟩ := by
  decide +kernel

@[expose] def revokeReviewer : Statement :=
  mk (.of "revoke-reviewer") <| .revocation ⟨⟨.of "agent", some (.of "assistant")⟩, .of "reviewer"⟩

theorem byReviewer_revoked :
    check project owners (log ++ [revokeReviewer]) byReviewer =
      .error ⟨.of "by-reviewer",
        .broken ⟨.of "auditor", some (.of "reviewer")⟩ (.revoked (.of "revoke-reviewer"))⟩ := by
  decide +kernel

@[expose] def retractOwner : Statement :=
  mk (.of "retract-owner") <| .retraction ⟨⟨.of "agent", some (.of "assistant")⟩, .of "by-owner"⟩

theorem byOwner_retracted :
    check project owners (log ++ [retractOwner]) byOwner =
      .error ⟨.of "by-owner", .retracted (.of "retract-owner")⟩ := by
  decide +kernel

@[expose] def loopA : Statement := mk (.of "loop-a") <| .delegation
  { delegator := ⟨.of "x", some (.of "loop-b")⟩
    delegate := ⟨.of "y", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := true }

@[expose] def loopB : Statement := mk (.of "loop-b") <| .delegation
  { delegator := ⟨.of "y", some (.of "loop-a")⟩
    delegate := ⟨.of "x", []⟩
    scope := ⟨.all, true, false, false⟩
    mayPassOn := true }

@[expose] def looping : Statement :=
  answer (.of "looping") ⟨.of "y", some (.of "loop-a")⟩ "LeanIntentExamples.sorting" .confirmed

theorem looping_refused :
    check project owners [loopA, loopB, looping] looping =
      .error ⟨.of "looping", .broken ⟨.of "y", some (.of "loop-a")⟩ .cycle⟩ := by
  decide +kernel

end LeanIntentExamples.Trace
