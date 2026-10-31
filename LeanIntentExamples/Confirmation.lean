import LeanIntent.Confirmation
import LeanIntentExamples.Sorting

/-!
# A project's confirmations, and what the check refuses

A deliverable of the sorting record (`sortingDeliverable`) keeps the consequence its explanation
records as a decision made on the owner's behalf. Its project's log (`log`) declares one owner,
`richard`, who lets an assistant, `claude`, answer for that record. `richard` confirms the plain
restatement; the assistant, under the delegation, confirms that the record fixes the function; and
that a function meeting it is not the empty-list one is recorded as derived from the owner's
confirmation. `current` is the revision as a build would show it, with short texts in place of the
rendering's, since the worked examples hold no text of a build. The check finds nothing (`confirmed`),
so the specification is met by a project in which an owner confirms the restatement and the rest
follows from it or is decided on their behalf. Each change below is refused by name:

* the record revised, so its rendering's text changes: the owner's confirmation is of the older
  revision, so it no longer stands, and the derived consequence with it, and the answer is older
  (`revised_refused`), and the standing the log gives is no longer a confirmation
  (`revised_standing`), though the record still holds the value;
* a definition changed under an unchanged name, so a kept consequence's text changes: the answer
  backs nothing, and it no longer has a kept answer (`meaningChanged_refused`);
* no owners declaration, an empty one, or two (`noOwners_refused`, `emptyOwners_refused`,
  `twoOwners_refused`), and no deliverable (`noDeliverable_refused`);
* the delegation revoked, or removed from the log, or the owner removed from the declaration after
  answering: those answers stop counting (`revoked_refused`, `delegationRemoved_refused`,
  `ownerRemoved_refused`), and of two owners, one confirming is enough (`secondOwner_confirmed`);
* an agent that marks its own answer as an owner's, with no answer that counts: refused
  (`selfConfirmed_refused`), though the same forged statement beside genuine answers does not count
  and is not what confirms them (`selfConfirmed_ignored`);
* a kept answer the deliverable drops, which the log still holds: refused until it is retracted
  (`dropped_refused`, `droppedRetracted_confirmed`);
* a statement of another project, such as a mistyped revocation (`foreign_refused`);
* a fork, and a consequence not settled (`fork_refused`, `unsettled_refused`);
* an answer that counts and records no source (`sourceless_refused`), while a blank source does not
  stop it counting (`sourceless_counted`);
* a consequence recorded as derived that someone answered (`derivedAnswered_refused`), and an owner's
  confirmation the explanation does not record (`ownerUnrecorded_refused`);
* a status that disagrees with the answers the deliverable keeps, naming an answerer they do not hold
  (`otherAnswerer_refused`, `bothKept_confirmed`) or saying that no one answered a consequence one of
  them answers (`derivedKept_refused`, `derivedRetracted_confirmed`);
* an id two statements share, where the statement sharing it would otherwise make an answer refuse
  and so drop out of what is checked: an owner's decline, which stops the deliverable
  (`ownerDeclined_refused`), with its id repeated by a tool statement (`declineRepeated_refused`), and
  a delegation, with its id repeated by another statement (`delegationRepeated_refused`).

A consequence cannot be recorded as derived in a revision whose restatement stands as unconfirmed:
`Settled.derived` is no value of `Settled .unconfirmed`.

The record also carries whose words a source is, and what an external tool did for a consequence
(`origin`, `measured`, `unmeasured`), for a checker to read (`origin_read`), and the check does not
ask for them (`carried_confirmed`). The owners' log as committed is the literal text of each statement
(`ownersText`), and `parseLog` reads such a text back as the same statement (`parseLog_ownersText`,
`parseLog_printed`).
-/

namespace LeanIntentExamples.Confirmation

open LeanIntent LeanIntent.Confirmation LeanIntentExamples.Sorting

/-! ## The deliverable -/

/-- Why the assistant decided that the record fixes the function, as `sortingExplained` records it. -/
def reason : String :=
  "The owner confirmed that the output is an ascending rearrangement of the input, which leaves \
    one such function."

/-- The assistant's decision on the owner's behalf. -/
def assistantAnswerer : Answerer := .onBehalf (.of "claude") (.of "assistant") reason

/-- The answer the deliverable keeps. -/
def sortingAnswers : List (Attributed (List Int → List Int)) :=
  [⟨⟨⟨"is Lean's merge sort", .entailment, fun f => f = sort⟩, .confirmed⟩, assistantAnswerer⟩]

/-- The deliverable: the corrected record, its explanation and the answer it keeps. -/
def sortingDeliverable : Deliverable (List Int → List Int) where
  record := sorting
  explanation := sortingExplained
  answers := sortingAnswers
  keeps := (keeps_iff _ _).mpr fun a ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact fun f hf => sorting_o5_eq.relates hf sorting_meets_sort
    · exact nomatch ha

/-! ## The log -/

/-- The project. -/
def project : Ident := .of "sorting-project"

/-- The owners it declares: `richard` alone. -/
def declared : Statement.Owners := ⟨[⟨.of "richard", []⟩], none⟩

/-- A statement of the project, on 2026-10-30, with the source `text`. -/
def mkWith (text : String) (id : Ident) (body : Statement.Body) : Statement :=
  { project, id, date := ⟨2026, 10, 30, by decide⟩, source := .words text, body }

/-- A statement of the project, in the owner's words. -/
def mk (id : Ident) (body : Statement.Body) : Statement := mkWith "As agreed." id body

/-- The owners declaration. -/
def owners : Statement := mk (.of "owners") (.owners declared)

/-- `richard`, as owner, lets `claude` answer for the sorting record. -/
def assistant : Statement := mk (.of "assistant") <| .delegation
  { delegator := ⟨.of "richard", none⟩
    delegate := ⟨.of "claude", []⟩
    scope := ⟨.only ["sorting"], true, true, true⟩
    mayPassOn := false }

/-- The answer by `author` to the consequence `q`, at the revision `revision`. -/
def answerBody (author : Authority) (q : Question) (revision : String := "revision 2") :
    Statement.Body :=
  .answer
    { author, record := "sorting", revision, consequence := q.consequence, kind := q.kind,
      predicate := q.predicate, verdict := .confirmed }

/-- The first consequence, with a short text for what its predicate means. -/
def notEmpty : Question := ⟨"is not the empty-list function", .entailment, "fun f => f ≠ nilSort"⟩

/-- The second consequence. -/
def isSort : Question := ⟨"is Lean's merge sort", .entailment, "fun f => f = sort"⟩

/-- `claude` acting under the delegation. -/
def underDelegation : Authority := ⟨.of "claude", some (.of "assistant")⟩

/-- `richard` confirms the plain restatement. -/
def restated : Statement := mk (.of "restated") (answerBody ⟨.of "richard", none⟩ restatement)

/-- `claude` confirms the second consequence, on the owner's behalf, for its reason. -/
def sortAnswer : Statement := mkWith reason (.of "sort") (answerBody underDelegation isSort)

/-- The project's log. -/
def log : List Statement := [owners, assistant, restated, sortAnswer]

/-- The standing the explanation records. -/
abbrev byOwner : Restatement := .confirmed (.of "richard")

/-- The revision with the text `text`, showing `shown` and keeping `kept`. -/
def revision (text : String) (shown : List (Question × Settled byOwner))
    (kept : List (Question × Verdict × Answerer)) : Revision :=
  { record := "sorting", text, standing := byOwner, shown, kept }

/-- What the revision shows. -/
def shownNow : List (Question × Settled byOwner) :=
  [(notEmpty, .derived), (isSort, .answered assistantAnswerer .confirmed)]

/-- What the revision keeps. -/
def keptNow : List (Question × Verdict × Answerer) := [(isSort, .confirmed, assistantAnswerer)]

/-- The current revision, as a build would show it. -/
def current : Revision := revision "revision 2" shownNow keptNow

/-- **The specification is met**: the owner's restatement, one consequence derived from it and one
decision on their behalf confirm the deliverable. -/
theorem confirmed : Confirmed log [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-! ## What it refuses -/

/-- The revision again, after a change to the record. -/
def revised : Revision := revision "revision 3" shownNow keptNow

theorem revised_refused :
    findings log [revised] =
      [.unanswered "sorting" restatement.consequence [.of "restated"] [],
       .unanswered "sorting" isSort.consequence [.of "sort"] []] := by
  decide +kernel

/-- The log gives the revised record no owner's confirmation, whatever value it holds. -/
theorem revised_standing : logStanding project declared log revised = .unconfirmed := by
  decide +kernel

/-- The second consequence after a definition it reaches has changed. -/
def isSort' : Question := { isSort with predicate := "fun f => f = sort, redefined" }

theorem meaningChanged_refused :
    findings log [revision "revision 2"
        [(notEmpty, .derived), (isSort', .answered assistantAnswerer .confirmed)]
        [(isSort', .confirmed, assistantAnswerer)]] =
      [.unanswered "sorting" isSort.consequence [.of "sort"] [],
       .unbacked "sorting" isSort.consequence [.of "sort"],
       .unkept "sorting" (.of "sort")] := by
  decide +kernel

theorem noOwners_refused : findings (log.erase owners) [current] = [.noOwners] := by
  decide +kernel

theorem emptyOwners_refused :
    findings (mk (.of "owners") (.owners ⟨[], none⟩) :: log.erase owners) [current] =
      [.noOwners] := by
  decide +kernel

theorem twoOwners_refused :
    findings (mk (.of "more") (.owners ⟨[⟨.of "claude", []⟩], none⟩) :: log) [current] =
      [.severalOwners [.of "more", .of "owners"]] := by
  decide +kernel

theorem noDeliverable_refused : findings log [] = [.noDeliverable] := by
  decide +kernel

theorem revoked_refused :
    findings (log ++ [mk (.of "revoke") (.revocation ⟨⟨.of "richard", none⟩, .of "assistant"⟩)])
        [current] =
      [.unanswered "sorting" isSort.consequence [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem delegationRemoved_refused :
    findings (log.erase assistant) [current] =
      [.unanswered "sorting" isSort.consequence [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem ownerRemoved_refused :
    findings (mk (.of "owners") (.owners ⟨[⟨.of "dana", []⟩], none⟩) :: log.erase owners)
        [current] =
      [.unanswered "sorting" restatement.consequence [] [.of "restated"],
       .unanswered "sorting" isSort.consequence [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

/-- Of two owners, one confirming is enough. -/
theorem secondOwner_confirmed :
    Confirmed (mk (.of "owners") (.owners ⟨[⟨.of "richard", []⟩, ⟨.of "dana", []⟩], none⟩) ::
      log.erase owners) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-- `claude` writes its own confirmation of the restatement as an owner's. -/
def selfConfirmed : Statement := mk (.of "self") (answerBody ⟨.of "claude", none⟩ restatement)

theorem selfConfirmed_refused :
    findings [owners, assistant, selfConfirmed, sortAnswer] [current] =
      [.unanswered "sorting" restatement.consequence [] [.of "self"]] := by
  decide +kernel

theorem selfConfirmed_ignored : Confirmed (log ++ [selfConfirmed]) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-- The revision with the decision dropped from those it keeps. -/
def dropped : Revision := revision "revision 2" [(notEmpty, .derived)] []

theorem dropped_refused : findings log [dropped] = [.unkept "sorting" (.of "sort")] := by
  decide +kernel

theorem droppedRetracted_confirmed :
    Confirmed (log ++ [mk (.of "retract-sort") (.retraction ⟨⟨.of "richard", none⟩, .of "sort"⟩)])
      [dropped] :=
  findings_eq_nil_iff.mp (by decide +kernel)

theorem foreign_refused :
    findings (log ++ [{ mk (.of "revoke") (.revocation ⟨⟨.of "richard", none⟩, .of "assistant"⟩) with
        project := .of "sorting-projct" }]) [current] =
      [.foreign (.of "revoke")] := by
  decide +kernel

theorem fork_refused :
    findings [owners, restated] [revision "revision 2" [(notEmpty, .fork)] []] =
      [.fork "sorting" notEmpty.consequence] := by
  decide +kernel

theorem unsettled_refused :
    findings [owners, restated] [revision "revision 2" [(notEmpty, .unsettled)] []] =
      [.unanswered "sorting" notEmpty.consequence [] []] := by
  decide +kernel

/-- `claude` confirms the second consequence, recording no source. -/
def sourcelessAnswer : Statement := mkWith " " (.of "sort") (answerBody underDelegation isSort)

theorem sourceless_refused :
    findings [owners, assistant, restated, sourcelessAnswer] [current] =
      [.sourceless (.of "sort"), .unanswered "sorting" isSort.consequence [] [],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

/-- Its authority traces back, so it counts: what is missing is its source, not its authority. -/
theorem sourceless_counted :
    Counts project declared [owners, assistant, restated, sourcelessAnswer] sourcelessAnswer :=
  counts_iff.mp (by decide +kernel)

/-- `claude` answers the consequence recorded as derived. -/
def derivedAnswer : Statement := mk (.of "derived") (answerBody underDelegation notEmpty)

theorem derivedAnswered_refused :
    findings (log ++ [derivedAnswer]) [current] =
      [.statusDisagrees "sorting" notEmpty.consequence [.of "derived"],
       .unkept "sorting" (.of "derived")] := by
  decide +kernel

theorem ownerUnrecorded_refused :
    findings [owners, restated]
        [{ record := "sorting", text := "revision 2", standing := .unconfirmed, shown := [],
           kept := [] }] =
      [.ownerUnrecorded "sorting" [.of "restated"]] := by
  decide +kernel

/-- The owner also confirms the second consequence. -/
def ownerAnswer : Statement := mk (.of "owner-sort") (answerBody ⟨.of "richard", none⟩ isSort)

/-- The owner, as the recorded answerer. -/
def richardAnswerer : Answerer := .owner (.of "richard")

/-- The revision, recording the owner's answer to the second consequence, keeping `kept`. -/
def byRichard (kept : List (Question × Verdict × Answerer)) : Revision :=
  revision "revision 2" [(notEmpty, .derived), (isSort, .answered richardAnswerer .confirmed)] kept

/-- The status names the owner; the deliverable keeps only the assistant's answer. -/
theorem otherAnswerer_refused :
    findings (log ++ [ownerAnswer]) [byRichard keptNow] =
      [.keptDisagrees "sorting" isSort.consequence] := by
  decide +kernel

/-- Both answers are in the log, and kept. -/
theorem bothKept_confirmed :
    Confirmed (log ++ [ownerAnswer])
      [byRichard (keptNow ++ [(isSort, .confirmed, richardAnswerer)])] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-- The owner confirms the restatement of the next revision. -/
def restatedAgain : Statement :=
  mk (.of "restated-again") (answerBody ⟨.of "richard", none⟩ restatement "revision 3")

/-- The next revision, recording the second consequence as derived, and keeping `kept`. -/
def bothDerived (kept : List (Question × Verdict × Answerer)) : Revision :=
  revision "revision 3" [(notEmpty, .derived), (isSort, .derived)] kept

/-- It says no one answered the second consequence, and keeps an answer to it. -/
theorem derivedKept_refused :
    findings (log ++ [restatedAgain]) [bothDerived keptNow] =
      [.keptDisagrees "sorting" isSort.consequence] := by
  decide +kernel

/-- Retracted, and no longer kept, the consequence can be recorded as derived. -/
theorem derivedRetracted_confirmed :
    Confirmed (log ++ [restatedAgain,
        mk (.of "retract-sort") (.retraction ⟨⟨.of "richard", none⟩, .of "sort"⟩)]) [bothDerived []] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-! ## What else the record carries -/

/-- Whose words the record's source is: the assistant wrote them, having read the code, and the
owner adopted them, which is this statement's own source. -/
def origin : Statement := mk (.of "origin") <| .origin
  { author := ⟨.of "richard", none⟩
    record := "sorting"
    writer := "claude"
    hadRead := "The implementation of the sort, and the change that added it."
    words := "The function sorts its input, and keeps its elements." }

/-- A consequence that rests on an external tool, measured. -/
def measured : Statement := mk (.of "measured") <| .tool
  { author := underDelegation
    record := "sorting"
    consequence := isSort.consequence
    tool := "lake build"
    outcome := .measured "v4.35.0" "the project's own configuration" "built with no warning"
      "20 seconds, 4 GiB" }

/-- A consequence whose tool is not yet measured. -/
def unmeasured : Statement := mk (.of "unmeasured") <| .tool
  { author := underDelegation
    record := "sorting"
    consequence := notEmpty.consequence
    tool := "lake check"
    outcome := .openItem "not run on this project" "whether the record's check passes under it" }

/-- The record carries them for a checker to read, and the check does not ask for them. -/
theorem carried_confirmed : Confirmed (log ++ [origin, measured, unmeasured]) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

/-- The origin's adoption traces back to the owner, and a checker reads what it says. -/
theorem origin_read :
    origins project declared (log ++ [origin]) =
      [(origin, { author := ⟨.of "richard", none⟩
                  record := "sorting"
                  writer := "claude"
                  hadRead := "The implementation of the sort, and the change that added it."
                  words := "The function sorts its input, and keeps its elements." }, true)] := by
  decide +kernel

/-! ## An id two statements share -/

/-- The log, with `dana` a second owner, who declines the restatement `richard` confirmed. -/
def declinedLog : List Statement :=
  mk (.of "owners") (.owners ⟨[⟨.of "richard", []⟩, ⟨.of "dana", []⟩], none⟩) :: log.erase owners ++
    [mk (.of "decline") <| .answer
      { author := ⟨.of "dana", none⟩, record := "sorting", revision := "revision 2",
        consequence := restatement.consequence, kind := restatement.kind,
        predicate := restatement.predicate, verdict := .declined }]

/-- An owner's decline stops the deliverable. -/
theorem ownerDeclined_refused :
    findings declinedLog [current] =
      [.declined "sorting" restatement.consequence [.of "decline"]] := by
  decide +kernel

/-- A tool statement with the decline's id, which would make `Trace` refuse the decline and so drop it
from what is checked, is refused instead, naming the id. -/
theorem declineRepeated_refused :
    findings (declinedLog ++ [{ measured with id := .of "decline" }]) [current] =
      [.repeated (.of "decline")] := by
  decide +kernel

/-- Another statement with the delegation's id, which would break the link of every answer citing it,
and so drop them from what the deliverable must keep, is refused too, naming the id. -/
theorem delegationRepeated_refused :
    findings (log ++ [{ origin with id := .of "assistant" }]) [current] =
      [.repeated (.of "assistant")] := by
  decide +kernel

/-! ## The log as committed -/

/-- A log's statement, as a project commits it: this literal is the text `Statement.print` writes of
`owners`, so `parseLog` reads it back as that statement. -/
def ownersText : String := r#"lean-intent statement 1
kind owners
project sorting-project
id owners
date 2026-10-30
words 1
| As agreed.
principals 1
principal richard
keys 0
no threshold
"#

theorem parseLog_ownersText : parseLog [ownersText] = .ok [owners] :=
  parseLog_eq_ok_iff.mpr (by decide +kernel)

/-- An owners' log as a project commits it: `LeanIntent.Confirmation.Read` reads each entry, which
must reduce to a string literal, from the finished build. -/
def committedLog : OwnersLog := ⟨[ownersText]⟩

/-- Every printed log reads back as its statements. -/
theorem parseLog_printed : parseLog (log.map Statement.print) = .ok log :=
  parseLog_eq_ok_iff.mpr rfl

end LeanIntentExamples.Confirmation
