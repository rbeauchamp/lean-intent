module

public import LeanIntent.Confirmation
public import LeanIntentExamples.Sorting

public section

namespace LeanIntentExamples.Confirmation

open LeanIntent LeanIntent.Confirmation LeanIntentExamples.Sorting

@[expose] def reason : String :=
  "The owner confirmed that the output is an ascending rearrangement of the input, which leaves \
    one such function."

@[expose] def assistantAnswerer : Answerer := .onBehalf (.of "claude") (.of "assistant") reason

@[expose] def sortingAnswers : List (Attributed (List Int → List Int)) :=
  [⟨⟨⟨"is Lean's merge sort", .entailment, fun f => f = sort⟩, .confirmed⟩, assistantAnswerer⟩]

@[expose] def sortingDeliverable : Deliverable (List Int → List Int) where
  record := sorting
  explanation := sortingExplained
  answers := sortingAnswers
  keeps := (keeps_iff _ _).mpr fun a ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact fun f hf => sorting_o5_eq.relates hf sorting_meets_sort
    · exact nomatch ha

@[expose] def project : Ident := .of "sorting-project"

@[expose] def declared : Statement.Owners := ⟨[⟨.of "richard", []⟩], none⟩

@[expose] def mkWith (text : String) (id : Ident) (body : Statement.Body) : Statement :=
  { project, id, date := ⟨2026, 10, 30, by decide⟩, source := .words text, body }

@[expose] def mk (id : Ident) (body : Statement.Body) : Statement := mkWith "As agreed." id body

@[expose] def owners : Statement := mk (.of "owners") (.owners declared)

@[expose] def assistant : Statement := mk (.of "assistant") <| .delegation
  { delegator := ⟨.of "richard", none⟩
    delegate := ⟨.of "claude", []⟩
    scope := ⟨.only ["sorting"], true, true, true⟩
    mayPassOn := false }

@[expose] def answerBody (author : Authority) (q : Question) (revision : String := "revision 2") :
    Statement.Body :=
  .answer
    { author, record := "sorting", revision, consequence := q.consequence, kind := q.kind,
      predicate := q.predicate, verdict := .confirmed }

@[expose] def notEmpty : Question := ⟨"is not the empty-list function", .entailment, "fun f => f ≠ nilSort"⟩

@[expose] def isSort : Question := ⟨"is Lean's merge sort", .entailment, "fun f => f = sort"⟩

@[expose] def underDelegation : Authority := ⟨.of "claude", some (.of "assistant")⟩

@[expose] def restatementBody (author : Authority) (revision : String := "revision 2")
    (verdict : Verdict := .confirmed) : Statement.Body :=
  .answer (restatementAnswer author "sorting" revision verdict)

@[expose] def restated : Statement := mk (.of "restated") (restatementBody ⟨.of "richard", none⟩)

@[expose] def sortAnswer : Statement := mkWith reason (.of "sort") (answerBody underDelegation isSort)

@[expose] def log : List Statement := [owners, assistant, restated, sortAnswer]

abbrev byOwner : Restatement := .confirmed (.of "richard")

@[expose] def revision (text : String) (shown : List (Question × Settled byOwner))
    (kept : List (Question × Verdict × Answerer)) : Revision :=
  { record := "sorting", text, standing := byOwner, shown, kept }

@[expose] def shownNow : List (Question × Settled byOwner) :=
  [(notEmpty, .derived), (isSort, .answered assistantAnswerer .confirmed)]

@[expose] def keptNow : List (Question × Verdict × Answerer) := [(isSort, .confirmed, assistantAnswerer)]

@[expose] def current : Revision := revision "revision 2" shownNow keptNow

theorem confirmed : Confirmed log [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

@[expose] def revised : Revision := revision "revision 3" shownNow keptNow

theorem revised_refused :
    findings log [revised] =
      [.unanswered "sorting" .restatement [.of "restated"] [],
       .unanswered "sorting" (.consequence isSort.consequence) [.of "sort"] []] := by
  decide +kernel

theorem revised_standing : logStanding project declared log revised = .unconfirmed := by
  decide +kernel

@[expose] def isSort' : Question := { isSort with predicate := "fun f => f = sort, redefined" }

theorem meaningChanged_refused :
    findings log [revision "revision 2"
        [(notEmpty, .derived), (isSort', .answered assistantAnswerer .confirmed)]
        [(isSort', .confirmed, assistantAnswerer)]] =
      [.unanswered "sorting" (.consequence isSort.consequence) [.of "sort"] [],
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
      [.unanswered "sorting" (.consequence isSort.consequence) [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem delegationRemoved_refused :
    findings (log.erase assistant) [current] =
      [.unanswered "sorting" (.consequence isSort.consequence) [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem ownerRemoved_refused :
    findings (mk (.of "owners") (.owners ⟨[⟨.of "dana", []⟩], none⟩) :: log.erase owners)
        [current] =
      [.unanswered "sorting" .restatement [] [.of "restated"],
       .unanswered "sorting" (.consequence isSort.consequence) [] [.of "sort"],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem secondOwner_confirmed :
    Confirmed (mk (.of "owners") (.owners ⟨[⟨.of "richard", []⟩, ⟨.of "dana", []⟩], none⟩) ::
      log.erase owners) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

@[expose] def selfConfirmed : Statement := mk (.of "self") (restatementBody ⟨.of "claude", none⟩)

theorem selfConfirmed_refused :
    findings [owners, assistant, selfConfirmed, sortAnswer] [current] =
      [.unanswered "sorting" .restatement [] [.of "self"]] := by
  decide +kernel

theorem selfConfirmed_ignored : Confirmed (log ++ [selfConfirmed]) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

@[expose] def dropped : Revision := revision "revision 2" [(notEmpty, .derived)] []

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
      [.unanswered "sorting" (.consequence notEmpty.consequence) [] []] := by
  decide +kernel

@[expose] def sourcelessAnswer : Statement := mkWith " " (.of "sort") (answerBody underDelegation isSort)

theorem sourceless_refused :
    findings [owners, assistant, restated, sourcelessAnswer] [current] =
      [.sourceless (.of "sort"), .unanswered "sorting" (.consequence isSort.consequence) [] [],
       .unbacked "sorting" isSort.consequence [.of "sort"]] := by
  decide +kernel

theorem sourceless_counted :
    Counts project declared [owners, assistant, restated, sourcelessAnswer] sourcelessAnswer :=
  counts_iff.mp (by decide +kernel)

@[expose] def derivedAnswer : Statement := mk (.of "derived") (answerBody underDelegation notEmpty)

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

@[expose] def ownerAnswer : Statement := mk (.of "owner-sort") (answerBody ⟨.of "richard", none⟩ isSort)

@[expose] def richardAnswerer : Answerer := .owner (.of "richard")

@[expose] def byRichard (kept : List (Question × Verdict × Answerer)) : Revision :=
  revision "revision 2" [(notEmpty, .derived), (isSort, .answered richardAnswerer .confirmed)] kept

theorem otherAnswerer_refused :
    findings (log ++ [ownerAnswer]) [byRichard keptNow] =
      [.keptDisagrees "sorting" isSort.consequence] := by
  decide +kernel

theorem bothKept_confirmed :
    Confirmed (log ++ [ownerAnswer])
      [byRichard (keptNow ++ [(isSort, .confirmed, richardAnswerer)])] :=
  findings_eq_nil_iff.mp (by decide +kernel)

@[expose] def restatedAgain : Statement :=
  mk (.of "restated-again") (restatementBody ⟨.of "richard", none⟩ "revision 3")

@[expose] def bothDerived (kept : List (Question × Verdict × Answerer)) : Revision :=
  revision "revision 3" [(notEmpty, .derived), (isSort, .derived)] kept

theorem derivedKept_refused :
    findings (log ++ [restatedAgain]) [bothDerived keptNow] =
      [.keptDisagrees "sorting" isSort.consequence] := by
  decide +kernel

theorem derivedRetracted_confirmed :
    Confirmed (log ++ [restatedAgain,
        mk (.of "retract-sort") (.retraction ⟨⟨.of "richard", none⟩, .of "sort"⟩)]) [bothDerived []] :=
  findings_eq_nil_iff.mp (by decide +kernel)

@[expose] def origin : Statement := mk (.of "origin") <| .origin
  { author := ⟨.of "richard", none⟩
    record := "sorting"
    writer := "claude"
    hadRead := "The implementation of the sort, and the change that added it."
    words := "The function sorts its input, and keeps its elements." }

@[expose] def measured : Statement := mk (.of "measured") <| .tool
  { author := underDelegation
    record := "sorting"
    consequence := isSort.consequence
    tool := "lake build"
    outcome := .measured "v4.35.0" "the project's own configuration" "built with no warning"
      "20 seconds, 4 GiB" }

@[expose] def unmeasured : Statement := mk (.of "unmeasured") <| .tool
  { author := underDelegation
    record := "sorting"
    consequence := notEmpty.consequence
    tool := "lake check"
    outcome := .openItem "not run on this project" "whether the record's check passes under it" }

theorem carried_confirmed : Confirmed (log ++ [origin, measured, unmeasured]) [current] :=
  findings_eq_nil_iff.mp (by decide +kernel)

theorem origin_read :
    origins project declared (log ++ [origin]) =
      [(origin, { author := ⟨.of "richard", none⟩
                  record := "sorting"
                  writer := "claude"
                  hadRead := "The implementation of the sort, and the change that added it."
                  words := "The function sorts its input, and keeps its elements." }, true)] := by
  decide +kernel

@[expose] def declinedLog : List Statement :=
  mk (.of "owners") (.owners ⟨[⟨.of "richard", []⟩, ⟨.of "dana", []⟩], none⟩) :: log.erase owners ++
    [mk (.of "decline") (restatementBody ⟨.of "dana", none⟩ "revision 2" .declined)]

theorem ownerDeclined_refused :
    findings declinedLog [current] =
      [.declined "sorting" .restatement [.of "decline"]] := by
  decide +kernel

theorem declineRepeated_refused :
    findings (declinedLog ++ [{ measured with id := .of "decline" }]) [current] =
      [.repeated (.of "decline")] := by
  decide +kernel

theorem delegationRepeated_refused :
    findings (log ++ [{ origin with id := .of "assistant" }]) [current] =
      [.repeated (.of "assistant")] := by
  decide +kernel

@[expose] def ownersText : String := r#"lean-intent statement 1
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

@[expose] def committedLog : OwnersLog := ⟨[ownersText]⟩

theorem parseLog_printed : parseLog (log.map Statement.print) = .ok log :=
  parseLog_eq_ok_iff.mpr rfl

@[expose] def homonymQuestion : Question :=
  ⟨restatementConsequence, .entailment, "fun f => f = sort"⟩

@[expose] def homonymRevision : Revision :=
  revision "revision 2" [(homonymQuestion, .answered assistantAnswerer .confirmed)]
    [(homonymQuestion, .confirmed, assistantAnswerer)]

@[expose] def homonymAnswer : Statement :=
  mkWith reason (.of "homonym") (answerBody underDelegation homonymQuestion)

theorem homonym_confirmed :
    Confirmed [owners, assistant, restated, homonymAnswer] [homonymRevision] :=
  findings_eq_nil_iff.mp (by decide +kernel)

theorem homonym_consequence_does_not_settle_restatement :
    findings [owners, assistant, homonymAnswer] [homonymRevision] =
      [.unanswered "sorting" .restatement [] []] := by
  decide +kernel

theorem homonym_restatement_does_not_settle_consequence :
    findings [owners, restated] [revision "revision 2" [(homonymQuestion, .unsettled)] []] =
      [.unanswered "sorting" (.consequence restatementConsequence) [] []] := by
  decide +kernel

end LeanIntentExamples.Confirmation
