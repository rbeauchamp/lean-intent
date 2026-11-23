module

public import LeanIntent.Render.Text
public meta import LeanIntent.Render.Text

public section

namespace LeanIntent.Render

open Lean Meta Elab

syntax (name := renderIntent) "#render_intent " ident : command

@[command_elab renderIntent]
meta def elabRenderIntent : Command.CommandElab := fun stx => asking do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl)

syntax (name := renderIntentExact) "#render_intent_exact " ident : command

@[command_elab renderIntentExact]
meta def elabRenderIntentExact : Command.CommandElab := fun stx => asking do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl .exact)

syntax (name := renderIntentAt) "#render_intent_at " ident (ppSpace colGt term:max)+ : command

@[command_elab renderIntentAt]
meta def elabRenderIntentAt : Command.CommandElab := fun stx => asking do
  let f := stx[1]
  let args : Array Syntax := stx[2].getArgs
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let text ← Command.liftTermElabM do
    let e ← Term.withoutErrToSorry <| Term.elabTerm (Syntax.mkApp ⟨f⟩ (args.map (⟨·⟩))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then
      throwError "the values must determine every parameter:{indentExpr e}"
    let .const c us := e.getAppFn
      | throwError "expected {decl} applied to values, found{indentExpr e}"
    unless c == decl do throwError "expected {decl} applied to values, found{indentExpr e}"
    renderAt decl us e.getAppArgs
  logInfo text

syntax (name := answerTextsCmd) "#answer_texts " ident ident : command

@[command_elab answerTextsCmd]
meta def elabAnswerTexts : Command.CommandElab := fun stx => asking do
  let ex ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let texts ← Command.liftTermElabM do
    let ci ← getConstInfo decl
    answerTexts ex (mkConst decl (ci.levelParams.map .param))
  for text in texts do logInfo text

end LeanIntent.Render
