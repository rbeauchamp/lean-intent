module

public import LeanIntent.Render.Text
public meta import LeanIntent.Render.Text

/-!
# The commands that show a rendering

`#render_intent e` shows the rendering of the explanation `e`, `#render_intent_exact e` the same in
the exact form, `#render_intent_at e a₁ … aₙ` the rendering of a generic explanation at the
representative values `a₁ … aₙ`, and `#answer_texts e l` the text of each attributed answer of the
list `l` to the explanation `e`, as information. Each runs a program of `LeanIntent.Render.Text`,
whose module comment says what a rendering holds and what is trusted of it.

The commands are a module of their own because the programs run in two phases. Lean runs them while
it elaborates one of these commands, so this module imports them with `meta` and marks each
command's elaborator `meta`. The checks a project runs after its build (`LeanIntent.Confirmation.Read`,
`LeanIntent.Implementation.Read`, `LeanIntent.Execution.Read`) run the same programs as ordinary
ones, so the programs themselves are not marked `meta`: a declaration marked `meta` can be called
only by one that is.
-/

public section

namespace LeanIntent.Render

open Lean Meta Elab

/-- `#render_intent e` shows the rendering of the explanation `e`. -/
syntax (name := renderIntent) "#render_intent " ident : command

@[command_elab renderIntent]
meta def elabRenderIntent : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl)

/-- `#render_intent_exact e` shows the rendering of the explanation `e` in the exact form: with every
implicit argument, by the audited printer. -/
syntax (name := renderIntentExact) "#render_intent_exact " ident : command

@[command_elab renderIntentExact]
meta def elabRenderIntentExact : Command.CommandElab := fun stx => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo (← Command.liftTermElabM <| renderExplanation decl .exact)

/-- `#render_intent_at e a₁ … aₙ` shows the rendering of the generic explanation `e` at the
representative values `a₁ … aₙ`, written as the arguments of an application of `e`, with what they do
not establish of the generic record. -/
syntax (name := renderIntentAt) "#render_intent_at " ident (ppSpace colGt term:max)+ : command

@[command_elab renderIntentAt]
meta def elabRenderIntentAt : Command.CommandElab := fun stx => do
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

/-- `#answer_texts ex e` shows the canonical text of each attributed answer of the list `e` to the
explanation `ex`. -/
syntax (name := answerTextsCmd) "#answer_texts " ident ident : command

@[command_elab answerTextsCmd]
meta def elabAnswerTexts : Command.CommandElab := fun stx => do
  let ex ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let texts ← Command.liftTermElabM do
    let ci ← getConstInfo decl
    answerTexts ex (mkConst decl (ci.levelParams.map .param))
  for text in texts do logInfo text

end LeanIntent.Render
