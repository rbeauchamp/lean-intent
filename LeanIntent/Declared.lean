module

public import LeanIntent.Declared.Handler
public meta import LeanIntent.Declared.Handler
public meta import Lean.Elab.Deriving.Basic

/-!
# `deriving LeanIntent.HasCode`: the handler's registration

Importing this module gives a project `deriving LeanIntent.HasCode`. The handler it registers,
`LeanIntent.Declared.handler`, and everything the handler runs are declared in
`LeanIntent.Declared.Handler`, whose module comment says what the handler writes and what it
refuses.

The registration is a module of its own because the handler's programs run in two phases. Lean runs
them while it elaborates a declaration that derives its code, so this module imports them with
`meta`, and marks the registration `meta`. The audit of declared types' codes
(`LeanIntent.CodeAudit`) runs the same reading of an attestation (`checkAttestation`) after the
build, as an ordinary program, so the programs themselves are not marked `meta`: a declaration
marked `meta` can be called only by one that is.
-/

public section

namespace LeanIntent.Declared

open Lean Elab in
meta initialize registerDerivingHandler ``HasCode handler

end LeanIntent.Declared
