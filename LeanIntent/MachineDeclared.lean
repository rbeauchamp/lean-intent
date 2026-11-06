module

public import LeanIntent.MachineDeclared.Handler
public meta import LeanIntent.MachineDeclared.Handler

/-!
# `deriving LeanIntent.CoveredMachine`: the handler's registration

Importing this module gives a project `deriving LeanIntent.CoveredMachine`. The handler it
registers, `LeanIntent.MachineDeclared.handler`, and everything the handler runs are declared in
`LeanIntent.MachineDeclared.Handler`, whose module comment says what the handler writes and what it
refuses.

The registration is a module of its own for the reason `LeanIntent.Declared` gives for the handler
of `LeanIntent.HasCode`: the handler's programs run in two phases. Lean runs them while it
elaborates a declaration that derives its coverage, so this module imports them with `meta`, and
marks the registration `meta`. The audit of declared types' codes (`LeanIntent.CodeAudit`) runs the
same reading of an attestation (`checkAttestation`) after the build, as an ordinary program, so the
programs themselves are not marked `meta`: a declaration marked `meta` can be called only by one
that is.
-/

public section

namespace LeanIntent.MachineDeclared

open Lean Elab in
meta initialize registerDerivingHandler ``CoveredMachine handler

end LeanIntent.MachineDeclared
