module

public import LeanIntent.MachineDeclared.Handler
public meta import LeanIntent.MachineDeclared.Handler

public section

namespace LeanIntent.MachineDeclared

open Lean Elab in
meta initialize registerDerivingHandler ``CoveredMachine handler

end LeanIntent.MachineDeclared
