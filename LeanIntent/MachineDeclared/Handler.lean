module

public import LeanIntent.Machines
public import LeanIntent.Declared.Handler

/-!
# The machines a project declares

A structure a project declares whose values carry their own memory type is covered as a machine
(`LeanIntent.CoveredMachine`) by `deriving LeanIntent.CoveredMachine` on the declaration (or
`deriving instance LeanIntent.CoveredMachine for T`). The module `LeanIntent.MachineDeclared`
registers the handler; this module declares it, with everything it runs. The handler below reads the
declaration through Lean's environment, never through its source text. It covers a structure, one constructor
with no indices that is neither recursive nor of a mutual declaration, living in `Type 1` once its
universe levels are zero, whose constructor has exactly three fields:

* the first a type of `Type`, the *memory*;
* one of the other two of the memory's type, the *initial memory*;
* and the other a function from the memory and an *input* type to the pair of an *output* type and
  the memory, the *step*, where the input and output types are types of `Type` naming no field.

The fields' names and the order of the last two are the project's; each field's role is read from
its type alone, and no two fields have one role, since the memory's type is no function. The
parameters may be types or values, as in an agent indexed by an interface whose percept and action
types it computes. The handler writes:

* the isomorphism between the type and the machines from the input to the output type
  (`instCoveredMachineT.iso`), which takes a value to the machine whose memory, initial memory and
  step are its fields of those roles, and a machine back to the constructor applied to its fields in
  the declaration's order; Lean's kernel checks that each map undoes the other, by the eta rule of
  each structure;
* the proof that the type stands for the machines through that isomorphism
  (`instCoveredMachineT.stands`), through the private constructor of `Machine.Stands` that admits a
  declared structure, which no other code of the library applies;
* the instance of `CoveredMachine` that carries the two, for every value of the parameters at which
  Lean's instance resolution finds a code (`LeanIntent.HasCode`) for the input type and for the
  output type.

The handler refuses, and so leaves not covered, every other declaration, saying why: one that is not
a structure of that shape, one that does not live in `Type 1`, an input or output type that names a
field or is not a type of `Type`, `LeanIntent.Machine` itself, which the library covers through the
identity, and a type that is already covered as a machine.

What the handler's output rests on: that it reads the constructor's fields and their roles as Lean's
environment records them, which is its own code below and not checked by Lean's kernel; and that no
other code applies the private constructor of `Machine.Stands`. Lean's privacy is a rule of name
resolution, so the `constructor` tactic or a metaprogram can still apply it. The audit of declared
types' codes (`LeanIntent.CodeAudit`) decides the second for a declaration: it reads every
attestation of this kind that the declaration depends on with `checkAttestation`, which reads the
roles through `readRoles`, the handler's own function, and compares, by Lean's kernel, the type, the
input and output types and where the isomorphism takes the constructor applied to its fields with
what the declaration fixes. An isomorphism is fixed by its forward map, and the forward map of a
structure by where it takes the constructor applied to its fields, by the structure's eta rule, so
this fixes the
isomorphism. The handler runs `checkAttestation` on what it writes and fails rather than write an
attestation the audit refuses, so the two agree on every type the handler covers.

In a `module` file the handler writes the isomorphism and the instance as exposed definitions, so
that a module that imports the structure's can reduce them, as the proofs of the checks' verdicts
do, and reads the attestation it wrote in the module's private scope (`withoutExporting`), since the
public scope holds a theorem's statement without its proof. A structure that is not public there,
because it is marked `private` or because no `public section` holds it and it is not marked
`public`, has a private name, and so has everything the handler writes for it
(`Declared.writtenName`); Lean exports no instance whose name is private, so such a structure is
covered in its own module only. For such a structure the handler writes as a `noncomputable section`
does, as the handler of `LeanIntent.HasCode` does for a type that is not public and for the reason
`LeanIntent.Declared.Handler` gives: what Lean's compiler refuses of a program whose type it reads
differently in the scope other modules see is left without compiled code, with no error, and
statements and proofs reduce it all the same. One command that derives a public structure together
with one that is not is refused, since Lean runs the handler for both in the private scope and the
public structure's coverage would be private too.
-/

public section

namespace LeanIntent.MachineDeclared

open Lean Elab Command Term Meta

/-- The positions of the fields of a structure declared as a machine, and its input and output types
under the parameters it is read at. -/
structure Roles where
  /-- The position of the field that holds the memory type. -/
  memory : Nat
  /-- The position of the field that holds the initial memory. -/
  initial : Nat
  /-- The position of the field that holds the step. -/
  step : Nat
  /-- The input type. -/
  input : Expr
  /-- The output type. -/
  output : Expr

/-- The constructor of `Machine.Stands` that admits a structure a project declares. -/
def standsDecl : MetaM Name := do
  let info ← getConstInfoInduct ``Machine.Stands
  let some c := info.ctors.find? fun c =>
      (privateToUserName? c).getD c == `LeanIntent.Machine.Stands.decl
    | throwError "LeanIntent.CoveredMachine: `Machine.Stands` has no constructor `decl`"
  return c

/-- Why the declaration `indVal` cannot be read as a machine, read from what Lean records of it. -/
@[expose] def refusal? (indVal : InductiveVal) : Option String :=
  if indVal.isUnsafe then some "it is unsafe"
  else if indVal.numIndices != 0 then some "it is an inductive family with indices"
  else if indVal.ctors.length != 1 then some "it does not have exactly one constructor"
  else if indVal.isRec || indVal.numNested != 0 then some "it is recursive"
  else if indVal.all.length != 1 then some "it is one of a mutual declaration"
  else if indVal.name == ``Machine then
    some "`LeanIntent.Machine` is covered by the library itself, through the identity"
  else none

/-- Whether the expression `e` names one of the local variables `fs`. -/
@[expose] def namesAny (e : Expr) (fs : Array Expr) : Bool :=
  fs.any fun f => e.containsFVar f.fvarId!

/-- The roles of the fields of `indVal`'s constructor, at the universe levels `us` and applied to
the parameters `as`: exactly three fields, the first a type of `Type`, the memory; one of the other
two of the memory's type; and the other of type `memory → input → output × memory`, read after
unfolding reducible definitions, where the input and output types are types of `Type` that name no
field. Throws an error saying why otherwise. -/
def readRoles (indVal : InductiveVal) (us : List Level) (as : Array Expr) : MetaM Roles := do
  let fail {α : Type} (why : String) : MetaM α :=
    throwError "LeanIntent.CoveredMachine: `{.ofConstName indVal.name}` is not covered: {why}"
  let some c := indVal.ctors.head? | fail "it has no constructor"
  let info ← getConstInfoCtor c
  let type ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) as
  forallTelescope type fun fs _ => do
    unless fs.size == 3 do
      fail "its constructor does not have exactly three fields: a memory type, an initial memory and a step"
    let mem := fs[0]!
    unless ← Declared.isType0 (← inferType mem) do
      fail "its first field is not a type of `Type`, the memory"
    let step? (t : Expr) : MetaM (Option (Expr × Expr)) := do
      let .forallE _ a b _ ← whnfR t | return none
      unless a.cleanupAnnotations == mem && !b.hasLooseBVars do return none
      let .forallE _ i c _ ← whnfR b | return none
      if c.hasLooseBVars then return none
      let c ← whnfR c
      let some (o, m') := c.app2? ``Prod | return none
      unless m' == mem do return none
      let i := i.cleanupAnnotations
      if namesAny i fs || namesAny o fs then
        fail "the input or output type of its step names a field"
      unless ← Declared.isType0 (← inferType i) do fail "its input type is not a type of `Type`"
      unless ← Declared.isType0 (← inferType o) do fail "its output type is not a type of `Type`"
      return some (i, o)
    let t1 := (← inferType fs[1]!).cleanupAnnotations
    let t2 := (← inferType fs[2]!).cleanupAnnotations
    if (← whnfR t1) == mem then
      let some (i, o) ← step? t2
        | fail "its third field is not a step `memory → input → output × memory`"
      return { memory := 0, initial := 1, step := 2, input := i, output := o }
    if (← whnfR t2) == mem then
      let some (i, o) ← step? t1
        | fail "its second field is not a step `memory → input → output × memory`"
      return { memory := 0, initial := 2, step := 1, input := i, output := o }
    fail "neither of its last two fields has the memory's type, the initial memory"

/-- The isomorphism between `T as`, of the roles `r`, and the machines from its input to its output
type: forth, the machine whose memory, initial memory and step are the fields of those roles; back,
the constructor applied to a machine's fields in the declaration's order. Each map undoes the other
by the eta rule of each structure, which Lean's kernel checks. -/
def mkIso (indVal : InductiveVal) (us : List Level) (as : Array Expr) (r : Roles) :
    MetaM Expr := do
  let W := mkAppN (mkConst indVal.name us) as
  let I := r.input
  let O := r.output
  let machine := mkApp2 (mkConst ``Machine) I O
  let toFn ← withLocalDeclD `w W fun w => do
    let get (k : Nat) := Expr.proj indVal.name k w
    mkLambdaFVars #[w] (mkApp5 (mkConst ``Machine.mk) I O (get r.memory) (get r.initial)
      (get r.step))
  let invFn ← withLocalDeclD `x machine fun x => do
    let mut fields : Array Expr := #[(mkApp3 (mkConst ``Machine.Memory) I O x), x, x]
    fields := fields.set! r.initial (mkApp3 (mkConst ``Machine.initial) I O x)
    fields := fields.set! r.step (mkApp3 (mkConst ``Machine.step) I O x)
    mkLambdaFVars #[x] (mkAppN (mkConst indVal.ctors.head! us) (as ++ fields))
  let invTo ← withLocalDeclD `w W fun w => do mkLambdaFVars #[w] (← mkEqRefl w)
  let toInv ← withLocalDeclD `x machine fun x => do mkLambdaFVars #[x] (← mkEqRefl x)
  return mkAppN (mkConst ``MachineIso.mk) #[W, I, O, toFn, invFn, invTo, toInv]

/-- Whether the declaration `ci` is an attestation the handler writes, where `ctor` is the private
constructor of `Machine.Stands` that admits a declared structure (`standsDecl`). It is one when `ci`
is a theorem whose statement does not name `ctor` and whose value names it once, as the whole value
under its `fun` binders, applied to a type, an input type, an output type and an isomorphism, where:

* the type, put in weak head normal form, is `T as` for a structure `T` at universe level zero that
  the handler covers (`refusal?`, `readRoles`), applied to its parameters `as`;
* the input and output types are those `readRoles` reads from `T`'s declaration at `as`;
* the isomorphism takes `T`'s constructor, applied to `as` and to fields of the memory, initial
  memory and step roles, to the machine of those fields.

Lean's kernel decides each equality by its definitional equality. Returns the type attested,
printed, with `none` when the attestation is the handler's, or the reason it is not. The type is
`none` when the attestation is refused before its type is read. -/
def checkAttestation (ctor : Name) (ci : ConstantInfo) : MetaM (Option String × Option String) := do
  let .thmInfo v := ci | return (none, some "it is not a theorem")
  if (Cone.exprRefs v.type []).contains ctor then
    return (none, some "its statement names the constructor")
  unless (Cone.exprRefs v.value []).count ctor == 1 do
    return (none, some "its value does not name the constructor exactly once")
  lambdaTelescope v.value fun _ body => do
    unless body.isAppOfArity ctor 4 do
      return (none, some "its value is not one application of the constructor under `fun` binders")
    let #[α, I, O, e] := body.getAppArgs | unreachable!
    let ty := toString (← ppExpr α)
    let fail (why : String) : MetaM (Option String × Option String) := return (some ty, some why)
    let α' ← whnf α
    let .const T us := α'.getAppFn | fail "the type is not a structure applied to its parameters"
    let some (.inductInfo indVal) := (← getEnv).find? T
      | fail "the type is not a structure applied to its parameters"
    if let some why := refusal? indVal then
      return ← fail s!"the handler does not cover `{T}`: {why}"
    unless us.all (·.normalize == Level.zero) do
      return ← fail "the type is not taken at universe level zero"
    let as := α'.getAppArgs
    unless as.size == indVal.numParams do
      return ← fail "the type is not a structure applied to its parameters"
    let roles ← try readRoles indVal us as
      catch ex => return ← fail (← ex.toMessageData.toString)
    let kernelEq (a b : Expr) : MetaM Bool := do
      return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
    unless ← kernelEq α (mkAppN (mkConst T us) as) do
      return ← fail "Lean's kernel does not find the type to be its declaration applied to its parameters"
    unless ← kernelEq I roles.input do
      return ← fail "Lean's kernel does not find its input type to be the one the declaration fixes"
    unless ← kernelEq O roles.output do
      return ← fail "Lean's kernel does not find its output type to be the one the declaration fixes"
    let stepTy ← withLocalDeclD `M (mkSort Level.one) fun M => do
      mkLambdaFVars #[M] (← mkArrow M (← mkArrow I (mkApp2 (mkConst ``Prod [0, 0]) O M)))
    let ok ← withLocalDeclD `M (mkSort Level.one) fun M =>
      withLocalDeclD `a M fun a =>
        withLocalDeclD `s (stepTy.beta #[M]) fun s => do
          let mut fields : Array Expr := #[M, a, s]
          fields := fields.set! roles.initial a
          fields := fields.set! roles.step s
          let lhs := mkApp (mkApp4 (mkConst ``MachineIso.to) α I O e)
            (mkAppN (mkConst indVal.ctors.head! us) (as ++ fields))
          kernelEq lhs (mkApp5 (mkConst ``Machine.mk) I O M a s)
    unless ok do
      return ← fail s!"its isomorphism does not take `{indVal.ctors.head!}` applied to its fields to the machine of their roles"
    return (some ty, none)

/-- Writes the isomorphism, the attestation and the instance of `CoveredMachine` for the structure
`declName`, each under the name Lean gives a declaration written there (`Declared.writtenName`) and
as `Declared.addFun` adds a definition or a theorem: a definition exposed, and following the scope
as one written there does. -/
def mkCoveredMachine (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  if let some why := refusal? indVal then
    throwError "LeanIntent.CoveredMachine: `{.ofConstName declName}` is not covered: {why}"
  let instName := (← getCurrNamespace) ++
    (← liftTermElabM <| Deriving.mkInstName ``CoveredMachine declName)
  let act ← Declared.writtenName
  let isoName := act (instName ++ `iso)
  let standsName := act (instName ++ `stands)
  let instName := act instName
  let ctor ← liftTermElabM standsDecl
  liftTermElabM do
    let us := indVal.levelParams.map fun _ => Level.zero
    let type := indVal.type.instantiateLevelParams indVal.levelParams us
    forallBoundedTelescope type indVal.numParams fun xs body => do
      withNewBinderInfos (xs.map fun x => (x.fvarId!, .implicit)) do
        match ← whnf body with
        | .sort l =>
          unless l.normalize == Level.ofNat 2 do
            throwError "LeanIntent.CoveredMachine: `{.ofConstName declName}` is not covered: it does not live in `Type 1`"
        | _ =>
          throwError "LeanIntent.CoveredMachine: `{.ofConstName declName}` is not covered: it does not live in `Type 1`"
        let roles ← readRoles indVal us xs
        let W := mkAppN (mkConst declName us) xs
        if (← synthInstance? (mkApp (mkConst ``CoveredMachine) W)).isSome then
          throwError "LeanIntent.CoveredMachine: `{.ofConstName declName}` is already covered as a machine"
        let I := roles.input
        let O := roles.output
        Declared.addFun isoName xs (mkApp3 (mkConst ``MachineIso) W I O)
          (← mkIso indVal us xs roles) false
        let isoApp := mkAppN (mkConst isoName) xs
        Declared.addFun standsName xs (mkApp4 (mkConst ``Machine.Stands) W I O isoApp)
          (mkApp4 (mkConst ctor) W I O isoApp) true
        withLocalDecl `instIn .instImplicit (mkApp (mkConst ``HasCode) I) fun iI =>
          withLocalDecl `instOut .instImplicit (mkApp (mkConst ``HasCode) O) fun iO => do
            Declared.addFun instName (xs ++ #[iI, iO]) (mkApp (mkConst ``CoveredMachine) W)
              (mkAppN (mkConst ``CoveredMachine.mk)
                #[W, I, O, iI, iO, isoApp, mkAppN (mkConst standsName) xs]) false
        addInstance instName .global (prio := 1000)
  -- The audit's reading of what the handler wrote, so that no structure the handler covers gets an
  -- attestation the audit would refuse (`LeanIntent.CodeAudit`).
  let (_, why?) ← liftTermElabM <| withoutExporting do
    checkAttestation ctor (← getConstInfo standsName)
  if let some why := why? then
    throwError "LeanIntent.CoveredMachine: the coverage written for `{.ofConstName declName}` fails the audit of declared types' codes: {why}"

/-- The deriving handler of `CoveredMachine`. For structures that are not public in a `module` file,
whose coverage is private (`Declared.writtenName`), it writes as a `noncomputable section` does, as
the handler of `HasCode` does (`Declared.handler`). It refuses a command that derives a public
structure together with one that is not, in a `module` file: Lean runs the handler for all of a
command's types in the private scope when one of them is private
(`Lean.Elab.applyDerivingHandlers`), which would make the public structure's coverage private. -/
def handler (declNames : Array Name) : CommandElabM Bool := do
  unless ← declNames.allM isInductive do
    return false
  if (← getEnv).header.isModule && declNames.any isPrivateName then
    let pub := declNames.toList.filter (!isPrivateName ·)
    unless pub.isEmpty do
      throwError "LeanIntent.CoveredMachine: {MessageData.andList (pub.map fun n => m!"`{.ofConstName n}`")} cannot be derived by this command: the command also derives a structure that is not public, so Lean would make every coverage it writes private; derive the public structures in a command of their own"
  let hidden := (← getEnv).header.isModule && !(← getScope).isPublic
  withScope (fun sc => { sc with isNoncomputable := sc.isNoncomputable || hidden }) do
    for n in declNames do
      mkCoveredMachine n
  return true

end LeanIntent.MachineDeclared
