module

public import LeanIntent.Machines
public import LeanIntent.Declared.Handler

public section

namespace LeanIntent.MachineDeclared

open Lean Elab Command Term Meta

structure Roles where
  memory : Nat
  initial : Nat
  step : Nat
  input : Expr
  output : Expr

def standsDecl : MetaM Name := asking do
  let info ← getConstInfoInduct ``Machine.Stands
  let some c := info.ctors.find? fun c =>
      (privateToUserName? c).getD c == `LeanIntent.Machine.Stands.decl
    | throwError "LeanIntent.CoveredMachine: `Machine.Stands` has no constructor `decl`"
  return c

@[expose] def refusal? (indVal : InductiveVal) : Option String :=
  if indVal.isUnsafe then some "it is unsafe"
  else if indVal.numIndices != 0 then some "it is an inductive family with indices"
  else if indVal.ctors.length != 1 then some "it does not have exactly one constructor"
  else if indVal.isRec || indVal.numNested != 0 then some "it is recursive"
  else if indVal.all.length != 1 then some "it is one of a mutual declaration"
  else if indVal.name == ``Machine then
    some "`LeanIntent.Machine` is covered by the library itself, through the identity"
  else none

@[expose] def namesAny (e : Expr) (fs : Array Expr) : Bool :=
  fs.any fun f => match f.fvarId? with | some id => e.containsFVar id | none => false

def readRoles (indVal : InductiveVal) (us : List Level) (as : Array Expr) : MetaM Roles := asking do
  let fail {α : Type} (why : String) : MetaM α :=
    throwError "LeanIntent.CoveredMachine: `{.ofConstName indVal.name}` is not covered: {why}"
  let some c := indVal.ctors.head? | fail "it has no constructor"
  let info ← getConstInfoCtor c
  let type ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) as
  forallTelescope type fun fs _ => do
    let #[mem, f1, f2] := fs
      | fail "its constructor does not have exactly three fields: a memory type, an initial memory and a step"
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
    let t1 := (← inferType f1).cleanupAnnotations
    let t2 := (← inferType f2).cleanupAnnotations
    if (← whnfR t1) == mem then
      let some (i, o) ← step? t2
        | fail "its third field is not a step `memory → input → output × memory`"
      return { memory := 0, initial := 1, step := 2, input := i, output := o }
    if (← whnfR t2) == mem then
      let some (i, o) ← step? t1
        | fail "its second field is not a step `memory → input → output × memory`"
      return { memory := 0, initial := 2, step := 1, input := i, output := o }
    fail "neither of its last two fields has the memory's type, the initial memory"

def mkIso (indVal : InductiveVal) (us : List Level) (as : Array Expr) (r : Roles) :
    MetaM Expr := asking do
  let some ctorName := indVal.ctors.head?
    | throwError "LeanIntent.CoveredMachine: `{.ofConstName indVal.name}` has no constructor"
  let W := mkAppN (mkConst indVal.name us) as
  let I := r.input
  let O := r.output
  let machine := mkApp2 (mkConst ``Machine) I O
  let toFn ← withLocalDeclD `w W fun w => do
    let get (k : Nat) := Expr.proj indVal.name k w
    mkLambdaFVars #[w] (mkApp5 (mkConst ``Machine.mk) I O (get r.memory) (get r.initial)
      (get r.step))
  let invFn ← withLocalDeclD `x machine fun x => do
    let memVal := mkApp3 (mkConst ``Machine.Memory) I O x
    let initVal := mkApp3 (mkConst ``Machine.initial) I O x
    let stepVal := mkApp3 (mkConst ``Machine.step) I O x
    let fields ← match r.memory, r.initial, r.step with
      | 0, 1, 2 => pure #[memVal, initVal, stepVal]
      | 0, 2, 1 => pure #[memVal, stepVal, initVal]
      | _, _, _ => throwError "LeanIntent.CoveredMachine: invalid field roles for `{.ofConstName indVal.name}`"
    mkLambdaFVars #[x] (mkAppN (mkConst ctorName us) (as ++ fields))
  let invTo ← withLocalDeclD `w W fun w => do mkLambdaFVars #[w] (← mkEqRefl w)
  let toInv ← withLocalDeclD `x machine fun x => do mkLambdaFVars #[x] (← mkEqRefl x)
  return mkAppN (mkConst ``MachineIso.mk) #[W, I, O, toFn, invFn, invTo, toInv]

def checkAttestation (ctor : Name) (ci : ConstantInfo) : MetaM (Option String × Option String) := asking do
  let .thmInfo v := ci | return (none, some "it is not a theorem")
  if (Cone.exprRefs v.type []).contains ctor then
    return (none, some "its statement names the constructor")
  unless (Cone.exprRefs v.value []).count ctor == 1 do
    return (none, some "its value does not name the constructor exactly once")
  lambdaTelescope v.value fun _ body => do
    unless body.isAppOfArity ctor 4 do
      return (none, some "its value is not one application of the constructor under `fun` binders")
    let .app (.app (.app (.app _ α) I) O) e := body
      | return (none, some "its value is not one application of the constructor under `fun` binders")
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
    let some ctorName := indVal.ctors.head?
      | return ← fail s!"the handler does not cover `{T}`: it has no constructor"
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
          let fields ← match roles.memory, roles.initial, roles.step with
            | 0, 1, 2 => pure #[M, a, s]
            | 0, 2, 1 => pure #[M, s, a]
            | _, _, _ => return false
          let lhs := mkApp (mkApp4 (mkConst ``MachineIso.to) α I O e)
            (mkAppN (mkConst ctorName us) (as ++ fields))
          kernelEq lhs (mkApp5 (mkConst ``Machine.mk) I O M a s)
    unless ok do
      return ← fail s!"its isomorphism does not take `{ctorName}` applied to its fields to the machine of their roles"
    return (some ty, none)

def mkCoveredMachine (declName : Name) : CommandElabM Unit := asking do
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
      withNewBinderInfos (xs.filterMap fun x => x.fvarId?.map (·, .implicit)) do
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
  let (_, why?) ← liftTermElabM <| withoutExporting do
    checkAttestation ctor (← getConstInfo standsName)
  if let some why := why? then
    throwError "LeanIntent.CoveredMachine: the coverage written for `{.ofConstName declName}` fails the audit of declared types' codes: {why}"

def handler (declNames : Array Name) : CommandElabM Bool := asking do
  unless ← declNames.allM isInductive do
    return false
  if (← getEnv).header.isModule && declNames.any isPrivateName then
    let pub := declNames.toList.filter (!isPrivateName ·)
    unless pub.isEmpty do
      throwError "LeanIntent.CoveredMachine: {MessageData.andList (pub.map fun n => m!"`{.ofConstName n}`")} cannot be derived by this command: the command also derives a structure that is not public, so Lean would make every coverage it writes private; derive the public structures in a command of their own"
  let hidden := (← getEnv).header.isModule && !(← getScope).isPublic
  withScope (fun sc => { sc with
    isNoncomputable := sc.isNoncomputable || hidden
    varDecls := #[]
    varUIds := #[]
    includedVars := []
    omittedVars := []
    levelNames := [] }) do
    for n in declNames do
      mkCoveredMachine n
  return true

end LeanIntent.MachineDeclared
