module

public import LeanIntent.Degenerate
public import LeanIntent.Cone
public import LeanIntent.Loaded
public import Lean.Elab.Deriving.Basic
public import Lean.Elab.Deriving.Util
import Lean.Meta.Eqns

public section

namespace LeanIntent.Declared

open Lean Elab Command Term Meta Parser.Term

@[expose] def chainCode (cs : List Expr) : Expr :=
  cs.foldr (fun c acc => mkApp2 (mkConst ``Ty.prod) c acc) (mkConst ``Ty.unit)

@[expose] def sumCode : List Expr → Expr
  | [] => mkConst ``Ty.unit
  | [c] => c
  | c :: cs => mkApp2 (mkConst ``Ty.sum) c (sumCode cs)

def chainStx (vs : List Term) : TermElabM Term := asking do
  match vs with
  | [] => `(())
  | v :: vs => `(Prod.mk $v $(← chainStx vs))

def injStx (k i : Nat) (v : Term) : TermElabM Term := asking do
  if k == 1 then return v
  let mut t ← if i + 1 == k then pure v else `(Sum.inl $v)
  for _ in [0:i] do
    t ← `(Sum.inr $t)
  return t

@[expose] def refusal? (indVal : InductiveVal) : Option String :=
  if indVal.isUnsafe then some "it is unsafe"
  else if indVal.numIndices != 0 then some "it is an inductive family with indices"
  else if indVal.ctors.isEmpty then some "it has no constructor, and so no empty value"
  else none

structure Ctor where
  name : Name
  fields : Array (Name × Expr)

def isType0 (e : Expr) : MetaM Bool := asking do
  match ← whnf e with
  | .sort l => return l.normalize == Level.one
  | _ => return false

def withInsts {α : Type} (xs : List Expr) (acc : Array Expr) (k : Array Expr → TermElabM α) :
    TermElabM α := asking do
  match xs with
  | [] => k acc
  | x :: xs =>
    withLocalDecl (← mkFreshUserName `inst) .instImplicit (mkApp (mkConst ``HasCode) x)
      fun inst => withInsts xs (acc.push x |>.push inst) k

def withParams {α : Type} (indVal : InductiveVal)
    (k : Array Expr → Array Expr → Expr → TermElabM α) : TermElabM α := asking do
  let us := indVal.levelParams.map fun _ => Level.zero
  let type := indVal.type.instantiateLevelParams indVal.levelParams us
  forallBoundedTelescope type indVal.numParams fun xs body => do
    unless ← isType0 body do
      throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: it does not live in `Type`"
    for x in xs do
      unless ← isType0 (← inferType x) do
        throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its parameter `{x}` is not a type of `Type`"
    withInsts xs.toList #[] fun binders => k xs binders (mkAppN (mkConst indVal.name us) xs)

def ctors (indVal : InductiveVal) (xs : Array Expr) : TermElabM (List Ctor) := asking do
  let us := indVal.levelParams.map fun _ => Level.zero
  indVal.ctors.mapM fun c => do
    let info ← getConstInfoCtor c
    let type ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) xs
    return { name := c, fields := ← ctorFields indVal.name c type #[] }
where
  ctorFields (indName ctorName : Name) (type : Expr) (fields : Array (Name × Expr)) :
      TermElabM (Array (Name × Expr)) := asking do
    match type with
    | .forallE n t b _ =>
      let t := t.cleanupAnnotations
      if b.hasLooseBVars then
        throwError "LeanIntent.HasCode: `{.ofConstName indName}` is not covered: the type of a field after `{n}` of `{.ofConstName ctorName}` depends on `{n}`"
      unless ← isType0 (← inferType t) do
        throwError "LeanIntent.HasCode: `{.ofConstName indName}` is not covered: the field `{n}` of `{.ofConstName ctorName}` has type `{t}`, which is not a type of `Type`"
      ctorFields indName ctorName b (fields.push (n, t))
    | _ => return fields

@[expose] def codeWith {m : Type → Type} [Monad m] (indVal : InductiveVal) (xs : Array Expr) (cs : List Ctor)
    (inst : Expr → m Expr) : m Expr := do
  let codeOf (t : Expr) : m Expr := return mkApp2 (mkConst ``HasCode.code) t (← inst t)
  let ps ← xs.toList.mapM codeOf
  let reps ← cs.mapM fun c => return chainCode (← c.fields.toList.mapM (codeOf ·.2))
  return mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name) (chainCode ps) (sumCode reps)

def code (indVal : InductiveVal) (xs : Array Expr) (cs : List Ctor) : TermElabM Expr := asking <|
  codeWith indVal xs cs fun t => do
    let some inst ← synthInstance? (mkApp (mkConst ``HasCode) t)
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return inst

def addFun (name : Name) (binders : Array Expr) (type value : Expr) (thm : Bool) : TermElabM Unit := asking do
  let type ← mkForallFVars binders type
  let value ← mkLambdaFVars binders value
  if thm then
    addDecl (.thmDecl { name, levelParams := [], type, value })
  else
    let isMeta := (← read).isMetaSection
    withExporting <| addAndCompile (logCompileErrors := !(← read).isNoncomputableSection || isMeta)
        (markMeta := isMeta) <| .defnDecl
      { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
    setReducibleAttribute name

def standsDecl : MetaM Name := asking do
  let info ← getConstInfoInduct ``Ty.Stands
  let some c := info.ctors.find? fun c => (privateToUserName? c).getD c == `LeanIntent.Ty.Stands.decl
    | throwError "LeanIntent.HasCode: `Ty.Stands` has no constructor `decl`"
  return c

inductive GField where
  | data (type : Expr)
  | ref (sort : Nat) (doms : Array Expr)

@[expose] def GField.isRef : GField → Bool
  | .ref _ _ => true
  | .data _ => false

structure GCtor where
  name : Name
  numParams : Nat
  fields : Array GField

@[expose] def GCtor.isBase (c : GCtor) : Bool := !c.fields.any GField.isRef

private def containsAnyExprFVar (e : Expr) (xs : Array Expr) : Bool :=
  xs.any fun x => match x.fvarId? with | some id => e.containsFVar id | none => false

def readGroup (indVal : InductiveVal) (xs : Array Expr) : TermElabM (Array (Expr × Array GCtor)) := asking do
  let notCovered {α : Type} (why : MessageData) : TermElabM α :=
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: {why}"
  let recVal ← getConstInfoRec (mkRecName indVal.name)
  let us := recVal.levelParams.map fun _ => Level.zero
  let type ← instantiateForall (recVal.type.instantiateLevelParams recVal.levelParams us) xs
  forallBoundedTelescope type recVal.numMotives fun motives rest => do
    let mut sorts : Array Expr := #[]
    for m in motives do
      let s ← forallTelescope (← inferType m) fun as _ => do
        if h : as.size = 1 then
          inferType as[0]
        else
          notCovered m!"a type of its group, nested or declared, is an inductive family with indices"
      unless ← isType0 (← inferType s) do
        notCovered m!"the type `{s}` of its group does not live in `Type`"
      sorts := sorts.push s
    forallBoundedTelescope rest recVal.numMinors fun minors _ => do
      let mut ctors : Array (Array GCtor) := sorts.map fun _ => #[]
      for minor in minors do
        let (k, ctor) ← forallTelescope (← inferType minor) fun args concl => do
          let some k := motives.idxOf? concl.getAppFn
            | notCovered m!"a minor premise of its recursor is not about a motive"
          let .app _ conclArg := concl
            | notCovered m!"a minor premise of its recursor is not about a constructor"
          let .const cname _ := conclArg.getAppFn
            | notCovered m!"a minor premise of its recursor is not about a constructor"
          let cinfo ← getConstInfoCtor cname
          let rule : RecursorRule := { ctor := cname, nfields := cinfo.numFields, rhs := default }
          let fs := args.extract 0 rule.nfields
          let mut refs : Vector (Option (Nat × Array Expr)) fs.size := Vector.replicate fs.size none
          for ih in args.extract rule.nfields args.size do
            let (fi, r) ← forallTelescope (← inferType ih) fun ys body => do
              let some l := motives.idxOf? body.getAppFn
                | notCovered m!"an induction hypothesis of `{.ofConstName rule.ctor}` is not about a motive"
              let .app _ x := body
                | notCovered m!"an induction hypothesis of `{.ofConstName rule.ctor}` is not about a field"
              let some fi := fs.finIdxOf? x.getAppFn
                | notCovered m!"an induction hypothesis of `{.ofConstName rule.ctor}` is not about a field"
              let field := fs[fi]
              unless x.getAppArgs == ys do
                notCovered m!"a recursive field of `{.ofConstName rule.ctor}` is not applied to its arguments"
              let dom ← ys.mapM fun y => inferType y
              if dom.any (containsAnyExprFVar · fs) then
                notCovered m!"an argument of the field `{field}` of `{.ofConstName rule.ctor}` depends on a field"
              if dom.any (containsAnyExprFVar · ys) then
                notCovered m!"an argument of the field `{field}` of `{.ofConstName rule.ctor}` depends on an earlier argument"
              for d in dom do
                unless ← isType0 (← inferType d) do
                  notCovered m!"an argument of the field `{field}` of `{.ofConstName rule.ctor}` is not a type of `Type`"
              return (fi, (l, dom))
            refs := refs.set fi (some r)
          let mut fields := #[]
          for h : fi in [0:fs.size] do
            match refs[fi] with
            | some (l, dom) => fields := fields.push (.ref l dom)
            | none =>
              let t := (← inferType fs[fi]).cleanupAnnotations
              if containsAnyExprFVar t (fs.extract 0 fi) then
                notCovered m!"the type of the field `{fs[fi]}` of `{.ofConstName rule.ctor}` depends on an earlier field"
              unless ← isType0 (← inferType t) do
                notCovered m!"the field `{fs[fi]}` of `{.ofConstName rule.ctor}` has type `{t}`, which is not a type of `Type`"
              fields := fields.push (.data t)
          return (k, { name := cname, numParams := cinfo.numParams, fields })
        ctors := ctors.modify k (·.push ctor)
      return sorts.zip ctors

@[expose] def reached (group : Array (Expr × Array GCtor)) (i : Nat) : Option (Array Bool) := Id.run do
  let next (k : Nat) : List Nat := (group[k]?.map (·.2.toList)).getD [] |>.flatMap fun c =>
    c.fields.toList.filterMap fun | .ref l _ => some l | .data _ => none
  let mut seen : Array Bool := group.map fun _ => false
  let mut todo : List Nat := []
  for l in next i do
    if hl : l < seen.size then
      if !seen[l] then
        seen := seen.set l true hl
        todo := l :: todo
  for _ in [0:group.size] do
    match todo with
    | [] => return some seen
    | l :: rest =>
      todo := rest
      for m in next l do
        if hm : m < seen.size then
          if !seen[m] then
            seen := seen.set m true hm
            todo := m :: todo
  return if todo.isEmpty then some seen else none

@[expose] def reachesItself (group : Array (Expr × Array GCtor)) (i : Nat) : Option Bool :=
  (reached group i).map fun seen => seen[i]?.getD false

@[expose] def rootOf (group : Array (Expr × Array GCtor)) (seen : Array Bool) (i : Nat) : Option Nat :=
  if (group[i]?.map (·.2.any GCtor.isBase)).getD false then some i
  else (List.range group.size).find? fun l =>
    seen[l]?.getD false && (group[l]?.map (·.2.any GCtor.isBase)).getD false

@[expose] def clockName : Name := `LeanIntent.Clock

@[expose] def isClockSort (s : Expr) : Bool := s.getAppFn.isConstOf clockName

@[expose] def reachedClock? (group : Array (Expr × Array GCtor)) (seen : Array Bool) : Option Expr :=
  (List.range group.size).findSome? fun l =>
    match group[l]? with
    | some entry => if seen[l]?.getD false && isClockSort entry.1 then some entry.1 else none
    | none => none

theorem reachedClock?_eq_none_iff (group : Array (Expr × Array GCtor)) (seen : Array Bool) :
    reachedClock? group seen = none ↔
      ∀ l (hl : l < group.size), seen[l]?.getD false = true → isClockSort group[l].1 = false := by
  simp only [reachedClock?, List.findSome?_eq_none_iff, List.mem_range]
  constructor
  · intro h l hl hs
    have hn := h l hl
    rw [Array.getElem?_eq_getElem hl] at hn
    cases hc : isClockSort group[l].1
    · rfl
    · simp [hs, hc] at hn
  · intro h l hl
    rw [Array.getElem?_eq_getElem hl]
    cases hs : seen[l]?.getD false
    · simp
    · simp [h l hl hs]

@[expose] def recCodeWith {m : Type → Type} [Monad m] [MonadError m] [MonadEnv m] [MonadLCtx m]
    (indVal : InductiveVal) (group : Array (Expr × Array GCtor)) (i : Nat)
    (codeOf : Expr → m Expr) : m (Expr × Expr × Expr × Nat) := asking do
  let dataCodes (c : GCtor) : m (List Expr) :=
    c.fields.toList.filterMapM fun | .data t => some <$> codeOf t | .ref _ _ => pure none
  let domCodes (c : GCtor) : m (List Expr) :=
    c.fields.toList.filterMapM fun
      | .data _ => pure none
      | .ref _ doms => do
        match doms.toList with
        | [] => return some (mkConst ``Ty.unit)
        | [d] => return some (← codeOf d)
        | ds => return some (chainCode (← ds.mapM codeOf))
  let targets (c : GCtor) : List Expr :=
    c.fields.toList.filterMap fun
      | .data _ => none
      | .ref l _ => some (mkApp (mkConst ``Ty.ref) (toExpr l))
  let some seen := reached group i
    | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: which types of its group it reaches was not settled"
  if let some s := reachedClock? group seen then
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its values hold values of `{s}`, a `LeanIntent.Clock` that is a type of its recursive group. A code names the types of a group only by their number, so the trivial-witness check could neither read this clock nor refuse it. Hold the clock outside the recursive group, where the check's clock parts reach it"
  let some root := rootOf group seen i
    | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: it has no value, since each constructor of each type of its group that it reaches has a field that holds a value of a type of the group"
  let some rootEntry := group[root]?
    | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` has invalid root index {root}"
  let bases := rootEntry.2.toList.filter GCtor.isBase
  let b := sumCode (← bases.mapM fun c => return chainCode (← dataCodes c))
  let others : List (List GCtor) := group.toList.mapIdx fun k (entry : Expr × Array GCtor) =>
    if k == root then entry.2.toList.filter fun c => !c.isBase else entry.2.toList
  let g := chainCode (← others.mapM fun cs => return chainCode (← cs.mapM fun c => do
    return chainCode [chainCode (← dataCodes c), chainCode (← domCodes c)]))
  let r := chainCode (others.map fun cs => chainCode (cs.map fun c => chainCode (targets c)))
  let kernelTrue (e : Expr) : m Bool := do
    return Kernel.isDefEq (← getEnv) (← getLCtx) e (toExpr true) matches .ok true
  let marked := mkApp4 (mkConst ``List.getD [Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Ty.inhabited) r (toExpr root)) (toExpr i) (toExpr false)
  unless ← kernelTrue marked do
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: it has no value, since each of its constructors has a field that holds a value of a type of its group that has none"
  let grows := if root == i then mkApp2 (mkConst ``Ty.grows) r (toExpr i)
    else mkApp3 (mkConst ``Ty.growsAt) r (toExpr root) (toExpr i)
  unless ← kernelTrue grows do
    throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: its recursive constructors do not build values of every depth, since a type of its group they need has no value"
  return (b, g, r, root)

@[expose] def recRep (b g r : Expr) (root i : Nat) : Expr :=
  if root == i then mkApp4 (mkConst ``Ty.mu) b g r (toExpr i)
  else mkApp5 (mkConst ``Ty.muAt) b g r (toExpr root) (toExpr i)

def recCode (indVal : InductiveVal) (group : Array (Expr × Array GCtor)) (i : Nat) :
    TermElabM (Expr × Expr × Expr × Nat) := asking <|
  recCodeWith indVal group i fun t => do
    let some inst ← synthInstance? (mkApp (mkConst ``HasCode) t)
      | throwError "LeanIntent.HasCode: `{.ofConstName indVal.name}` is not covered: the type `{t}` of one of its fields has no code; derive `LeanIntent.HasCode` for it first if the project declares it"
    return mkApp2 (mkConst ``HasCode.code) t inst

@[expose] def denoteE (c : Expr) : Expr := mkApp (mkConst ``Ty.denote) c

@[expose] def sumType : List Expr → Expr
  | [] => mkConst ``Unit
  | [t] => t
  | t :: ts => mkApp2 (mkConst ``Sum [Level.zero, Level.zero]) t (sumType ts)

@[expose] def injExpr : List Expr → Nat → Expr → Expr
  | [], _, v | [_], _, v => v
  | t :: ts, 0, v => mkApp3 (mkConst ``Sum.inl [Level.zero, Level.zero]) t (sumType ts) v
  | t :: ts, i + 1, v =>
    mkApp3 (mkConst ``Sum.inr [Level.zero, Level.zero]) t (sumType ts) (injExpr ts i v)

@[expose] def chainExpr : List (Expr × Expr) → Expr
  | [] => mkConst ``Unit.unit
  | (c, v) :: fs =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (denoteE c)
      (denoteE (chainCode (fs.map (·.1)))) v (chainExpr fs)

def builtinHeads : MetaM (Array Name) := asking do
  let kernelWhnf (e : Expr) : MetaM Expr := do
    match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok w => return w
    | .error ex =>
      throwError "LeanIntent.HasCode: kernel reduction failed: {ex.toMessageData (← getOptions)}"
  let inductiveHead? (w : Expr) : MetaM (Option Name) := do
    if let .const h _ := w.getAppFn then
      if ← isInductive h then
        return some h
    return none
  let mut heads := #[]
  for (ind, den) in [(``Ty, ``Ty.denote), (``Atom, ``Atom.denote)] do
    for c in (← getConstInfoInduct ind).ctors do
      let newHeads ← forallTelescope (← inferType (mkConst c)) fun args _ => do
        let e := mkApp (mkConst den) (mkAppN (mkConst c) args)
        let w ← kernelWhnf e
        if let some h ← inductiveHead? w then
          return #[h]
        else if c == ``Ty.decl then
          let some rep := args[2]?
            | throwError "LeanIntent.HasCode: unexpected arity for `{.ofConstName c}`"
          let nilNat := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat)
          let expected := mkAppN (mkConst ``Ty.den) #[rep, nilNat]
          if Kernel.isDefEq (← getEnv) (← getLCtx) w expected matches .ok true then
            return #[]
        else if c == ``Ty.atom then
          let some k := args[0]?
            | throwError "LeanIntent.HasCode: unexpected arity for `{.ofConstName c}`"
          let expected := mkApp (mkConst ``Atom.denote) k
          if Kernel.isDefEq (← getEnv) (← getLCtx) w expected matches .ok true then
            return #[]
        else if c == ``Ty.arrow && w.isForall then
          return #[]
        else if c == ``Ty.muAt && w.isAppOfArity ``Bool.rec 4 then
          let ka := w.getAppArgs
          let some fBr := ka[1]?
            | throwError "LeanIntent.HasCode: missing false branch for `{.ofConstName c}`"
          let some tBr := ka[2]?
            | throwError "LeanIntent.HasCode: missing true branch for `{.ofConstName c}`"
          let mut brHeads := #[]
          for br in [tBr, fBr] do
            let some h ← inductiveHead? (← kernelWhnf br)
              | throwError "LeanIntent.HasCode: non-inductive branch for `{.ofConstName c}`: `{br}`"
            brHeads := brHeads.push h
          return brHeads
        throwError "LeanIntent.HasCode: unrecognized built-in denotation for `{.ofConstName c}`: `{w}`"
      heads := heads ++ newHeads
  return heads

def checkRecMaps (group : Array (Expr × Array GCtor)) (root i : Nat) (f : Expr)
    (instOf : Expr → MetaM (Option Expr)) (candidate : Nat → MetaM (Option Expr)) :
    MetaM (Option String) := asking do
  let kernelEq (a b : Expr) : MetaM Bool := do
    return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
  let codeOf (t inst : Expr) : Expr := mkApp2 (mkConst ``HasCode.code) t inst
  let carry (fn : Name) (t inst v : Expr) : Expr :=
    mkApp4 (mkConst fn) t (denoteE (codeOf t inst)) (mkApp2 (mkConst ``HasCode.iso) t inst) v
  let dataParts (c : GCtor) (xs : Array Expr) : MetaM (Option (List (Expr × Expr))) := do
    let mut parts := #[]
    for (fld, x) in c.fields.zip xs do
      if let .data t := fld then
        let some inst ← instOf t | return none
        parts := parts.push (codeOf t inst, carry ``Iso.to t inst x)
    return some parts.toList
  let iFin? : Option (Fin group.size) :=
    if hi : i < group.size then some ⟨i, hi⟩ else none
  let some iFin := iFin?
    | return some "invalid group index"
  let some rootEntry := group[root]?
    | return some "invalid root index"
  let mut baseAlts := #[]
  for c in rootEntry.2.filter GCtor.isBase do
    let mut codes := #[]
    for fld in c.fields do
      if let .data t := fld then
        let some inst ← instOf t | return some s!"the type `{t}` of a field of `{c.name}` has no code"
        codes := codes.push (codeOf t inst)
    baseAlts := baseAlts.push (denoteE (chainCode codes.toList))
  let reduce (e : Expr) : MetaM Expr := do
    let w ← whnf e
    if w.isAppOf ``MuVal.base || w.isAppOf ``MuVal.node then return w
    match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok k => return k
    | .error _ => return w
  let mut maps : Vector (Option Expr) group.size := Vector.replicate group.size none
  maps := maps.set iFin (some f)
  let mut todo : List (Fin group.size) := [iFin]
  for _ in [0:group.size] do
    let k :: rest := todo | return none
    todo := rest
    let some F := maps[k] | return some "a map of the group is missing"
    let (τ, cs) := group[k]
    let .const tName tUs := τ.getAppFn | return some s!"`{τ}` is not an inductive type applied to its parameters"
    let _ := tName
    let mut nb := 0
    let mut nn := 0
    for c in cs do
      let isBase := k.1 == root && c.isBase
      let mut types : Array Expr := #[]
      for fld in c.fields do
        match fld with
        | .data t => types := types.push t
        | .ref l doms =>
          let some entry := group[l]?
            | return some s!"invalid group index {l}"
          types := types.push (← doms.foldrM (fun d acc => mkArrow d acc) entry.1)
      let outcome : Except String (Array (Fin group.size × Expr)) ←
          withLocalDeclsDND (types.mapIdx fun j t => (Name.mkSimple s!"x{j}", t)) fun xs => do
        let lhs ← reduce (mkApp F (mkAppN (mkConst c.name tUs) (τ.getAppArgs ++ xs)))
        let some parts ← dataParts c xs | return .error s!"a field of `{c.name}` has no code"
        if isBase then
          unless lhs.isAppOfArity ``MuVal.base 8 do
            return .error s!"the map does not take `{c.name}` to a base value"
          let .app _ baseVal := lhs
            | return .error s!"the map does not take `{c.name}` to a base value"
          unless ← kernelEq baseVal (injExpr baseAlts.toList nb (chainExpr parts)) do
            return .error s!"the map does not take `{c.name}` to base alternative {nb} holding its fields, each carried through its own type's isomorphism"
          return .ok #[]
        unless lhs.isAppOfArity ``MuVal.node 11 do
          return .error s!"the map does not take `{c.name}` to a node"
        let .app (.app (.app _ cE) d) kids := lhs
          | return .error s!"the map does not take `{c.name}` to a node"
        let some nE := (← whnf (← inferType cE)).app1? ``Fin
          | return .error s!"the node of `{c.name}` has no constructor number"
        unless ← kernelEq (mkApp2 (mkConst ``Fin.val) nE cE) (mkNatLit nn) do
          return .error s!"the map does not take `{c.name}` to the node of constructor {nn}"
        unless ← kernelEq d (chainExpr parts) do
          return .error s!"the node of `{c.name}` does not hold its other fields, each carried through its own type's isomorphism"
        let .forallE _ kidsDom _ _ ← whnf (← inferType kids)
          | return .error s!"the children of `{c.name}` are not numbered"
        let some aE := kidsDom.app1? ``Fin
          | return .error s!"the children of `{c.name}` are not numbered"
        let mut found := #[]
        let mut r := 0
        for (fld, x) in c.fields.zip xs do
          let .ref l doms := fld | continue
          let lFin? : Option (Fin group.size) :=
            if hl : l < group.size then some ⟨l, hl⟩ else none
          let some lFin := lFin?
            | return .error s!"invalid group index {l}"
          let lt := mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``Nat) (mkConst ``instLTNat)
            (mkNatLit r) aE
          let h := mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) (mkNatLit r) aE)
            (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
          let pos := mkApp3 (mkConst ``Fin.mk) aE (mkNatLit r) h
          let .forallE _ yTy _ _ ← whnf (← inferType (mkApp kids pos))
            | return .error s!"the children of `{c.name}` take no element"
          let res : Except String (Option Expr) ← withLocalDeclD `y yTy fun y => do
            let mut argVals := #[]
            for h : q in [0:doms.size] do
              let d := doms[q]
              let some inst ← instOf d | return .error s!"an argument type of `{c.name}` has no code"
              let v ← if doms.size == 1 then pure y else do
                let mut v := y
                for _ in [0:q] do v ← mkAppM ``Prod.snd #[v]
                mkAppM ``Prod.fst #[v]
              argVals := argVals.push (carry ``Iso.inv d inst v)
            let arg := mkAppN x argVals
            let child ← whnfR (mkApp2 kids pos y)
            let some yId := y.fvarId?
              | return .error s!"a child of `{c.name}` has no local variable"
            match maps[lFin], found.find? (·.1 == lFin) with
            | some G, _ | none, some (_, G) =>
              return if ← kernelEq child (mkApp G arg) then .ok none
                else .error s!"a child of `{c.name}` is not the map of its type at the field"
            | none, none =>
              if let some G ← candidate l then
                return if ← kernelEq child (mkApp G arg) then .ok (some G)
                  else .error s!"a child of `{c.name}` is not the map of its type at the field"
              let .app childFn childArg := child
                | return .error s!"a child of `{c.name}` is not a map applied to the field"
              unless ← kernelEq childArg arg do
                return .error s!"a child of `{c.name}` is not a map applied to the field"
              let G := childFn
              if G.hasAnyFVar fun v => v == yId || xs.any (fun x => x.fvarId? == some v) then
                return .error s!"a child of `{c.name}` is not a map of its type"
              return .ok (some G)
          match res with
          | .error why => return .error why
          | .ok (some G) => found := found.push (lFin, G)
          | .ok none => pure ()
          r := r + 1
        return .ok found
      match outcome with
      | .error why => return some why
      | .ok found =>
        for (lFin, G) in found do
          if maps[lFin].isNone then
            maps := maps.set lFin (some G)
            todo := todo ++ [lFin]
      if isBase then nb := nb + 1 else nn := nn + 1
  return if todo.isEmpty then none else some "the maps of the group were not all read"

def checkAttestation (ctor : Name) (ci : ConstantInfo) : MetaM (Option String × Option String) := asking do
  let .thmInfo v := ci | return (none, some "it is not a theorem")
  if (Cone.exprRefs v.type []).contains ctor then
    return (none, some "its statement names the constructor")
  unless (Cone.exprRefs v.value []).count ctor == 1 do
    return (none, some "its value does not name the constructor exactly once")
  lambdaTelescope v.value fun binders body => do
    unless body.isAppOfArity ctor 5 do
      return (none, some "its value is not one application of the constructor under `fun` binders")
    let .app (.app (.app (.app (.app _ α) n) ps) r) e := body
      | return (none, some "its value is not one application of the constructor under `fun` binders")
    let ty := toString (← ppExpr α)
    let fail (why : String) : MetaM (Option String × Option String) := return (some ty, some why)
    let α' ← whnf α
    let .const T us := α'.getAppFn | fail "the type is not an inductive type applied to its parameters"
    let some (.inductInfo indVal) := (← getEnv).find? T
      | fail "the type is not an inductive type applied to its parameters"
    if (← builtinHeads).contains T then
      return ← fail s!"`{T}` is a type `LeanIntent.Ty` builds in, whose code is not a declaration's"
    if let some why := refusal? indVal then
      return ← fail s!"the handler does not cover `{T}`: {why}"
    unless us.all (·.normalize == Level.zero) do
      return ← fail "the type is not taken at universe level zero"
    let as := α'.getAppArgs
    unless as.size == indVal.numParams do
      return ← fail "the type is not an inductive type applied to its parameters"
    try
      (withParams indVal fun xs _ _ => discard <| ctors indVal xs : TermElabM Unit).run'
    catch ex => return ← fail (← ex.toMessageData.toString)
    let kernelEq (a b : Expr) : MetaM Bool := do
      return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
    if indVal.isRec || indVal.numNested != 0 then
      let i := indVal.all.idxOf T
      let codeOf (t : Expr) : StateT (Array (Expr × Expr)) MetaM Expr := do
        if let some (_, inst) := (← get).find? (·.1 == t) then
          return mkApp2 (mkConst ``HasCode.code) t inst
        let inst ← mkFreshExprMVar (mkApp (mkConst ``HasCode) t)
        modify (·.push (t, inst))
        return mkApp2 (mkConst ``HasCode.code) t inst
      let read : Except String
          (Option (Array (Expr × Array GCtor) × Nat × Expr × Array (Expr × Expr))) ← try
          let group ← (readGroup indVal as : TermElabM _).run'
          match reachesItself group i with
          | none => pure (Except.error "whether it reaches itself through the fields of its group is not settled")
          | some false => pure (.ok none)
          | some true =>
            let ((b, g, refs, root, ps), insts) ← (do
                let (b, g, refs, root) ← recCodeWith indVal group i codeOf
                return (b, g, refs, root, ← as.toList.mapM codeOf)).run #[]
            pure (.ok (some (group, root, mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name)
              (chainCode ps) (recRep b g refs root i), insts)))
        catch ex => pure (.error (← ex.toMessageData.toString))
      match read with
      | .error why => return ← fail why
      | .ok none => pure ()
      | .ok (some (group, root, derived, insts)) =>
        let given := mkApp3 (mkConst ``Ty.decl) n ps r
        unless ← isDefEq given derived do
          return ← fail "its code is not the one the declaration fixes"
        let derived ← instantiateMVars derived
        let insts ← insts.mapM fun (t, inst) => return (t, ← instantiateMVars inst)
        if derived.hasMVar || insts.any (·.2.hasMVar) then
          return ← fail "its code does not fix an instance of `HasCode` for each of its parts"
        unless ← kernelEq α (mkAppN (mkConst T us) as) do
          return ← fail "Lean's kernel does not find the type to be its declaration applied to its parameters"
        unless ← kernelEq given derived do
          return ← fail "Lean's kernel does not find its code to be the one the declaration fixes"
        let instOf (t : Expr) : MetaM (Option Expr) := return (insts.find? (·.1 == t)).map (·.2)
        let candidate (l : Nat) : MetaM (Option Expr) := do
          let nm := ci.name.modifyBase (·.getPrefix ++ Name.mkSimple s!"to{l}")
          return if (← getEnv).contains nm then some (mkAppN (mkConst nm) binders) else none
        if let some why ← checkRecMaps group root i (mkApp3 (mkConst ``Iso.to) α (denoteE given) e)
            instOf candidate then
          return ← fail s!"its isomorphism is not the handler's: {why}"
        return (some ty, none)
    let cs ← (ctors indVal as : TermElabM _).run'
    let (derived, insts) ← (codeWith indVal as cs fun t => do
      let i ← mkFreshExprMVar (mkApp (mkConst ``HasCode) t)
      modify (·.push i)
      return i : StateT (Array Expr) MetaM Expr).run #[]
    let given := mkApp3 (mkConst ``Ty.decl) n ps r
    unless ← isDefEq given derived do
      return ← fail "its code is not the one the declaration fixes"
    let derived ← instantiateMVars derived
    let insts ← insts.mapM instantiateMVars
    if derived.hasMVar || insts.any (·.hasMVar) then
      return ← fail "its code does not fix an instance of `HasCode` for each of its parts"
    let kernelEq (a b : Expr) : MetaM Bool := do
      return Kernel.isDefEq (← getEnv) (← getLCtx) a b matches .ok true
    unless ← kernelEq α (mkAppN (mkConst T us) as) do
      return ← fail "Lean's kernel does not find the type to be its declaration applied to its parameters"
    unless ← kernelEq given derived do
      return ← fail "Lean's kernel does not find its code to be the one the declaration fixes"
    let mut k := as.size
    let mut chains : Array (Ctor × List (Name × Expr × Expr)) := #[]
    for c in cs do
      chains := chains.push (c, (c.fields.toList.zip (insts.extract k (k + c.fields.size)).toList).map
        fun ((x, t), i) => (x, t, i))
      k := k + c.fields.size
    let codeOf (t i : Expr) : Expr := mkApp2 (mkConst ``HasCode.code) t i
    let alts := chains.toList.map fun (_, fs) => denoteE (chainCode (fs.map fun (_, t, i) => codeOf t i))
    for h : j in [0:chains.size] do
      let (c, fs) := chains[j]
      let ok ← withLocalDeclsDND (fs.map fun (x, t, _) => (x, t)).toArray fun xs => do
        let lhs := mkApp4 (mkConst ``Iso.to) α (denoteE given) e
          (mkAppN (mkConst c.name us) (as ++ xs))
        let parts := (fs.zip xs.toList).map fun ((_, t, i), x) =>
          (codeOf t i, mkApp4 (mkConst ``Iso.to) t (denoteE (codeOf t i))
            (mkApp2 (mkConst ``HasCode.iso) t i) x)
        kernelEq lhs (injExpr alts j (chainExpr parts))
      unless ok do
        return ← fail s!"its isomorphism does not take `{c.name}` to alternative {j} holding its fields, each carried through its own type's isomorphism"
    return (some ty, none)

def writtenName : CommandElabM (Name → Name) := asking do
  let env ← getEnv
  return if env.header.isModule && !(← getScope).isPublic then mkPrivateName env else id

private def relIdent (ns n : Name) : Lean.Ident :=
  mkIdent (n.modifyBase (·.replacePrefix ns .anonymous))

private def mkEqIdent (c : Name) : Lean.Ident :=
  let id := addMacroScope `_internal `eqLemma reservedMacroScope
  ⟨Syntax.ident SourceInfo.none (toString c).toRawSubstring id [.decl c []]⟩

def mkStandsAndInstance (declName : Name) (indVal : InductiveVal) (instName codeName isoName standsName : Name)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (args : Array Term) (tStx : Term) :
    CommandElabM Unit := asking do
  let ctor ← liftTermElabM standsDecl
  liftTermElabM <| withParams indVal fun _ binders tApp => do
    let codeE := (← getConstInfoDefn codeName).value.beta binders
    let codeApp := mkAppN (mkConst codeName) binders
    let isoApp := mkAppN (mkConst isoName) binders
    let some (_, ps, rep) := codeE.app3? ``Ty.decl
      | throwError "LeanIntent.HasCode: the code of `{.ofConstName declName}` is not a `Ty.decl`"
    addFun standsName binders (mkApp3 (mkConst ``Ty.Stands) tApp codeApp isoApp)
      (mkAppN (mkConst ctor) #[tApp, toExpr declName, ps, rep, isoApp]) true
  let instRel := relIdent (← getCurrNamespace) instName
  elabCommand (← `(command|
    instance $instRel:ident $binders* : LeanIntent.HasCode $tStx :=
      ⟨@$(mkCIdent codeName) $args*, @$(mkCIdent isoName) $args*, @$(mkCIdent standsName) $args*⟩))
  let (_, why?) ← liftTermElabM <| withoutExporting do
    checkAttestation ctor (← getConstInfo standsName)
  if let some why := why? then
    throwError "LeanIntent.HasCode: the code written for `{.ofConstName declName}` fails the audit of declared types' codes: {why}"

inductive Role where
  | base (ib kb : Nat)
  | node (c : Nat)

structure CtorPlan where
  name : Name
  numParams : Nat
  fields : Array (Option (Nat × Nat))
  role : Role
  alt : Nat

def chainGet (d : Term) (q : Nat) : TermElabM Term := asking do
  match q with
  | 0 => `(Prod.fst $d)
  | q + 1 => chainGet (← `(Prod.snd $d)) q

def chainEq (ps : List Term) : TermElabM Term := asking do
  match ps with
  | [] => `(rfl)
  | p :: ps => `(Prod.ext $p $(← chainEq ps))

def mkRecHasCode (declName : Name) (indVal : InductiveVal) (i : Nat) : CommandElabM Unit := asking do
  let instName := (← getCurrNamespace) ++ (← liftTermElabM <| Deriving.mkInstName ``HasCode declName)
  let codeName := instName ++ `code
  let baseName := instName ++ `base
  let groupName := instName ++ `group
  let refsName := instName ++ `refs
  let sortName := instName ++ `sort
  let isoName := instName ++ `iso
  let standsName := instName ++ `stands
  let toName (k : Nat) := instName ++ Name.mkSimple s!"to{k}"
  let invToName (k : Nat) := instName ++ Name.mkSimple s!"invTo{k}"
  let baseInvName := instName ++ `baseInv
  let algName := instName ++ `alg
  let toGName := instName ++ `toG
  let toInvName := instName ++ `toInv
  let act ← writtenName
  let ns ← getCurrNamespace
  let rel := relIdent ns
  let (plans, root) ← liftTermElabM <| withParams indVal fun xs binders tApp => do
    if (← synthInstance? (mkApp (mkConst ``HasCode) tApp)).isSome then
      throwError "LeanIntent.HasCode: `{.ofConstName declName}` already has a code"
    let group ← readGroup indVal xs
    let (b, g, r, root) ← recCode indVal group i
    let ps ← xs.toList.mapM fun x => do
      let some inst ← synthInstance? (mkApp (mkConst ``HasCode) x)
        | throwError "LeanIntent.HasCode: a parameter of `{.ofConstName declName}` has no code"
      return mkApp2 (mkConst ``HasCode.code) x inst
    addFun (act baseName) binders (mkConst ``Ty) b false
    addFun (act groupName) binders (mkConst ``Ty) g false
    addFun (act refsName) #[] (mkConst ``Ty) r false
    let rep := recRep (mkAppN (mkConst (act baseName)) binders) (mkAppN (mkConst (act groupName)) binders)
      (mkConst (act refsName)) root i
    addFun (act codeName) binders (mkConst ``Ty) (mkApp3 (mkConst ``Ty.decl) (toExpr indVal.name)
      (chainCode ps) rep) false
    let fam ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      let mut body := Lean.mkConst ``Empty
      for j in (List.finRange group.size).reverse do
        body ← mkAppOptM ``cond #[none, mkApp2 (mkConst ``Nat.beq) k (toExpr (j : Nat)), group[j].1, body]
      mkLambdaFVars #[k] body
    addFun (act sortName) binders (← mkArrow (mkConst ``Nat) (mkSort Level.one)) fam false
    let some rootEntry := group[root]?
      | throwError "LeanIntent.HasCode: `{.ofConstName declName}` has invalid root index {root}"
    let kb := (rootEntry.2.filter GCtor.isBase).size
    return (· , root) <| group.mapIdx fun k (entry : Expr × Array GCtor) => Id.run do
      let cs := entry.2
      let mut out : Array CtorPlan := #[]
      let mut nb := 0
      let mut nn := 0
      for h : p in [0:cs.size] do
        let c := cs[p]
        let role := if k == root && c.isBase then Role.base nb kb else Role.node nn
        if k == root && c.isBase then nb := nb + 1 else nn := nn + 1
        let fields : Array (Option (Nat × Nat)) := c.fields.map fun (f : GField) => match f with
          | GField.data _ => none
          | GField.ref l d => some (l, d.size)
        out := out.push ⟨c.name, c.numParams, fields, role, p + 1⟩
      return out
  let K := plans.size
  let nodes (k : Nat) (hk : k < plans.size := by get_elem_tactic) : Nat :=
    (plans[k].filter fun (c : CtorPlan) => c.role matches .node _).size
  let binderStx ← liftTermElabM <| (List.range indVal.numParams).toArray.mapM fun _ => do
    return (mkIdent (← mkFreshUserName `α), mkIdent (← mkFreshUserName `inst))
  let binders ← binderStx.flatMapM fun (a, i) => do
    return #[← `(bracketedBinderF| {$a : Type}), ← `(bracketedBinderF| [$i : LeanIntent.HasCode $a])]
  let args := binderStx.flatMap fun (a, i) => #[a, i]
  let tStx ← `(@$(mkCIdent declName) $(binderStx.map (·.1))*)
  let G ← `(@$(mkCIdent (act sortName)) $args*)
  let B ← `(@$(mkCIdent (act baseName)) $args*)
  let Gr ← `(@$(mkCIdent (act groupName)) $args*)
  let R : Term := mkCIdent (act refsName)
  let iq : Term := quote i
  let rq : Term := quote root
  let famTy (k : Term) : Term :=
    if root == i then Syntax.mkApp (mkCIdent ``LeanIntent.Ty.MuOf) #[B, Gr, R, iq, k]
    else Syntax.mkApp (mkCIdent ``LeanIntent.Ty.MuAtOf) #[B, Gr, R, rq, k]
  let algTy ← if root == i then `(LeanIntent.Ty.MuAlg $Gr $R $iq $G)
    else `(LeanIntent.Ty.MuAlgOf $Gr $R (LeanIntent.Ty.muN $R) $G)
  let kId := mkIdent `k
  let famK := famTy kId
  let fold ← `(LeanIntent.Ty.muFold $G (@$(mkCIdent (act baseInvName)) $args*) (@$(mkCIdent (act algName)) $args*))
  let fin (n : Nat) : TermElabM Term := `(⟨$(quote n), of_decide_eq_true rfl⟩)
  let (toDefs, baseAlts, algAlts) ← liftTermElabM do
    let mut toDefs := #[]
    let mut baseAlts := #[]
    let mut algAlts := #[]
    for h : k in [0:K] do
      let mut toAlts := #[]
      for c in plans[k] do
        let holes ← (List.range c.numParams).toArray.mapM fun _ => `(_)
        let xs ← c.fields.mapM fun _ => return (mkIdent (← mkFreshUserName `x) : Term)
        let pat ← `(@$(mkCIdent c.name) $holes* $xs*)
        let datas := (c.fields.zip xs).filterMap fun (f, x) => if f.isNone then some x else none
        let refs := (c.fields.zip xs).filterMap fun (f, x) => f.map fun (l, arr) => (l, arr, x)
        let dataTo ← datas.toList.mapM fun x => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $x)
        let rhs ← match c.role with
          | .base ib kb => do `(LeanIntent.MuVal.base $(← injStx kb ib (← chainStx dataTo)))
          | .node cn => do
            let children ← if refs.isEmpty then `(fun e => e.elim0) else do
              let alts ← refs.mapIdxM fun r (l, n, x) => do
                let ys ← match n with
                  | 0 => pure #[]
                  | 1 => pure #[(mkIdent `y : Term)]
                  | n => (List.range n).toArray.mapM fun q => chainGet (mkIdent `y) q
                let ys ← ys.mapM fun y => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $y)
                let call ← `($(rel (toName l)) ($x $ys*))
                `(matchAltExpr| | ⟨$(quote r), _⟩ => $call)
              if refs.any (·.2.1 > 0) then `(fun e $(mkIdent `y):ident => match e with $alts:matchAlt*)
              else `(fun e _ => match e with $alts:matchAlt*)
            `(LeanIntent.MuVal.node $(← fin cn) $(← chainStx dataTo) $children)
        toAlts := toAlts.push (← `(matchAltExpr| | $pat => $rhs))
        match c.role with
        | .base ib kb =>
          let ys ← datas.mapM fun _ => return (mkIdent (← mkFreshUserName `y) : Term)
          let invVal ← `(@$(mkCIdent c.name) $holes* $(← ys.mapM fun y => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $y))*)
          baseAlts := baseAlts.push (← `(matchAltExpr| | $(← injStx kb ib (← chainStx ys.toList)) => $invVal))
        | .node cn =>
          let d := mkIdent `d
          let ih := mkIdent `ih
          let mut q := 0
          let mut r := 0
          let mut algArgs := #[]
          for f in c.fields do
            match f with
            | none =>
              algArgs := algArgs.push (← `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $(← chainGet d q)))
              q := q + 1
            | some (_, 0) =>
              algArgs := algArgs.push (← `($ih $(← fin r) ()))
              r := r + 1
            | some (_, 1) =>
              algArgs := algArgs.push (← `(fun y => $ih $(← fin r)
                (LeanIntent.Iso.to LeanIntent.HasCode.iso y)))
              r := r + 1
            | some (_, n) =>
              let ys ← (List.range n).toArray.mapM fun _ => return mkIdent (← mkFreshUserName `y)
              let coded ← ys.toList.mapM fun y => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $(⟨y.raw⟩):term)
              algArgs := algArgs.push (← `(fun $ys* => $ih $(← fin r) $(← chainStx coded)))
              r := r + 1
          let dPat : Term ← if datas.isEmpty then `(_) else pure d
          let ihPat : Term ← if refs.isEmpty then `(_) else pure ih
          algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), ⟨$(quote cn), _⟩, $dPat, $ihPat =>
            @$(mkCIdent c.name) $holes* $algArgs*))
      let n := nodes k
      if n > 0 then
        let nn := mkIdent `n
        let hh := mkIdent `h
        algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), ⟨$nn + $(quote n), $hh⟩, _, _ =>
          absurd $hh (LeanIntent.Ty.not_add_lt $nn $(quote n))))
      else
        algAlts := algAlts.push (← `(matchAltExpr| | $(quote k), c, _, _ => c.elim0))
      let x := mkIdent `x
      toDefs := toDefs.push (← `(command|
        @[expose] def $(rel (toName k)) $binders* ($x : $G $(quote k)) :
            $(famTy (quote k)) :=
          match $x:ident with $toAlts:matchAlt*))
    let nn := mkIdent `n
    algAlts := algAlts.push (← `(matchAltExpr| | $nn + $(quote K), c, _, _ => c.elim0))
    return (toDefs, baseAlts, algAlts)
  elabCommand (← `(command| mutual $toDefs:command* end))
  elabCommand (← `(command|
    @[expose] def $(rel baseInvName) $binders* (x : LeanIntent.Ty.denote $B) : $G $rq :=
      match x with $baseAlts:matchAlt*))
  elabCommand (← `(command|
    @[expose] def $(rel algName) $binders* : $algTy :=
      fun j c d ih => match j, c, d, ih with $algAlts:matchAlt*))
  let toGAlts ← liftTermElabM do
    let mut alts := #[]
    for k in [0:K] do
      alts := alts.push (← `(matchAltExpr| | $(quote k) => @$(mkCIdent (act (toName k))) $args*))
    alts.push <$> `(matchAltExpr| | _ + $(quote K) => fun e => nomatch e)
  elabCommand (← `(command|
    @[expose] def $(rel toGName) $binders* ($kId : Nat) : $G $kId → $famK :=
      match $kId:ident with $toGAlts:matchAlt*))
  let (invToDefs, toInvAlts) ← liftTermElabM do
    let mut invToDefs := #[]
    let mut toInvAlts := #[]
    for h : k in [0:K] do
      let eqs ← if plans[k].isEmpty then pure #[] else withoutExporting do
        let some eqs ← Lean.Meta.getEqnsFor? (act (toName k))
          | throwError "LeanIntent.HasCode: no equation theorems for `{.ofConstName (act (toName k))}`"
        pure eqs
      let mut invToAlts := #[]
      for c in plans[k] do
        let some eqName := eqs[c.alt - 1]?
          | throwError "LeanIntent.HasCode: missing equation theorem {c.alt} for `{.ofConstName c.name}`"
        let eqLemma := mkEqIdent eqName
        let holes ← (List.range c.numParams).toArray.mapM fun _ => `(_)
        let xs ← c.fields.mapM fun _ => return (mkIdent (← mkFreshUserName `x) : Term)
        let pat ← `(@$(mkCIdent c.name) $holes* $xs*)
        let ctorFn ← `(@$(mkCIdent c.name) $holes*)
        let fieldPrfs ← (c.fields.zip xs).toList.mapM fun (f, x) => match f with
          | none => `(LeanIntent.Iso.inv_to LeanIntent.HasCode.iso $x)
          | some (l, n) => do
            let ys ← (List.range n).toArray.mapM fun _ => return (mkIdent (← mkFreshUserName `y) : Term)
            let ih ← `($(rel (invToName l)) ($x $ys*))
            let p ← if n == 0 then pure ih else
              `(by simp only [LeanIntent.Iso.inv_to] <;> exact $ih)
            ys.foldrM (fun y p => `(funext fun $(⟨y.raw⟩):ident => $p)) p
        let prf ← match fieldPrfs with
          | [] => `(rfl)
          | p :: ps => ps.foldlM (fun acc q => `(congr $acc $q)) (← `(congrArg $ctorFn $p))
        invToAlts := invToAlts.push (← `(matchAltExpr| | $pat => by rw [$eqLemma:ident]; exact $prf))
        let nData := (c.fields.filter Option.isNone).size
        let refArities := c.fields.filterMap (·.map (·.2))
        match c.role with
        | .base ib kb =>
          let ys ← (List.range nData).toArray.mapM fun _ => return (mkIdent (← mkFreshUserName `y) : Term)
          let z := mkIdent `z
          let pz ← chainEq (← ys.toList.mapM fun y => `(LeanIntent.Iso.to_inv LeanIntent.HasCode.iso $y))
          toInvAlts := toInvAlts.push (← `(matchAltExpr| | _, LeanIntent.MuVal.base $(← injStx kb ib (← chainStx ys.toList)) =>
            ($eqLemma ..).trans (congrArg (fun $z => LeanIntent.MuVal.base $(← injStx kb ib z)) $pz)))
        | .node cn =>
          let d := mkIdent `d
          let dPat : Term ← if nData == 0 then `(_) else pure d
          let pd ← chainEq (← (List.range nData).mapM fun q' => do
            `(LeanIntent.Iso.to_inv LeanIntent.HasCode.iso $(← chainGet d q')))
          let kk := mkIdent `kk
          let pk ← if refArities.isEmpty then `(funext fun e => e.elim0) else do
            let alts ← refArities.mapIdxM fun r n => do
              let ih ← `($(rel toInvName) ($kk $(← fin r) $(mkIdent `y)))
              let p ← if n == 0 then pure ih else
                `(by simp only [LeanIntent.Iso.to_inv] <;> exact $ih)
              `(matchAltExpr| | ⟨$(quote r), _⟩ => $p)
            `(funext fun e => funext fun $(mkIdent `y):ident => match e with $alts:matchAlt*)
          let kkPat : Term ← if refArities.isEmpty then `(_) else pure kk
          toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node ⟨$(quote cn), _⟩ $dPat $kkPat =>
            ($eqLemma ..).trans (congr (congrArg (LeanIntent.MuVal.node _) $pd) $pk)))
      let n := nodes k
      if n > 0 then
        let nn := mkIdent `n
        let hh := mkIdent `h
        toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node ⟨$nn + $(quote n), $hh⟩ _ _ =>
          absurd $hh (LeanIntent.Ty.not_add_lt $nn $(quote n))))
      else
        toInvAlts := toInvAlts.push (← `(matchAltExpr| | $(quote k), LeanIntent.MuVal.node c _ _ => c.elim0))
      let x := mkIdent `x
      invToDefs := invToDefs.push (← `(command|
        theorem $(rel (invToName k)) $binders* ($x : $G $(quote k)) :
            $fold ($(mkCIdent (act (toName k))) $x) = $x :=
          match $x:ident with $invToAlts:matchAlt*))
    let nn := mkIdent `n
    toInvAlts := toInvAlts.push (← `(matchAltExpr| | $nn + $(quote K), LeanIntent.MuVal.node c _ _ => c.elim0))
    return (invToDefs, toInvAlts)
  elabCommand (← `(command| mutual $invToDefs:command* end))
  elabCommand (← `(command|
    theorem $(rel toInvName) $binders* {$kId : Nat} (v : $famK) :
        @$(mkCIdent (act toGName)) $args* $kId ($fold v) = v :=
      match $kId:ident, v with $toInvAlts:matchAlt*))
  elabCommand (← `(command|
    @[expose] def $(rel isoName) $binders* :
        LeanIntent.Iso $tStx (LeanIntent.Ty.denote (@$(mkCIdent (act codeName)) $args*)) where
      to := @$(mkCIdent (act (toName i))) $args*
      inv := $fold
      inv_to := @$(mkCIdent (act (invToName i))) $args*
      to_inv := @$(mkCIdent (act toInvName)) $args* $iq))
  mkStandsAndInstance declName indVal instName (act codeName) (act isoName) (act standsName) binders args tStx

def mkHasCode (declName : Name) : CommandElabM Unit := asking do
  let indVal ← getConstInfoInduct declName
  if let some why := refusal? indVal then
    throwError "LeanIntent.HasCode: `{.ofConstName declName}` is not covered: {why}"
  let i := indVal.all.idxOf declName
  let recursive ← liftTermElabM <| withParams indVal fun xs _ _ => do
    if indVal.isRec || indVal.numNested != 0 then
      let some r := reachesItself (← readGroup indVal xs) i
        | throwError "LeanIntent.HasCode: `{.ofConstName declName}` is not covered: whether it reaches itself through the fields of its group was not settled"
      return r
    return false
  if recursive then
    return ← mkRecHasCode declName indVal i
  let instName := (← getCurrNamespace) ++ (← liftTermElabM <| Deriving.mkInstName ``HasCode declName)
  let codeName := instName ++ `code
  let isoName := instName ++ `iso
  let standsName := instName ++ `stands
  let act ← writtenName
  let ns ← getCurrNamespace
  let shapes ← liftTermElabM <| withParams indVal fun xs binders tApp => do
    if (← synthInstance? (mkApp (mkConst ``HasCode) tApp)).isSome then
      throwError "LeanIntent.HasCode: `{.ofConstName declName}` already has a code"
    let cs ← ctors indVal xs
    addFun (act codeName) binders (mkConst ``Ty) (← code indVal xs cs) false
    return cs.map fun c => (c.name, c.fields.size)
  let k := shapes.length
  let binderStx ← liftTermElabM <| (List.range indVal.numParams).toArray.mapM fun _ => do
    return (mkIdent (← mkFreshUserName `α), mkIdent (← mkFreshUserName `inst))
  let binders ← binderStx.flatMapM fun (a, i) => do
    return #[← `(bracketedBinderF| {$a : Type}), ← `(bracketedBinderF| [$i : LeanIntent.HasCode $a])]
  let args := binderStx.flatMap fun (a, i) => #[a, i]
  let tStx ← `(@$(mkCIdent declName) $(binderStx.map (·.1))*)
  let holes ← (List.range indVal.numParams).toArray.mapM fun _ => `(_)
  let (toAlts, invAlts, invToAlts, toInvAlts) ← liftTermElabM do
    let mut toAlts := #[]
    let mut invAlts := #[]
    let mut invToAlts := #[]
    let mut toInvAlts := #[]
    for h : i in [0:k] do
      let (c, m) := shapes[i]
      let vars ← (List.range m).mapM fun _ => return (⟨(mkIdent (← mkFreshUserName `x)).raw⟩ : Term)
      let ctorPat ← `(@$(mkCIdent c) $holes* $(vars.toArray)*)
      let repPat ← injStx k i (← chainStx vars)
      let toVal ← injStx k i (← chainStx (← vars.mapM fun x => `(LeanIntent.Iso.to LeanIntent.HasCode.iso $x)))
      let invVal ← `(@$(mkCIdent c) $holes* $(← vars.toArray.mapM fun x => `(LeanIntent.Iso.inv LeanIntent.HasCode.iso $x))*)
      let anon ← (List.range m).mapM fun _ => `(_)
      let ctorAnon ← `(@$(mkCIdent c) $holes* $(anon.toArray)*)
      let repAnon ← injStx k i (← chainStx anon)
      toAlts := toAlts.push (← `(matchAltExpr| | $ctorPat => $toVal))
      invAlts := invAlts.push (← `(matchAltExpr| | $repPat => $invVal))
      invToAlts := invToAlts.push (← `(matchAltExpr| | $ctorAnon =>
        by dsimp only; try simp only [LeanIntent.Iso.inv_to]))
      toInvAlts := toInvAlts.push (← `(matchAltExpr| | $repAnon =>
        by dsimp only; try simp only [LeanIntent.Iso.to_inv]))
    return (toAlts, invAlts, invToAlts, toInvAlts)
  elabCommand (← `(command|
    @[expose] def $(relIdent ns isoName) $binders* :
        LeanIntent.Iso $tStx (LeanIntent.Ty.denote (@$(mkCIdent (act codeName)) $args*)) where
      to t := match t with $toAlts:matchAlt*
      inv r := match r with $invAlts:matchAlt*
      inv_to t := match t with $invToAlts:matchAlt*
      to_inv r := match r with $toInvAlts:matchAlt*))
  mkStandsAndInstance declName indVal instName (act codeName) (act isoName) (act standsName) binders
    (args.map fun a => ⟨a.raw⟩) tStx

def handler (declNames : Array Name) : CommandElabM Bool := asking do
  unless ← declNames.allM isInductive do
    return false
  if (← getEnv).header.isModule && declNames.any isPrivateName then
    let pub := declNames.toList.filter (!isPrivateName ·)
    unless pub.isEmpty do
      throwError "LeanIntent.HasCode: {MessageData.andList (pub.map fun n => m!"`{.ofConstName n}`")} cannot be derived by this command: the command also derives a type that is not public, so Lean would make every code it writes private; derive the public types in a command of their own"
  let hidden := (← getEnv).header.isModule && !(← getScope).isPublic
  withScope (fun sc => { sc with
    isNoncomputable := sc.isNoncomputable || hidden
    varDecls := #[]
    varUIds := #[]
    includedVars := []
    omittedVars := []
    levelNames := [] }) do
    for n in declNames do
      mkHasCode n
  return true

end LeanIntent.Declared
