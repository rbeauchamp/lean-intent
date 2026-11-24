module

public import Lean.Expr
public import LeanIntent.Print.Token

public section

namespace LeanIntent.Print

open Lean (Name Level Expr Literal BinderInfo)

inductive Prec where
  | term | simple | head | arg
  deriving @[expose] DecidableEq

@[expose] def Prec.tight : Prec → Bool
  | .head | .arg => true
  | _ => false

@[expose] def Prec.isArg : Prec → Bool
  | .arg => true
  | _ => false

@[expose] def Prec.isTerm : Prec → Bool
  | .term => true
  | _ => false

@[expose] def paren (b : Bool) (ts : List Tok) : List Tok := if b then .lparen :: ts ++ [.rparen] else ts

@[expose] def compOk (s : String) : Bool := rawable s || !(s.toList.contains '»')

@[expose] def atomOk : Name → Bool
  | .str .anonymous s => compOk s
  | _ => false

@[expose] def nameOk (n : Name) : Bool :=
  match comps n with
  | some ss => !ss.isEmpty && ss.all compOk
  | none => false

@[expose] def lookup (n : Name) : List Name → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (lookup n ms).map (· + 1)

@[expose] def natOf : Level → Option Nat
  | .zero => some 0
  | .succ l => (natOf l).map (· + 1)
  | _ => none

@[expose] def levelOfNat : Nat → Level
  | 0 => .zero
  | k + 1 => .succ (levelOfNat k)

@[expose] def addN (l : Level) : Nat → Level
  | 0 => l
  | k + 1 => .succ (addN l k)

@[expose] def prLevel : Level → Bool → Option (List Tok)
  | .zero, _ => some [.num 0]
  | .succ l, atom =>
    match natOf l with
    | some k => some [.num (k + 1)]
    | none => (prLevel l true).map fun t => paren atom (t ++ [.plus, .num 1])
  | .max a b, atom => do
    let ta ← prLevel a true
    let tb ← prLevel b true
    some (paren atom (.kwMax :: ta ++ tb))
  | .imax a b, atom => do
    let ta ← prLevel a true
    let tb ← prLevel b true
    some (paren atom (.kwImax :: ta ++ tb))
  | .param n, _ => if atomOk n then some [.ident n] else none
  | .mvar _, _ => none

@[expose] def prLevels : List Level → Option (List Tok)
  | [] => some []
  | [l] => prLevel l false
  | l :: ls => do
    let t ← prLevel l false
    let r ← prLevels ls
    some (t ++ .comma :: r)

@[expose] def prUnivs (us : List Level) : Option (List Tok) :=
  match us with
  | [] => some []
  | us => (prLevels us).map fun t => .dotBrace :: t ++ [.rbrace]

@[expose] def levelTail (a : Level) : List Tok → Option (Level × List Tok)
  | .plus :: .num k :: ts => some (addN a k, ts)
  | ts => some (a, ts)

mutual
@[expose] def psLevelAtom : Nat → List Tok → Option (Level × List Tok)
  | 0, _ => none
  | f + 1, ts =>
    match ts with
    | .num k :: ts => some (levelOfNat k, ts)
    | .ident n :: ts => some (.param n, ts)
    | .lparen :: ts => do
      let (l, ts) ← psLevel f ts
      match ts with
      | .rparen :: ts => some (l, ts)
      | _ => none
    | _ => none

@[expose] def psLevel : Nat → List Tok → Option (Level × List Tok)
  | 0, _ => none
  | f + 1, ts =>
    match ts with
    | .kwMax :: ts => do
      let (a, ts) ← psLevelAtom f ts
      let (b, ts) ← psLevelAtom f ts
      some (.max a b, ts)
    | .kwImax :: ts => do
      let (a, ts) ← psLevelAtom f ts
      let (b, ts) ← psLevelAtom f ts
      some (.imax a b, ts)
    | ts => do
      let (a, ts) ← psLevelAtom f ts
      levelTail a ts
end

@[expose] def psLevels : Nat → List Tok → Option (List Level × List Tok)
  | 0, _ => none
  | f + 1, ts => do
    let (l, ts) ← psLevel (2 * ts.length + 2) ts
    match ts with
    | .comma :: ts => do
      let (ls, ts) ← psLevels f ts
      some (l :: ls, ts)
    | .rbrace :: ts => some ([l], ts)
    | _ => none

@[expose] def psUnivs (ts : List Tok) : Option (List Level × List Tok) :=
  match ts with
  | .dotBrace :: ts => psLevels (ts.length + 1) ts
  | ts => some ([], ts)

@[expose] def openTok : BinderInfo → Tok
  | .default => .lparen
  | .implicit => .lbrace
  | .strictImplicit => .lstrict
  | .instImplicit => .lbrack

@[expose] def closer : BinderInfo → Tok
  | .default => .rparen
  | .implicit => .rbrace
  | .strictImplicit => .rstrict
  | .instImplicit => .rbrack

@[expose] def binderToks (bi : BinderInfo) (n : Name) (t : List Tok) : List Tok :=
  openTok bi :: .ident n :: .colon :: t ++ [closer bi]

@[expose] def isZero : Level → Bool
  | .zero => true
  | _ => false

@[expose] def prSort : Level → Option (List Tok)
  | .zero => some [.kwProp]
  | .succ l => if isZero l then some [.kwType] else (prLevel l true).map (.kwType :: ·)
  | l => (prLevel l true).map (.kwSort :: ·)

@[expose] def letToks (nonDep : Bool) (n : Name) (t v b : List Tok) : List Tok :=
  (if nonDep then .kwHave else .kwLet) :: .ident n :: .colon :: t ++ .colonEq :: v ++
    .semicolon :: b

@[expose] def isArrow : Name → BinderInfo → Bool
  | .anonymous, .default => true
  | _, _ => false

@[expose] def pr (bare : Name → Bool) : List Name → Expr → Prec → Option (List Tok)
  | sc, .bvar i, _ =>
    match sc[i]? with
    | some n => if atomOk n && lookup n sc == some i then some [.ident n] else none
    | none => none
  | sc, .const c us, _ =>
    if nameOk c then
      (prUnivs us).map fun u =>
        if bare c && lookup c sc == none then .ident c :: u else .atSign :: .ident c :: u
    else none
  | _, .sort l, p => (prSort l).map (paren (!isZero l && p.tight))
  | _, .lit (.strVal s), _ => some [.str s]
  | _, .lit (.natVal n), p => some (paren p.tight [.kwNatLit, .num n])
  | sc, .app f a, p => do
    let tf ← pr bare sc f .head
    let ta ← pr bare sc a .arg
    some (paren p.isArg (tf ++ ta))
  | sc, .lam n t b bi, p =>
    if atomOk n then do
      let tt ← pr bare sc t .term
      let tb ← pr bare (n :: sc) b .term
      some (paren (!p.isTerm) (.kwFun :: binderToks bi n tt ++ .darrow :: tb))
    else none
  | sc, .forallE n t b bi, p =>
    if isArrow n bi then do
      let tt ← pr bare sc t .simple
      let tb ← pr bare (n :: sc) b .term
      some (paren (!p.isTerm) (tt ++ .arrow :: tb))
    else if atomOk n then do
      let tt ← pr bare sc t .term
      let tb ← pr bare (n :: sc) b .term
      some (paren (!p.isTerm) (.pi :: binderToks bi n tt ++ .comma :: tb))
    else none
  | sc, .letE n t v b nd, p =>
    if atomOk n then do
      let tt ← pr bare sc t .term
      let tv ← pr bare sc v .term
      let tb ← pr bare (n :: sc) b .term
      some (paren (!p.isTerm) (letToks nd n tt tv tb))
    else none
  | _, _, _ => none

@[expose] def atomStart : List Tok → Bool
  | .ident _ :: _ | .atSign :: _ | .kwProp :: _ | .str _ :: _ | .lparen :: _ => true
  | _ => false

@[expose] def levelStart : List Tok → Bool
  | .num _ :: _ | .ident _ :: _ | .lparen :: _ => true
  | _ => false

@[expose] def opener : Tok → Option BinderInfo
  | .lparen => some .default
  | .lbrace => some .implicit
  | .lstrict => some .strictImplicit
  | .lbrack => some .instImplicit
  | _ => none

mutual
@[expose] def psTerm : Nat → List Name → List Tok → Option (Expr × List Tok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match ts with
    | .kwFun :: ts => do
      let (bi, n, t, ts) ← psBinder f sc ts
      match ts with
      | .darrow :: ts => do
        let (b, ts) ← psTerm f (n :: sc) ts
        some (.lam n t b bi, ts)
      | _ => none
    | .pi :: ts => do
      let (bi, n, t, ts) ← psBinder f sc ts
      match ts with
      | .comma :: ts => do
        let (b, ts) ← psTerm f (n :: sc) ts
        some (.forallE n t b bi, ts)
      | _ => none
    | .kwLet :: ts => psLet f sc false ts
    | .kwHave :: ts => psLet f sc true ts
    | ts => do
      let (a, ts) ← psSimple f sc ts
      match ts with
      | .arrow :: ts => do
        let (b, ts) ← psTerm f (.anonymous :: sc) ts
        some (.forallE .anonymous a b .default, ts)
      | ts => some (a, ts)

@[expose] def psLet : Nat → List Name → Bool → List Tok → Option (Expr × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, nd, ts =>
    match ts with
    | .ident n :: .colon :: ts => do
      let (t, ts) ← psTerm f sc ts
      match ts with
      | .colonEq :: ts => do
        let (v, ts) ← psTerm f sc ts
        match ts with
        | .semicolon :: ts => do
          let (b, ts) ← psTerm f (n :: sc) ts
          some (.letE n t v b nd, ts)
        | _ => none
      | _ => none
    | _ => none

@[expose] def psBinder : Nat → List Name → List Tok → Option (BinderInfo × Name × Expr × List Tok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match ts with
    | o :: .ident n :: .colon :: ts =>
      match opener o with
      | some bi => do
        let (t, ts) ← psTerm f sc ts
        match ts with
        | c :: ts => if c = closer bi then some (bi, n, t, ts) else none
        | [] => none
      | none => none
    | _ => none

@[expose] def psSimple : Nat → List Name → List Tok → Option (Expr × List Tok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match ts with
    | .kwSort :: ts => (psLevelAtom (2 * ts.length + 2) ts).map fun (l, ts) => (.sort l, ts)
    | .kwType :: ts =>
      if levelStart ts then
        (psLevelAtom (2 * ts.length + 2) ts).map fun (l, ts) => (.sort (.succ l), ts)
      else some (.sort (.succ .zero), ts)
    | .kwNatLit :: .num n :: ts => some (.lit (.natVal n), ts)
    | ts => do
      let (h, ts) ← psAtom f sc ts
      psArgs f sc h ts

@[expose] def psArgs : Nat → List Name → Expr → List Tok → Option (Expr × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, h, ts =>
    if atomStart ts then do
      let (a, ts) ← psAtom f sc ts
      psArgs f sc (.app h a) ts
    else some (h, ts)

@[expose] def psAtom : Nat → List Name → List Tok → Option (Expr × List Tok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match ts with
    | .ident n :: ts =>
      match lookup n sc with
      | some i => some (.bvar i, ts)
      | none => (psUnivs ts).map fun (us, ts) => (.const n us, ts)
    | .atSign :: .ident n :: ts => (psUnivs ts).map fun (us, ts) => (.const n us, ts)
    | .kwProp :: ts => some (.sort .zero, ts)
    | .str s :: ts => some (.lit (.strVal s), ts)
    | .lparen :: ts => do
      let (e, ts) ← psTerm f sc ts
      match ts with
      | .rparen :: ts => some (e, ts)
      | _ => none
    | _ => none
end

end LeanIntent.Print
