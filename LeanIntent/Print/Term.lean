import Lean.Expr
import LeanIntent.Print.Token

/-!
# Printing a Lean term as tokens, and parsing the tokens back

`pr` writes a Lean term (`Lean.Expr`) as the tokens of Lean's surface syntax, in a closed grammar:

* a bound variable as the name of its binder;
* a constant as its full name, after `@` unless `bare` chooses it and no binder in scope has its
  name, with its universe levels after `.{` when it has any;
* `Prop`, `Type`, `Type u` and `Sort u` for sorts, a string literal as itself, and a natural
  number literal as `nat_lit n`;
* an application as the function followed by its arguments;
* `fun (x : T) => b` and `∀ (x : T), b`, with `{x : T}`, `⦃x : T⦄` or `[x : T]` for the other
  binder annotations, and `A → B` for a `∀` whose binder has no name and the default annotation;
* `let x : T := v; b` for a `let` (`Expr.letE`) that may depend on its value, and
  `have x : T := v; b` for one that does not (its flag `nonDep` set), which is how Lean reads each;
* parentheses where a part's precedence requires them.

It refuses, by returning `none`, every other term: a free or meta variable, metadata, a
projection, a universe metavariable, a name with a numeric component or one that cannot be
written, a binder name that is not one component, and a bound variable whose binder another binder
of the same name shadows. `psTerm` parses the tokens back. `LeanIntent.Print.RoundTrip` proves that
it returns the very term `pr` printed, and `LeanIntent.Print.Printable` that `pr` prints exactly the
terms `Printable` admits.
-/

namespace LeanIntent.Print

open Lean (Name Level Expr Literal BinderInfo)

/-- The precedence a term is printed at: anywhere, before `→`, as the function of an application,
or as an argument. -/
inductive Prec where
  | term | simple | head | arg
  deriving DecidableEq

/-- Whether a sort, a natural number literal or an application needs parentheses at `p`: as the
function of an application or as an argument. -/
def Prec.tight : Prec → Bool
  | .head | .arg => true
  | _ => false

/-- Whether `p` is an argument's precedence. -/
def Prec.isArg : Prec → Bool
  | .arg => true
  | _ => false

/-- Whether `p` is the lowest precedence. -/
def Prec.isTerm : Prec → Bool
  | .term => true
  | _ => false

/-- `ts` in parentheses when `b`. -/
def paren (b : Bool) (ts : List Tok) : List Tok := if b then .lparen :: ts ++ [.rparen] else ts

/-- A component that can be written: as it is, or escaped since it holds no `»`. -/
def compOk (s : String) : Bool := rawable s || !(s.toList.contains '»')

/-- A name that is one component that can be written. -/
def atomOk : Name → Bool
  | .str .anonymous s => compOk s
  | _ => false

/-- A name of at least one component, each a string that can be written. -/
def nameOk (n : Name) : Bool :=
  match comps n with
  | some ss => !ss.isEmpty && ss.all compOk
  | none => false

/-- The position of the innermost binder named `n` in the scope `sc`, innermost first. -/
def lookup (n : Name) : List Name → Option Nat
  | [] => none
  | m :: ms => if m = n then some 0 else (lookup n ms).map (· + 1)

/-! ## Universe levels -/

/-- The number `l` is, when it is a numeral. -/
def natOf : Level → Option Nat
  | .zero => some 0
  | .succ l => (natOf l).map (· + 1)
  | _ => none

/-- The level a numeral denotes. -/
def levelOfNat : Nat → Level
  | 0 => .zero
  | k + 1 => .succ (levelOfNat k)

/-- `l` after `k` successors. -/
def addN (l : Level) : Nat → Level
  | 0 => l
  | k + 1 => .succ (addN l k)

/-- A level's tokens, in parentheses when `atom` and it is not a numeral or a parameter. -/
def prLevel : Level → Bool → Option (List Tok)
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

/-- A list of levels separated by commas. -/
def prLevels : List Level → Option (List Tok)
  | [] => some []
  | [l] => prLevel l false
  | l :: ls => do
    let t ← prLevel l false
    let r ← prLevels ls
    some (t ++ .comma :: r)

/-- A constant's universe levels: nothing when it has none, and otherwise `.{` and the levels. -/
def prUnivs (us : List Level) : Option (List Tok) :=
  match us with
  | [] => some []
  | us => (prLevels us).map fun t => .dotBrace :: t ++ [.rbrace]

/-- The level `a` followed by an offset `+ k`, if one follows. -/
def levelTail (a : Level) : List Tok → Option (Level × List Tok)
  | .plus :: .num k :: ts => some (addN a k, ts)
  | ts => some (a, ts)

mutual
/-- A level written as a numeral, a parameter or in parentheses. -/
def psLevelAtom : Nat → List Tok → Option (Level × List Tok)
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

/-- A level. -/
def psLevel : Nat → List Tok → Option (Level × List Tok)
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

/-- Levels separated by commas and closed by `}`. -/
def psLevels : Nat → List Tok → Option (List Level × List Tok)
  | 0, _ => none
  | f + 1, ts => do
    let (l, ts) ← psLevel (2 * ts.length + 2) ts
    match ts with
    | .comma :: ts => do
      let (ls, ts) ← psLevels f ts
      some (l :: ls, ts)
    | .rbrace :: ts => some ([l], ts)
    | _ => none

/-- A constant's universe levels, after `.{` when it has any. -/
def psUnivs (ts : List Tok) : Option (List Level × List Tok) :=
  match ts with
  | .dotBrace :: ts => psLevels (ts.length + 1) ts
  | ts => some ([], ts)

/-! ## Terms -/

/-- The opening bracket of a binder annotation. -/
def openTok : BinderInfo → Tok
  | .default => .lparen
  | .implicit => .lbrace
  | .strictImplicit => .lstrict
  | .instImplicit => .lbrack

/-- The closing bracket of a binder annotation. -/
def closer : BinderInfo → Tok
  | .default => .rparen
  | .implicit => .rbrace
  | .strictImplicit => .rstrict
  | .instImplicit => .rbrack

/-- A binder's tokens: its name and type in the brackets of its annotation. -/
def binderToks (bi : BinderInfo) (n : Name) (t : List Tok) : List Tok :=
  openTok bi :: .ident n :: .colon :: t ++ [closer bi]

/-- Whether a level is `0`, whose sort `Prop` is written as one token. -/
def isZero : Level → Bool
  | .zero => true
  | _ => false

/-- A sort's tokens: `Prop`, `Type`, `Type` and a level, or `Sort` and a level. -/
def prSort : Level → Option (List Tok)
  | .zero => some [.kwProp]
  | .succ l => if isZero l then some [.kwType] else (prLevel l true).map (.kwType :: ·)
  | l => (prLevel l true).map (.kwSort :: ·)

/-- A `let`'s tokens: `let`, or `have` when `nonDep`, its name and type, `:=`, its value, `;` and its
body. -/
def letToks (nonDep : Bool) (n : Name) (t v b : List Tok) : List Tok :=
  (if nonDep then .kwHave else .kwLet) :: .ident n :: .colon :: t ++ .colonEq :: v ++
    .semicolon :: b

/-- Whether a `∀` is written as an arrow: its binder has no name and the default annotation. -/
def isArrow : Name → BinderInfo → Bool
  | .anonymous, .default => true
  | _, _ => false

/-- The tokens of `e` at precedence `p`, under the binders `sc`, innermost first; `none` when `e`
is not printable. A constant is written without `@` when `bare` chooses it and no binder in scope
has its name. -/
def pr (bare : Name → Bool) : List Name → Expr → Prec → Option (List Tok)
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

/-- Whether the tokens start an argument of an application. -/
def atomStart : List Tok → Bool
  | .ident _ :: _ | .atSign :: _ | .kwProp :: _ | .str _ :: _ | .lparen :: _ => true
  | _ => false

/-- Whether the tokens start a level written as a numeral, a parameter or in parentheses. -/
def levelStart : List Tok → Bool
  | .num _ :: _ | .ident _ :: _ | .lparen :: _ => true
  | _ => false

/-- The binder annotation an opening bracket starts. -/
def opener : Tok → Option BinderInfo
  | .lparen => some .default
  | .lbrace => some .implicit
  | .lstrict => some .strictImplicit
  | .lbrack => some .instImplicit
  | _ => none

mutual
/-- A term at the lowest precedence. -/
def psTerm : Nat → List Name → List Tok → Option (Expr × List Tok)
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

/-- A `let` after its keyword, `nonDep` when the keyword is `have`: its name and type, `:=`, its
value, `;` and its body. -/
def psLet : Nat → List Name → Bool → List Tok → Option (Expr × List Tok)
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

/-- A binder: its annotation, name and type. -/
def psBinder : Nat → List Name → List Tok → Option (BinderInfo × Name × Expr × List Tok)
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

/-- A term before `→`: a sort with its level, a natural number literal, or an application. -/
def psSimple : Nat → List Name → List Tok → Option (Expr × List Tok)
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

/-- The arguments applied to `h`. -/
def psArgs : Nat → List Name → Expr → List Tok → Option (Expr × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, h, ts =>
    if atomStart ts then do
      let (a, ts) ← psAtom f sc ts
      psArgs f sc (.app h a) ts
    else some (h, ts)

/-- An argument: an identifier, a constant after `@`, `Prop`, a string literal, or a term in
parentheses. An identifier is the innermost binder in scope of its name, or else a constant. -/
def psAtom : Nat → List Name → List Tok → Option (Expr × List Tok)
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
