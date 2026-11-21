module

public import LeanIntent.Print.Term

public section

namespace LeanIntent.Print

open Lean (Name Expr BinderInfo)

@[expose] def usesBVar : Expr → Nat → Bool
  | .bvar j, i => j == i
  | .app f a, i => usesBVar f i || usesBVar a i
  | .lam _ t b _, i | .forallE _ t b _, i => usesBVar t i || usesBVar b (i + 1)
  | .letE _ t v b _, i => usesBVar t i || usesBVar v i || usesBVar b (i + 1)
  | .mdata _ e, i | .proj _ _ e, i => usesBVar e i
  | _, _ => false

@[expose] def constRoots : Expr → List Name
  | .const c _ => [c.getRoot]
  | .app f a => constRoots f ++ constRoots a
  | .lam _ t b _ | .forallE _ t b _ => constRoots t ++ constRoots b
  | .letE _ t v b _ => constRoots t ++ constRoots v ++ constRoots b
  | .mdata _ e | .proj _ _ e => constRoots e
  | _ => []

@[expose] def keeps (avoid : List Name) (n : Name) : Bool := atomOk n && !avoid.contains n

@[expose] def pick (avoid : List Name) (n : Name) : Name :=
  let base := n.eraseMacroScopes
  if keeps avoid base then base
  else
    let cands := (List.range (avoid.length + 1)).map fun k =>
      if k = 0 then Name.mkSimple "x" else Name.mkSimple ("x_" ++ toString k)
    (cands.find? fun c => !avoid.contains c).getD (Name.mkSimple "x")

@[expose] def isDefault : BinderInfo → Bool
  | .default => true
  | _ => false

@[expose] def canon (avoid : List Name) : List Name → Expr → Expr
  | sc, .app f a => .app (canon avoid sc f) (canon avoid sc a)
  | sc, .lam n t b bi =>
    let n' := if keeps (avoid ++ sc) n then n else pick (avoid ++ sc) n
    .lam n' (canon avoid sc t) (canon avoid (n' :: sc) b) bi
  | sc, .forallE n t b bi =>
    let n' :=
      if keeps (avoid ++ sc) n then n
      else if isDefault bi && !usesBVar b 0 then .anonymous
      else pick (avoid ++ sc) n
    .forallE n' (canon avoid sc t) (canon avoid (n' :: sc) b) bi
  | sc, .letE n t v b nd =>
    let n' := if keeps (avoid ++ sc) n then n else pick (avoid ++ sc) n
    .letE n' (canon avoid sc t) (canon avoid sc v) (canon avoid (n' :: sc) b) nd
  | sc, .mdata m e => .mdata m (canon avoid sc e)
  | sc, .proj s i e => .proj s i (canon avoid sc e)
  | _, e => e

@[expose] def eraseMData : Expr → Expr
  | .app f a => .app (eraseMData f) (eraseMData a)
  | .lam n t b bi => .lam n (eraseMData t) (eraseMData b) bi
  | .forallE n t b bi => .forallE n (eraseMData t) (eraseMData b) bi
  | .letE n t v b nd => .letE n (eraseMData t) (eraseMData v) (eraseMData b) nd
  | .mdata _ e => eraseMData e
  | .proj s i e => .proj s i (eraseMData e)
  | e => e

@[expose] def eraseNames : Expr → Expr
  | .app f a => .app (eraseNames f) (eraseNames a)
  | .lam _ t b bi => .lam .anonymous (eraseNames t) (eraseNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (eraseNames t) (eraseNames b) bi
  | .letE _ t v b nd => .letE .anonymous (eraseNames t) (eraseNames v) (eraseNames b) nd
  | .mdata m e => .mdata m (eraseNames e)
  | .proj s i e => .proj s i (eraseNames e)
  | e => e

theorem eraseNames_canon (avoid : List Name) (sc : List Name) (e : Expr) :
    eraseNames (canon avoid sc e) = eraseNames e := by
  induction e generalizing sc <;> simp [canon, eraseNames, *]

end LeanIntent.Print
