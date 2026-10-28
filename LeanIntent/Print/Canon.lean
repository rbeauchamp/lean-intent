import LeanIntent.Print.Term

/-!
# Binder names the printer can write

Lean names the binders it makes itself with macro scopes (`a✝`), which no identifier can write, and
a term may shadow one binder by another of the same name. `canon` renames the binders of a term so
that the printer can write every bound variable, and renames only those it must: a binder keeps
its name when that is one component that can be written and neither an enclosing binder nor the
first component of a constant in the term has it, so that neither the printer's parser nor Lean
can read the variable as another. A binder that cannot keep its name loses it when it is a `∀`
whose body does not use its variable and whose annotation is the default, and is printed as an
arrow; otherwise it takes its name without macro scopes when that can be kept, and else the first
of `x`, `x_1`, `x_2`, ... that can.

A binder's name is not part of what a term means: Lean's kernel compares terms with binder names
ignored. `eraseNames_canon` proves that `canon` changes nothing else: with every binder name
erased, a term and its renaming are equal.
-/

namespace LeanIntent.Print

open Lean (Name Expr BinderInfo)

/-- Whether the loose bound variable `i` occurs in `e`. -/
def usesBVar : Expr → Nat → Bool
  | .bvar j, i => j == i
  | .app f a, i => usesBVar f i || usesBVar a i
  | .lam _ t b _, i | .forallE _ t b _, i => usesBVar t i || usesBVar b (i + 1)
  | .letE _ t v b _, i => usesBVar t i || usesBVar v i || usesBVar b (i + 1)
  | .mdata _ e, i | .proj _ _ e, i => usesBVar e i
  | _, _ => false

/-- The first components of the names of the constants in `e`. -/
def constRoots : Expr → List Name
  | .const c _ => [c.getRoot]
  | .app f a => constRoots f ++ constRoots a
  | .lam _ t b _ | .forallE _ t b _ => constRoots t ++ constRoots b
  | .letE _ t v b _ => constRoots t ++ constRoots v ++ constRoots b
  | .mdata _ e | .proj _ _ e => constRoots e
  | _ => []

/-- Whether a binder can keep the name `n`: one component that can be written, which `avoid` does
not hold. -/
def keeps (avoid : List Name) (n : Name) : Bool := atomOk n && !avoid.contains n

/-- A name for a binder named `n` that `avoid` does not hold. -/
def pick (avoid : List Name) (n : Name) : Name :=
  let base := n.eraseMacroScopes
  if keeps avoid base then base
  else
    let cands := (List.range (avoid.length + 1)).map fun k =>
      if k = 0 then Name.mkSimple "x" else Name.mkSimple ("x_" ++ toString k)
    (cands.find? fun c => !avoid.contains c).getD (Name.mkSimple "x")

/-- Whether a binder annotation is the default one. -/
def isDefault : BinderInfo → Bool
  | .default => true
  | _ => false

/-- `e` with its binders renamed, under the binders `sc`, innermost first, avoiding the names in
`avoid` as well. -/
def canon (avoid : List Name) : List Name → Expr → Expr
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
    .letE n (canon avoid sc t) (canon avoid sc v) (canon avoid (n :: sc) b) nd
  | sc, .mdata m e => .mdata m (canon avoid sc e)
  | sc, .proj s i e => .proj s i (canon avoid sc e)
  | _, e => e

/-- `e` with every metadata node replaced by the term it annotates. Lean documents an annotated
term, `Expr.mdata data e`, as definitionally equal to `e` itself, so this changes nothing a term
means; `LeanIntent.Render` applies it before printing, since the printer writes no metadata. -/
def eraseMData : Expr → Expr
  | .app f a => .app (eraseMData f) (eraseMData a)
  | .lam n t b bi => .lam n (eraseMData t) (eraseMData b) bi
  | .forallE n t b bi => .forallE n (eraseMData t) (eraseMData b) bi
  | .letE n t v b nd => .letE n (eraseMData t) (eraseMData v) (eraseMData b) nd
  | .mdata _ e => eraseMData e
  | .proj s i e => .proj s i (eraseMData e)
  | e => e

/-- `e` with every binder name erased. -/
def eraseNames : Expr → Expr
  | .app f a => .app (eraseNames f) (eraseNames a)
  | .lam _ t b bi => .lam .anonymous (eraseNames t) (eraseNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (eraseNames t) (eraseNames b) bi
  | .letE _ t v b nd => .letE .anonymous (eraseNames t) (eraseNames v) (eraseNames b) nd
  | .mdata m e => .mdata m (eraseNames e)
  | .proj s i e => .proj s i (eraseNames e)
  | e => e

/-- Renaming binders changes nothing but their names. -/
theorem eraseNames_canon (avoid : List Name) (sc : List Name) (e : Expr) :
    eraseNames (canon avoid sc e) = eraseNames e := by
  induction e generalizing sc <;> simp [canon, eraseNames, *]

end LeanIntent.Print
