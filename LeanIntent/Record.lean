module

public section

namespace LeanIntent

universe u

structure Clause (W : Type u) where
  name : String
  holds : W → Prop

structure Pred where
  name : String
  Arg : Type u
  holds : Arg → Prop

structure Member (W : Type u) where
  name : String
  In : Type u
  Out : Type u
  get : W → In → Out

inductive Shape : Type u → Type (u + 1) where
  | value (W : Type u) : Shape W
  | function (A : Type u) (B : A → Type u) : Shape ((x : A) → B x)
  | step (S : Type u) : Shape (S → S)
  | stepOn (S I : Type u) : Shape (S → I → S)
  | action (S O : Type u) : Shape (S → O × S)
  | actionOn (S I O : Type u) : Shape (S → I → O × S)
  | bundle {W D : Type u} (data : W → D) (first : Member W) (rest : List (Member W)) : Shape W

structure IntentRecord (W : Type u) where
  shape : Shape W
  dom : List (Clause W)
  props : List (Clause W)
  vocab : List Pred.{u}

namespace IntentRecord

variable {W : Type u}

@[expose] def Dom (r : IntentRecord W) (w : W) : Prop := ∀ d ∈ r.dom, d.holds w

@[expose] def Props (r : IntentRecord W) (w : W) : Prop := ∀ p ∈ r.props, p.holds w

@[expose] def Meets (r : IntentRecord W) (w : W) : Prop := r.Dom w ∧ r.Props w

@[expose] def Fulfilled (r : IntentRecord W) (w : W) : Prop := r.Dom w → r.Props w

theorem meets_of_fulfilled {r : IntentRecord W} {w : W} (h : r.Fulfilled w) (hd : r.Dom w) :
    r.Meets w := ⟨hd, h hd⟩

theorem dom_of_nil {r : IntentRecord W} (h : r.dom = []) (w : W) : r.Dom w :=
  fun _ hd => nomatch h ▸ hd

end IntentRecord

end LeanIntent
