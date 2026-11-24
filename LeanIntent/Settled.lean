module

public import LeanIntent.Statement

public section

namespace LeanIntent

universe u

inductive Answerer where
  | owner (principal : Ident)
  | onBehalf (principal delegation : Ident) (reason : String)
  deriving @[expose] DecidableEq

@[expose] def Authority.answerer (a : Authority) (reason : String) : Answerer :=
  match a.delegation with
  | none => .owner a.principal
  | some d => .onBehalf a.principal d reason

theorem Authority.answerer_owner (a : Authority) (why : String) (h : a.delegation = none) :
    a.answerer why = .owner a.principal := by
  simp [answerer, h]

theorem Authority.answerer_onBehalf (a : Authority) (why : String) {d : Ident}
    (h : a.delegation = some d) : a.answerer why = .onBehalf a.principal d why := by
  simp [answerer, h]

structure Attributed (W : Type u) where
  answer : Answer W
  answerer : Answerer

inductive Restatement where
  | unconfirmed
  | confirmed (owner : Ident)
  deriving @[expose] DecidableEq

inductive Settled : Restatement → Type where
  | answered {s : Restatement} (answerer : Answerer) (verdict : Verdict) : Settled s
  | derived {owner : Ident} : Settled (.confirmed owner)
  | fork {s : Restatement} : Settled s
  | unsettled {s : Restatement} : Settled s

namespace Settled

inductive Claim where
  | ownerConfirmed
  | ownerDeclined
  | behalfConfirmed
  | behalfDeclined
  | derived
  | fork
  | unsettled
  deriving @[expose] DecidableEq

@[expose] def Claim.phrase : Claim → List Char
  | .ownerConfirmed => chars!"Confirmed by the owner "
  | .ownerDeclined => chars!"Declined by the owner "
  | .behalfConfirmed => chars!"Confirmed on the owner's behalf by "
  | .behalfDeclined => chars!"Declined on the owner's behalf by "
  | .derived => chars!"Derived from what the owner confirmed: "
  | .fork => chars!"A fork for the owner to decide: "
  | .unsettled => chars!"Not settled: "

theorem Claim.phrase_diverge {k k' : Claim} (h : k ≠ k') : Diverge k.phrase k'.phrase = true := by
  cases k <;> cases k' <;> first | exact absurd rfl h | decide

@[expose] def claim {s : Restatement} : Settled s → Claim
  | .answered (.owner _) .confirmed => .ownerConfirmed
  | .answered (.owner _) .declined => .ownerDeclined
  | .answered (.onBehalf ..) .confirmed => .behalfConfirmed
  | .answered (.onBehalf ..) .declined => .behalfDeclined
  | .derived => .derived
  | .fork => .fork
  | .unsettled => .unsettled

@[expose] def details : {s : Restatement} → Settled s → List Char
  | _, .answered (.owner p) _ => p.toString.toList ++ chars!".\n"
  | _, .answered (.onBehalf p d why) _ =>
    p.toString.toList ++ chars!", under the delegation " ++ d.toString.toList ++
      chars!", for this reason: " ++ Codec.line.print why
  | .confirmed o, .derived =>
    chars!"it holds of the record as shown, and the owner " ++ o.toString.toList ++
      chars!" confirmed the record's restatement; no one answered it.\n"
  | _, .fork => chars!"their intent does not settle it, and no answer is recorded.\n"
  | _, .unsettled =>
    chars!"no answer is recorded, and nothing records that it follows from what the owner \
      confirmed.\n"

@[expose] def words {s : Restatement} (x : Settled s) : List Char := x.claim.phrase ++ x.details

theorem says_iff {s : Restatement} (x : Settled s) (k : Claim) :
    k.phrase <+: x.words ↔ x.claim = k := by
  constructor
  · rintro ⟨t, ht⟩
    apply Classical.byContradiction
    intro hne
    have hd := stripPrefix_of_diverge (Claim.phrase_diverge fun h => hne h.symm) x.details
    have hs := stripPrefix_append k.phrase t
    rw [ht] at hs
    simp [words, hd] at hs
  · rintro rfl
    exact List.prefix_append _ _

theorem says_confirmed_by_owner_iff {s : Restatement} (x : Settled s) :
    Claim.ownerConfirmed.phrase <+: x.words ↔ ∃ p, x = .answered (.owner p) .confirmed := by
  rw [says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

theorem says_declined_by_owner_iff {s : Restatement} (x : Settled s) :
    Claim.ownerDeclined.phrase <+: x.words ↔ ∃ p, x = .answered (.owner p) .declined := by
  rw [says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

theorem says_on_behalf_iff {s : Restatement} (x : Settled s) :
    (Claim.behalfConfirmed.phrase <+: x.words ∨ Claim.behalfDeclined.phrase <+: x.words) ↔
      ∃ p d why v, x = .answered (.onBehalf p d why) v := by
  rw [says_iff, says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

theorem onBehalf_not_owners {s : Restatement} (p d : Ident) (why : String) (v : Verdict) :
    ¬ Claim.ownerConfirmed.phrase <+: (Settled.answered (s := s) (.onBehalf p d why) v).words ∧
      ¬ Claim.ownerDeclined.phrase <+: (Settled.answered (s := s) (.onBehalf p d why) v).words := by
  simp [says_iff, claim]; cases v <;> simp

theorem says_derived_confirmed {s : Restatement} (x : Settled s)
    (h : Claim.derived.phrase <+: x.words) : ∃ o, s = .confirmed o := by
  rw [says_iff] at h
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim] at h
  | derived => exact ⟨_, rfl⟩
  | fork | unsettled => simp [claim] at h

theorem names_owner {s : Restatement} (p : Ident) (v : Verdict) :
    p.toString.toList <:+: (Settled.answered (s := s) (.owner p) v).words :=
  List.infix_append' ..

theorem names_onBehalf {s : Restatement} (p d : Ident) (why : String) (v : Verdict) :
    let w := (Settled.answered (s := s) (.onBehalf p d why) v).words
    p.toString.toList <:+: w ∧ d.toString.toList <:+: w ∧ Codec.line.print why <:+: w := by
  intro w
  have hw : w = (Settled.answered (s := s) (.onBehalf p d why) v).claim.phrase ++
      (p.toString.toList ++ (chars!", under the delegation " ++ (d.toString.toList ++
        (chars!", for this reason: " ++ Codec.line.print why)))) := by
    simp [w, words, details]
  rw [hw]
  refine ⟨List.infix_append' .., ?_, ?_⟩
  · exact List.infix_append_of_infix_right
      (List.infix_append_of_infix_right (List.infix_append' ..))
  · exact List.infix_append_of_infix_right
      (List.infix_append_of_infix_right
        (List.infix_append_of_infix_right
          (List.infix_append_of_infix_right (List.infix_append_right ..))))

theorem names_derived (o : Ident) : o.toString.toList <:+: (Settled.derived (owner := o)).words :=
  List.infix_append_of_infix_right (List.infix_append ..)

end Settled

@[expose] def Restatement.words : Restatement → List Char
  | .unconfirmed => chars!"No confirmation by an owner is recorded.\n"
  | .confirmed o => Settled.Claim.ownerConfirmed.phrase ++ o.toString.toList ++ chars!".\n"

theorem Restatement.says_confirmed_iff (s : Restatement) :
    Settled.Claim.ownerConfirmed.phrase <+: s.words ↔ ∃ o, s = .confirmed o := by
  cases s with
  | unconfirmed => simp only [words, reduceCtorEq, exists_false, iff_false]; decide
  | confirmed o =>
    simp only [words, List.append_assoc, List.prefix_append, Restatement.confirmed.injEq, true_iff]
    exact ⟨o, rfl⟩

theorem Restatement.names_confirmed (o : Ident) :
    o.toString.toList <:+: (Restatement.confirmed o).words :=
  List.infix_append ..

@[expose] def Answerer.title : Answerer → String
  | .owner _ => "An answer of the owner"
  | .onBehalf .. => "A decision made on the owner's behalf"

@[expose] def Answerer.says (a : Answerer) (v : Verdict) : List Char :=
  (Settled.answered (s := .unconfirmed) a v).words

end LeanIntent
