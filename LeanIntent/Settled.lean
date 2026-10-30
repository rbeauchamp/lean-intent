import LeanIntent.Statement

/-!
# Who settled each thing

The owner states and confirms a system's contract, and the agents decide what lies below it on the
owner's behalf, so a reader of a rendered record must be told which is which: never that the owner
confirmed what they never saw. This module holds what is recorded about that, and the only words
`LeanIntent.Render` prints about it.

Three types hold the record:

* `Answerer`: who gave an answer, the owner acting as owner, or another principal under a named
  delegation, deciding on the owner's behalf for a stated reason. `Authority.answerer` reads it from
  an authority of the owners' log.
* `Restatement`: whether an owner is recorded as having confirmed a record's plain restatement.
* `Settled s`: who settled one consequence shown with a record whose restatement stands as `s`. It
  was answered, by an `Answerer` with a verdict; it is derived from the restatement the owner
  confirmed; it is a fork for the owner to decide; or it is not settled. The type is indexed by `s`,
  and `derived` lives only at `.confirmed owner`, so a consequence of a record with no recorded
  confirmation cannot be recorded as derived from one: Lean's elaborator refuses it.

`Attributed` is an answer with its `Answerer`. `LeanIntent.Answer`, which says what every later
revision must keep, names no author, and the canonical text of an answer takes an `Attributed`, so
no answer is printed without who gave it.

The words are a function of the status: `Settled.words` is the phrase of the status's `Settled.Claim`
followed by its details, and the phrases differ at a position they share (`Claim.phrase_diverge`). So
the printed text starts with a claim's phrase exactly when the status makes that claim
(`Settled.says_iff`), whatever names and reason it holds. In particular:

* it says the owner confirmed, or declined, exactly when the owner is the recorded answerer with that
  verdict (`says_confirmed_by_owner_iff`, `says_declined_by_owner_iff`), so an answer given on the
  owner's behalf is never printed as the owner's (`onBehalf_not_owners`), and a consequence that is
  derived, a fork or not settled is never printed as confirmed by the owner;
* it says a consequence is derived only for a record whose restatement stands as confirmed
  (`says_derived_confirmed`), and `Restatement.words` says the restatement is confirmed exactly when
  that is recorded (`Restatement.says_confirmed_iff`), so a record with no answers and no
  confirmation prints none.

What this module does not establish: that what is recorded is true. These are values a project
writes, so a record can name as owner a principal who is not one, or keep `.confirmed` after a
revision the owner never saw. `LeanIntent.Trace` decides, from a project's owners' log, whether an
answer's authority traces back to a declared owner; tying the values here to that log, and each to
the revision it applies to, is lean-intent #5's. That the renderer reads what it prints from the
recorded term is argued from `LeanIntent.Render`'s code, not stated as a theorem. Nor does it check a
reason: a reason is a model's or a person's words, printed as written.
-/

namespace LeanIntent

universe u

/-- Who gave an answer. -/
inductive Answerer where
  /-- The principal named, acting as owner: the owner's own answer. -/
  | owner (principal : Ident)
  /-- The principal named, acting under the delegation named: a decision made on the owner's behalf,
  for the reason given. -/
  | onBehalf (principal delegation : Ident) (reason : String)
  deriving DecidableEq

/-- The answerer an authority of the owners' log names: a principal acting as owner, or one acting
under its delegation, for the reason given, which the owner's own answer does not need. -/
def Authority.answerer (a : Authority) (reason : String) : Answerer :=
  match a.delegation with
  | none => .owner a.principal
  | some d => .onBehalf a.principal d reason

/-- An answer with who gave it. -/
structure Attributed (W : Type u) where
  /-- The answer. -/
  answer : Answer W
  /-- Who gave it. -/
  answerer : Answerer

/-- Whether a record's plain restatement stands as confirmed by an owner. -/
inductive Restatement where
  /-- No confirmation by an owner is recorded. -/
  | unconfirmed
  /-- The owner named confirmed it. -/
  | confirmed (owner : Ident)
  deriving DecidableEq

/-- Who settled a consequence shown with a record whose restatement stands as the index. -/
inductive Settled : Restatement → Type where
  /-- It was answered, with this verdict, by this answerer. -/
  | answered {s : Restatement} (answerer : Answerer) (verdict : Verdict) : Settled s
  /-- It holds of the record whose restatement the owner confirmed, and no one answered it. -/
  | derived {owner : Ident} : Settled (.confirmed owner)
  /-- It is a fork the owner's intent does not settle, left to the owner, and no one answered it. -/
  | fork {s : Restatement} : Settled s
  /-- Nothing is recorded about it. -/
  | unsettled {s : Restatement} : Settled s

namespace Settled

/-- What a status claims, which decides how its printed words start. -/
inductive Claim where
  /-- The owner confirmed it. -/
  | ownerConfirmed
  /-- The owner declined it. -/
  | ownerDeclined
  /-- It was confirmed on the owner's behalf. -/
  | behalfConfirmed
  /-- It was declined on the owner's behalf. -/
  | behalfDeclined
  /-- It follows from what the owner confirmed. -/
  | derived
  /-- It is left to the owner to decide. -/
  | fork
  /-- Nothing settled it. -/
  | unsettled
  deriving DecidableEq

/-- The words a printed status of each claim starts with. -/
def Claim.phrase : Claim → List Char
  | .ownerConfirmed => chars!"Confirmed by the owner "
  | .ownerDeclined => chars!"Declined by the owner "
  | .behalfConfirmed => chars!"Confirmed on the owner's behalf by "
  | .behalfDeclined => chars!"Declined on the owner's behalf by "
  | .derived => chars!"Derived from what the owner confirmed: "
  | .fork => chars!"A fork for the owner to decide: "
  | .unsettled => chars!"Not settled: "

/-- Two different claims start with words that differ at a position they share, so neither is a
prefix of the other. -/
theorem Claim.phrase_diverge {k k' : Claim} (h : k ≠ k') : Diverge k.phrase k'.phrase = true := by
  cases k <;> cases k' <;> first | exact absurd rfl h | decide

/-- What the status `x` claims. -/
def claim {s : Restatement} : Settled s → Claim
  | .answered (.owner _) .confirmed => .ownerConfirmed
  | .answered (.owner _) .declined => .ownerDeclined
  | .answered (.onBehalf ..) .confirmed => .behalfConfirmed
  | .answered (.onBehalf ..) .declined => .behalfDeclined
  | .derived => .derived
  | .fork => .fork
  | .unsettled => .unsettled

/-- What the printed status says after its claim's phrase: the names and reason it holds, and each
on one line, since an identifier holds no line break and `Codec.line` escapes each in a reason. -/
def details : {s : Restatement} → Settled s → List Char
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

/-- The printed status: its claim's phrase, then its details. -/
def words {s : Restatement} (x : Settled s) : List Char := x.claim.phrase ++ x.details

/-- **The printed words say what the status claims:** they start with a claim's phrase exactly when
the status makes that claim, whatever names and reason it holds. -/
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

/-- The words say the owner confirmed exactly when the owner is the recorded answerer, confirming. -/
theorem says_confirmed_by_owner_iff {s : Restatement} (x : Settled s) :
    Claim.ownerConfirmed.phrase <+: x.words ↔ ∃ p, x = .answered (.owner p) .confirmed := by
  rw [says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

/-- The words say the owner declined exactly when the owner is the recorded answerer, declining. -/
theorem says_declined_by_owner_iff {s : Restatement} (x : Settled s) :
    Claim.ownerDeclined.phrase <+: x.words ↔ ∃ p, x = .answered (.owner p) .declined := by
  rw [says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

/-- The words say an answer was given on the owner's behalf exactly when a principal under a
delegation is the recorded answerer. -/
theorem says_on_behalf_iff {s : Restatement} (x : Settled s) :
    (Claim.behalfConfirmed.phrase <+: x.words ∨ Claim.behalfDeclined.phrase <+: x.words) ↔
      ∃ p d why v, x = .answered (.onBehalf p d why) v := by
  rw [says_iff, says_iff]
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim]
  | derived | fork | unsettled => simp [claim]

/-- An answer given on the owner's behalf is never printed as the owner's. -/
theorem onBehalf_not_owners {s : Restatement} (p d : Ident) (why : String) (v : Verdict) :
    ¬ Claim.ownerConfirmed.phrase <+: (Settled.answered (s := s) (.onBehalf p d why) v).words ∧
      ¬ Claim.ownerDeclined.phrase <+: (Settled.answered (s := s) (.onBehalf p d why) v).words := by
  simp [says_iff, claim]; cases v <;> simp

/-- The words say a consequence is derived only of a record whose restatement stands as confirmed. -/
theorem says_derived_confirmed {s : Restatement} (x : Settled s)
    (h : Claim.derived.phrase <+: x.words) : ∃ o, s = .confirmed o := by
  rw [says_iff] at h
  cases x with
  | answered a v => cases a <;> cases v <;> simp [claim] at h
  | derived => exact ⟨_, rfl⟩
  | fork | unsettled => simp [claim] at h

end Settled

/-- The words that say whether a record's restatement stands as confirmed. -/
def Restatement.words : Restatement → List Char
  | .unconfirmed => chars!"No confirmation by an owner is recorded.\n"
  | .confirmed o => Settled.Claim.ownerConfirmed.phrase ++ o.toString.toList ++ chars!".\n"

/-- The words say the restatement is confirmed exactly when that is recorded. -/
theorem Restatement.says_confirmed_iff (s : Restatement) :
    Settled.Claim.ownerConfirmed.phrase <+: s.words ↔ ∃ o, s = .confirmed o := by
  cases s with
  | unconfirmed => simp only [words, reduceCtorEq, exists_false, iff_false]; decide
  | confirmed o =>
    simp only [words, List.append_assoc, List.prefix_append, Restatement.confirmed.injEq, true_iff]
    exact ⟨o, rfl⟩

/-- How the answerer's answer is titled where it is printed alone: an answer of the owner only when
the recorded answerer is the owner. -/
def Answerer.title : Answerer → String
  | .owner _ => "An answer of the owner"
  | .onBehalf .. => "A decision made on the owner's behalf"

/-- The words that say this answerer gave this verdict, as a consequence of a record prints them. -/
def Answerer.says (a : Answerer) (v : Verdict) : List Char :=
  (Settled.answered (s := .unconfirmed) a v).words

end LeanIntent
