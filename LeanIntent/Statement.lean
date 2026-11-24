module

public import LeanIntent.Answers
public import LeanIntent.Codec.Text

public section

namespace LeanIntent

open Codec

@[expose] def identChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    n == 46 || n == 95 || n == 45 || n == 64 || n == 43 || n == 47

@[expose] def base64Char (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 43 || n == 47 || n == 61

structure Word (p : Char → Bool) where
  toString : String
  valid : toString.toList ≠ [] ∧ toString.toList.all p = true

instance {p : Char → Bool} : DecidableEq (Word p) := fun a b =>
  decidable_of_iff (a.toString = b.toString) ⟨fun h => by cases a; cases b; cases h; rfl, (· ▸ rfl)⟩

@[expose] def Word.of {p : Char → Bool} (s : String)
    (h : s.toList ≠ [] ∧ s.toList.all p = true := by simp only [String.reduceToList]; decide) :
    Word p :=
  ⟨s, h⟩

abbrev Ident := Word identChar

inductive KeyAlgorithm where
  | ed25519
  | ed25519Sk
  | ecdsaP256
  | ecdsaP384
  | ecdsaP521
  | ecdsaP256Sk
  | rsa
  deriving @[expose] DecidableEq

@[expose] def KeyAlgorithm.keyword : KeyAlgorithm → List Char
  | .ed25519 => chars!"ssh-ed25519 "
  | .ed25519Sk => chars!"sk-ssh-ed25519@openssh.com "
  | .ecdsaP256 => chars!"ecdsa-sha2-nistp256 "
  | .ecdsaP384 => chars!"ecdsa-sha2-nistp384 "
  | .ecdsaP521 => chars!"ecdsa-sha2-nistp521 "
  | .ecdsaP256Sk => chars!"sk-ecdsa-sha2-nistp256@openssh.com "
  | .rsa => chars!"ssh-rsa "

structure PublicKey where
  algorithm : KeyAlgorithm
  data : Word base64Char
  deriving @[expose] DecidableEq

structure Principal where
  name : Ident
  keys : List PublicKey
  deriving @[expose] DecidableEq

structure Authority where
  principal : Ident
  delegation : Option Ident
  deriving @[expose] DecidableEq

@[expose] def Date.daysIn (year month : Nat) : Nat :=
  if month = 2 then (if year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0) then 29 else 28)
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

@[expose] def Date.isValid (year month day : Nat) : Bool :=
  1 ≤ month && month ≤ 12 && 1 ≤ day && day ≤ Date.daysIn year month

structure Date where
  year : Nat
  month : Nat
  day : Nat
  valid : Date.isValid year month day = true
  deriving @[expose] DecidableEq

inductive Source where
  | words (text : String)
  | reference (location : String)
  deriving @[expose] DecidableEq

inductive Records where
  | all
  | only (names : List String)
  deriving @[expose] DecidableEq

structure Scope where
  records : Records
  confirm : Bool
  decline : Bool
  retract : Bool
  deriving @[expose] DecidableEq

deriving instance @[expose] DecidableEq for Consequence.Kind
deriving instance @[expose] DecidableEq for Verdict

namespace Statement

structure Owners where
  principals : List Principal
  threshold : Option Nat
  deriving @[expose] DecidableEq

structure Delegation where
  delegator : Authority
  delegate : Principal
  scope : Scope
  mayPassOn : Bool
  deriving @[expose] DecidableEq

structure Answer where
  author : Authority
  record : String
  revision : String
  consequence : String
  kind : Consequence.Kind
  predicate : String
  verdict : Verdict
  deriving @[expose] DecidableEq

structure Retraction where
  author : Authority
  answer : Ident
  deriving @[expose] DecidableEq

structure Revocation where
  author : Authority
  delegation : Ident
  deriving @[expose] DecidableEq

structure Origin where
  author : Authority
  record : String
  writer : String
  hadRead : String
  words : String
  deriving @[expose] DecidableEq

inductive ToolOutcome where
  | measured (version configuration result cost : String)
  | openItem (item dependents : String)
  deriving @[expose] DecidableEq

structure ToolBasis where
  author : Authority
  record : String
  consequence : String
  tool : String
  outcome : ToolOutcome
  deriving @[expose] DecidableEq

inductive Body where
  | owners (o : Owners)
  | delegation (d : Delegation)
  | answer (a : Answer)
  | retraction (r : Retraction)
  | revocation (r : Revocation)
  | origin (o : Origin)
  | tool (t : ToolBasis)
  deriving @[expose] DecidableEq

end Statement

structure Statement where
  project : Ident
  id : Ident
  date : Date
  source : Source
  body : Statement.Body
  deriving @[expose] DecidableEq

namespace Grammar

theorem identChar_plain (c : Char) (h : identChar c = true) : concealing c = false := by
  simp only [identChar, concealing, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h ⊢
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega

theorem base64Char_plain (c : Char) (h : base64Char c = true) : concealing c = false := by
  simp only [base64Char, concealing, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h ⊢
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega

@[expose] def word (p : Char → Bool) (hp : ∀ c, p c = true → concealing c = false) (term : Char)
    (ht : p term = false) (hterm : Plain [term] := by decide) : Codec (Word p) :=
  map (token p term ht hp hterm) (fun w => ⟨w.toString.toList, w.valid.2⟩)
    (fun l => if h : l.1 ≠ [] then some ⟨String.ofList l.1, by simp [h, l.2]⟩ else none)
    (fun w => by obtain ⟨w, h⟩ := w; simp [h.1, String.ofList_toList])

@[expose] def ident : Codec Ident := word identChar identChar_plain '\n' (by decide)

@[expose] def yesNo : Codec Bool :=
  keywords (fun b => if b then chars!"yes\n" else chars!"no\n") [false, true]
    (by intro b; cases b <;> decide) (by decide) (by intro b; cases b <;> decide)

@[expose] def publicKey : Codec PublicKey :=
  map (keyed chars!"key " (by decide)
      ((keywords KeyAlgorithm.keyword
        [.ed25519, .ed25519Sk, .ecdsaP256, .ecdsaP384, .ecdsaP521, .ecdsaP256Sk, .rsa]
        (by intro a; cases a <;> decide) (by decide) (by intro a; cases a <;> decide)).seq
        (word base64Char base64Char_plain '\n' (by decide))))
    (fun k => (k.algorithm, k.data)) (fun (a, d) => some ⟨a, d⟩) (fun _ => rfl)

@[expose] def principal (role : List Char) (hr : Plain role := by decide) : Codec Principal :=
  map (keyed role hr (ident.seq (keyed chars!"keys " (by decide) (list publicKey))))
    (fun p => (p.name, p.keys)) (fun (n, k) => some ⟨n, k⟩) (fun _ => rfl)

@[expose] def authority : Codec Authority :=
  map (keyed chars!"by " (by decide)
      (ident.seq
        (option chars!"as owner\n" chars!"under " (by decide) (by decide) (by decide) ident)))
    (fun a => (a.principal, a.delegation)) (fun (p, d) => some ⟨p, d⟩) (fun _ => rfl)

@[expose] def date : Codec Date :=
  map (keyed chars!"date " (by decide)
      ((nat 4 '-' (by decide)).seq ((nat 2 '-' (by decide)).seq (nat 2 '\n' (by decide)))))
    (fun d => (d.year, d.month, d.day))
    (fun (y, m, d) => if h : Date.isValid y m d = true then some ⟨y, m, d, h⟩ else none)
    (fun d => by obtain ⟨y, m, d, h⟩ := d; simp [h])

@[expose] def source : Codec Source :=
  map (sum chars!"words " chars!"reference " (by decide) (by decide) (by decide) text line)
    (fun | .words t => .inl t | .reference r => .inr r)
    (fun | .inl t => some (.words t) | .inr r => some (.reference r))
    (fun s => by cases s <;> rfl)

@[expose] def records : Codec Records :=
  map (option chars!"all records\n" chars!"records " (by decide) (by decide) (by decide)
      (list (keyed chars!"record " (by decide) line)))
    (fun | .all => none | .only ns => some ns)
    (fun | none => some .all | some ns => some (.only ns))
    (fun r => by cases r <;> rfl)

@[expose] def scope : Codec Scope :=
  map (records.seq ((keyed chars!"may confirm " (by decide) yesNo).seq
      ((keyed chars!"may decline " (by decide) yesNo).seq
        (keyed chars!"may retract " (by decide) yesNo))))
    (fun s => (s.records, s.confirm, s.decline, s.retract))
    (fun (r, c, d, t) => some ⟨r, c, d, t⟩) (fun _ => rfl)

@[expose] def owners : Codec Statement.Owners :=
  map ((keyed chars!"principals " (by decide) (list (principal chars!"principal "))).seq
      (option chars!"no threshold\n" chars!"threshold " (by decide) (by decide) (by decide)
        (nat 0 '\n' (by decide))))
    (fun o => (o.principals, o.threshold)) (fun (p, t) => some ⟨p, t⟩) (fun _ => rfl)

@[expose] def delegation : Codec Statement.Delegation :=
  map (authority.seq ((principal chars!"delegate ").seq
      (scope.seq (keyed chars!"may pass on " (by decide) yesNo))))
    (fun d => (d.delegator, d.delegate, d.scope, d.mayPassOn))
    (fun (a, p, s, m) => some ⟨a, p, s, m⟩) (fun _ => rfl)

@[expose] def consequenceKind : Codec Consequence.Kind :=
  keywords (fun | .entailment => chars!"shown as entailment\n"
                | .possibility => chars!"shown as possibility\n")
    [.entailment, .possibility] (by intro k; cases k <;> decide) (by decide)
    (by intro k; cases k <;> decide)

@[expose] def verdict : Codec Verdict :=
  keywords (fun | .confirmed => chars!"verdict confirmed\n"
                | .declined => chars!"verdict declined\n")
    [.confirmed, .declined] (by intro v; cases v <;> decide) (by decide)
    (by intro v; cases v <;> decide)

@[expose] def answer : Codec Statement.Answer :=
  map (authority.seq ((keyed chars!"record " (by decide) line).seq
      ((keyed chars!"revision " (by decide) text).seq
      ((keyed chars!"consequence " (by decide) line).seq
      (consequenceKind.seq ((keyed chars!"predicate " (by decide) text).seq verdict))))))
    (fun a => (a.author, a.record, a.revision, a.consequence, a.kind, a.predicate, a.verdict))
    (fun (a, r, v, c, k, p, d) => some ⟨a, r, v, c, k, p, d⟩) (fun _ => rfl)

@[expose] def retraction : Codec Statement.Retraction :=
  map (authority.seq (keyed chars!"retracts " (by decide) ident))
    (fun r => (r.author, r.answer)) (fun (a, i) => some ⟨a, i⟩) (fun _ => rfl)

@[expose] def revocation : Codec Statement.Revocation :=
  map (authority.seq (keyed chars!"revokes " (by decide) ident))
    (fun r => (r.author, r.delegation)) (fun (a, i) => some ⟨a, i⟩) (fun _ => rfl)

@[expose] def origin : Codec Statement.Origin :=
  map (authority.seq ((keyed chars!"record " (by decide) line).seq
      ((keyed chars!"written by " (by decide) line).seq
      ((keyed chars!"had read " (by decide) text).seq (keyed chars!"adopted " (by decide) text)))))
    (fun o => (o.author, o.record, o.writer, o.hadRead, o.words))
    (fun (a, r, w, h, t) => some ⟨a, r, w, h, t⟩) (fun _ => rfl)

@[expose] def toolOutcome : Codec Statement.ToolOutcome :=
  map (sum chars!"measured\n" chars!"open item " (by decide) (by decide) (by decide)
      ((keyed chars!"version " (by decide) line).seq
        ((keyed chars!"configuration " (by decide) text).seq
        ((keyed chars!"result " (by decide) text).seq (keyed chars!"cost " (by decide) line))))
      (text.seq (keyed chars!"depended on by " (by decide) text)))
    (fun | .measured v c r k => .inl (v, c, r, k) | .openItem i d => .inr (i, d))
    (fun | .inl (v, c, r, k) => some (.measured v c r k) | .inr (i, d) => some (.openItem i d))
    (fun o => by cases o <;> rfl)

@[expose] def tool : Codec Statement.ToolBasis :=
  map (authority.seq ((keyed chars!"record " (by decide) line).seq
      ((keyed chars!"consequence " (by decide) line).seq
      ((keyed chars!"tool " (by decide) line).seq toolOutcome))))
    (fun t => (t.author, t.record, t.consequence, t.tool, t.outcome))
    (fun (a, r, c, n, o) => some ⟨a, r, c, n, o⟩) (fun _ => rfl)

inductive Kind where
  | owners
  | delegation
  | answer
  | retraction
  | revocation
  | origin
  | tool
  deriving @[expose] DecidableEq

@[expose] def Kind.Body : Kind → Type
  | .owners => Statement.Owners
  | .delegation => Statement.Delegation
  | .answer => Statement.Answer
  | .retraction => Statement.Retraction
  | .revocation => Statement.Revocation
  | .origin => Statement.Origin
  | .tool => Statement.ToolBasis

@[expose] def kind : Codec Kind :=
  keywords (fun | .owners => chars!"kind owners\n" | .delegation => chars!"kind delegation\n"
                | .answer => chars!"kind answer\n" | .retraction => chars!"kind retraction\n"
                | .revocation => chars!"kind revocation\n" | .origin => chars!"kind origin\n"
                | .tool => chars!"kind tool\n")
    [.owners, .delegation, .answer, .retraction, .revocation, .origin, .tool]
    (by intro k; cases k <;> decide)
    (by decide) (by intro k; cases k <;> decide)

@[expose] def body : (k : Kind) → Codec k.Body
  | .owners => owners
  | .delegation => delegation
  | .answer => answer
  | .retraction => retraction
  | .revocation => revocation
  | .origin => origin
  | .tool => tool

@[expose] def header : Codec (Ident × Ident × Date × Source) :=
  (keyed chars!"project " (by decide) ident).seq ((keyed chars!"id " (by decide) ident).seq
    (date.seq source))

end Grammar

namespace Statement

@[expose] def codec : Codec Statement :=
  map (keyed chars!"lean-intent statement 1\n" (by decide)
      (Grammar.kind.dep (γ := fun k => (Ident × Ident × Date × Source) × k.Body)
        fun k => Grammar.header.seq (Grammar.body k)))
    (fun s => match s with
      | ⟨p, i, d, o, .owners b⟩ => ⟨.owners, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .delegation b⟩ => ⟨.delegation, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .answer b⟩ => ⟨.answer, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .retraction b⟩ => ⟨.retraction, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .revocation b⟩ => ⟨.revocation, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .origin b⟩ => ⟨.origin, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .tool b⟩ => ⟨.tool, (p, i, d, o), b⟩)
    (fun x => match x with
      | ⟨.owners, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .owners b⟩
      | ⟨.delegation, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .delegation b⟩
      | ⟨.answer, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .answer b⟩
      | ⟨.retraction, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .retraction b⟩
      | ⟨.revocation, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .revocation b⟩
      | ⟨.origin, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .origin b⟩
      | ⟨.tool, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .tool b⟩)
    (fun s => by obtain ⟨p, i, d, o, b⟩ := s; cases b <;> rfl)

@[expose] def print (s : Statement) : String := String.ofList (codec.print s)

@[expose] def parse (t : String) : Option Statement := codec.read t.toList

theorem parse_eq_some_iff (t : String) (s : Statement) : parse t = some s ↔ print s = t := by
  rw [parse, Codec.read_eq_some_iff, print]
  constructor
  · intro h; rw [h, String.ofList_toList]
  · rintro rfl; exact String.toList_ofList.symm

theorem parse_print (s : Statement) : parse (print s) = some s :=
  (parse_eq_some_iff _ _).mpr rfl

theorem print_injective {s s' : Statement} (h : print s = print s') : s = s' := by
  have := parse_print s
  rw [h, parse_print] at this
  exact (Option.some.inj this).symm

@[expose] def parseUTF8 (b : ByteArray) : Option Statement := (String.fromUTF8? b).bind parse

theorem fromUTF8?_eq_some_iff (b : ByteArray) (t : String) :
    String.fromUTF8? b = some t ↔ t.toUTF8 = b := by
  rw [String.toUTF8_eq_toByteArray]
  constructor
  · intro h
    unfold String.fromUTF8? at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl
    show (if h : t.toByteArray.IsValidUTF8 then some (String.fromUTF8 t.toByteArray h) else none) =
      some t
    exact (dite_eq_left t.isValidUTF8).trans rfl

theorem parseUTF8_eq_some_iff (b : ByteArray) (s : Statement) :
    parseUTF8 b = some s ↔ (print s).toUTF8 = b := by
  simp only [parseUTF8, Option.bind_eq_some_iff, fromUTF8?_eq_some_iff, parse_eq_some_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem plain_print (s : Statement) : Plain (print s).toList := by
  rw [print, String.toList_ofList]
  exact codec.plain s

end Statement

end LeanIntent
