import LeanIntent.Answers
import LeanIntent.Codec.Text

/-!
# Statements: the owners' log, one text each

A project records who may answer for its intent, and every answer, as statements committed in the
project: an owners declaration, a delegation, an answer, a retraction of an answer and a revocation
of a delegation. Each statement is a record of where it came from: the date, and the owner's words
or a reference to where they are kept. A reviewer reads its text, the project commits its text, and
a check reads its text, so each statement has exactly one text and each text at most one statement:

* `Statement.print` writes a statement's text, a function of the statement alone;
* `Statement.parse` reads a text back, and accepts exactly the texts `print` writes
  (`Statement.parse_eq_some_iff`), so `parse (print s) = some s` for every statement
  (`Statement.parse_print`), no two statements share a text (`Statement.print_injective`), and a
  text that `print` does not write is refused, never read leniently;
* `Statement.parseUTF8` reads the bytes of a committed file, and accepts exactly the UTF-8 encoding
  of a printed text (`Statement.parseUTF8_eq_some_iff`), so the bytes a project commits, and those a
  signature covers for a project that signs, are fixed by the statement alone;
* every printed text is plain (`Statement.plain_print`): its only control character is the line feed
  that ends each line, and it holds no line or paragraph separator or bidirectional formatting
  character, so each line a display shows is a line the parser reads.

The grammar is closed. Every value has a fixed place: there is no optional whitespace, every list is
printed in the order the statement holds it, and every number in decimal with no leading zeros
except those that pad a date. Names of projects, principals and statements are identifiers in a
closed set of ASCII characters (`identChar`). Any other string is printed on one line by
`Codec.line` or as lines by `Codec.text`, with `\` and each concealing character escaped. A
public key is printed as OpenSSH writes it, its algorithm from a closed list and its data in
base64.

What this module does not decide: whether a statement's authority traces back to a declared owner
(`LeanIntent.Trace` decides it for answers and retractions), whether a signature over it is valid
(lean-intent #19), and whether an answer's text has changed since it was given. The text an answer
is recorded against is `LeanIntent.Render.answerText`; recording that text with an answer
statement, whose `revision` and `predicate` fields hold what was shown, and refusing an answer whose
text has since changed, are lean-intent #5's. It reads the text of each statement, and no more.
-/

namespace LeanIntent

open Codec

/-- The characters of an identifier: the ASCII letters and digits, and `.`, `_`, `-`, `@`, `+` and
`/`. None is a character OpenSSH's allowed-signers format treats as a pattern or separator. -/
def identChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    n == 46 || n == 95 || n == 45 || n == 64 || n == 43 || n == 47

/-- The characters of base64: the ASCII letters and digits, and `+`, `/` and `=`. -/
def base64Char (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 43 || n == 47 || n == 61

/-- A non-empty string of characters that `p` admits. -/
structure Word (p : Char → Bool) where
  /-- The string. -/
  toString : String
  /-- It is not empty, and `p` admits each of its characters. -/
  valid : toString.toList ≠ [] ∧ toString.toList.all p = true

instance {p : Char → Bool} : DecidableEq (Word p) := fun a b =>
  decidable_of_iff (a.toString = b.toString) ⟨fun h => by cases a; cases b; cases h; rfl, (· ▸ rfl)⟩

/-- The word `s`, for a string literal `s`: Lean decides that it is a word of `p` by writing out its
characters. -/
def Word.of {p : Char → Bool} (s : String)
    (h : s.toList ≠ [] ∧ s.toList.all p = true := by simp only [String.reduceToList]; decide) :
    Word p :=
  ⟨s, h⟩

/-- The name of a project, a principal or a statement. -/
abbrev Ident := Word identChar

/-- The algorithms of the public keys a principal may declare: OpenSSH's plain key types, without
certificates and without DSA, which OpenSSH no longer supports. -/
inductive KeyAlgorithm where
  /-- `ssh-ed25519`. -/
  | ed25519
  /-- `sk-ssh-ed25519@openssh.com`, an Ed25519 key held by a FIDO authenticator. -/
  | ed25519Sk
  /-- `ecdsa-sha2-nistp256`. -/
  | ecdsaP256
  /-- `ecdsa-sha2-nistp384`. -/
  | ecdsaP384
  /-- `ecdsa-sha2-nistp521`. -/
  | ecdsaP521
  /-- `sk-ecdsa-sha2-nistp256@openssh.com`, an ECDSA key held by a FIDO authenticator. -/
  | ecdsaP256Sk
  /-- `ssh-rsa`. -/
  | rsa
  deriving DecidableEq

/-- The name OpenSSH gives the algorithm, then the space that ends it in a public key line. -/
def KeyAlgorithm.keyword : KeyAlgorithm → List Char
  | .ed25519 => chars!"ssh-ed25519 "
  | .ed25519Sk => chars!"sk-ssh-ed25519@openssh.com "
  | .ecdsaP256 => chars!"ecdsa-sha2-nistp256 "
  | .ecdsaP384 => chars!"ecdsa-sha2-nistp384 "
  | .ecdsaP521 => chars!"ecdsa-sha2-nistp521 "
  | .ecdsaP256Sk => chars!"sk-ecdsa-sha2-nistp256@openssh.com "
  | .rsa => chars!"ssh-rsa "

/-- A public key, as the first two fields of an OpenSSH public key line: its algorithm and its data
in base64. Two texts of the same key data are two keys here; a check that compares keys decodes
them. -/
structure PublicKey where
  /-- The key's algorithm. -/
  algorithm : KeyAlgorithm
  /-- The key's data, in base64. -/
  data : Word base64Char
  deriving DecidableEq

/-- A principal: a person or an agent, by name, with the public keys it signs with, if any. -/
structure Principal where
  /-- The principal's name. -/
  name : Ident
  /-- The public keys of the principal; empty for a principal that does not sign. -/
  keys : List PublicKey
  deriving DecidableEq

/-- Who makes a statement: a principal, acting as an owner, or under the delegation named. -/
structure Authority where
  /-- The principal who makes the statement. -/
  principal : Ident
  /-- The id of the delegation the principal acts under; `none` when it acts as an owner. -/
  delegation : Option Ident
  deriving DecidableEq

/-- The number of days of a month of the Gregorian calendar. -/
def Date.daysIn (year month : Nat) : Nat :=
  if month = 2 then (if year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0) then 29 else 28)
  else if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then 30 else 31

/-- `year`, `month` and `day` name a day of the Gregorian calendar. -/
def Date.isValid (year month day : Nat) : Bool :=
  1 ≤ month && month ≤ 12 && 1 ≤ day && day ≤ Date.daysIn year month

/-- A day of the Gregorian calendar, printed as ISO 8601 writes it, `YYYY-MM-DD`. -/
structure Date where
  /-- The year. -/
  year : Nat
  /-- The month, from 1 to 12. -/
  month : Nat
  /-- The day of the month, from 1. -/
  day : Nat
  /-- The three name a day. -/
  valid : Date.isValid year month day = true
  deriving DecidableEq

/-- Where a statement came from: the owner's words, as written, or a reference to where they are
kept. -/
inductive Source where
  /-- The owner's words, as written. -/
  | words (text : String)
  /-- Where the owner's words are kept, such as a link to a comment or a message. -/
  | reference (location : String)
  deriving DecidableEq

/-- The intent records a delegation covers. -/
inductive Records where
  /-- Every intent record of the project. -/
  | all
  /-- The intent records named. -/
  | only (names : List String)
  deriving DecidableEq

/-- What a delegation lets its delegate do: answer for which records, and which acts. -/
structure Scope where
  /-- The intent records covered. -/
  records : Records
  /-- The delegate may confirm a consequence. -/
  confirm : Bool
  /-- The delegate may decline a consequence. -/
  decline : Bool
  /-- The delegate may retract an answer. -/
  retract : Bool
  deriving DecidableEq

deriving instance DecidableEq for Consequence.Kind
deriving instance DecidableEq for Verdict

namespace Statement

/-- A declaration of the project's owners. The first in a project's log is its root of trust; the
threshold, for a project that signs, is how many owners must sign the next declaration. -/
structure Owners where
  /-- The owners. -/
  principals : List Principal
  /-- How many owners must approve the next declaration, if the project sets a number. -/
  threshold : Option Nat
  deriving DecidableEq

/-- A delegation: `delegator` lets `delegate` act within `scope`, and, if `mayPassOn`, delegate
within it in turn. -/
structure Delegation where
  /-- Who grants the delegation. -/
  delegator : Authority
  /-- Who receives it. -/
  delegate : Principal
  /-- What it lets the delegate do. -/
  scope : Scope
  /-- Whether the delegate may pass it on. -/
  mayPassOn : Bool
  deriving DecidableEq

/-- An answer to one consequence of one revision of an intent record. -/
structure Answer where
  /-- Who answers. -/
  author : Authority
  /-- The intent record's name. -/
  record : String
  /-- The revision of the record answered, as it was shown. -/
  revision : String
  /-- The consequence's name, as it was shown. -/
  consequence : String
  /-- Whether the consequence was shown as entailed or as possible. -/
  kind : Consequence.Kind
  /-- The consequence's predicate, as it was shown. -/
  predicate : String
  /-- The answer. -/
  verdict : Verdict
  deriving DecidableEq

/-- A retraction of the answer stated by the statement named. -/
structure Retraction where
  /-- Who retracts it. -/
  author : Authority
  /-- The id of the answer's statement. -/
  answer : Ident
  deriving DecidableEq

/-- A revocation of the delegation stated by the statement named. -/
structure Revocation where
  /-- Who revokes it. -/
  author : Authority
  /-- The id of the delegation's statement. -/
  delegation : Ident
  deriving DecidableEq

/-- What a statement states, one of the five kinds. -/
inductive Body where
  /-- A declaration of the owners. -/
  | owners (o : Owners)
  /-- A delegation. -/
  | delegation (d : Delegation)
  /-- An answer. -/
  | answer (a : Answer)
  /-- A retraction of an answer. -/
  | retraction (r : Retraction)
  /-- A revocation of a delegation. -/
  | revocation (r : Revocation)
  deriving DecidableEq

end Statement

/-- A statement of a project's log: its project, its id, unique in the log, its date and source,
and what it states. -/
structure Statement where
  /-- The project the statement belongs to. -/
  project : Ident
  /-- The statement's id. -/
  id : Ident
  /-- The day it was made. -/
  date : Date
  /-- Where it came from. -/
  source : Source
  /-- What it states. -/
  body : Statement.Body
  deriving DecidableEq

/-! ## The grammar -/

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

/-- A word of `p`'s characters, then `term`. -/
def word (p : Char → Bool) (hp : ∀ c, p c = true → concealing c = false) (term : Char)
    (ht : p term = false) (hterm : Plain [term] := by decide) : Codec (Word p) :=
  map (token p term ht hp hterm) (fun w => ⟨w.toString.toList, w.valid.2⟩)
    (fun l => if h : l.1 ≠ [] then some ⟨String.ofList l.1, by simp [h, l.2]⟩ else none)
    (fun w => by obtain ⟨w, h⟩ := w; simp [h.1, String.ofList_toList])

/-- An identifier on the rest of a line. -/
def ident : Codec Ident := word identChar identChar_plain '\n' (by decide)

/-- `yes` or `no` on the rest of a line. -/
def yesNo : Codec Bool :=
  keywords (fun b => if b then chars!"yes\n" else chars!"no\n") [false, true]
    (by intro b; cases b <;> decide) (by decide) (by intro b; cases b <;> decide)

/-- A public key on a line of its own: `key`, its algorithm and its data. -/
def publicKey : Codec PublicKey :=
  map (keyed chars!"key " (by decide)
      ((keywords KeyAlgorithm.keyword
        [.ed25519, .ed25519Sk, .ecdsaP256, .ecdsaP384, .ecdsaP521, .ecdsaP256Sk, .rsa]
        (by intro a; cases a <;> decide) (by decide) (by intro a; cases a <;> decide)).seq
        (word base64Char base64Char_plain '\n' (by decide))))
    (fun k => (k.algorithm, k.data)) (fun (a, d) => some ⟨a, d⟩) (fun _ => rfl)

/-- A principal after the fixed text `role`: its name, then its keys. -/
def principal (role : List Char) (hr : Plain role := by decide) : Codec Principal :=
  map (keyed role hr (ident.seq (keyed chars!"keys " (by decide) (list publicKey))))
    (fun p => (p.name, p.keys)) (fun (n, k) => some ⟨n, k⟩) (fun _ => rfl)

/-- Who makes a statement: `by` and a principal, then `as owner`, or `under` and a delegation. -/
def authority : Codec Authority :=
  map (keyed chars!"by " (by decide)
      (ident.seq
        (option chars!"as owner\n" chars!"under " (by decide) (by decide) (by decide) ident)))
    (fun a => (a.principal, a.delegation)) (fun (p, d) => some ⟨p, d⟩) (fun _ => rfl)

/-- `date` and a day, as `YYYY-MM-DD`. -/
def date : Codec Date :=
  map (keyed chars!"date " (by decide)
      ((nat 4 '-' (by decide)).seq ((nat 2 '-' (by decide)).seq (nat 2 '\n' (by decide)))))
    (fun d => (d.year, d.month, d.day))
    (fun (y, m, d) => if h : Date.isValid y m d = true then some ⟨y, m, d, h⟩ else none)
    (fun d => by obtain ⟨y, m, d, h⟩ := d; simp [h])

/-- `words` and the owner's words as text, or `reference` and a location on the rest of the line. -/
def source : Codec Source :=
  map (sum chars!"words " chars!"reference " (by decide) (by decide) (by decide) text line)
    (fun | .words t => .inl t | .reference r => .inr r)
    (fun | .inl t => some (.words t) | .inr r => some (.reference r))
    (fun s => by cases s <;> rfl)

/-- The records of a scope: `all records`, or `records` and a list of `record` lines. -/
def records : Codec Records :=
  map (option chars!"all records\n" chars!"records " (by decide) (by decide) (by decide)
      (list (keyed chars!"record " (by decide) line)))
    (fun | .all => none | .only ns => some ns)
    (fun | none => some .all | some ns => some (.only ns))
    (fun r => by cases r <;> rfl)

/-- A scope: its records, then whether the delegate may confirm, decline and retract. -/
def scope : Codec Scope :=
  map (records.seq ((keyed chars!"may confirm " (by decide) yesNo).seq
      ((keyed chars!"may decline " (by decide) yesNo).seq
        (keyed chars!"may retract " (by decide) yesNo))))
    (fun s => (s.records, s.confirm, s.decline, s.retract))
    (fun (r, c, d, t) => some ⟨r, c, d, t⟩) (fun _ => rfl)

/-- An owners declaration: `principals` and a list of `principal` entries, then `no threshold`, or
`threshold` and a number. -/
def owners : Codec Statement.Owners :=
  map ((keyed chars!"principals " (by decide) (list (principal chars!"principal "))).seq
      (option chars!"no threshold\n" chars!"threshold " (by decide) (by decide) (by decide)
        (nat 0 '\n' (by decide))))
    (fun o => (o.principals, o.threshold)) (fun (p, t) => some ⟨p, t⟩) (fun _ => rfl)

/-- A delegation: who grants it, the `delegate`, the scope, and whether it may be passed on. -/
def delegation : Codec Statement.Delegation :=
  map (authority.seq ((principal chars!"delegate ").seq
      (scope.seq (keyed chars!"may pass on " (by decide) yesNo))))
    (fun d => (d.delegator, d.delegate, d.scope, d.mayPassOn))
    (fun (a, p, s, m) => some ⟨a, p, s, m⟩) (fun _ => rfl)

/-- The kind of a consequence: `shown as entailment` or `shown as possibility`. -/
def consequenceKind : Codec Consequence.Kind :=
  keywords (fun | .entailment => chars!"shown as entailment\n"
                | .possibility => chars!"shown as possibility\n")
    [.entailment, .possibility] (by intro k; cases k <;> decide) (by decide)
    (by intro k; cases k <;> decide)

/-- A verdict: `verdict confirmed` or `verdict declined`. -/
def verdict : Codec Verdict :=
  keywords (fun | .confirmed => chars!"verdict confirmed\n"
                | .declined => chars!"verdict declined\n")
    [.confirmed, .declined] (by intro v; cases v <;> decide) (by decide)
    (by intro v; cases v <;> decide)

/-- An answer: who answers, the `record`, its `revision`, the `consequence`, its kind, its
`predicate`, and the verdict. -/
def answer : Codec Statement.Answer :=
  map (authority.seq ((keyed chars!"record " (by decide) line).seq
      ((keyed chars!"revision " (by decide) text).seq
      ((keyed chars!"consequence " (by decide) line).seq
      (consequenceKind.seq ((keyed chars!"predicate " (by decide) text).seq verdict))))))
    (fun a => (a.author, a.record, a.revision, a.consequence, a.kind, a.predicate, a.verdict))
    (fun (a, r, v, c, k, p, d) => some ⟨a, r, v, c, k, p, d⟩) (fun _ => rfl)

/-- A retraction: who retracts, then `retracts` and the answer's statement id. -/
def retraction : Codec Statement.Retraction :=
  map (authority.seq (keyed chars!"retracts " (by decide) ident))
    (fun r => (r.author, r.answer)) (fun (a, i) => some ⟨a, i⟩) (fun _ => rfl)

/-- A revocation: who revokes, then `revokes` and the delegation's statement id. -/
def revocation : Codec Statement.Revocation :=
  map (authority.seq (keyed chars!"revokes " (by decide) ident))
    (fun r => (r.author, r.delegation)) (fun (a, i) => some ⟨a, i⟩) (fun _ => rfl)

/-- The five kinds of statement. -/
inductive Kind where
  /-- An owners declaration. -/
  | owners
  /-- A delegation. -/
  | delegation
  /-- An answer. -/
  | answer
  /-- A retraction. -/
  | retraction
  /-- A revocation. -/
  | revocation
  deriving DecidableEq

/-- What a statement of each kind states. -/
def Kind.Body : Kind → Type
  | .owners => Statement.Owners
  | .delegation => Statement.Delegation
  | .answer => Statement.Answer
  | .retraction => Statement.Retraction
  | .revocation => Statement.Revocation

/-- The line that names a statement's kind. -/
def kind : Codec Kind :=
  keywords (fun | .owners => chars!"kind owners\n" | .delegation => chars!"kind delegation\n"
                | .answer => chars!"kind answer\n" | .retraction => chars!"kind retraction\n"
                | .revocation => chars!"kind revocation\n")
    [.owners, .delegation, .answer, .retraction, .revocation] (by intro k; cases k <;> decide)
    (by decide) (by intro k; cases k <;> decide)

/-- The codec of what a statement of kind `k` states. -/
def body : (k : Kind) → Codec k.Body
  | .owners => owners
  | .delegation => delegation
  | .answer => answer
  | .retraction => retraction
  | .revocation => revocation

/-- The fields every statement has, after its kind: `project`, `id`, `date` and its source. -/
def header : Codec (Ident × Ident × Date × Source) :=
  (keyed chars!"project " (by decide) ident).seq ((keyed chars!"id " (by decide) ident).seq
    (date.seq source))

end Grammar

namespace Statement

/-- A statement: the line `lean-intent statement 1`, which names the grammar's version, its kind,
the fields every statement has, and what it states. -/
def codec : Codec Statement :=
  map (keyed chars!"lean-intent statement 1\n" (by decide)
      (Grammar.kind.dep (γ := fun k => (Ident × Ident × Date × Source) × k.Body)
        fun k => Grammar.header.seq (Grammar.body k)))
    (fun s => match s with
      | ⟨p, i, d, o, .owners b⟩ => ⟨.owners, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .delegation b⟩ => ⟨.delegation, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .answer b⟩ => ⟨.answer, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .retraction b⟩ => ⟨.retraction, (p, i, d, o), b⟩
      | ⟨p, i, d, o, .revocation b⟩ => ⟨.revocation, (p, i, d, o), b⟩)
    (fun x => match x with
      | ⟨.owners, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .owners b⟩
      | ⟨.delegation, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .delegation b⟩
      | ⟨.answer, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .answer b⟩
      | ⟨.retraction, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .retraction b⟩
      | ⟨.revocation, (p, i, d, o), b⟩ => some ⟨p, i, d, o, .revocation b⟩)
    (fun s => by obtain ⟨p, i, d, o, b⟩ := s; cases b <;> rfl)

/-! ## Printing and parsing -/

/-- The text of a statement. -/
def print (s : Statement) : String := String.ofList (codec.print s)

/-- The statement whose text is `t`, or `none` when `print` writes no statement as `t`. -/
def parse (t : String) : Option Statement := codec.read t.toList

/-- `parse` accepts exactly the texts `print` writes, and reads each as the statement printed. -/
theorem parse_eq_some_iff (t : String) (s : Statement) : parse t = some s ↔ print s = t := by
  rw [parse, Codec.read_eq_some_iff, print]
  constructor
  · intro h; rw [h, String.ofList_toList]
  · rintro rfl; exact String.toList_ofList.symm

/-- Parsing a statement's text gives back the statement. -/
theorem parse_print (s : Statement) : parse (print s) = some s :=
  (parse_eq_some_iff _ _).mpr rfl

/-- No two statements have the same text. -/
theorem print_injective {s s' : Statement} (h : print s = print s') : s = s' := by
  have := parse_print s
  rw [h, parse_print] at this
  exact (Option.some.inj this).symm

/-- The statement whose text's UTF-8 encoding is `b`, or `none` when there is none. -/
def parseUTF8 (b : ByteArray) : Option Statement := (String.fromUTF8? b).bind parse

theorem fromUTF8?_eq_some_iff (b : ByteArray) (t : String) :
    String.fromUTF8? b = some t ↔ t.toUTF8 = b := by
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

/-- `parseUTF8` accepts exactly the UTF-8 encodings of printed texts, so the bytes of a statement
are fixed by the statement alone. -/
theorem parseUTF8_eq_some_iff (b : ByteArray) (s : Statement) :
    parseUTF8 b = some s ↔ (print s).toUTF8 = b := by
  simp only [parseUTF8, Option.bind_eq_some_iff, fromUTF8?_eq_some_iff, parse_eq_some_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

/-- A statement's text is plain: its only control character is the line feed, and it holds no line
or paragraph separator or bidirectional formatting character. -/
theorem plain_print (s : Statement) : Plain (print s).toList := by
  rw [print, String.toList_ofList]
  exact codec.plain s

end Statement

end LeanIntent
