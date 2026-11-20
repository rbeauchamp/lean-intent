---
name: delete-comment
description: >-
  Audit and delete Lean code comments in lean-intent under the NO-COMMENTS ratchet
  (tools/comment-ratchet.json): classify every comment as Tautology, Excuse, Stale,
  or Decision Record, file GitHub issues for Excuses, move Decision Records into
  docs/adr/, update any doc references to removed module comments, tighten the
  ratchet, and verify with tools/check.lean. Use when draining remaining comments
  in lean-intent or on /delete-comment.
user-invocable: true
---

# delete-comment

Drain Lean code comments (`--`, `/- ... -/`, `/-- ... -/`, `/-! ... -/`) out of `lean-intent` under the strict per-file downward-only ratchet enforced by `tools/check.lean` (`NO-COMMENTS`, [ADR-0004](../../../docs/adr/0004-ratcheted-ban-on-lean-comments.md)).

Config/workflow `#` comments (`.no-mistakes.yaml`, `.github/workflows/check.yml`, `lakefile.toml`) and Markdown documentation are out of scope.

## Procedure

1. **Inspect the remaining ratchet backlog.**
   Ensure `.lake/build` exists (`lake build --wfail` if needed), then list remaining files and exact parser-verified comment locations through Lean's own parser:
   ```sh
   lean --run tools/check.lean --comments
   lean --run tools/check.lean --comments <path/to/File.lean>
   ```
   Never rely on regexes or ad-hoc grep to count comments; `tools/check.lean --comments` uses the exact same `Lean.Parser` / frontend pass as `NO-COMMENTS`.

2. **Choose a reviewable batch.**
   Pick one file or a small cohesive group of related modules (for example, one feature's modules and worked example) to clear completely to `0` comments in one PR.

3. **Check open issues and doc cross-references first.**
   - List open issues (`gh issue list --state open --limit 50`) so you do not file duplicates for known defects.
   - Check whether `README.md`, `AGENTS.md`, `.no-mistakes.yaml`, or `docs/*.md` explicitly cite any module comment you are about to delete:
     ```sh
     git grep -n -i "comment" -- README.md AGENTS.md .no-mistakes.yaml docs/
     ```
     Whenever a document cites a module comment (e.g., `docs/execution.md` citing `LeanIntent/Execution/Read.lean`, `docs/implementation.md` citing `LeanIntent/Implementation/Read.lean`, `docs/required-theorems.md` citing `LeanIntent/Required/Read.lean`), migrate the cited content into that doc or an ADR in `docs/adr/` and update every citation in the same PR so no statement becomes false.

4. **Read every target file in full and categorize every comment.**
   Read the actual surrounding Lean code before classifying each comment into exactly one category:
   - **Tautology**: simply repeats what is already visible from the code, types, names, or theorem statements (including trivial field/constructor docstrings and `/-! ## ... -/` section dividers).
     - **Action**: delete the comment.
   - **Stale**: references nonexistent or renamed symbols, removed modules, outdated Lean behavior, or claims that contradict the code.
     - **Action**: delete the comment. If the stale claim also appears in `docs/*.md`, correct it there too; if it masked a real code defect, file an issue.
   - **Excuse**: rationalizes a hacky, fragile, arbitrary, or corner-cutting implementation (magic bounds, silent skips, stringly-typed sentinels, unnecessary `import all`, workarounds) instead of fixing it properly.
     - **Action**: delete the comment AND file a GitHub issue (`gh issue create --label bug` or `--label enhancement`, writing one line per paragraph and list item with no hard wrapping, citing exact file/lines, failed property, contract, and assumption), unless an open issue already tracks the exact defect (in which case reference it in your report).
   - **Decision Record**: documents an important, non-obvious architectural, semantic, security, performance, or Trusted Computing Base (TCB) decision not visible from reading the code alone (including source-verified Lean toolchain facts needed for upgrades).
     - **Action**: verify whether `docs/*.md` or an existing ADR in `docs/adr/` already records the full decision and rationale. Move any non-obvious detail not already documented into a new ADR `docs/adr/NNNN-<slug>.md` (or extend the directly relevant existing ADR), update [docs/adr/README.md](../../../docs/adr/README.md), and delete the comment.

5. **Delete the comments cleanly.**
   Remove only comment text and redundant consecutive blank lines left behind; change no Lean code semantics in a pure comment-drain PR (fixes for filed Excuse issues land in their own PRs).

6. **Tighten `tools/comment-ratchet.json` strictly downward.**
   - Remove every file whose comment count reached `0`.
   - If a file was only partially cleaned, lower its `comments` and `lines` values to the exact counts reported by `lean --run tools/check.lean --comments <file>`.
   - Never raise any ceiling, never add an unlisted file, and never leave a `0/0` entry (`NO-COMMENTS` rejects all three).

7. **Verify with the repository checks.**
   ```sh
   lean --run tools/check.lean
   lean --run tools/check.lean --tests
   ```
   - `lean --run tools/check.lean` must exit `0` (confirming `LAKE-CONFIG`, `LEAN-BUILD`, `LEAN-MODULE`, `AXIOMS`, `PROCESS`, `CODES`, and `NO-COMMENTS`).
   - `lean --run tools/check.lean --tests` must exit `0` and print nothing.

8. **Report the drain-down.**
   Summarize counts by category (Tautology, Stale, Excuse, Decision Record), every GitHub issue filed (or existing issue referenced), every ADR added/updated, lines shed in this PR, and remaining files/comments/lines in `tools/comment-ratchet.json`.
