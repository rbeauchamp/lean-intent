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
   Build the library first (`lake build --wfail`): the inventory reads each file through Lean's frontend against the built library, in a child process per file, three at a time (about a minute for the whole repository). Then list the remaining files, and one file's remaining comments with each one's kind, line range and fingerprint:
   ```sh
   lean --run tools/check.lean --comments
   lean --run tools/check.lean --comments <path/to/File.lean>
   ```
   Never rely on regexes or ad-hoc grep to count comments; `tools/check.lean --comments` reads through the same frontend child processes as `NO-COMMENTS`. Keep the `--comments <file>` output of each file you will touch: it tells which fingerprints the comments you delete have.

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
   Remove only comment text and redundant consecutive blank lines left behind; change no Lean code semantics in a pure comment-drain PR (fixes for filed Excuse issues land in their own PRs). Do not edit, reword, re-indent or move a comment you keep: its fingerprint is the hash of its exact text, so `NO-COMMENTS` reads a changed comment as a new one, and a comment that moves to another file as new there.

6. **Tighten `tools/comment-ratchet.json` strictly downward.**
   Each entry records a file's remaining comments by fingerprint: `{"file": ..., "comments": N, "lines": M, "fingerprints": [...]}`, the fingerprints in ascending order, one per comment, repeats kept.
   - Remove the whole entry of every file whose comment count reached `0`.
   - For a file only partially cleaned, run `lean --run tools/check.lean --comments <file>` again, delete from its entry the fingerprint of each comment that is gone (one occurrence per deleted comment; the remaining ones stay in order), and set `comments` and `lines` to the counts that command prints. `NO-COMMENTS` names the fingerprints to remove and the counts to set when an entry is not yet tight.
   - A drain's diff of the manifest only deletes lines and lowers counts. `NO-COMMENTS` refuses a manifest that does not describe the files exactly, and, wherever Git gives a merge base with `origin/main` or `main` that holds the manifest, one that records a file or a fingerprint the merge base's does not. That comparison is skipped, with a note on standard error, in a checkout with no such merge base (a shallow clone, or one with neither ref): there a comment added together with its fingerprint passes, so run the check where `origin/main` is fetched.

7. **Verify with the repository checks.**
   ```sh
   lean --run tools/check.lean
   lean --run tools/check.lean --tests
   ```
   - `lean --run tools/check.lean` must exit `0` (confirming `LAKE-CONFIG`, `LEAN-BUILD`, `LEAN-MODULE`, `AXIOMS`, `PROCESS`, `CODES`, and `NO-COMMENTS`).
   - `lean --run tools/check.lean --tests` must exit `0` and print nothing.

8. **Report the drain-down.**
   Summarize counts by category (Tautology, Stale, Excuse, Decision Record), every GitHub issue filed (or existing issue referenced), every ADR added/updated, lines shed in this PR, and remaining files/comments/lines in `tools/comment-ratchet.json`.
