# ADR-0004: Ratcheted ban on Lean comments (`NO-COMMENTS`)

## Status

Accepted

## Context

Code comments across `lean-intent`'s `.lean` files accumulated 6,804 comment lines (~26.1% of all Lean source lines; ~7,030 lines or 27.0% including collapsed blank lines): mostly tautological docstrings restating types and definitions, alongside stale comments that drifted behind code changes and excuse comments that rationalized hacky or incomplete implementations (e.g., unnecessary `import all`, skipped generic explanations, hardcoded magic fuel bounds, and stringly-typed sentinels; tracked in #85–#95). Meanwhile, genuine architectural and TCB rationale belongs in durable documentation (`docs/` and `docs/adr/`) rather than scattered inside source files.

Removing all ~2,400 comments cleanly in one change would make a single pull request too large to audit and review carefully.

## Decision

### Scope

- All four Lean comment forms are banned across every tracked `.lean` file (`git ls-files -z -- '*.lean'`, including `LeanIntent/`, `LeanIntentExamples/`, and `tools/`):
  - line comments (`-- ...`),
  - plain block comments (`/- ... -/`),
  - declaration docstrings (`/-- ... -/`), and
  - module docstrings (`/-! ... -/`).
- Non-Lean configuration and workflow files (`.no-mistakes.yaml`, `.github/workflows/check.yml`, `lakefile.toml`) and Markdown documentation (`README.md`, `docs/`, `.github/pull_request_template.md`) are excluded: `tools/check.lean` has no YAML parser (and `LAKE-CONFIG` forbids external dependencies), `.no-mistakes.yaml`'s timeout messages and `AGENTS.md` cite its config comments, and `check.yml` documents a commit-pinned GitHub Action version.

### Owning-system enforcement (`NO-COMMENTS` in `tools/check.lean`)

`NO-COMMENTS` parses every tracked `.lean` file through Lean's own parser rather than regexes or hand-rolled lexers:

- Fast path: `Lean.Parser.parseHeader` followed by `Lean.Parser.parseCommand` in a loop until `Parser.Command.eoi` against the built library environment (plus `Lean` and `Lake`, loaded with `loadExts := true`).
- Frontend fallback: if a file requires elaborated local/opened syntax (e.g., `open Lean.Parser.Term` for `bracketedBinderF` in `LeanIntent/Declared/Handler.lean`), `NO-COMMENTS` runs Lean's incremental frontend (`Elab.processHeader` + `Elab.IO.processCommandsIncrementally` with `debug.byAsSorry := true`) on that file.
- Fail-closed completeness checks:
  - any header, parser, or frontend error fails the check rather than silently counting 0;
  - `#exit` is rejected and final parser position must equal `inputString.rawEndPos`, so trailing comments after `#exit` or EOF cannot escape;
  - every `SourceInfo.original` `leading`/`trailing` trivia slice (plus inter-command byte spans `[0, headerPos)` and `[prevPos, cmdPos)`, deduplicated by byte range) is scanned using the exact rules of `Lean.Parser.whitespace` (`Lean/Parser/Basic.lean:563-587`), failing on any unexpected non-whitespace byte or unterminated block comment;
  - every `Parser.Command.docComment`, `Parser.Command.plainDocComment`, and `Parser.Command.moduleDoc` node is counted once without recursing into its interior tokens (inspecting only outer `leading` of `getHeadInfo?` and outer `trailing` of `getTailInfo?`).
- `Check.check` runs `--check-comments` in a separate child process (with the same `0`/`1`/`2` exit-code protocol as `tools/codes.lean`) before importing the library environment for `AXIOMS`/`PROCESS`, keeping `Check.check` non-`unsafe` and preventing multiple imported `Environment`s from residing in memory simultaneously.
- `lean --run tools/check.lean --comments [file]` prints the parser-verified comment counts (and per-comment line spans when given a file path), and `--comments-json` emits the sorted JSON ratchet format, for use by the `/delete-comment` skill (`.agents/skills/delete-comment/SKILL.md`).

### Strict per-file downward-only ratchet (`tools/comment-ratchet.json`)

- Remaining comments in files not yet cleared are recorded in `tools/comment-ratchet.json` as a JSON array of objects `[{"file": "...", "comments": N, "lines": M}, ...]`.
- A JSON array is used instead of a top-level JSON object because `Lean.Json.parse` silently overwrites duplicate object keys; the checker rejects duplicate `file` entries, unknown keys, malformed entries, entries with `comments == 0` or `lines == 0`, and entries naming files not in `git ls-files -- '*.lean'`.
- Tracking both `comments` (count of comment tokens/nodes) and `lines` (distinct 1-based line numbers touched by any comment) prevents both adding new comments and growing existing block/doc comments onto additional lines.
- The ratchet is **strict**:
  - any tracked `.lean` file absent from `tools/comment-ratchet.json` must have `0` comments and `0` lines (enforcing zero comments on all new files and all cleared files);
  - any file whose `comments` or `lines` exceeds its ratchet ceiling is rejected;
  - any file whose `comments` or `lines` drops below its ratchet ceiling is rejected until `tools/comment-ratchet.json` is tightened to match (or the entry is removed at `0/0`), preventing deleted comments from leaving slack for new comments later.

## Consequences

- Deleting `/--` docstrings removes Lean LSP hover tooltips and `#print` docstrings; module specifications and non-obvious design rationale must live in `docs/` and `docs/adr/`.
- Any documentation link referencing a removed module comment (such as `README.md`, `.no-mistakes.yaml`, and `docs/*.md`) must be updated in the same change that removes that comment.
- Once every entry in `tools/comment-ratchet.json` is drained to `[]`, the codebase will carry zero Lean comments and `NO-COMMENTS` enforces a total ban.
