# Instructions for agents

These instructions govern coding agents working on `lean-intent` itself under any harness. They do not apply to agents working in repositories that depend on `lean-intent` (which use [`skills/`](skills/) and [`README.md`](README.md)). Read [`CONTRIBUTING.md`](CONTRIBUTING.md) in full before modifying code, proofs, or documentation.

## Standalone deductive and formal engineering rules

This repository is self-contained for all engineering rules governing `lean-intent` and does not depend on external user-level instructions:

- **Proofs, not tests:** Establish every library claim by machine-checked Lean theorems resting only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Never add tests (`--tests` must exit `0` with empty stdout), never add external Lake dependencies (`LAKE-CONFIG`), and keep every tracked `.lean` file as a `module` file (`LEAN-MODULE`) with zero Lean comments of any form (`NO-COMMENTS`, drained `[]` ratchet).
- **Methodology:** Follow [`CONTRIBUTING.md#deductive-and-formal-engineering-standards`](CONTRIBUTING.md#deductive-and-formal-engineering-standards) — the 5-rung enforcement ladder and cost bound, design-and-attack-first, guard-removal caller-route derivation, proof-to-execution linkage, proof economy, and 3-part defect closure.
- **Environment readers and Regula:** Every library declaration handed an `Environment` must guard against unloaded extensions with `LeanIntent.asking` or `LeanIntent.askingIn`, take a `LeanIntent.Loaded` proof, or belong to the closed `stateless` list (`READERS`); no declaration outside `LeanIntent.Imported.stored` may import modules with extensions unloaded (`LOADED`); and all library modules must pass out-of-tree strict `regula` `standard-logical` proof-verdict checking (`REGULA`), `CODES`, and `PROCESS`.
- **Evidence honesty and unread sources:** Distinguish machine-checked, argued, observed, assumed, and open claims; read every affected module and relevant source in full, and report any unreadable source immediately rather than guessing or summarizing.
- **Review cost bound and convergence:** Fix every finding whose failure is serious, hard to undo, or observed; record cheap/unobserved static remainders as accepted risk with reason. Cap validation review loops at 3 rounds and triage remaining findings under the cost bound rather than looping indefinitely.

## Merge gate and landing pull requests

Every change lands through a squash-merged pull request onto `main`:

- `main` refuses direct pushes, force-pushes, and commits without a verified GPG signature, and requires the GitHub Actions `lean` check from [`.github/workflows/check.yml`](.github/workflows/check.yml) alongside `Analyze (actions)` and `CodeQL` with the branch up to date.
- Local validation runs through `no-mistakes` ([`.no-mistakes.yaml`](.no-mistakes.yaml)), executing `lean --run tools/check.lean` and verifying `lean --run tools/check.lean --tests` exits `0` with empty stdout.
- Use a [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) PR title (`type(scope)!: summary`), fill all four top-level headings of [`.github/pull_request_template.md`](.github/pull_request_template.md) with single-line paragraphs and list items, link each resolved issue on its own line (`Closes #N.`), and scrub public PR/issue text of local paths, internal pipeline IDs, and private workspace tokens before posting.
- **Zero AI co-author trailers:** No commit on a PR branch or squash commit on `main` may carry a `Co-Authored-By:` trailer naming a model or assistant. Before merging, ensure every branch commit lacks such a trailer, squash-merge using the PR title and description verbatim so GitHub does not substitute default multi-commit messages or synthesize a model co-author line, inspect the landed commit message and tree on `main`, and verify every linked issue closed.

## In a cloud session (without local `no-mistakes`)

When working in a cloud environment that cannot run the local `no-mistakes` pipeline:

1. **Independent adversarial review:** Have an agent that did not author the change review the diff and PR description (treating the description's claims as assertions to attack) before calling the PR ready or merging. Fix every finding or answer it in the PR description; any edit to the tree after review requires a fresh review pass.
2. **Clean local check and CI:** Run `lean --run tools/check.lean` (exit `0`) and `lean --run tools/check.lean --tests` (exit `0`, empty stdout) from a clean checkout without `.lake`, and confirm [`.github/workflows/check.yml`](.github/workflows/check.yml) passes on the exact head commit standing on current `main`. Rebase and re-verify both checks, CI, and review if `main` moves or the tree changes.
3. **Accepted risk accounting:** Record under **Accepted risk** in the PR description that local `no-mistakes` did not run, naming the exact commit checked, both command results, the CI workflow run, who reviewed, and anything left unchecked. Only record observed results.
4. **Merge authority and branch rewrites:** Wait for explicit owner direction before merging from a cloud session, and do not force-push a PR branch except when authorized (such as stripping an accidental co-author trailer on the session's own branch, followed by re-running the checks on the new head).

## Cloud build toolchain notes

[`lean-toolchain`](lean-toolchain) pins the Lean release (`v4.36.0`). [`.github/workflows/check.yml`](.github/workflows/check.yml) installs the SHA-256-verified Linux release archive matching [`lean-toolchain`](lean-toolchain) directly from GitHub Releases; environments using `elan` instead require network access to `release.lean-lang.org` and `releases.lean-lang.org`.
