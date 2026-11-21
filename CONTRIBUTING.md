# Contributing

Issues, documentation improvements, and pull requests (including AI-assisted contributions directed by a contributor) are welcome. Participation is governed by the [Code of Conduct](CODE_OF_CONDUCT.md), and contributions are submitted under the [MIT License](LICENSE) (except [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md), which is adapted from the Contributor Covenant 2.1 under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)). Do not report security bugs or check/audit bypasses in public issues or pull requests; use GitHub private vulnerability reporting as described in [SECURITY.md](SECURITY.md).

## Toolchain and checks

`lean-intent` pins its Lean release in [`lean-toolchain`](lean-toolchain) (`v4.36.0`) and permits no external Lake dependencies ([`lakefile.toml`](lakefile.toml)). Before opening or updating a pull request, run the full repository check and test-listing verification from the repository root:

```sh
lean --run tools/check.lean
lean --run tools/check.lean --tests
```

- `lean --run tools/check.lean` checks `LAKE-CONFIG`, `LEAN-BUILD` (`lake build --wfail` over every library target and tracked library file), `LEAN-MODULE`, `AXIOMS`, `PROCESS`, `CODES` (via `tools/codes.lean`), and `NO-COMMENTS` (against `tools/comment-ratchet.json` and the merge base with `--base-ref <ref>`, defaulting to `refs/remotes/origin/main` then `refs/heads/main`). It must exit with status `0`. See [ADR-0001](docs/adr/0001-repository-checks-and-trusted-base.md) through [ADR-0004](docs/adr/0004-ratcheted-ban-on-lean-comments.md).
- `lean --run tools/check.lean --tests` must exit with status `0` and print nothing to standard output.
- Because `NO-COMMENTS` verifies monotonicity against the merge base's `tools/comment-ratchet.json`, run checks in a checkout with full history (not a shallow clone without a base commit). If `origin/main` points to your own fork or equals `HEAD`, pass `--base-ref <ref>` (for example, `lean --run tools/check.lean --base-ref upstream/main` or the pre-change base commit SHA) so the ratchet compares against upstream `main` rather than a stale fork branch or the commit itself.

## Coding and verification standards

- **Module files (`LEAN-MODULE`):** Every `.lean` file in `LeanIntent/`, `LeanIntentExamples/`, and `tools/` must be a `module` file following [`README.md`](README.md#module-files) and [`README.md`](README.md#adding-a-feature).
- **No Lean comments (`NO-COMMENTS`):** All four Lean comment forms (`--`, `/- ... -/`, `/-- ... -/`, `/-! ... -/`) are banned in new or edited `.lean` code; keep non-obvious architectural and trusted-base rationale in `docs/` or [`docs/adr/`](docs/adr/README.md). If draining legacy comments recorded in `tools/comment-ratchet.json`, inspect them with `lean --run tools/check.lean --comments [<file>]` and lower the manifest monotonically ([ADR-0004](docs/adr/0004-ratcheted-ban-on-lean-comments.md)).
- **No tests (`--tests`):** `lean-intent` establishes its claims by machine-checked Lean theorems resting only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), never by tests (`#eval`, `#guard`, `native_decide`, `testDriver`, or project-declared test elaborators). See [`README.md`](README.md#checks) and [ADR-0002](docs/adr/0002-test-listing-and-pinned-lean-tokens.md).
- **Adding a feature:** Place new modules under `LeanIntent/`, worked examples under `LeanIntentExamples/`, and documentation under `docs/` without modifying shared module lists; `lakefile.toml` selects modules by glob ([`README.md`](README.md#adding-a-feature)).

## Pull requests, commits, and triage

- Coding agents working on `lean-intent` itself must read [`AGENTS.md`](AGENTS.md) (projects depending on `lean-intent` use [`skills/`](skills/) instead).
- Pull requests are squash-merged onto `main` using the PR title and body; `main` refuses direct pushes, force-pushes, and commits without a verified signature.
- Title each pull request as a [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) header (`type(scope)!: summary`). Keep issue and pull-request descriptions to single-line paragraphs and list items, fill every top-level heading of [`.github/pull_request_template.md`](.github/pull_request_template.md), link each resolved issue on its own line (`Closes #N.`), and include no AI/assistant `Co-Authored-By:` trailers.
- [`.github/workflows/check.yml`](.github/workflows/check.yml) runs `lean --run tools/check.lean` (passing `--base-ref` with the PR base SHA on pull requests and the pre-push `before` SHA on pushes to `main`) and verifies empty `lean --run tools/check.lean --tests` output on every pull request and push to `main`; the `lean` check is required (with the branch up to date) to merge into `main`.
- `lean-intent` is maintained by [@rbeauchamp](https://github.com/rbeauchamp) without a promised response SLA. Pull requests touching the paths listed in [`.github/CODEOWNERS`](.github/CODEOWNERS) automatically request review from `@rbeauchamp`.
