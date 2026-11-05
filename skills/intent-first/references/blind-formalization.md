# The blind formalization's inputs and prompts

## The directory

Make a new directory outside the repository and put in it only:

- `owner-words.md`: the owner's words, exactly as given, with nothing of yours added: those at the level step 1 started from, and, where the owner adopted a statement, that statement exactly as adopted, with nothing of the proposal's reasoning;
- `types.lean`: the source of the definitions of the types the subject is stated over, copied without the implementation or any other definition that is not a type;
- `Record.lean`: lean-intent's `LeanIntent/Record.lean`, from the commit the project pins.

Where the subject's type or domain is itself what is in question (step 3), the directory instead holds `owner-words.md`, `types.lean` where the input already has a Lean type, and `input-format.md`: the input's own format from that format's owner, such as the section of a tool's documentation that says what its configuration holds, with nothing that says what is wanted and nothing about your record.

Start the second model in a fresh session or context whose only material is that directory's contents: no earlier conversation, and nothing of your account, record, reasoning or the implementation in anything it can read (its workspace, memory, attached files or system prompt). Give it the prompt below that fits what you ask for, and save the prompt and its reply.
Through a command line, for example `codex exec` as the next section gives it, or `claude -p "<prompt>"` run from `<dir>` with the isolation of step 3 found in that tool's own help; through a desktop app, a new conversation whose workspace is `<dir>`; through an API, a request that carries only the prompt and the directory's files. Use a model of another provider than the one that wrote your record, and check the interface's own help for how to start it that way.
Before you take its reply as evidence, confirm what it read: from the interface's own record of the files the session opened (a transcript or tool log) where it keeps one, otherwise from the list the prompt asks for; anything outside the directory's files means the formalization is not blind, so discard it and start a fresh session.

## The Codex command

Keep the prompt, the reply and the event log in a second directory outside `<dir>`, so that the session's only material stays the directory's files.

```sh
codex exec -C <dir> --skip-git-repo-check \
  --ephemeral --ignore-user-config -s read-only \
  --disable memories --disable hooks \
  -m <model> -c model_reasoning_effort=<effort> \
  --json -o <outside>/reply.md \
  "$(cat <outside>/prompt.txt)" < /dev/null > <outside>/events.jsonl
```

Each flag was read from the help of codex-cli 0.166.0 (`codex exec --help`, and `codex features list` for the two feature names); if your version differs, read them again, and where a flag has gone find its current equivalent rather than dropping it.
No model was run with this exact command when it was written: the Acorn pilot of this method, then called spec-first, ran a session of this kind at 0.165.0 (rbeauchamp/acorn PR 188, `docs/spec-first-pilot.md`), so treat your first run as the check of it.

| Part | What it does |
|---|---|
| `< /dev/null` | Closes the command's input; the Acorn pilot observed Codex otherwise waiting on stdin, and the help says piped stdin is appended to the prompt. |
| `--ephemeral` | Persists no session files. |
| `-C`, `--skip-git-repo-check` | Make `<dir>` the working root and allow it not to be a Git repository. |
| `--ignore-user-config` | Does not load `$CODEX_HOME/config.toml`, so what that file configures stays out; auth still uses `CODEX_HOME`. That includes the configured model and effort, so name them with `-m` and `-c`. |
| `-s read-only` | Runs the model's commands in the read-only sandbox. Its permission text limits writes and network, not which files may be read, so treat reads as unconfined: blindness rests on the prompt and on the confirmation below, not on this flag. |
| `--disable memories`, `--disable hooks` | Turn those two features off (`-c features.<name>=false`). |
| `--json` | Prints the events to stdout. With `--ephemeral` no session file is kept, so this stream is the interface's only record of what the session opened. |
| `-o` | Writes the final message to a file. |

These options do not switch off Codex's global instruction file (`$CODEX_HOME/AGENTS.md`): `--ignore-user-config` covers `config.toml` only, and the file still loads.
`codex debug prompt-input --disable memories --disable hooks`, run from `<dir>`, shows what reaches the model without calling one: at 0.166.0 it showed that file and, beside it, the list of installed skills, though that subcommand does not take `--ignore-user-config` and so renders with the user's configuration.
Check that what it shows carries nothing of your account or record, and name the global instruction file in your report as loaded.

Confirm from `events.jsonl` that every command and file the session opened is one of the directory's files and that it made no web request; whether web search is available under this command was not established when this was written, so the log decides it.

## Inside a session that is already sandboxed

Codex runs the model's commands under its own sandbox, which on macOS it applies with `sandbox-exec`, and a process already inside a macOS sandbox could not apply a second one wherever this was tried. This rests on observation, not on documentation: on 2026-11-05, from an agent session confined that way on macOS 27.2, `/usr/bin/sandbox-exec -p '(version 1)(allow default)' /usr/bin/true`, whose profile allows everything, and `codex sandbox -- /usr/bin/true` at codex-cli 0.166.0 both exited 71 with `sandbox-exec: sandbox_apply: Operation not permitted`; and in an adopting project's runs of this step from such a session, the command above returned replies saying that every read of the directory's files failed with that message, and no formalization.

Tell which case you are in before the run, from the session that will start Codex, with `codex sandbox -- /usr/bin/true`, which runs a command under Codex's own sandbox (`codex sandbox --help`), and keep its output. Exit status 0: Codex's sandbox starts there, so use the command above unchanged. Exit status 71 with `sandbox_apply: Operation not permitted`: it cannot, so use the form below. Anything else: find out why before going on.

**The form.** Run the command above exactly as it stands, `-s read-only` included, and change only the prompt: after the prompt that fits, unchanged, put a blank line, then the line

```text
This session cannot open files, so the contents of the directory's files are given here, each exactly as it stands, between the lines that name it; read nothing else.
```

and then each of the directory's files between a line `----- begin <name> -----` and a line `----- end <name> -----`. Build it from the files by a script, never by retyping them, so that each block is its file exactly.

Keep `-s read-only`. Under it the model's commands go through Codex's sandbox (`-s` selects "the sandbox policy to use when executing model-generated shell commands", `codex exec --help`), which cannot start here, so none runs. Two things in Codex's source at `rust-v0.166.0` bear on that. A command that a rule of Codex's exec policy allows outright runs outside the sandbox (`codex-rs/core/src/exec_policy.rs` lines 442-451), so check before the run that no rules file in Codex's configuration folders allows one (`$CODEX_HOME/rules`; `<dir>` holds none). And `codex exec` asks for no approval (`AskForApproval::Never`, `codex-rs/exec/src/lib.rs` lines 595-597), under which a failure is "immediately returned to the model, and never escalated to the user for approval" (`codex-rs/protocol/src/protocol.rs` lines 1165-1167), unless a configuration it still loads, such as one your machine manages, routes approvals to automatic review (`codex-rs/exec/src/lib.rs` lines 785-816). Do not reach for `-s danger-full-access` or `--dangerously-bypass-approvals-and-sandbox`, which the help offers for "environments that are externally sandboxed": under either, the model's commands run with whatever your own session may read, your repository and record included.

**That the whole prompt arrived.** The prompt goes on the command line, so it must fit the argument list with the environment (`getconf ARG_MAX`, 1048576 bytes on the machine observed), and Codex takes at most 1,048,576 characters in one input (`MAX_USER_INPUT_TEXT_CHARS`, `codex-rs/protocol/src/user_input.rs` line 10). Each refuses a longer input rather than cutting it: `execve(2)` fails with `E2BIG`, and `codex exec` sends the prompt in one `turn/start` request (`codex-rs/exec/src/lib.rs` lines 1236-1274), which the app server refuses with "Input exceeds the maximum length" before the turn starts (`codex-rs/app-server/src/request_processors/turn_processor.rs` lines 524-552). So record the prompt's size in bytes and in characters (`wc -c`, `wc -m`), and a log holding `turn.started` and `turn.completed` shows that Codex took the whole prompt. Nothing at 0.166.0 reports a later cut, such as a compaction of a context longer than the model's window (the log drops that kind of item, below): keep the prompt well inside that window, and treat it as an assumption that nothing else shortens it.

**The evidence to record**, beside the prompt and the reply: the probe's output; that no rules file allowed a command; the prompt's two sizes; `events.jsonl`, in which every item must be an `agent_message` or a `reasoning` item, since an item of any other kind means the session was not what this form assumes, so discard its reply and find out why; and the reply's part 3. Read them for what each shows:

- That the session ran no command rests on the probe and the rules check: each command Codex runs under its sandbox fails to start in this session, and no rule let one run outside it.
- The log alone does not show it. At 0.166.0 the log reports, of what the session does, only commands, file changes, MCP tool calls, sub-agent calls and web searches, and drops every other kind of item (`codex-rs/exec/src/event_processor_with_jsonl_output.rs` lines 143-325, `_ => None` at line 323), among them an image the model views by path and a compaction of the context. Nor did it list commands refused before they start: in the adopting project's refused sessions, whose replies say that each read was attempted and refused, it held nothing but agent messages.
- What the log adds is that it logged none of the kinds it reports: no web search, MCP call, file change or sub-agent.
- That the session changed nothing rests on no command having run, on `-s read-only`, whose permission text limits writes, and on `--ephemeral`, which keeps no session files.
- That the session viewed no image rests on its reply alone.

## The prompt for a record

Fill in the subject line, keep the rest as written, and add nothing about what you think the owner wants.

```text
You are formalizing what an owner wants from one deliverable, as a Lean 4 intent record. Work independently: another formalization exists, and you must neither look for it nor guess at it.

Read only the three files in this directory: owner-words.md (the owner's words, exactly as given), types.lean (the definitions of the types the subject is stated over) and Record.lean (the lean-intent library's intent record). Read nothing else, on this machine or online.

The subject is <its name> : <its Lean type>, or, where this line gives no type, a subject whose type you choose and state.

Reply with three parts.

1. A Lean file that imports LeanIntent.Record and declares one LeanIntent.IntentRecord for the subject:
   - a property for each thing the owner's words require of the subject, named so that the owner can read it;
   - a domain hypothesis for each fact about the world that those properties rely on;
   - the predicates the properties are written in, in vocab;
   - the shape that fits what the subject is, as Shape in Record.lean describes.

2. In plain words: each property and hypothesis; each point where the owner's words left you a choice, with the choice you made and why; and each requirement you inferred rather than read in the words.

3. Every file you read, by its path.

Formalize what the words require, as their owner would mean them, at full strength: no property weaker or stronger than the words support, and none they do not support.
```

## The prompt for cases

Use this where the subject's type or domain is itself what is in question, because a record can take that type or predicate as a parameter and so compare nothing.
Fill in the three lines in angle brackets from the owner's words and the input's format, in their terms and never in your record's, keep the rest as written, and add nothing about what you think the owner wants.
No number of cases is required: rbeauchamp/regula PR 524's second reading gave 76, and what counts is that they reach each distinction.

```text
You are reading what an owner wants from one deliverable, and you will answer with concrete cases and verdicts. Work independently: another reading exists, and you must neither look for it nor guess at it.

Read only the files in this directory: owner-words.md (the owner's words, exactly as given), input-format.md (what an input is, which says nothing of what the owner wants) and types.lean, where it is present (the input's Lean type). Read nothing else, on this machine or online.

The deliverable is <its name>.
An input is <what one input is>.
The verdict on an input is one of <the outcomes the owner's words name>, or "the words do not settle this".

Reply with three parts.

1. A numbered list of inputs, each with its verdict and the words it rests on:
   - write each input out in full, in its own format, with no free variable or placeholder and no reference to a predicate, so that a reader with only that case can tell what the input is;
   - give one verdict for each, resting on nothing left undefined: where you would say "it depends", write each alternative as an input of its own;
   - choose the inputs yourself, as many as it takes to reach each distinction you can find in the words: ordinary inputs, unusual inputs the words still cover, ordinary-looking inputs the words exclude, and for each distinction a pair of inputs that differ in that one respect and get different verdicts.

2. In plain words: each point where the owner's words left you a choice, with the choice you made and why; and each requirement you inferred rather than read in the words.

3. Every file you read, by its path.

Give no Lean record and no general rule in place of the cases. Judge what the words require, as their owner would mean them, at full strength: no verdict that the words do not support.
```
