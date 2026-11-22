# The blind formalization's inputs, prompts and results

## The directory

Make a new directory outside the repository and put in it only:

- `owner-words.md`: the owner's words, exactly as given, with nothing of yours added: those at the level step 1 started from, and, where the owner adopted a statement, that statement exactly as adopted, with nothing of the proposal's reasoning;
- `types.lean`: the source of the definitions of the types the subject is stated over, copied without the implementation or any other definition that is not a type;
- `Record.lean`: lean-intent's `LeanIntent/Record.lean`, from the commit the project pins.

Where the subject's type or domain is itself what is in question (step 3), the directory instead holds `owner-words.md`, `types.lean` where the input already has a Lean type, and `input-format.md`: the input's own format from that format's owner, such as the section of a tool's documentation that says what its configuration holds, with nothing that says what is wanted and nothing about your record.

Start the second model in a fresh session or context whose only material is that directory's contents: no earlier conversation, and nothing of the protected set (your record, your account, reasoning, implementation, notes, session transcripts or anything derived from them) in anything it can read (its workspace, memory, attached files or system prompt). Give it the prompt below that fits what you ask for, and save the prompt and its reply.
Use a model of another provider than the one that wrote your record, through a command line, a desktop app or an API, checking the interface's own help at the version in use for how to start it in that fresh context.
Whichever interface it is, take its reply as a blind reading only under [What makes a reading blind](#what-makes-a-reading-blind), which states the rule without naming a tool; [the Codex recipe below](#a-worked-recipe-for-codex) keeps one tool's flags, restriction and observations beside the rule as evidence.
The directory and the session stay outside the repository; what the project keeps of the result, and where, is set out in [the last section](#where-the-formalization-and-the-comparison-live).

## What makes a reading blind

Agreement between the two readings is evidence only if it is not explainable by the second reader having seen the first reading or anything derived from it.
What must stay out of the second reader's reach is **the protected set**, the set the project owns and can list: the author's record (the first formalization), the account, the reasoning behind it, the implementation, notes and session transcripts, and anything derived from them.

**Why the condition is stated over the protected set and not over every route.** Earlier versions stated a stronger property — that the second model could read nothing beyond its inputs — and, while they included a tool-free, stateless request and kept the record unpublished against web search, their local-tool path checked file reads alone or tried to list every route by which a byte could reach the model. Those routes belong to the interface's tool and to its provider, and they change with each release: an open-domain condition over every route cannot be established, and source-level evidence for one release expires with the next (`rbeauchamp/lean-intent#79`). The property the comparison needs concerns only whether the protected set can be reached.

**The three paths to the protected set.** Establish that each of the three paths by which the protected set can be reached is closed by evidence the project can produce, and say in your report how each was closed and what stays trusted:

1. **Files on the machine that runs the reader.** Either you build the whole request directly with no local tool, workspace or file access (for example, an API request carrying only the prompt and the directory's files), or the whole process of the interface's tool, every child included, runs under an operating-system restriction that refuses every file read except a closed list of paths, none of which holds, or is a directory above, any of the protected set; and before the run, with the run's own command, flags and restriction, you observed at the version in use that the restriction refuses a read of a canary file beside your record, both through a plain command and through the tool's own in-process file read, each read having first been observed to succeed without the restriction. Check whatever the interface still adds to the model's input by itself from the machine (instruction files, skills, plugins, local configuration or items triggered by mentions in the prompt): keep it outside the closed list so the restriction refuses it, or read it from the interface's own rendering or effective configuration and verify it holds none of the protected set, naming in your report what loaded and what was refused. Check each admitted path in the closed list yourself.
   Whether the operating-system restriction refuses a read made through a tool the session does not list is argued from the restriction covering the whole process and has not been observed for such a tool. If an interface reads files in-process outside its own command sandbox and runs inside a process sandbox that refuses a nested operating-system read restriction, this path is not closed there.
2. **Published copies.** Until the reading is done, none of the protected set is anywhere the reader or its provider could reach: a public repository, a private store that an account, app or configured server connected to the reader's session can read, or an earlier session of the second model's provider. Establish this from the project's own record of where each item was pushed, read from the repository itself, and from where any draft, note or transcript was sent or stored. Keep the record unpublished until the reading is done.
3. **Tools the provider runs.** Either the request you build declares no tools (hosted tools included) and no stored state (no conversation, stored response, uploaded file or memory), with provider documentation for that model and endpoint read for anything applied by default (turning off anything that can be disabled, and noting whether either stores or retrieves without a setting to turn that off) and the returned response reporting no tool call or retrieval; or the session, as it reports its own tools (made before the run and again at the end of the run's own session, with a positive control showing that a network or connected-app tool appears when enabled), has none that reaches the network, a connected app, or a configured server whose effective configuration is unknown or can reach the network or a connected app. Listing calls that contact ready servers and return empty lists do not establish that no server is configured when a reported tool (such as an MCP resource reader) can still address configured servers; wherever such a tool remains registered and the effective server configuration is unknown, path 3 is unestablished (while keeping path 2's requirement over every store a configured server, connected app or account can read).
   One assumption is trusted here, not shown, and your report names it as trusted: **a provider runs no tool that the session does not report**, and adds no stored state or retrieval beyond what the request or session declares. Whether a provider lets a model call a tool it was not shown is not established, and provider-side state or retrieval cannot be observed from outside the provider; only a model run on your own machine would remove them.

**What each kind of interface needs.** For any interface you use, build those same three items of evidence from that interface's own help at the version in use:

- **A direct API request** closes path 1 by construction (no local workspace or file tools), path 2 through the repository push record and send log, and path 3 through the exact request sent (empty tools, no stored state), the returned response and the provider's documentation read for defaults. Prefer this route where you can reach it: it closes tools by omitting them from the request rather than by observations tied to one version of a local tool.
- **A command-line tool** closes path 1 through the operating-system read restriction, both canary observations (with positive controls) and checking machine-loaded inputs and admitted paths; path 2 through the repository push record and send log (including any store readable by an account, app or configured server connected to the session); and path 3 through the session's own report of its tools (before and in the run, with positive control) showing no tool reaching the network, a connected app, or an unknown or external configured server (where a server-addressing tool remains registered and the effective server configuration is unknown, path 3 is unestablished, while path 2 still governs where protected copies reside). [The Codex recipe below](#a-worked-recipe-for-codex) keeps one tool's flags, restriction and observations beside this rule as evidence; for any other tool, build those three items of evidence from its own help at the version in use.
- **A desktop app** closes path 1 only if its whole process runs under such an operating-system read restriction with canary observations and checked workspace, memory and instruction inputs; path 2 through the push and send record; and path 3 only if the session's reported tools and account settings show no network or connected-app tool and no stored state. Where you cannot inspect or disable all settings and stored state, those paths cannot be closed there.

**A transcript, a tool log or the model's own list of files** may still be recorded, and each can discard a reading: anything in them outside the directory's files, an unexpected tool call or a log item that the recipe does not admit means the formalization is not blind, so discard it and start a fresh session. None of them establishes a reading: a session can read files or call tools that none of them records.

Where you cannot close files on the machine or tools the provider runs (or a transcript, log or list discards the reading), do not accept the reading: discard it and either use an interface that closes those paths or report step 3 as blocked, as step 3's item 2 says for a model that cannot be reached.

## When part of the protected set is already reachable

Step 3 has you keep the protected set unpublished until the reading is done, leaving the trusted side of path 3 with nothing of it to return. Sometimes part of the protected set is already reachable when the reading is due: for example, the implementation of a public project when an existing deliverable is changed, or a record pushed to a public repository, placed in a store a connected app or server can read, or given to a session of the second model's provider (for example to review a change).

A reading whose independence is weaker is **labelled, not refused**:

- Do not try to undo publication: deleting what was pushed does not show that no copy remains where a search or provider could reach it.
- Still close **path 1** (files on the machine) and **path 3** (tools the provider runs, so the session has no reported tool that could fetch what is public or stored), and keep every still-unpublished item of the protected set unpublished (**path 2**).
- Where the publication might also have entered the model's weights, check the date the item first became reachable against the model's documented training cutoff and record both with where you read the cutoff. A cutoff earlier than publication addresses training while leaving provider-side state, retrieval and unreported tools named as trusted where the provider saw the item; if the item became reachable earlier than the cutoff or no cutoff is documented, do not refuse the reading for that — keep it as a weaker reading (or use a model whose documented cutoff precedes publication if one is reachable).
- Report which part of the protected set was reachable, by which path (including training and documented cutoff dates where read), and state that the comparison's premise is weakened that far, as step 1 does where the record's source inherited from the code.

## Earlier readings under the old rule

Before the change that closed `rbeauchamp/lean-intent#79`, this reference already required keeping the record unpublished where web search could reach it and specified a tool-free, stateless request under condition (a) (without the provider-default check, response check or named trusted assumption); its local-tool recipe under condition (b), however, checked only file reads (path 1) and lacked evidence for all three paths — neither path 3 evidence of what tools and state the session held nor the full path 2 check over every protected item, private store, connected app or server and earlier provider session. An earlier reading where only file reads (or only part of the three paths) were checked is **unconfirmed** on the unchecked paths, not shown to be contaminated, since nothing shows that such a session used a path outside its condition. Credit the evidence each earlier reading actually retained: report it under this corrected rule — stating which of the three paths were closed, which were not checked, what remains trusted, and how far that leaves the comparison's premise unconfirmed — or take the reading again under this rule. The theorems that compare the two formalizations stand as proved either way; what is unconfirmed is only that the second was made without sight of the first.

## A worked recipe for Codex

This section is not the rule above; it is a recipe for one interface (`codex-cli`, observed at `0.166.0` on macOS `27.2` and `0.170.0` on macOS `27.2.1` with `gpt-6-astra`), kept beside the rule as evidence. Flags, tool lists and source-line citations hold only for the versions and model observed and expire at other releases: at any other version, read `codex exec --help`, `codex features list` and the session's tool report again to build the three items of evidence above.

### The Codex command

Keep the prompt, the reply and the event log in a second directory outside `<dir>`, so that the session's only material stays the directory's files.

```sh
codex exec -C <dir> --skip-git-repo-check \
  --ephemeral --ignore-user-config -s read-only \
  --disable memories --disable hooks --disable view_image \
  -c 'web_search="disabled"' --disable apps --disable plugins --disable image_generation \
  --disable shell_tool --disable goals --disable sleep_tool \
  -c agents.enabled=false -c tools.experimental_request_user_input.enabled=false \
  -m <model> -c model_reasoning_effort=<effort> \
  --json -o <outside>/reply.md \
  "$(cat <outside>/prompt.txt)" < /dev/null > <outside>/events.jsonl
```

Each flag was read from the help of `codex-cli 0.166.0` and again at `0.170.0` (`codex exec --help`, and `codex features list` for the feature names). Of the `-c` keys in the fourth to sixth lines, `agents.enabled` and `tools.experimental_request_user_input.enabled` were read from Codex's source at `rust-v0.170.0` (`codex-rs/core/src/config/mod.rs` lines 4111-4115 and 2803-2809), and `web_search` rests on its observed effect ([below](#what-the-session-can-call)). If your version differs, read them again, and where a flag has gone find its current equivalent rather than dropping it.
The tool settings are the means and never the evidence: a version, model or account may give the session a tool that none of them removes, so what decides is [the session's own report of its tools](#what-the-session-can-call).
Run it only in [the form below](#under-a-restriction-on-what-codex-can-read), under the restriction for path 1: Codex's own sandbox limits the commands the model runs, not the reads Codex makes itself, and where that sandbox starts, the model's commands run, and [the event log does not show everything they read](#what-the-event-log-shows).
The Acorn pilot of this method, then called spec-first, ran a session of this kind at `0.165.0` (rbeauchamp/acorn PR 188, `docs/spec-first-pilot.md`), and [the sessions below](#what-the-event-log-shows) ran the command as it then stood, without the tool settings of lines 4-6, at `0.166.0` from a session already sandboxed, some with `-s danger-full-access` in place of `-s read-only`, with short prompts of their own rather than a formalization's, and none under an operating-system read restriction. On 2026-11-18, at `0.170.0`, sessions ran the command as it stands here, again with short prompts of their own, under such a restriction ([below](#what-the-session-can-call)), leaving path 3 unestablished wherever the effective server configuration is unknown; no formalization was run with it.

| Part | What it does |
|---|---|
| `< /dev/null` | Closes the command's input; the Acorn pilot observed Codex otherwise waiting on stdin, and the help says piped stdin is appended to the prompt. |
| `--ephemeral` | Persists no session files. |
| `-C`, `--skip-git-repo-check` | Make `<dir>` the working root and allow it not to be a Git repository. |
| `--ignore-user-config` | Does not load `$CODEX_HOME/config.toml` or a selected profile, so what they configure stays out; auth still uses `CODEX_HOME`. That includes the configured model and effort, so name them with `-m` and `-c`. It drops that one layer and no other: servers and settings from other configuration layers stay in. |
| `-s read-only` | Runs the model's commands in the read-only sandbox. Its permission text limits writes and network, not which files may be read, so treat reads as unconfined: path 1 rests on the operating-system restriction below, not on this flag. |
| `--disable memories`, `--disable hooks`, `--disable view_image` | Turn those three features off (`-c features.<name>=false`). The third removes the tool that shows the model an image file by its path, which Codex registers only while that feature is on (`codex-rs/core/src/tools/spec_plan.rs` line 1440 at `rust-v0.166.0`, line 1491 at `rust-v0.170.0`) and whose use the event log does not list (below). |
| `-c 'web_search="disabled"'`, `--disable apps`, `--disable plugins`, `--disable image_generation` | Remove the web, connected-app, plugin and image tools (though `list_mcp_resources`, `list_mcp_resource_templates` and `read_mcp_resource` stay registered whenever code-mode tools are active, [below](#what-the-session-can-call)). [The table below](#what-the-session-can-call) gives what each was observed to remove at `0.170.0`. |
| `--disable shell_tool`, `--disable goals`, `--disable sleep_tool`, `-c agents.enabled=false`, `-c tools.experimental_request_user_input.enabled=false` | Remove tools the reading does not need, leaving fewer to account for: shell commands, goals, sleep, sub-agents and `request_user_input`. The same table gives each. |
| `--json` | Prints the events to stdout. With `--ephemeral` no session file is kept, so this stream is the interface's only record of the session, and it does not list everything the session reads (below), so it can discard a reading but never establish one. |
| `-o` | Writes the final message to a file. |

These options do not switch off Codex's global instruction file (`$CODEX_HOME/AGENTS.md`): `--ignore-user-config` covers `config.toml` only, and without a restriction the file still loads.
Under the restriction below it loads only where the closed list of paths admits it. At `0.170.0`, with `$CODEX_HOME/AGENTS.md` and installed skills directories outside that list, neither loads: each session's event log held one `error` item, `Failed to read global AGENTS.md instructions from <path>: Operation not permitted (os error 1)`, and the session's standard error reported of each skills directory that it could not be walked, for the same reason. Keep both outside the closed list, and name in your report that neither loaded, citing that log item and those lines.
`codex debug prompt-input --disable memories --disable hooks --disable view_image`, run from `<dir>` without the restriction, shows what reaches the model without calling one: at `0.166.0` it showed that file and the list of installed skills, though it does not take `--ignore-user-config` and so renders with the user's configuration; for the same reason it cannot run inside the restriction, where at `0.170.0` it exited 1 with `Failed to read config file`. Because that unrestricted rendering includes `$CODEX_HOME/config.toml`, `$CODEX_HOME/AGENTS.md` and installed skills that the restricted session ignores or refuses, verify only the machine-loaded inputs and paths that the restricted session actually loads or admits rather than checking un-admitted `$CODEX_HOME` files for the protected set. It is not a list of the session's tools: it renders direct tools and the code tool's description, which can omit tools nested under the code tool (at `0.170.0`, without the tool settings above, the rendering named no `web__run`, which a live session reported).

### What the event log shows

`events.jsonl` cannot confirm what a session read, because at `0.166.0` and `0.170.0` it does not list every read.
Its mapping keeps agent messages, reasoning, command executions, file changes, MCP tool calls, some sub-agent calls and web searches, and drops every other kind of item (`codex-rs/exec/src/event_processor_with_jsonl_output.rs` lines 143-325, `_ => None` at line 323 at `rust-v0.166.0`; lines 144-326 and line 324 at `rust-v0.170.0`), among them `ImageView`, which carries the path of a file the model viewed (`codex-rs/app-server-protocol/src/protocol/v2/item.rs` line 473); at `rust-v0.170.0` a warning or notice from Codex is written as an `error` item (lines 412-422 and 430-510).
The model reaches its tools through a code-mode `exec` tool, which runs JavaScript that calls the others: Codex takes the tool mode from the model's catalogue entry first (`codex-rs/core/src/tools/mod.rs` lines 66-67), and the entry Codex had cached for `gpt-6-astra` gave `code_mode_only`.
On 2026-11-05, on macOS 27.2 at `codex-cli 0.166.0`, sessions of `gpt-6-astra` at low effort were run with the command as it then stood (without the tool settings of lines 4-6, and without `--disable view_image` except where said), in a scratch directory holding only a text file that carried a random token and a small image, of one colour at first and of two later.
They ran from an agent session that was already sandboxed, so the four sessions below in which a read was to succeed used `-s danger-full-access`, for this observation only: under it Codex applies no sandbox of its own, and the commands ran under that session's sandbox.

- Asked to run `cat` on the text file, a session replied with the token, and the log listed the command, `/bin/zsh -lc 'cat note.txt'`, with exit code 0: a command that runs inside the code-mode tool is listed.
- Asked to view the image, a session named its colour, and the log held agent messages and nothing else; so it did with the flags of the form as it then stood, where a session named both colours of the second image.
- Asked to have a sub-agent read the text file, a session replied with the token, and the log listed a wait on a sub-agent and no command.
- Asked to start a shell and type `cat` on the text file into it through `write_stdin`, a session replied with the token, and the log listed the shell, `/bin/zsh -lc sh`, as started, and nothing typed into it.

Codex also reads files itself, outside its command sandbox, so that sandbox does not bound what a session reads even where no command runs. At `rust-v0.166.0` its local filesystem routes a read through the sandbox only when the sandbox context asks for that, and otherwise reads unsandboxed (`codex-rs/exec-server/src/local_file_system.rs` lines 91-105); and `apply_patch` reads each file its patch names while preparing the patch, before the file-change event is emitted (`codex-rs/core/src/tools/handlers/apply_patch.rs` lines 464-590, `emitter.begin` at line 590; the read itself in `codex-rs/apply-patch/src/file_update.rs` lines 32-43), so its error can tell the model whether a file could be read and whether lines the patch quotes are in it, with nothing in the log. And a session with the flags the form then had viewed an image while Codex's sandbox could not start (the second observation above).

So a session can open files that the log never shows, through a command that runs or through a read Codex makes itself, and a confirmation read from the log would pass such a session as blind.
Nor does the log show every tool call: at `0.170.0`, sessions that ran the code tool twice ([below](#what-the-session-can-call)) logged nothing for the code tool itself, and logged the two calls it made to tools that list a server's resources as `mcp_tool_call` items.
Without `--ephemeral`, Codex keeps a session file, but keeping it breaks step 3's requirement that the session keep nothing behind, and no positive control has shown that it lists each kind of read.
So neither a record Codex keeps nor its command sandbox establishes path 1: run Codex under the restriction below, or use an interface that closes all three paths.

### What the session can call

At `rust-v0.170.0`, a tool is declared to the model either directly or nested under the code tool `functions.exec`. The code tool's runtime builds its `tools` object and `ALL_TOOLS` from the same list (`codex-rs/code-mode-runtime/src/runtime/globals.rs` lines 26-27, 65-78 and 80-109), whereas `codex debug prompt-input` may omit nested tools (`codex-rs/code-mode-protocol/src/description.rs` lines 17-18). A web search the provider runs is declared directly and never nested (`codex-rs/core/src/tools/spec_plan.rs` lines 686, 724-754 and 1031-1033), so for directly declared tools there is no listing except the model's own report.

**The tool report** asks the session for both. Sent by itself, it follows the line `Report your tools, in the two parts A and B below, and reply with nothing else.` and a blank line; [the form below](#under-a-restriction-on-what-codex-can-read) also appends it to the run's own prompt.

```text
A. Every tool declared to you directly, that is, every tool you can call without going through another tool, hosted tools such as a web search included: one per line, as its namespace, a dot and its name.

B. Call your code tool once with exactly this JavaScript, and give its output exactly as it was returned, changing nothing:

text(JSON.stringify(ALL_TOOLS.map(t => t.name).sort()))

If you have no code tool, write "no code tool" as part B.
```

Do not call `tools.list_mcp_resources({})` and `tools.list_mcp_resource_templates({})` (asked as a third part C in the 2026-11-18 probe below) during a blind formalization run: at `0.170.0` those listing calls contact ready configured servers, a server returning empty lists produces the expected empty output, and `read_mcp_resource` can still address that server.

**Observed tool report at `0.170.0`.** On 2026-11-18, on macOS 27.2.1 at `codex-cli 0.170.0`, a session of `gpt-6-astra` at low effort started from an unsandboxed shell with the command above and `-c 'approval_policy="never"'`, under the restriction below (asked for parts A and B above and a third part C calling `tools.list_mcp_resources({})` and `tools.list_mcp_resource_templates({})`), reported: in part A, `functions.exec` and `functions.wait`; in part B, `["apply_patch","clock__curr_time","list_mcp_resource_templates","list_mcp_resources","read_mcp_resource"]`; and in part C, `["{\"resources\":[]}","{\"resourceTemplates\":[]}"]`. Its event log held four `mcp_tool_call` items (start and completion for `list_mcp_resources` and `list_mcp_resource_templates` of server `codex`) and nothing for the code tool itself. Of those seven tools, four reach neither the open web nor a connected app, while the three MCP resource tools contact or address whatever servers the session has configured, so they leave path 3 unestablished wherever the effective server configuration is unknown:

| Tool | What it can return |
|---|---|
| `functions.exec` | What the nested tools below return; by its own description, raw JavaScript with no Node, file system, network or console, holding values only across `exec` calls in the same session (read, not tested). |
| `functions.wait` | By its description, new output or completion of a running code-tool call. |
| `apply_patch` | Whether a file could be read and whether lines are in it: bounded by path 1's restriction (canary observation 3). |
| `clock__curr_time` | By its description, the current time in UTC. |
| `list_mcp_resources`, `list_mcp_resource_templates`, `read_mcp_resource` | What the session's configured servers offer. At `rust-v0.170.0` Codex keeps these three registered whenever code-mode tools are active (`spec_plan.rs` lines 1323-1343). `list_mcp_resources` and `list_mcp_resource_templates` contact ready servers when called (`binding_clients.rs` lines 89-186) and return empty even when a server is configured (the `probe_server` observation below), so empty lists from them cannot distinguish a network-connected or connected-app server returning empty lists from no server, while `read_mcp_resource` can still address that server; they can discard a session if a resource appears and never establish path 3. |

**What each setting removed at `0.170.0`.** That same day, with the same version and model (from an already-sandboxed session, with the tool report prompt), removing one setting at a time from the command showed:

| Setting left out | What the report held beyond those seven tools |
|---|---|
| `-c 'web_search="disabled"'` | `web__run`, nested |
| `--disable apps` | 340 nested tools named `mcp__codex_apps__…` |
| `--disable plugins` | 26 nested tools (`mcp__codex_security__…`, `mcp__data__…`) |
| `--disable image_generation` | `image_gen__imagegen`, nested |
| `--disable shell_tool` | `exec_command`, `write_stdin`, nested |
| `--disable goals` | `create_goal`, `get_goal`, `update_goal`, nested |
| `--disable sleep_tool` | `clock.sleep`, direct |
| `-c agents.enabled=false` | six direct tools under `collaboration` (`spawn_agent` among them) |
| `-c tools.experimental_request_user_input.enabled=false` | `functions.request_user_input`, `functions.request_user_input_async`, direct |

With none of the nine (the earlier form), a session under the restriction reported the two direct tools plus nine more, and 350 nested tools (`web__run`, `image_gen__imagegen`, `exec_command`, `write_stdin`, `request_plugin_install` and 340 connected-app tools beside the five above). Earlier prose-only questions at `0.170.0` without the `ALL_TOOLS` snippet also failed to mention the three resource tools that `ALL_TOOLS` reports.

**Observations for path 3 and configured servers.** Before the run, with the command, flags and restriction:

1. **Tool report:** Run the command with the tool report (parts A and B) alone. No tool reaching the open web, a connected app or an unexpected capability may appear (at `0.170.0`, parts A and B equaled the seven tools above). Because `list_mcp_resources`, `list_mcp_resource_templates` and `read_mcp_resource` stay registered in part B, this check alone does not accept path 3 wherever the effective server configuration is unknown.
2. **Positive control:** Run it again with the tool report alone, omitting `-c 'web_search="disabled"'` and `--disable sleep_tool`. The report must show both a direct tool (`clock.sleep` in A) and a nested web tool (`web__run` in B) when enabled.
3. **In the run:** Append the tool report (parts A and B) to the formalization prompt and verify that the run's end-of-reply tool report still names no web, connected-app or unexpected tool beyond those; otherwise discard the reading. Where `list_mcp_resources`, `list_mcp_resource_templates` and `read_mcp_resource` stay in part B and the effective server configuration is unknown, path 3 remains unestablished.
4. **Local feature listing and why `codex mcp list --json` is omitted:** Because `read_mcp_resource` remains registered at `0.170.0` and resource-listing calls contacted ready servers while still returning empty even with `-c 'mcp_servers.probe_server.command="/usr/bin/true"'`, local feature settings can be checked with `codex features list` (showing disabled features `false` and `agent_message_board` / `agent_message_board_mcp` `false`, with positive control; `codex-rs/cli/src/cloud_config.rs` lines 17-33 and 73-79). Omit `codex mcp list --json` from preflight and recorded-evidence checks: at `rust-v0.170.0` it serializes literal configured `http_headers`, `env`, `args`, and `url` verbatim into the transcript, and local listings do not establish cloud-managed server configuration layers under the credentials `codex exec` uses (finding R2 of the earlier draft of `rbeauchamp/lean-intent#79`; source citations expire with the next release). Keep the **path 2** conclusion: any configured server, connected app or account that could read a copy of the protected set is closed under path 2 by keeping the protected set out of every store it can read (and labelling any already-reachable copy as a weaker reading). For **path 3**, because `read_mcp_resource` stays registered and neither resource-listing calls nor local listings verify the full effective server configuration, report path 3 as **unestablished** wherever the effective server configuration is unknown.

### Under a restriction on what Codex can read

Path 1 asks that the whole Codex process, every child included, run under an operating-system restriction that refuses every file read except a closed list of paths, none of which holds, or is a directory above, any of the protected set. On macOS one way to build it is to start `codex` under `sandbox-exec` with a profile that denies `file-read*` and then allows the closed list. On 2026-11-18, on macOS 27.2.1 at `codex-cli 0.170.0`, one such list sufficed for the sessions above: system locations (`/System`, `/usr/lib`, `/usr/share`, `/usr/bin`, `/bin`, `/sbin`, `/private/etc`, `/private/var/db/dyld`, `/private/var/db/timezone`, `/dev`, `/Library/Keychains` and `/Library/Preferences/SystemConfiguration`), the directory of the Codex release, three single files of `$CODEX_HOME` (`auth.json`, `installation_id` and `models_cache.json`), `<dir>` and the output directory, with ancestor directories answering metadata requests only, plus denying connections to Unix sockets (apart from the system's name resolver) and loopback addresses. Another machine or version may need another list, and these observations cannot judge paths outside the canary's directory (`$CODEX_HOME` and ancestor `.codex/config.toml` files included): verify each admitted path holds none of the protected set and no `.codex/config.toml` above `<dir>`, and name every admitted path in your report.

Codex runs the model's commands under its own sandbox, which on macOS it applies with `sandbox-exec`, and a process already inside a macOS sandbox could not apply a second one wherever this was tried: on 2026-11-05 (`0.166.0` on macOS 27.2) and 2026-11-18 (`0.170.0` on macOS 27.2.1), `/usr/bin/sandbox-exec -p '(version 1)(allow default)' /usr/bin/true` and `codex sandbox -- /usr/bin/true` both exited 71 with `sandbox_apply: Operation not permitted`, while `apply_patch` still read files unsandboxed (`0.170.0`).
So a Codex session started from a session that is already sandboxed cannot close path 1: use a direct tool-free request or an unsandboxed host under the restriction, or report step 3 as blocked (step 3, item 2).

Tell which case you are in before the run, from the session that will start Codex, with `codex sandbox -- /usr/bin/true`, and keep its output. Exit status 71 with `sandbox_apply: Operation not permitted`: your session is already sandboxed, so path 1 cannot be closed here. Exit status 0: build the restriction, and probe inside it with `/usr/bin/sandbox-exec -p '(version 1)(allow default)' /usr/bin/true`, which must exit 71 the same way (showing no second sandbox starts inside the restriction, so Codex's own cannot). Do not use `codex sandbox` for the probe inside the restriction: that subcommand reads `config.toml`, which the closed list keeps out, and at `0.170.0` it exited 1 there with `Failed to read config file` before reaching the sandbox (with `config.toml` admitted for the probe alone, it exited 71). Anything else from either probe: find out why before going on.

**The canary.** Before the run, with the run's own command, flags and restriction, observe at the version in use that the restriction refuses a read beside your record, both ways:

1. Write a file holding a random token in the directory that holds your record, outside version control: untracked, and never committed.
2. Read it through a plain command, `cat <canary>`: without the restriction it must print the token, and under the restriction it must be refused.
3. Read it through Codex's own in-process read: run the command of the form with a prompt asking the model to call `apply_patch` with an update to the canary, by its absolute path, whose patch quotes a line the canary does not hold, and to reply with the tool's error exactly. Without the restriction the error must be `Failed to find expected lines`, showing Codex read the file (`codex-rs/apply-patch/src/file_update.rs` line 156 at `rust-v0.166.0`), and under the restriction it must be `Failed to read file to update` (line 38; observed at `0.170.0` ending `: Operation not permitted (os error 1)`).
4. Delete the canary.

Each read without the restriction is the positive control: a read that does not succeed there shows nothing when it fails under the restriction. If any observation differs, path 1 is not closed: do not run the form under it.

**The form.** Run the command above under the restriction, with `-c 'approval_policy="never"'` added before the prompt argument, and otherwise as it stands (`-s read-only` and each tool setting included); besides that flag, change only the prompt: after the prompt that fits, unchanged, put a blank line, then the line

```text
This session cannot open files, so the contents of the directory's files are given here, each exactly as it stands, between the lines that name it; read nothing else.
```

then each of the directory's files between `----- begin <name> -----` and `----- end <name> -----` (built by a script, never retyped), then a blank line, the line `After the parts asked for above, report your tools, in two further parts.`, a blank line and [the tool report](#what-the-session-can-call). The pre-run canary and tool-report observations use this same command and flag with their own prompts.

Because Codex reads `$name`, `[$name](path)` and `[@name](plugin://...)` mentions in the prompt and can inject matching skills, apps or plugins without a sandbox (`rust-v0.166.0`: `codex-rs/skills/src/mentions.rs` lines 84-148, `codex-rs/ext/skills/src/host_outcome.rs` line 124, `codex-rs/core/src/plugins/mentions.rs` lines 99-101), confirm before the run that each admitted path (including the three admitted files under `$CODEX_HOME`: `auth.json`, `installation_id` and `models_cache.json`) and any skill, plugin, app or machine-loaded input still admitted or loaded by the restricted session carries none of the protected set, and record that check; do not require un-admitted paths under `$CODEX_HOME` (such as protected transcripts outside the closed list) to be free of protected material. (Keeping skills directories outside the closed list and `apps`/`plugins` disabled blocks loading at `0.170.0`; check what your closed list admits.)

Keep `-s read-only`, check that no rules file under `$CODEX_HOME/rules` allows a command outside the sandbox (noting that system/managed rule layers are not shown by inspecting `$CODEX_HOME/rules` alone), and verify outside the restriction that `codex debug prompt-input --disable memories --disable hooks --disable view_image -c 'approval_policy="never"' "probe"` outputs `Approval policy is currently never.` and does not output `view_image`; if it fails either, do not run the form, and never use `-s danger-full-access` or `--dangerously-bypass-approvals-and-sandbox`.

**That the whole prompt arrived.** Record the prompt's size in bytes (`wc -c`) and characters (`wc -m`), confirm it fits `getconf ARG_MAX` and Codex's input limit (`1,048,576` characters at `rust-v0.166.0`), keep it well inside the model's context window, and confirm `events.jsonl` holds `turn.started` and `turn.completed`.

**The evidence to record** beside the prompt and reply: the outer `codex sandbox` probe output and the inner `sandbox-exec` probe output; the restriction with every admitted path and your check that none holds the protected set or an ancestor `.codex/config.toml`; both canary observations with positive controls and canary deletion; the two pre-run tool reports (main + positive control) with event logs, and the configuration checks (`codex features list`, `$CODEX_HOME/rules`, `codex debug prompt-input` approval/image lines, and the admitted-path and machine-loaded mention check including the three admitted `$CODEX_HOME` files; omit `codex mcp list --json`); prompt byte and character counts; `events.jsonl`; and the reply's part 3 and end-of-reply tool report. In `events.jsonl` at `0.170.0` without resource-listing calls, every item must be an `agent_message`, a `reasoning` item, or the one `error` item saying `AGENTS.md` could not be read under the restriction; any other item (such as a `web_search`, command execution or another tool call, including any `mcp_tool_call`) discards the reading (the 2026-11-18 probe sessions that ran resource-listing calls logged four `mcp_tool_call` items on `codex` for those calls).

Read that evidence for what each part shows and does not show:

- **Path 1 (Files on the machine):** The OS restriction, both canary observations (with positive controls) and your check of each admitted path establish that local files outside the closed list could not be read through commands or `apply_patch`; that the restriction blocks a read by an unlisted tool is argued from covering the whole process and not observed for such a tool. That `$CODEX_HOME/AGENTS.md` and skills did not load rests on the `error` item and stderr lines at `0.170.0`.
- **Path 3 (Tools the provider runs):** The pre-run and end-of-reply tool reports (parts A and B), with the positive control showing `clock.sleep` and `web__run` when enabled, show that no other declared tool reaches the open web or a connected app. However, `list_mcp_resources`, `list_mcp_resource_templates` and `read_mcp_resource` remain registered at `0.170.0`, and neither resource-listing calls (which contact ready servers and return empty when a server offers no resources) nor local configuration listings establish every effective server configuration layer; **wherever the effective server configuration is unknown, path 3 is unestablished** (while path 2 keeps the protected set out of every store a configured server, connected app or account could read). Under the rule above, do not accept such a session as closing path 3 unless the effective server configuration is established to hold no network- or connected-app-reaching server — use a direct tool-free request or another interface that closes all three paths, or report step 3 as blocked (step 3, item 2). That the provider runs no tool the session does not report, and adds no unreported state or retrieval, is named as trusted and not shown.
- **Commands, writes and images:** That the session ran no command rests on the tool reports (neither `shell_tool` nor `collaboration` tools), the inner `sandbox-exec` probe, `$CODEX_HOME/rules` and `approval_policy="never"`; that it changed nothing rests on no command having run, `-s read-only` and `--ephemeral`; and that it viewed no image rests on `--disable view_image`, the tool reports and `codex debug prompt-input` rendering no `view_image`.
- **Event log limit:** `events.jsonl` drops `ImageView`, compaction and several tool interactions, and never establishes blindness on its own; it can only discard a reading.

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
   - the shape that fits what the subject is, a constructor of Shape in Record.lean: function for a function whose result depends only on its arguments; for a subject that carries state from one call to the next, the step constructor its type has (step, stepOn, action or actionOn: from a state, with or without an input, to the next state, with or without an output); bundle for a description made of functions that carries no state from one use to the next, such as a world's rules, with each of its functions named as a Member (first and rest, at least one function) and the plain values that are the rest of the subject (data); and value only for a value with no behaviour.

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

## Where the formalization and the comparison live

The step exists so that a machine checks the comparison between the second model's formalization and your record, and a comparison that the project's proof check never builds is checked by nothing, however finished it reads: in an adopting project, the second model's record and the theorems comparing it with the intent record sat in an uncommitted scratch file that the proof check never ran, and the step read as done. By the proof check this section means the check the project runs on every change to establish its proofs, such as the build its validation gate or CI runs. So what the step proves is committed in the project, in modules that check builds, and is checked on every run of it:

- **The second model's formalization**, in a module of its own beside your record: its record, elaborated, or, where it gave cases, each case written in your input's type. The module imports only what defines the types the subject is stated over, as your record's module does (step 1), and lean-intent's `LeanIntent.Record` where it holds a record; it never imports your record, so nothing of yours can enter it. Correct only what Lean refuses to elaborate, without changing the meaning, and note each correction in a comment beside it, with what the reply had. Where it holds a record, declare that record as a record only, never as a deliverable: lean-intent's confirmation check asks about every deliverable it finds as one the owner must confirm (`docs/confirmation.md`, under what is trusted).
- **Every theorem comparing it with your record**, in a module of its own that imports both: each direction proved (`∀ w, mine.Meets w → theirs.Meets w`), each subject exhibited as meeting one record and failing the other, and, where it gave cases, your record's verdict on each case. Prove each with no `sorry`, audited as the project audits axioms, as step 2 asks of the obligations. A direction you can neither prove nor refute stays a difference stated in plain words and labelled unproved, never a theorem left with `sorry`.

Committing a module does not make the check build it. A check that builds declared targets builds only the modules those targets reach: in Lake, each built-in facet of a library that compiles its modules, `leanArts` and `elabArts` among them, builds the modules its `globs` name, which default to one for each of its `roots`, and, recursively, every module of the workspace they import, its `roots` defaulting to the library's own name, and `lake build` with no argument builds the package's default targets and nothing else (Lake's README, `Lake/Config/LeanLibConfig.lean`, `Lake/Build/Library.lean` and `resolveDefaultPackageTarget` in `Lake/CLI/Build.lean`, at Lean v4.36.0). So a module under the library's directory that no root imports and no glob names is not built. Reach every such module from a target whose selected facets compile it, following the project's own rules for where its files go: for example, import the comparison module, which imports the formalization's, from a root of a library of which the check builds such a facet, or name each module in that library's `globs`.

Then confirm that the check builds them, once every such module is committed and `git status` shows none of them untracked or changed, since a glob also finds a file that is not committed. lean-intent's required-theorems check makes this confirmation ([its document](../../../docs/required-theorems.md)): list each comparison theorem by its name in a value of `LeanIntent.Required` for the deliverable, in a module the check builds, beside the other theorems the procedure asks for (the skill's step 4, item 4), and run it with the confirmation check, given the module names the build lists. It refuses each listed theorem whose module, as Lean's environment records it, is not among them, naming the theorem and the module, and each value of `LeanIntent.Required` declared in such a module, wherever a module the gate imports reaches it, and its report lists each theorem with its module. Those names come from Lake: for each Lean library of which the check builds a built-in facet that compiles its modules (`leanArts`, `elabArts`, `irArts`, `static`, `static.export` or `shared`, whichever it is), `lake query --json @/<library>:modules` prints the modules that facet builds, those its `globs` name and, recursively, the modules of the same library they import, and the check's reader takes that output as it is printed (`LeanIntent.Required.Read.queryModules`). Which libraries those are follows from the command the project runs on every change: a bare `lake build` builds the package's default targets, and an unqualified library target selects its `default` facet, which builds the library's `defaultFacets`, normally `#[LeanLib.leanArtsFacet]`, while an empty array builds nothing, and a library whose `defaultFacets` names another of those facets, such as `elabArts`, is built as much as one that names `leanArts`, so its list is given too; the document gives the Lake source for each at Lean v4.36.0. A theorem, or a value naming one, in a module that appears in no such library's list is refused, even where a module the check builds imports it from another library: move it into a library of which the check builds such a facet, or name it in that library's `globs`. A proof check that is not a Lake build of named targets gives the check the list of files it compiles from its own definition; say in the report how you read it. Lean stops reading a file at `#exit` and reports only a warning, so a module the check builds checks nothing written after one: keep no `#exit` in these modules. Building a module by name, such as `lake build <Module>`, shows only that the module builds, not that the check builds it. Keep the check's command and the required-theorems check's report for the report.

The step is not done until every such module is committed and the required-theorems check finds nothing. A later change that makes any of them fail the check, such as a revision of your record, is a failing proof of the project like any other: prove it again, or, where the revision changed what holds, state the difference it now shows and settle it as step 3 says of each difference; never delete the module or take it out of what the check builds to make the check pass.

What may stay private to the project's agents, outside the repository, is the sessions themselves: each prompt you sent, the reply as the model gave it, each session's logs, such as Codex's event log, and the other evidence this reference has you record. The report draws on them; the check needs none of them, since the modules carry the formalization, each correction made to it and the comparison.
