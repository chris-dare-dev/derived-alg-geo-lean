#!/usr/bin/env python3
r"""Refuse whole-library Lean builds on the developer's machine.

Lean builds for this repository belong on a runner. In this repository
`ci.yml` runs every event on `ubuntu-latest`; the owner's self-hosted runners
serve a private mirror instead (`docs/ci/owner-lane.md`). Since 2026-09-19
`push` fires on `main` alone, so the way to get a verdict on a branch is to
OPEN THE PULL REQUEST -- or to dispatch `ci.yml` on it by hand -- not to run
`lake` locally.

## What is refused, and what is not

Refused:

  * `lake build` with no target -- the whole library;
  * `lake build DerivedAlgGeo` / `lake build DerivedAlgGeoSweep` -- naming an
    all-library umbrella is the same whole-library build, because
    `lakefile.toml` sets `defaultTargets = ["DerivedAlgGeo"]`. Until #837 this
    passed, and on 2026-08-27 it ran for over an hour in a worktree that DID
    have the hook;
  * `scripts/gates.sh`, in any mode, because its `build` gate is that same
    whole-library build. RUNNING it, that is -- see READERS below;
  * `lake build <Target>` without `LEAN_NUM_THREADS`, or with it above
    `MAX_LOCAL_THREADS` -- see "Width, not just size" below;
  * `lake build <Target>` run through a `lake` that lives inside a self-hosted
    runner's working directory -- see "Whose lake" below.

Allowed, deliberately:

  * `scripts/precheck.sh` -- the subset of `gates.sh` that needs no Lean build
    at all, plus a targeted build of the modules the branch changed. It exists
    because refusing `gates.sh` without offering anything in its place left
    every agent skill with no local pre-flight whatsoever;
  * `lake build <Target>` for any target below an umbrella, including the three
    audits and `DerivedAlgGeo.Development` (which `gates.sh` and `ci.yml` both
    build by name), as long as it declares its concurrency;
  * `lake env lean <file>` -- the seconds-long probe that interactive proof work
    depends on. Routing those through CI would make each attempt a ~12 minute
    round trip and stop anyone from writing a proof at all;
  * `lake exe runLinter`, `lake exe lint-style`, and the python checkers;
  * READING `scripts/gates.sh` -- `cat`, `grep`, `git ls-tree`, `diff`. The cost
    this gate exists to refuse is running the file, not looking at it, and
    CONTRIBUTING.md tells contributors to read it to know what CI will check.

The distinction is cost, not principle. A targeted build on a warm cache is
seconds; the whole library from cold is hours, and on 2026-08-27 an agent spent
three of them rebuilding a cache that a machine-wide cleanup had deleted --
work a runner would have done off the developer's machine entirely.

## Width, not just size

Refusing big builds is only half of a resource rule. A permitted `lake build
DerivedAlgGeo.Foo` still takes one `lean` process per core unless
`LEAN_NUM_THREADS` says otherwise, and on this 16-core host, shared by dozens of
agent worktrees and four self-hosted runners, that is how the machine runs out
of COMMIT rather than CPU. See `MAX_LOCAL_THREADS` for what that cost on
2026-09-15.

So a targeted build must declare its concurrency, and the ceiling is enforced
rather than documented. `DAG_ALLOW_LOCAL_BUILD=1` overrides this rule too,
because it overrides the whole gate -- but it is the wrong tool here: the right
answer to "I need more threads" is a smaller number, not a bypass.

## Whose lake

Every rule above is about what a build COSTS. This one is about which `lake`
runs it.

ON WINDOWS THIS WAS AUTOMATIC, which is why the rule exists. Each of the four
runners kept an elan under `C:\actions-runner\<runner>\.elan`, and those `bin`
directories sat on the developer's own PATH, AHEAD of `~/.elan/bin`, because
`lean-action` invokes `elan-init` with no `--no-modify-path` and
`run-runner.cmd` pointed HOME at the runner directory -- so every CI job
re-persisted its own shim directory into the user environment, and removing
the entries did not hold. A plain `lake` in an agent shell therefore executed
a RUNNER's `lake.exe`; Windows will not replace a running image, so the next
job on that runner could not relink its shims and died about a second in with

    error: could not create link from 'elan.exe' to 'lake.exe'

On 2026-09-16 that held `main` red across three consecutive runs (bc973621,
6217d770, b9e18832) behind ONE local build that broke none of the other rules
here: named target, `LEAN_NUM_THREADS=2`, this gate green.

THE OWNER RETIRED WINDOWS ON 2026-09-21 (#1443), and both halves of that
mechanism went with it. The four Ubuntu runners under
`~/.local/share/github-runners/<runner>/` each own their HOME, `.elan`, `_work`
and caches, and their services run a minimal PATH that never reaches the
developer's shell, so no runner shim lands on your PATH by itself; and POSIX
lets a running image be unlinked and replaced, so there is no relink failure
left to cause. A bare `lake` here resolves to your own elan, or to nothing.

WHAT REMAINS is narrower, and is still worth refusing: naming a runner's shim
EXPLICITLY, by path. `docs/ci/ubuntu-runners.md` makes each runner's tree its
own state -- "no writable cache or package symlinks between runners or into
developer checkouts" -- and a build driven through one of those shims writes
into that runner's `.elan` and competes for its cgroup budget while a job may
be using it. So the check is kept and matched against the current layout as
well as the historical one, with a smaller claim behind it: state isolation
now, not image locking.

What this does NOT cost is correctness, and the distinction matters because the
two have very different blast radii. On 2026-09-16 the same declaration sweep
was run twice on this host, once through runner-3's shim and once through
`~/.elan/bin/lake`: the outputs were byte-identical (14589 rows, `diff -q`
clean) and audit-completeness reported the same numbers both ways. These shims
are all the same elan, and they resolve the same toolchain content; what differs
is whose tree the executing file lives in. So a result already produced through
a runner's shim does not need re-running. This gate exists to stop the
CONTENTION -- one process holding a file another process must relink -- not to
cast doubt on a build that has already finished.

## What this gate does NOT say

It does not say that CI is a superset of `gates.sh`. It is not, and the text
here used to claim otherwise ("CI runs every gate in it, and more"). Four gates
in `scripts/gates.sh` have no counterpart in any workflow: `workflows`,
`local-build`, `mathlib-style`, and `single-instantiation`. The
first three are local by construction -- they test hooks, or a pre-push linter
that cannot run after the file reaches GitHub. `single-instantiation` was not,
and the cost of the false claim is on the record: it ran nowhere for agents,
and 24 names drifted past its baseline unseen until `bb8a1278` recorded them.
PR #1355 wires it into `ci.yml`.

## Override

Set `DAG_ALLOW_LOCAL_BUILD=1` in the environment for one command. That is the
intended path when the runner is genuinely unavailable, and it is deliberately
explicit: an agent that sets it has to say so in its report.

Exit codes follow `scripts/check_workflows.sh`: 2 under `--hook` so the
PreToolUse hook blocks, 1 otherwise, 0 for anything off-target.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import sys

from _output import force_utf8_output

# Shell operators that separate one simple command from the next. A compound
# such as `cd x && lake build` has to be examined segment by segment, or the
# check is trivially evaded by prefixing anything.
SEPARATORS = re.compile(r"\|\||&&|[;|&\n()]")

# The all-library umbrellas. Naming one is the build that naming none does:
# `lakefile.toml` sets `defaultTargets = ["DerivedAlgGeo"]`, so `lake build` and
# `lake build DerivedAlgGeo` resolve to the same work. `DerivedAlgGeoSweep` is
# worse -- it imports the stable root AND the development probes.
#
# Exact names only. `DerivedAlgGeo.Development` is a module target and is
# precisely the targeted build this gate exists to permit: both `gates.sh` and
# `ci.yml` build it by name before the audits.
UMBRELLAS = {"DerivedAlgGeo", "DerivedAlgGeoSweep"}

# A `lake` living inside a self-hosted runner's tree, in either layout a shell
# might hand us: the retired Windows one (`C:\actions-runner\<runner>\`) and the
# current Ubuntu one (`~/.local/share/github-runners/<runner>/`). Matching only
# the first left this check dead from the 2026-09-21 migration (#1443) onward.
# See "Whose lake" in the module docstring for what each layout can do.
RUNNER_TREE = re.compile(r"[\\/](?:actions-runner|github-runners)[\\/]", re.IGNORECASE)

# Lake's concurrency, and the ceiling a targeted build may use on this host.
#
# WHY A TARGETED BUILD IS ALSO A RESOURCE DECISION. The rest of this gate is
# about the SIZE of a build; this is about its WIDTH. Without `LEAN_NUM_THREADS`
# Lake takes one `lean` process per core, and each one can hold several GB. On
# the 16-core host this repository is developed on that is up to 16 heavyweight
# processes from a single `lake build DerivedAlgGeo.Foo` -- which the size rule
# above deliberately permits.
#
# That is not hypothetical. On 2026-09-15 the host ran ~60 concurrent `lean`
# processes across agent worktrees and self-hosted runners, the commit limit
# collapsed to 2.9 GB free, and the consequences were: CI `build` jobs dying
# with zero step records ("the self-hosted runner lost communication") on five
# branches; `lean` dying mid-build with `std::bad_alloc` / exit code 3221226505;
# and `elan` failing to relink `lake.exe` behind a crashed job's processes.
#
# `CLAUDE.md` has required `LEAN_NUM_THREADS=2` for local builds for some time,
# and `~/.claude/settings.json` sets it per agent session. Both are advice: the
# variable is absent in any shell that does not inherit that file, which
# `CLAUDE.md` says in as many words ("set it explicitly if you are building from
# a shell that does not inherit that"). Advice is what failed on 2026-08-27 for
# the size rule, and the fix there was to enforce it. This is the same fix for
# the width rule.
#
# The ceiling is 4 rather than the documented 2 so that someone who has thought
# about it has room; it is not 16, because 16 is the failure.
LEAN_THREADS_VAR = "LEAN_NUM_THREADS"
MAX_LOCAL_THREADS = 4


def inline_assignment(tokens: list[str], name: str) -> str | None:
    """The value of `name=...` written as a prefix assignment on this command.

    `LEAN_NUM_THREADS=2 lake build X` and `env LEAN_NUM_THREADS=2 lake build X`
    both set the variable for that one command without exporting it, so neither
    reaches `os.environ` here. Scanning stops at the command word: a `name=...`
    AFTER it is an argument, not an assignment.
    """
    for tok in tokens:
        if os.path.basename(tok) == "lake":
            return None
        if tok.startswith(name + "="):
            return tok.split("=", 1)[1]
    return None


def threads_offence(value: str | None) -> str | None:
    """Return why this `LEAN_NUM_THREADS` value is refused, or None.

    Unset is refused rather than defaulted. A gate that silently substituted a
    safe value would leave the caller's command meaning something other than
    what it says, and the next person to copy that command out of a transcript
    would run it uncapped.
    """
    advice = (
        f"Prefix the command: `{LEAN_THREADS_VAR}=2 lake build <Target>`, or "
        f"export {LEAN_THREADS_VAR} in the shell."
    )
    if value is None or not value.strip():
        return (
            f"`lake build` without {LEAN_THREADS_VAR} lets Lake take one `lean` "
            f"process per core, and each can hold several GB. {advice}"
        )
    try:
        n = int(value.strip())
    except ValueError:
        return (
            f"{LEAN_THREADS_VAR}={value!r} is not a number, so Lake's "
            f"concurrency is whatever it defaults to. {advice}"
        )
    if n < 1:
        # `LEAN_NUM_THREADS=0` is not "no threads": it is Lean's spelling of
        # "decide for me", which on this host means one per core.
        return (
            f"{LEAN_THREADS_VAR}={n} means one `lean` process per core, not "
            f"none. {advice}"
        )
    if n > MAX_LOCAL_THREADS:
        return (
            f"{LEAN_THREADS_VAR}={n} exceeds the local ceiling of "
            f"{MAX_LOCAL_THREADS} on this host, which several worktrees and the "
            f"self-hosted runners share. {advice}"
        )
    return None


# Commands that can only READ a file named on their command line.
#
# Until 2026-09-16 this check scanned every token of every segment, so any
# command that so much as MENTIONED `gates.sh` was refused -- `cat`, `grep`,
# `diff`, and `git ls-tree origin/main --name-only scripts/gates.sh`, which is
# the tooling probe `.claude/skills/land-pr` runs in its own first step. A gate
# whose purpose is "do not spend three hours of the developer's machine" has no
# business refusing a read, and CONTRIBUTING.md §"Local workflow" tells you to
# read that file to know what CI will check.
#
# The list is an allow-list rather than a deny-list on purpose: an unrecognised
# command word that mentions `gates.sh` is still refused, which is the safe
# direction for a check whose job is refusing things.
READERS = {
    "awk", "bat", "cat", "cut", "diff", "echo", "egrep", "fgrep", "file",
    "grep", "head", "less", "ls", "md5sum", "more", "nl", "printf", "rg", "sed",
    "sha256sum", "shellcheck", "sort", "stat", "tail", "uniq", "wc",
}

# `git` is a reader only for these subcommands. It is NOT one in general:
# `git bisect run scripts/gates.sh` runs the script once per revision, which is
# the worst version of the thing this gate refuses, and `git rebase --exec`,
# `git submodule foreach` and `git filter-branch` all execute too. An allow-list
# of subcommands keeps the probe in .claude/skills/land-pr working without
# opening that door. The index and history commands from `add` on take a path
# as data -- staging, committing or deleting `scripts/gates.sh` runs nothing.
GIT_READ_SUBCOMMANDS = {
    "blame", "cat-file", "diff", "grep", "log", "ls-files", "ls-tree",
    "rev-parse", "show", "status",
    "add", "checkout", "commit", "mv", "reset", "restore", "rm", "stash",
}

# A leading `VAR=value` is an environment assignment, not the command.
ASSIGNMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")

# `env` flags that swallow the following token. Without these, `env -u FOO grep
# ... gates.sh` reports its command word as `FOO`, which is in no allow-list, so
# a read would be refused -- and `env -u DAG_ALLOW_LOCAL_BUILD` is exactly how
# scripts/test_local_build.sh invokes this checker.
ENV_FLAGS_WITH_ARG = {"-u", "--unset", "-C", "--chdir", "-S", "--split-string"}


def reads_only(tokens: list[str]) -> bool:
    """Does this simple command only READ the files it names?

    An allow-list, so an unrecognised command word means "refuse". `git` is
    resolved one level deeper, to its subcommand.
    """
    word = command_word(tokens)
    if word is None:
        return False
    base = os.path.basename(word)
    if base in READERS:
        return True
    if base != "git":
        return False
    rest = tokens[tokens.index(word) + 1 :]
    skip_next = False
    for tok in rest:
        if skip_next:
            skip_next = False
            continue
        if tok.startswith("-"):
            # `git --no-pager log`, and the two global flags that take a
            # separate argument: `git -C dir show`, `git -c k=v log`.
            skip_next = tok in {"-C", "-c"}
            continue
        return tok in GIT_READ_SUBCOMMANDS
    return False


def command_word(tokens: list[str]) -> str | None:
    """The executable a simple command actually runs.

    Skips leading environment assignments and a leading `env` with its flags, so
    that `env -u FOO grep x scripts/gates.sh` reports `grep`.
    """
    skip_next = False
    saw_env = False
    for tok in tokens:
        if skip_next:
            skip_next = False
            continue
        if ASSIGNMENT.match(tok):
            continue
        if saw_env and tok.startswith("-"):
            skip_next = tok in ENV_FLAGS_WITH_ARG
            continue
        if os.path.basename(tok) == "env":
            saw_env = True
            continue
        return tok
    return None


def target_name(token: str) -> str:
    """The library or module a Lake target token names, bare.

    `lake build DerivedAlgGeo:leanArts` and `lake build +DerivedAlgGeo` are the
    same whole-library build as `lake build DerivedAlgGeo`. A check that
    compared the raw token would be one colon away from being evaded.
    """
    return token.lstrip("@+").split(":", 1)[0]


# Programs that run their input as shell commands. A heredoc or here-string fed
# to one of these is code, and `bash -c STRING` runs STRING; fed to anything
# else, the same text is data.
SHELLS = {"bash", "sh", "zsh", "dash", "ksh"}

HEREDOC = re.compile(r"<<(-?)[ \t]*(['\"]?)([A-Za-z0-9_.-]+)\2")


def _matching_paren(text: str, start: int) -> int:
    """Index of the `)` closing the `(` at `start`, or -1. Quotes are skipped."""
    depth, i, quote = 0, start, None
    while i < len(text):
        c = text[i]
        if quote:
            if c == "\\" and quote == '"':
                i += 2
                continue
            if c == quote:
                quote = None
        elif c in "'\"":
            quote = c
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def _substitutions(text: str) -> list[str]:
    """The commands inside `$(...)` and backticks in expanding text.

    Double-quoted strings and unquoted heredoc bodies are data to the command
    that receives them, but a command substitution inside them still runs.
    """
    found: list[str] = []
    i = 0
    while i < len(text):
        if text.startswith("$(", i):
            end = _matching_paren(text, i + 1)
            if end < 0:
                found.append(text[i + 2 :])
                break
            found.append(text[i + 2 : end])
            i = end + 1
        elif text[i] == "`":
            end = text.find("`", i + 1)
            found.append(text[i + 1 :] if end < 0 else text[i + 1 : end])
            if end < 0:
                break
            i = end + 1
        else:
            i += 1
    return found


def split_commands(command: str) -> list[str] | None:
    """The simple commands a shell would run for `command`, as raw strings.

    Operators split only outside quotes: `grep -E 'a|b' file` is one command.
    Command substitutions inside double quotes are returned as commands of
    their own, because they run. A heredoc body is skipped when the command it
    feeds is not a shell, and is split as commands when it is; an unquoted
    delimiter also expands substitutions in the body. Returns None when the
    quoting does not balance, so the caller can fall back to over-splitting.
    """
    out: list[str] = []
    buf: list[str] = []
    pending: list[tuple[str, bool, bool, str]] = []  # delimiter, strip tabs, quoted, owner
    i, n, quote = 0, len(command), None

    def flush() -> None:
        raw = "".join(buf).strip()
        if raw:
            out.append(raw)
        buf.clear()

    while i < n:
        c = command[i]
        if quote == "'":
            buf.append(c)
            quote = None if c == "'" else quote
            i += 1
            continue
        if c == "\\" and i + 1 < n:
            buf.append(command[i : i + 2])
            i += 2
            continue
        if quote == '"':
            if c == '"':
                quote = None
            elif command.startswith("$(", i) or c == "`":
                close = _matching_paren(command, i + 1) if c == "$" else command.find("`", i + 1)
                if close < 0:
                    return None
                inner = command[i + 2 : close] if c == "$" else command[i + 1 : close]
                out.extend(split_commands(inner) or [inner])
                buf.append(command[i : close + 1])
                i = close + 1
                continue
            buf.append(c)
            i += 1
            continue
        if c in "'\"":
            quote = c
            buf.append(c)
            i += 1
            continue
        if command.startswith("<<", i) and not command.startswith("<<<", i):
            if m := HEREDOC.match(command, i):
                owner = "".join(buf)
                pending.append((m.group(3), m.group(1) == "-", bool(m.group(2)), owner))
                buf.append(m.group(0))
                i = m.end()
                continue
        if c == "\n" and pending:
            flush()
            i += 1
            for delim, strip_tabs, quoted, owner in pending:
                body: list[str] = []
                while i < n:
                    end = command.find("\n", i)
                    line = command[i:] if end < 0 else command[i:end]
                    i = n if end < 0 else end + 1
                    if (line.lstrip("\t") if strip_tabs else line) == delim:
                        break
                    body.append(line)
                text = "\n".join(body)
                try:
                    word = command_word(shlex.split(owner))
                except ValueError:
                    word = None
                if word is not None and os.path.basename(word) in SHELLS:
                    out.extend(split_commands(text) or [text])
                elif not quoted:
                    for inner in _substitutions(text):
                        out.extend(split_commands(inner) or [inner])
            pending.clear()
            continue
        if command.startswith(("&&", "||"), i):
            flush()
            i += 2
            continue
        if c in ";|&\n()":
            flush()
            i += 1
            continue
        if c == "`":
            close = command.find("`", i + 1)
            if close < 0:
                return None
            flush()
            out.extend(split_commands(command[i + 1 : close]) or [command[i + 1 : close]])
            i = close + 1
            continue
        buf.append(c)
        i += 1
    if quote:
        return None
    flush()
    return out


def segments(command: str) -> list[list[str]]:
    """Split a shell command into simple commands, tokenised.

    Quote-aware first (`split_commands`). Only when the quoting does not
    balance does it fall back to splitting at every operator character,
    which over-approximates and is the safe direction for a check that
    refuses things.
    """
    raws = split_commands(command)
    if raws is None:
        raws = [r.strip() for r in SEPARATORS.split(command) if r.strip()]
    out: list[list[str]] = []
    for raw in raws:
        try:
            out.append(shlex.split(raw))
        except ValueError:
            out.append(raw.split())
    return out


def nested_commands(tokens: list[str]) -> list[str]:
    """Strings this simple command hands to a shell to run.

    `bash -c STRING`, `eval ARGS` and a here-string fed to a shell all run
    their text as commands, so it is checked as commands rather than as an
    argument that merely mentions a file.
    """
    word = command_word(tokens)
    if word is None:
        return []
    base = os.path.basename(word)
    rest = tokens[tokens.index(word) + 1 :]
    if base == "eval":
        return [" ".join(rest)]
    if base not in SHELLS:
        return []
    nested = []
    for flag, arg in zip(rest, rest[1:]):
        if flag == "<<<" or (flag.startswith("-") and not flag.startswith("--") and "c" in flag):
            nested.append(arg)
    return nested


def lake_interpreter_offence(token: str) -> str | None:
    """Refuse a `lake` that is one of the self-hosted runners' elan shims.

    `token` is the word the shell would run. A path is read as written; a bare
    `lake` is resolved against PATH, the way the shell resolves it.

    An UNRESOLVABLE `lake` passes. This process cannot see the shell's real
    environment -- Claude Code's Bash tool sources a generated snapshot this
    hook never reads -- so a failed lookup means "the hook's PATH is not the
    shell's", which is an environment quirk rather than evidence of the
    offence. Refusing on it would fire on every machine that has no runner at
    all, which is every machine but this one.
    """
    if "/" in token or "\\" in token:
        resolved = token
    else:
        resolved = shutil.which(token)
    if not resolved or not RUNNER_TREE.search(resolved):
        return None
    return (
        f"`{token}` resolves to `{resolved}`, a self-hosted runner's elan shim "
        "rather than your own. It writes into that runner's isolated .elan and "
        "competes for its cgroup budget while a job may be using it; on the "
        "retired Windows lane it also held `lake.exe` open and took `main` red "
        "three times on 2026-09-16. Name your own elan instead: "
        "`~/.elan/bin/lake build <Target>`."
    )


def offence(tokens: list[str]) -> str | None:
    """Return the reason this simple command is refused, or None."""
    if not tokens:
        return None

    for tok in tokens:
        # Matches `scripts/gates.sh`, `./scripts/gates.sh`, `bash scripts/gates.sh`.
        if tok.endswith("gates.sh"):
            if reads_only(tokens):
                break  # reading the file, not running it
            return (
                "scripts/gates.sh runs the whole-library build gate. Run "
                "`scripts/precheck.sh` for the local subset that needs no Lean "
                "build, and take the verdict from the runners."
            )

    # `lake build` with no explicit target builds the default targets, i.e. the
    # whole library. A flag is not a target.
    for i, tok in enumerate(tokens):
        if os.path.basename(tok) != "lake":
            continue
        rest = tokens[i + 1 :]
        if not rest or rest[0] != "build":
            continue
        # Which binary, before which target: a runner's shim is the wrong lake
        # even when what it is asked to build is entirely reasonable.
        reason = lake_interpreter_offence(tok)
        if reason is not None:
            return reason
        targets = [t for t in rest[1:] if not t.startswith("-")]
        if not targets:
            return (
                "`lake build` with no target builds the whole library. Either "
                "name the module you changed (`lake build DerivedAlgGeo.Foo`) "
                "or push the branch and let the runner do it."
            )
        umbrellas = [t for t in targets if target_name(t) in UMBRELLAS]
        if umbrellas:
            return (
                f"`lake build {umbrellas[0]}` names an all-library umbrella, "
                "which is the same whole-library build as `lake build` with no "
                "target at all. Naming it is not a targeted build. Either name "
                "the module you changed (`lake build DerivedAlgGeo.Foo`) or "
                "push the branch and let the runner do it."
            )
        # The build is an allowed SIZE. It still has to declare its WIDTH.
        # An inline assignment beats the ambient environment, because that is
        # the precedence the shell itself gives it.
        reason = threads_offence(
            inline_assignment(tokens, LEAN_THREADS_VAR)
            or os.environ.get(LEAN_THREADS_VAR)
        )
        if reason is not None:
            return reason
    return None


def check(command: str, depth: int = 0) -> str | None:
    for tokens in segments(command):
        reason = offence(tokens)
        if reason is not None:
            return reason
        if depth < 8:
            for nested in nested_commands(tokens):
                reason = check(nested, depth + 1)
                if reason is not None:
                    return reason
    return None


def main() -> int:
    hook_mode = "--hook" in sys.argv[1:]

    if os.environ.get("DAG_ALLOW_LOCAL_BUILD") == "1":
        return 0

    if hook_mode:
        # Same contract as the other hooks here: anything unparseable or
        # off-target is a silent pass. A PreToolUse hook that errored on every
        # non-Bash tool call would fire on every edit in the repository.
        try:
            payload = json.load(sys.stdin)
        except Exception:
            return 0
        if payload.get("tool_name") not in (None, "Bash"):
            return 0
        command = (payload.get("tool_input") or {}).get("command") or ""
    else:
        command = " ".join(sys.argv[1:])

    if not command:
        return 0

    reason = check(command)
    if reason is None:
        return 0

    print(
        "local-build gate: refused.\n"
        f"  {reason}\n"
        "\n"
        "Lean builds for this repository run on a runner (`ci.yml` runs on\n"
        "ubuntu-latest here; the owner's runners serve a private mirror, see\n"
        "docs/ci/owner-lane.md).\n"
        "\n"
        "`push` triggers on `main` alone, so for a verdict on a branch OPEN THE\n"
        "PULL REQUEST, or dispatch CI on the pushed branch:\n"
        "    gh workflow run ci.yml --ref <branch>\n"
        "\n"
        "Still allowed locally: `scripts/precheck.sh` (every gate that needs no\n"
        "Lean build, plus a targeted build of what the branch changed),\n"
        "`LEAN_NUM_THREADS=2 lake build <Target>`, `lake env lean <file>`,\n"
        "`lake exe runLinter`, `lake exe lint-style`, the python checkers,\n"
        "and READING gates.sh.\n"
        "\n"
        "CI is NOT a superset of gates.sh: `workflows`, `local-build`,\n"
        "`mathlib-style` and `single-instantiation` have no ci.yml\n"
        "counterpart. `precheck.sh` runs the first three.\n"
        "\n"
        "If the runner is genuinely unavailable, set DAG_ALLOW_LOCAL_BUILD=1 for\n"
        "the command -- and say so in your report.",
        file=sys.stderr,
    )
    return 2 if hook_mode else 1


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
