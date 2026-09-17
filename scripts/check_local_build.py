#!/usr/bin/env python3
"""Refuse whole-library Lean builds on the developer's machine.

Lean builds for this repository belong on the self-hosted Windows runner.
`ci.yml` already routes them there: `push` and `workflow_dispatch` resolve
`runs-on` to `["self-hosted", "owner-win"]`, while `pull_request` stays on
`ubuntu-latest`. So the way to build is to PUSH THE BRANCH, not to run `lake`
locally.

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
work the Windows runner would have done off the developer's machine entirely.

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

The four self-hosted runners each keep an elan under
`C:\actions-runner\<runner>\.elan`, and those `bin` directories sit on the
developer's own Windows PATH, AHEAD of `~/.elan/bin`. That is not a setup
mistake waiting to be tidied away. `lean-action` invokes `elan-init` with no
`--no-modify-path`, and `run-runner.cmd` points HOME at the runner directory,
so every CI job re-persists its own shim directory into the user environment.
Remove the entries and the next job puts them back.

So a plain `lake` in an agent shell executes a RUNNER's `lake.exe`. Windows
will not replace a running image, so the next job on that runner cannot relink
its shims and dies about a second in with

    error: could not create link from 'elan.exe' to 'lake.exe'

On 2026-09-16 that held `main` red across three consecutive runs (bc973621,
6217d770, b9e18832) behind ONE local build that broke none of the other rules
here: named target, `LEAN_NUM_THREADS=2`, this gate green. Naming the
interpreter is the only fix that survives, because it does not depend on PATH
order -- and PATH order is not ours to keep.

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
here used to claim otherwise ("CI runs every gate in it, and more"). Five gates
in `scripts/gates.sh` have no counterpart in any workflow: `workflows`,
`trust-guard`, `local-build`, `mathlib-style`, and `single-instantiation`. The
first four are local by construction -- they test hooks, or a pre-push linter
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

# A `lake` living inside a self-hosted runner's working directory, in either
# spelling a shell might hand us. See "Whose lake" in the module docstring for
# why these end up on the developer's PATH and why editing the PATH does not
# keep them off it.
RUNNER_TREE = re.compile(r"[\\/]actions-runner[\\/]", re.IGNORECASE)

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
    "awk", "bat", "cat", "cut", "diff", "egrep", "fgrep", "file",
    "grep", "head", "less", "ls", "md5sum", "more", "nl", "rg", "sed",
    "sha256sum", "shellcheck", "sort", "stat", "tail", "uniq", "wc",
}

# `git` is a reader only for these subcommands. It is NOT one in general:
# `git bisect run scripts/gates.sh` runs the script once per revision, which is
# the worst version of the thing this gate refuses, and `git rebase --exec`,
# `git submodule foreach` and `git filter-branch` all execute too. An allow-list
# of subcommands keeps the probe in .claude/skills/land-pr working without
# opening that door.
GIT_READ_SUBCOMMANDS = {
    "blame", "cat-file", "diff", "grep", "log", "ls-files", "ls-tree",
    "rev-parse", "show", "status",
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


def segments(command: str) -> list[list[str]]:
    """Split a shell command into simple commands, tokenised.

    `shlex` is used per segment rather than over the whole string so that an
    unbalanced quote in one segment cannot silently swallow the rest.
    """
    out: list[list[str]] = []
    for raw in SEPARATORS.split(command):
        raw = raw.strip()
        if not raw:
            continue
        try:
            out.append(shlex.split(raw))
        except ValueError:
            # Unparseable: fall back to whitespace, which over-approximates and
            # is the safe direction for a check that refuses things.
            out.append(raw.split())
    return out


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
        "rather than your own. Running it holds that runner's `lake.exe` open, "
        "and the next CI job on that runner cannot relink its shims -- `main` "
        "went red three times this way on 2026-09-16. Name your own elan "
        "instead: `~/.elan/bin/lake build <Target>`."
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


def check(command: str) -> str | None:
    for tokens in segments(command):
        reason = offence(tokens)
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
        "Lean builds for this repository run on the self-hosted Windows runner\n"
        "(`ci.yml` routes `push` and `workflow_dispatch` to "
        "[\"self-hosted\", \"owner-win\"]).\n"
        "\n"
        "For a verdict, push the branch, or without pushing:\n"
        "    gh workflow run ci.yml --ref <branch>\n"
        "\n"
        "Still allowed locally: `scripts/precheck.sh` (every gate that needs no\n"
        "Lean build, plus a targeted build of what the branch changed),\n"
        "`LEAN_NUM_THREADS=2 lake build <Target>`, `lake env lean <file>`,\n"
        "`lake exe runLinter`, `lake exe lint-style`, the python checkers,\n"
        "and READING gates.sh.\n"
        "\n"
        "CI is NOT a superset of gates.sh: `workflows`, `trust-guard`,\n"
        "`local-build`, `mathlib-style` and `single-instantiation` have no\n"
        "ci.yml counterpart. `precheck.sh` runs the first four.\n"
        "\n"
        "If the runner is genuinely unavailable, set DAG_ALLOW_LOCAL_BUILD=1 for\n"
        "the command -- and say so in your report.",
        file=sys.stderr,
    )
    return 2 if hook_mode else 1


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
