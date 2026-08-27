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
  * `scripts/gates.sh`, in any mode, because its `build` gate is that same
    whole-library build.

Allowed, deliberately:

  * `lake build <Target>` with an explicit target, including the three audits;
  * `lake env lean <file>` -- the seconds-long probe that interactive proof work
    depends on. Routing those through CI would make each attempt a ~12 minute
    round trip and stop anyone from writing a proof at all;
  * `lake exe runLinter`, `lake exe lint-style`, and the python checkers.

The distinction is cost, not principle. A targeted build on a warm cache is
seconds; the whole library from cold is hours, and on 2026-08-27 an agent spent
three of them rebuilding a cache that a machine-wide cleanup had deleted --
work the Windows runner would have done off the developer's machine entirely.

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
import sys

# Shell operators that separate one simple command from the next. A compound
# such as `cd x && lake build` has to be examined segment by segment, or the
# check is trivially evaded by prefixing anything.
SEPARATORS = re.compile(r"\|\||&&|[;|&\n()]")


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


def offence(tokens: list[str]) -> str | None:
    """Return the reason this simple command is refused, or None."""
    if not tokens:
        return None

    for tok in tokens:
        # Matches `scripts/gates.sh`, `./scripts/gates.sh`, `bash scripts/gates.sh`.
        if tok.endswith("gates.sh"):
            return (
                "scripts/gates.sh runs the whole-library build gate. Push the "
                "branch instead: CI runs every gate in it, and more."
            )

    # `lake build` with no explicit target builds the default targets, i.e. the
    # whole library. A flag is not a target.
    for i, tok in enumerate(tokens):
        if os.path.basename(tok) != "lake":
            continue
        rest = tokens[i + 1 :]
        if not rest or rest[0] != "build":
            continue
        targets = [t for t in rest[1:] if not t.startswith("-")]
        if not targets:
            return (
                "`lake build` with no target builds the whole library. Either "
                "name the module you changed (`lake build DerivedAlgGeo.Foo`) "
                "or push the branch and let the runner do it."
            )
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
        "Still allowed locally: `lake build <Target>`, `lake env lean <file>`,\n"
        "`lake exe runLinter`, `lake exe lint-style`, the python checkers.\n"
        "\n"
        "If the runner is genuinely unavailable, set DAG_ALLOW_LOCAL_BUILD=1 for\n"
        "the command -- and say so in your report.",
        file=sys.stderr,
    )
    return 2 if hook_mode else 1


if __name__ == "__main__":
    sys.exit(main())
