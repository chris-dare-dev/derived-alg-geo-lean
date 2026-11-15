#!/usr/bin/env bash
# Validate the GitHub Actions workflow files with actionlint.
#
# WHY THIS EXISTS. A single wrong character in a workflow -- a double quote
# inside a `${{ }}` expression, where workflow expressions accept only single
# quotes -- makes the file invalid, and GitHub answers an invalid workflow with
# a failed run NAMED AFTER THE FILE: no annotation, no job, and no checks
# reported at all. `gh pr checks` then says "no checks reported on the branch",
# which is indistinguishable from "CI has not started yet". actionlint names it
# exactly:
#
#   got unexpected character '"' while lexing expression [...] only single
#   quotes are available for string delimiter
#
# The failure mode is what justifies a dedicated gate. Most CI mistakes announce
# themselves as a red check; this one announces itself as silence, and silence
# is what a broken pipeline and a slow pipeline have in common.
#
# THIS IS NOT A CI GATE, and cannot usefully be one: a workflow too invalid to
# parse is also too invalid to run the job that would have checked it. It has to
# fire before the file reaches GitHub. Three callers do that:
#
#   .claude/settings.json   PostToolUse, on every agent edit  (--hook)
#   scripts/gates.sh        the pre-push gate list
#   .git/hooks/pre-push     if installed; hooks are not versioned
#
# Usage:
#   scripts/check_workflows.sh          lint every workflow file
#   scripts/check_workflows.sh --hook   hook JSON on stdin; no-op off-target
#
# Exit codes follow scripts/check_mathlib_style.py: 2 under --hook so the
# PostToolUse hook blocks and the agent fixes it before moving on, 1 otherwise.

set -uo pipefail
cd "$(dirname "$0")/.."

HOOK_MODE=0
[ "${1:-}" = "--hook" ] && HOOK_MODE=1

if [ "$HOOK_MODE" = 1 ]; then
  # Same contract as check_mathlib_style.py --hook: the tool payload arrives on
  # stdin, and anything unparseable or off-target is a silent pass. An edit hook
  # that errored on every non-workflow edit would fire on every Lean file in the
  # repository.
  payload="$(cat)"
  file="$(printf '%s' "$payload" | python3 -c \
    'import json,sys
try:
    print((json.load(sys.stdin).get("tool_input") or {}).get("file_path") or "")
except Exception:
    print("")' 2>/dev/null)"
  case "$file" in
    */.github/workflows/*.yml|*/.github/workflows/*.yaml) ;;
    .github/workflows/*.yml|.github/workflows/*.yaml) ;;
    *) exit 0 ;;
  esac
fi

dir=".github/workflows"
[ -d "$dir" ] || exit 0
files=$(find "$dir" -maxdepth 1 \( -name '*.yml' -o -name '*.yaml' \) 2>/dev/null)
[ -n "$files" ] || exit 0

if ! command -v actionlint >/dev/null 2>&1; then
  # Loud, never a silent pass. This repository's own CI comments make the
  # argument -- "a gate that silently does not run is worse than a slow one" --
  # and a checker that succeeds when its checker is missing is exactly that.
  echo "actionlint is not installed, so the workflow files were NOT checked." >&2
  echo "  brew install actionlint      # or: go install github.com/rhysd/actionlint/cmd/actionlint@latest" >&2
  echo "  SKIP_ACTIONLINT=1            # to proceed without it, deliberately" >&2
  [ "${SKIP_ACTIONLINT:-0}" = "1" ] && exit 0
  [ "$HOOK_MODE" = 1 ] && exit 2
  exit 1
fi

# -shellcheck= -pyflakes= disable the optional sub-linters, deliberately. The
# `run:` blocks in ci.yml embed `${{ }}` expressions that shellcheck cannot
# parse and reports as syntax errors, so leaving them on would make this gate
# cry wolf on a correct file -- and a gate that is usually wrong gets ignored,
# which is the same as not having it. The target here is workflow validity:
# schema, expression syntax, action inputs, contexts, runner labels.
# shellcheck disable=SC2086
if actionlint -shellcheck= -pyflakes= $files; then
  exit 0
fi

echo "" >&2
echo "The workflow files above are invalid. GitHub reports this class of error" >&2
echo "as a run named after the file with NO checks at all, which reads exactly" >&2
echo "like CI never triggered -- fix it here, where the message is useful." >&2
[ "$HOOK_MODE" = 1 ] && exit 2
exit 1
