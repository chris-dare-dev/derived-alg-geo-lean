#!/usr/bin/env bash
# The local pre-flight: every gate that needs no Lean build, plus a targeted
# build of what this branch changed.
#
# WHY THIS EXISTS. `scripts/check_local_build.py` refuses `scripts/gates.sh` in
# any mode, because its `build` gate is the whole-library build that cost a
# developer three hours on 2026-08-27. That refusal was correct and it was also
# the whole story: nothing replaced it. Both agent skills under `.claude/skills/`
# called `scripts/gates.sh fast` and then `scripts/gates.sh` as their definition
# of done, so every unattended iteration hit a blocked hook at exactly the step
# that decides whether the work is finished, and got no verdict at all.
#
# This is the half of the gate list that a laptop can honestly run: no
# `lake build` of the library, no audits, no emitter. It takes seconds, it
# catches the failures that actually recur on this queue -- a retired source
# root, a missing umbrella export, a style violation, an invalid workflow --
# and it is allowed by the hook by construction, because it never asks Lake for
# an umbrella.
#
# THIS IS NOT A CI VERDICT, and the difference is the point of the file.
#
#   * It does not run the library build, the three axiom audits, the
#     audit-completeness ratchet, the linters, the warning ratchet, the emitter,
#     or the emission-coverage check. Those need the library elaborated.
#   * It does not run `single-instantiation` either, for the same reason --
#     `scripts/EnumInhabitants.lean` needs the same elaborated environment.
#   * It does not run the `mfc` contract tooling, which is CI-only and which
#     `scripts/gates.sh` does not reproduce either.
#
# Get the verdict from the self-hosted Windows runners. Pushing an `agent/**`
# branch already does it; without pushing:
#
#   gh workflow run ci.yml --ref <branch>
#
# Usage:
#   scripts/precheck.sh          the checks above, plus the targeted build
#   scripts/precheck.sh --no-build   skip Lake entirely (no toolchain needed)
#
# Each check prints `GATE <name>: pass|FAIL`, in the order `scripts/gates.sh`
# runs them. It does not stop at the first failure -- an unattended run wants
# the whole picture in one pass -- and exits 1 if any check failed.

set -uo pipefail
cd "$(dirname "$0")/.."

WITH_BUILD=1
[ "${1:-}" = "--no-build" ] && WITH_BUILD=0

FAILED=()
# Every gate name this script ran, for the agreement check at the end.
RAN=()

# Per-run scratch directory, for the same reason gates.sh has one: agent
# sessions run in worktrees and two self-hosted runners share this host, so a
# fixed /tmp path lets one branch read another's artifacts.
tmp_base="${TMPDIR:-/tmp}"
PRE_TMP="$(mktemp -d "${tmp_base%/}/dag-precheck.XXXXXX")" || {
  echo "could not create a scratch directory under ${tmp_base%/}"
  exit 1
}
PRE_TMP_KEEP=0
trap '[ "$PRE_TMP_KEEP" -eq 1 ] || rm -rf "$PRE_TMP"' EXIT

gate() {
  local name="$1"; shift
  local log
  RAN+=("$name")
  log="$(mktemp)"
  if "$@" >"$log" 2>&1; then
    echo "GATE $name: pass"
  else
    echo "GATE $name: FAIL"
    echo "--- last 40 lines of $name ---"
    if [ -s "$log" ]; then
      tail -40 "$log"
    else
      echo "(no output captured -- this gate redirects internally;"
      echo " check $PRE_TMP/${name%%-*}-*.txt or run the command directly)"
    fi
    echo "--- end $name ---"
    FAILED+=("$name")
  fi
  rm -f "$log"
}

gates_agreement() {
  # Two lists of gate names in two files drift, and the drift is silent: a gate
  # renamed or removed in gates.sh would quietly keep "passing" here against a
  # script that no longer exists, or vanish from CI's list while precheck went on
  # reporting it green. That is the exact shape of the failure this whole lane
  # exists to fix, so it gets a check rather than a comment.
  #
  # Only one direction is checkable cheaply: every name precheck runs must still
  # be a gate in gates.sh. The reverse -- which gates.sh gates need no Lean build
  # -- is a judgement about their bodies, not a grep.
  local missing=()
  local name
  for name in "${GATES_SOURCED[@]}"; do
    # Leading spaces: the full-mode gates sit inside gates.sh's `if` block.
    grep -qE "^ *gate ${name} " scripts/gates.sh || missing+=("$name")
  done
  if [ ${#missing[@]} -ne 0 ]; then
    echo "these precheck gates are no longer gates in scripts/gates.sh:"
    printf '  %s\n' "${missing[@]}"
    echo "Rename or remove them here too, or precheck reports a green that means nothing."
    return 1
  fi
  return 0
}

changed_lean_files() {
  # `origin/main`, not `main`: the local `main` in this clone is hundreds of
  # commits stale, and diffing against it would hand every check the whole
  # library instead of the branch's own changes.
  git diff --name-only origin/main...HEAD -- '*.lean'
  git diff --name-only -- '*.lean'
}

mathlib_style() {
  local files
  files="$(changed_lean_files | sort -u)"
  [ -z "$files" ] && return 0
  # --diff-only, matching gates.sh: judge the lines this branch wrote, not the
  # pre-existing debt in a file it happens to touch.
  # shellcheck disable=SC2086
  python3 scripts/check_mathlib_style.py --diff-only origin/main $files
}

changed_targets() {
  # `DerivedAlgGeo/Foo/Bar.lean` -> `DerivedAlgGeo.Foo.Bar`. Only library
  # modules: `scripts/`, `exe/` and `Development` roots are not Lake module
  # targets under the same mapping, and `DerivedAlgGeo.lean` at the root is the
  # all-library umbrella the hook refuses by name -- correctly, since naming it
  # is the whole-library build.
  changed_lean_files \
    | sort -u \
    | grep '^DerivedAlgGeo/' \
    | sed -e 's/\.lean$//' -e 's#/#.#g'
}

targeted_build() {
  local targets
  targets="$(changed_targets)"
  if [ -z "$targets" ]; then
    echo "no changed library modules; nothing to build"
    return 0
  fi
  echo "building: $targets"
  # WIDTH, not just size. `check_local_build.py` refuses a targeted build that
  # does not declare `LEAN_NUM_THREADS`, or that sets it above
  # MAX_LOCAL_THREADS -- on 2026-09-15 an uncapped host reached ~60 concurrent
  # `lean` processes and CI jobs died with no log at all. This script is invoked
  # as one command, so the hook never sees the `lake build` inside it; declaring
  # the width here is therefore a promise the hook cannot check, and it is kept.
  #
  # An ambient value is honoured but clamped: a shell exporting 16 would put
  # this script on the wrong side of a rule the hook would have enforced on the
  # same build typed by hand.
  local threads="${LEAN_NUM_THREADS:-2}"
  case "$threads" in
    ''|*[!0-9]*) threads=2 ;;
    *) [ "$threads" -lt 1 ] && threads=2
       [ "$threads" -gt 4 ] && threads=4 ;;
  esac
  echo "LEAN_NUM_THREADS=$threads"
  # WHOSE lake -- the same kind of promise as the width above, kept for the same
  # reason: the hook only ever sees the command an agent types, and this script
  # is typed as one word.
  #
  # On the development host every runner's `.elanin` sits on PATH AHEAD of
  # `~/.elan/bin`, and not by hand: `lean-action` runs `elan-init` without
  # `--no-modify-path` and `run-runner.cmd` points HOME at the runner directory,
  # so each CI job re-persists its own shim directory into the user environment.
  # A bare `lake` here therefore runs a RUNNER's shim and holds its `lake.exe`
  # open; the next job on that runner cannot relink its shims and dies about a
  # second in. On 2026-09-16 that held `main` red across three runs.
  #
  # Falls back to PATH where there is no user elan, which is every machine that
  # is not this one.
  local lake="lake"
  [ -x "$HOME/.elan/bin/lake" ] && lake="$HOME/.elan/bin/lake"
  echo "lake: $lake"
  # shellcheck disable=SC2086
  LEAN_NUM_THREADS="$threads" "$lake" build $targets
}

echo "== precheck =="
echo "(not a CI verdict -- see the header, and gh workflow run ci.yml --ref <branch>)"
echo

# First and cheapest, and the one whose failure is otherwise invisible: an
# invalid workflow does not produce a red check, it produces no checks. It also
# cannot be a CI gate at all; see scripts/check_workflows.sh.
gate workflows scripts/check_workflows.sh
gate output-encoding python3 scripts/_output.py
# These two test hooks and a workflow guard. Neither has a ci.yml counterpart,
# and neither can have one: a pull request cannot be trusted to run the check
# that decides whether a pull request is trusted.
gate trust-guard scripts/test_trust_guard.sh
gate local-build scripts/test_local_build.sh
gate mathlib-style mathlib_style
gate explicit-numerical-data python3 scripts/check_explicit_numerical_data.py
gate foundation-import-boundary python3 scripts/check_foundation_import_boundary.py
gate nolints-ratchet python3 scripts/check_nolints.py
gate pin python3 scripts/check_pin.py
gate source-independence python3 scripts/check_source_independence.py
gate subject-layering python3 scripts/check_layering.py
gate umbrella-coverage python3 scripts/check_umbrella_coverage.py
gate root-reachability python3 scripts/check_root_reachability.py
gate coherent-families python3 scripts/check_coherent_families.py
gate coverage-map python3 scripts/check_coverage_map.py
# No `--require-api`, matching gates.sh: offline this reports NOT_RUN and
# passes, which is the script's documented local contract. CI passes the flag.
gate roadmap python3 scripts/check_roadmap.py

# Everything above is a gate borrowed from scripts/gates.sh by name. Snapshot the
# list before adding the two that are precheck's own.
GATES_SOURCED=("${RAN[@]}")
gate gates-agreement gates_agreement

if [ "$WITH_BUILD" -eq 1 ]; then
  gate targeted-build targeted_build
fi

echo
if [ ${#FAILED[@]} -eq 0 ]; then
  echo "precheck clean -- this is NOT a CI verdict."
  echo "Push the branch, or: gh workflow run ci.yml --ref \$(git branch --show-current)"
  exit 0
fi
echo "FAILED: ${FAILED[*]}"
PRE_TMP_KEEP=1
echo "artifacts kept in $PRE_TMP"
exit 1
