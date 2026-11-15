#!/usr/bin/env bash
# The pre-push gate list from CONTRIBUTING.md, as one command.
#
# An unattended run needs a single exit code to branch on, and it needs the
# gates in cheapest-first order so a failure is reported in minutes rather than
# after the whole build.
#
#   scripts/gates.sh fast   build + style                         (~minutes)
#   scripts/gates.sh        the full list below, in CI's order
#   scripts/precheck.sh     the subset with no Lean build         (~seconds)
#
# DO NOT RUN THIS SCRIPT ON THE DEVELOPER'S MACHINE. `scripts/check_local_build.py`
# is a PreToolUse hook and refuses it in any mode, because the `build` gate below
# is the whole-library build. Full verification runs in CI: open the pull
# request, or `gh workflow run ci.yml --ref <branch>`. This file remains the
# readable list of what is checked, and reading it is allowed -- `cat`, `grep`
# and `git ls-tree` pass the hook. `scripts/precheck.sh` is what you run locally.
#
# This file runs every gate CI runs. What it has and `ci.yml` does not:
#
#   workflows        cannot be a CI gate. A workflow file too invalid to parse is
#                    also too invalid to run the job that would have checked it;
#                    GitHub fails a run named after the file and reports no
#                    checks at all. It has to fire before the file reaches
#                    GitHub. See scripts/check_workflows.sh.
#   mathlib-style    its `--diff-only` pass is the edit hook's checker over the
#                    branch diff, a pre-push linter by design. Its fixtures and
#                    baseline ratchet also run in CI.
#
# Each gate prints `GATE <name>: pass|FAIL`. The script does not stop at the
# first failure -- an unattended run wants the whole picture in one pass -- and
# exits 1 if any gate failed.

set -uo pipefail
cd "$(dirname "$0")/.."

MODE="${1:-full}"
FAILED=()

# Per-run scratch directory. Agent worktrees and self-hosted runners share one
# host, and with a fixed path two concurrent runs read and write the same file,
# so a gate can pass or fail on another branch's data with nothing in the output
# naming the branch that wrote it.
gate_tmp_base="${TMPDIR:-/tmp}"
GATE_TMP="$(mktemp -d "${gate_tmp_base%/}/dag-gates.XXXXXX")" || {
  echo "could not create a scratch directory under ${gate_tmp_base%/}"
  exit 1
}
# Kept on gate failure so the artifacts survive for inspection; the final
# report prints the path. Removed on success and on interrupt.
GATE_TMP_KEEP=0
trap '[ "$GATE_TMP_KEEP" -eq 1 ] || rm -rf "$GATE_TMP"' EXIT

gate() {
  local name="$1"; shift
  local log
  log="$(mktemp)"
  if "$@" >"$log" 2>&1; then
    echo "GATE $name: pass"
  else
    echo "GATE $name: FAIL"
    echo "--- last 40 lines of $name ---"
    if [ -s "$log" ]; then
      tail -40 "$log"
    else
      # A gate whose body redirects its own output leaves this empty. An
      # unattended run then reports a failure with no reason, which is worse
      # than the failure: say so rather than printing nothing.
      echo "(no output captured -- this gate redirects internally;"
      echo " check $GATE_TMP/${name%%-*}-*.txt or run the command directly)"
    fi
    echo "--- end $name ---"
    FAILED+=("$name")
  fi
  rm -f "$log"
}

warning_ratchet() {
  # The `build` gate above already compiled the library, so this recompiles
  # nothing: Lake replays the cached modules and reprints their warnings. The
  # capture has to be its own command anyway, because `build` streams straight
  # to the console and there is nothing to grep afterwards.
  lake build DerivedAlgGeo > "$GATE_TMP"/lean-warnings.txt 2>&1 || {
    tail -20 "$GATE_TMP"/lean-warnings.txt
    return 1
  }
  python3 scripts/check_warnings.py "$GATE_TMP"/lean-warnings.txt
}

single_instantiation() {
  # The disease detector. `EnumInhabitants.lean` also imports
  # `DerivedAlgGeo.Development`, which the `build` gate's default target omits.
  lake build DerivedAlgGeo.Development || return 1
  lake env lean scripts/EnumInhabitants.lean > "$GATE_TMP"/enum-inhabitants.txt 2>&1 || {
    tail -20 "$GATE_TMP"/enum-inhabitants.txt
    return 1
  }
  python3 scripts/check_single_instantiation.py "$GATE_TMP"/enum-inhabitants.txt
}

axiom_audit() {
  # `lake env lean` does not build, and the sweep umbrella is not a default
  # target.
  lake build DerivedAlgGeoSweep || return 1
  lake env lean scripts/AxiomAudit.lean
}

changed_lean_files() {
  # `origin/main`, not `main`: the local `main` in this clone is hundreds of
  # commits stale, and diffing against it would hand every gate the whole
  # library instead of the branch's own changes.
  git diff --name-only --diff-filter=d origin/main...HEAD -- '*.lean'
  git diff --name-only --diff-filter=d -- '*.lean'
}

mathlib_style() {
  local files
  # Known-answer fixtures first: they do not depend on the diff, and a branch
  # that changes the checker can break what it rejects without changing a
  # single .lean file.
  python3 scripts/check_mathlib_style.py --self-test || return 1
  # The ratchet over the whole library, for the same reason the fixtures run
  # here: neither depends on the diff, and a branch that adds a style ERROR to
  # a file no agent edited would otherwise reach CI to find out.
  python3 scripts/check_mathlib_style.py --check-baseline || return 1
  # Library sources only: the checker refuses a run in which no file it judges
  # was given, and `scripts/` Lean files are outside its scope.
  files="$(changed_lean_files | grep -E '^DerivedAlgGeo(/|\.lean$)' | sort -u)"
  [ -z "$files" ] && return 0
  # --diff-only: judge the lines this branch wrote, not the pre-existing debt in
  # a file it happens to touch. The edit hook stays strict on what you just
  # typed; a branch gate that demanded you also refactor everything around it
  # would make touching any legacy file an unbounded task.
  # shellcheck disable=SC2086
  python3 scripts/check_mathlib_style.py --diff-only origin/main $files
}

echo "== gates ($MODE) =="

# First because it is the cheapest gate here by three orders of magnitude
# (~100ms against minutes) and because it is the one whose failure is otherwise
# invisible: an invalid workflow does not produce a red check, it produces no
# checks. In `fast` mode too, for the same reason.
gate workflows scripts/check_workflows.sh
# Also cheap, also in `fast` mode: every gate below prints declaration names,
# and on a console that cannot encode `δ` a gate dies with a `charmap` traceback
# instead of its finding. This checks that each script routes its console
# through scripts/_output.py, and that the helper survives a cp1252 console.
gate output-encoding python3 scripts/_output.py
gate tree-areas python3 scripts/check_tree_areas.py origin/main
gate mathlib-style mathlib_style
gate explicit-numerical-data python3 scripts/check_explicit_numerical_data.py
gate foundation-import-boundary python3 scripts/check_foundation_import_boundary.py
gate build lake build

if [ "$MODE" != "fast" ]; then
  gate runLinter lake exe runLinter DerivedAlgGeo
  gate nolints-ratchet python3 scripts/check_nolints.py
  gate lint-style lake exe lint-style
  gate warning-ratchet warning_ratchet
  # No `--require-api`: see the header. Offline this reports NOT_RUN and passes,
  # which is the script's documented local contract; CI runs it with the flag so
  # the one environment guaranteed to have the API cannot silently skip.
  gate pin python3 scripts/check_pin.py
  gate source-independence python3 scripts/check_source_independence.py
  gate subject-layering python3 scripts/check_layering.py
  gate umbrella-coverage python3 scripts/check_umbrella_coverage.py
  gate root-reachability python3 scripts/check_root_reachability.py
  gate coherent-families python3 scripts/check_coherent_families.py
  gate single-instantiation single_instantiation
  gate axiom-audit axiom_audit
fi

echo
if [ ${#FAILED[@]} -eq 0 ]; then
  echo "all gates passed ($MODE)"
  exit 0
fi
echo "FAILED: ${FAILED[*]}"
GATE_TMP_KEEP=1
echo "artifacts kept in $GATE_TMP"
exit 1
