#!/usr/bin/env bash
# The pre-push gate list from CONTRIBUTING.md, as one command.
#
# An unattended formalization loop needs a single exit code to branch on, and it
# needs the gates in cheapest-first order so a failure is reported in two minutes
# rather than forty.
#
#   scripts/gates.sh fast   build + style                         (~minutes)
#   scripts/gates.sh        the full list below, in CI's order
#   scripts/precheck.sh     the subset with no Lean build         (~seconds)
#
# DO NOT RUN THIS SCRIPT ON THE DEVELOPER'S MACHINE. `scripts/check_local_build.py`
# is a PreToolUse hook and refuses it in any mode, because the `build` gate below
# is the whole-library build that cost a developer three hours on 2026-08-27.
# Full verification runs on the self-hosted Windows runners: push the branch, or
# `gh workflow run ci.yml --ref <branch>`. This file remains the readable list of
# what is checked, and reading it is allowed -- `cat`, `grep` and `git ls-tree`
# pass the hook. `scripts/precheck.sh` is what you actually run locally.
#
# NEITHER LIST CONTAINS THE OTHER, and saying so precisely is the point of this
# paragraph, because the imprecise version caused a real regression.
#
# What CI has and this file does not: the `Contract gates` step runs the `mfc`
# contract tooling -- validate / env / bundle / lint / check-ilean-coverage
# against the pinned registry -- from a venv it builds per run, and none of it is
# reproduced below. A green `scripts/gates.sh` does not imply a green CI.
#
# What this file has and `.github/workflows/` does not, verified against ci.yml,
# cache-warm.yml and docs.yml on 2026-09-16, and re-verified when the trust
# guard was removed:
#
#   workflows        cannot be a CI gate. A workflow file too invalid to parse is
#                    also too invalid to run the job that would have checked it;
#                    GitHub fails a run named after the file and reports no
#                    checks at all. It has to fire before the file reaches
#                    GitHub. See scripts/check_workflows.sh.
#   local-build      tests a PreToolUse hook, which exists only on a developer's
#                    machine.
#   mathlib-style    is the PostToolUse edit hook's checker, run over the branch
#                    diff. It is a pre-push linter by design.
#   emit-build       runs in cache-warm.yml rather than ci.yml -- linking is
#                    expensive on a cold tree, and exe/Emit.lean cannot link on
#                    Windows at all. Deliberate; see the gate's own comment.
#   single-instantiation  was NOT deliberate. Until PR #1355 it appeared in no
#                    workflow at all, so for anyone who could not run this script
#                    -- which, since the hook, is every agent -- it ran nowhere.
#                    It drifted in silence: `bb8a1278` records 24 generic
#                    abstractions that reached at most one inhabitant with
#                    nothing going red. The first four entries above are local by
#                    construction; this one was local by omission, and the header
#                    that claimed "ONE deliberate exception" is what hid it.
#
# `roadmap` is the one piece of that step cheap enough to run here, and it was
# added on 2026-08-27 after the gap bit: RM-07 went red on main and on every
# open pull request for half an hour -- a roadmap entry left at `planned` after
# its issue closed -- while `scripts/gates.sh` stayed green on all of them,
# because it never looked. It is deliberately invoked WITHOUT `--require-api`:
# the script's own contract is that a contributor with no `gh` gets a NOT_RUN
# report rather than a blocked push, and CI passes the flag instead.
#
# Each gate prints `GATE <name>: pass|FAIL`. The script does not stop at the
# first failure -- an unattended run wants the whole picture in one pass -- and
# exits 1 if any gate failed.

set -uo pipefail
cd "$(dirname "$0")/.."

MODE="${1:-full}"
FAILED=()

# Per-run scratch directory. These artifacts used to live at fixed /tmp paths,
# which is wrong on this machine twice over: agent sessions run in worktrees
# under /tmp, and two self-hosted CI runners share the host. Two concurrent
# runs then read and write the same file, so a gate can pass or fail on another
# branch's data with nothing in the output naming the branch that wrote it.
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
  # The disease detector. `EnumInhabitants.lean` imports only modules the
  # `build` gate compiles, so it runs after that gate.
  lake env lean scripts/EnumInhabitants.lean > "$GATE_TMP"/enum-inhabitants.txt 2>&1 || {
    tail -20 "$GATE_TMP"/enum-inhabitants.txt
    return 1
  }
  python3 scripts/check_single_instantiation.py "$GATE_TMP"/enum-inhabitants.txt
}

exe_sorry() {
  # The one file the emitter cannot cover: an `lean_exe` root is not part of the
  # environment built from its own imports. CI runs the same loop; see the
  # "No declaration uses sorry" step in .github/workflows/ci.yml.
  # RestateHistoricalNames is deliberately outside both library umbrellas, so
  # a clean tree must build that executable-only dependency explicitly before
  # elaborating exe/Restate.lean.
  lake build DerivedAlgGeoSweep RestateHistoricalNames || return 1
  local log="$GATE_TMP"/exe-sorry-check.txt
  : > "$log"
  for f in exe/*.lean; do
    lake env lean "$f" >> "$log" 2>&1 || { tail -20 "$log"; return 1; }
  done
  if grep -q "declaration uses 'sorry'" "$log"; then
    echo "a declaration uses sorry"
    return 1
  fi
  return 0
}

changed_lean_files() {
  # `origin/main`, not `main`: the local `main` in this clone is hundreds of
  # commits stale, and diffing against it would hand every gate the whole
  # library instead of the branch's own changes.
  git diff --name-only origin/main...HEAD -- '*.lean'
  git diff --name-only -- '*.lean'
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
  files="$(changed_lean_files | sort -u)"
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
# and on the Windows runner a gate that cannot print `δ` dies with a
# `charmap` traceback instead of its finding (#868, #869). This checks that
# each script routes its console through scripts/_output.py, and that the
# helper actually survives a cp1252 console.
gate output-encoding python3 scripts/_output.py
gate codex-entrypoint python3 scripts/check_codex_entrypoint.py
gate loop-engine-tests python3 -m unittest discover -s scripts/tests -p "test_*.py"
# Next to it for the same reason: `check_local_build.py` is a PreToolUse hook,
# and a hook that has stopped refusing is indistinguishable from a hook with
# nothing to catch. #837 found it silently allowing `lake build DerivedAlgGeo`
# -- the whole library under a target name -- for as long as it had existed.
gate local-build scripts/test_local_build.sh
gate mathlib-style mathlib_style
gate review-docs python3 scripts/check_review_evidence.py docs --base origin/main
gate emission-sources python3 scripts/check_emission_coverage.py --source-only
gate explicit-numerical-data python3 scripts/check_explicit_numerical_data.py
gate foundation-import-boundary python3 scripts/check_foundation_import_boundary.py
gate build lake build

if [ "$MODE" != "fast" ]; then
  gate runLinter lake exe runLinter DerivedAlgGeo
  gate nolints-ratchet python3 scripts/check_nolints.py
  gate lint-style lake exe lint-style
  gate warning-ratchet warning_ratchet
  gate pin python3 scripts/check_pin.py
  gate source-independence python3 scripts/check_source_independence.py
  gate subject-layering python3 scripts/check_layering.py
  gate neutral-stability-imports python3 scripts/check_neutral_stability_imports.py
  gate umbrella-coverage python3 scripts/check_umbrella_coverage.py
  gate root-reachability python3 scripts/check_root_reachability.py
  gate coherent-families python3 scripts/check_coherent_families.py
  gate coverage-map python3 scripts/check_coverage_map.py
  gate single-instantiation single_instantiation
  # No `--require-api`: see the header. Offline this reports NOT_RUN and passes,
  # which is the script's documented local contract; CI runs it with the flag so
  # the one environment guaranteed to have the API cannot silently skip.
  gate roadmap python3 scripts/check_roadmap.py
  # emit-build keeps proving the executable still LINKS -- linking is the only
  # thing that exercises the native-object path at all, and exe/Emit.lean notes
  # it cannot be linked on Windows. It is the expensive gate on a cold tree
  # (4173 Mathlib `:c.o` targets) and cheap on a warm one, which is why CI runs
  # it only in the cache-warm workflow and not per pull request.
  gate emit-build lake build emit
  # ...but the emission itself runs INTERPRETED, matching CI. It needs no native
  # objects, and on a warm tree it is faster than the compiled path (134s vs
  # 158s) because it never loads the 278 MB binary. Verified equivalent: same
  # 11945 constants, same names, same counts; `emitted_at` is the only byte that
  # differs. Exit codes propagate through `--run`, which matters because this
  # non-zero exit IS the repository-wide sorry gate.
  gate emit lake env lean --run exe/Emit.lean --out "$GATE_TMP"/derived-alg-geo-emission.json
  # The emit gate above is the repository-wide sorry gate. This one checks that
  # it swept everything -- without it, a library root nobody imported into
  # DerivedAlgGeoSweep.lean drops out of coverage with every gate still green.
  gate emission-coverage python3 scripts/check_emission_coverage.py \
    "$GATE_TMP"/derived-alg-geo-emission.json
  gate exe-sorry exe_sorry
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
