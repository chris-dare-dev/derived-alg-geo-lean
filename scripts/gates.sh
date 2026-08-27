#!/usr/bin/env bash
# The pre-push gate list from CONTRIBUTING.md, as one command.
#
# An unattended formalization loop needs a single exit code to branch on, and it
# needs the gates in cheapest-first order so a failure is reported in two minutes
# rather than forty. Every gate below also runs in `.github/workflows/ci.yml`,
# with ONE deliberate exception: `workflows`. That one cannot be a CI gate,
# because a workflow file too invalid to parse is also too invalid to run the
# job that would have checked it -- GitHub just fails a run named after the file
# and reports no checks at all. It has to fire before the file reaches GitHub,
# which means here. See scripts/check_workflows.sh.
#
#   scripts/gates.sh fast   build + style + axiom audits          (~minutes)
#   scripts/gates.sh        everything CI runs, in CI's order
#
# The containment runs ONE WAY ONLY, and saying so is the point of this
# paragraph. Every gate here runs in CI; CI is NOT every gate here. CI's
# `Contract gates` step additionally runs the `mfc` contract tooling --
# validate / env / bundle / lint / check-ilean-coverage against the pinned
# registry -- from a venv it builds per run, and none of that is reproduced
# below. A green `scripts/gates.sh` therefore does not imply a green CI.
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
# Observed 2026-08-16: audit-complete passed, then the same unchanged
# /tmp/enum-decls.txt reported 73 declarations over ceiling, because a
# concurrent worktree had regenerated it in between.
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

algebraic_geometry_audit() {
  # The algebraic-geometry audit imports development probes and dimension
  # specializations, none of which the default target reaches -- `lake build`
  # builds DerivedAlgGeo, and the umbrella does not import the probes. CI builds
  # them explicitly before the audit; so must this, or the gate fails with a
  # missing-olean error in any tree where they were not already built by hand.
  lake build DerivedAlgGeo.Development \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold || return 1
  # Since #480 the records live in per-area files; `#print axioms` output does
  # not replay across the import boundary, so each area file is run directly.
  : > "$GATE_TMP"/algebraic-geometry-audit.txt
  for f in scripts/AlgebraicGeometryAudit/*.lean; do
    lake env lean "$f" >> "$GATE_TMP"/algebraic-geometry-audit.txt 2>&1 || {
      # Show the reason: this function redirects its own output, so without
      # this the wrapper's log is empty and the gate fails silently.
      echo "failed: $f"
      tail -20 "$GATE_TMP"/algebraic-geometry-audit.txt
      return 1
    }
  done
  grep -q 'sorryAx' "$GATE_TMP"/algebraic-geometry-audit.txt && { echo "sorryAx reached the audit"; return 1; }
  # Allowlist + truncation + parse checks, matching CI and the other two audit
  # lanes; until 2026-08-18 this lane checked only sorryAx (review P2-3).
  python3 scripts/check_audit.py "$GATE_TMP"/algebraic-geometry-audit.txt \
    scripts/AlgebraicGeometryAudit.lean
}

dg_audit() {
  lake env lean scripts/DGCategoryAudit.lean > "$GATE_TMP"/dg-audit.txt 2>&1 || {
    tail -20 "$GATE_TMP"/dg-audit.txt
    return 1
  }
  python3 scripts/check_audit.py "$GATE_TMP"/dg-audit.txt scripts/DGCategoryAudit.lean
}

audit_complete() {
  # The other direction from check_audit.py: a new public declaration nobody
  # listed. Needs the same prerequisite build as coh_audit, because the sweep
  # imports Development and the dimension specializations.
  lake build DerivedAlgGeo.Development \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold || return 1
  lake env lean scripts/EnumDecls.lean > "$GATE_TMP"/enum-decls.txt 2>&1 || {
    tail -20 "$GATE_TMP"/enum-decls.txt
    return 1
  }
  python3 scripts/check_audit_complete.py "$GATE_TMP"/enum-decls.txt
}

stability_condition_audit() {
  # Per-area invocation, as above: the umbrella alone would emit no records.
  : > "$GATE_TMP"/stability-condition-audit.txt
  for f in scripts/StabilityConditionAudit/*.lean; do
    lake env lean "$f" >> "$GATE_TMP"/stability-condition-audit.txt 2>&1 || {
      echo "failed: $f"
      tail -20 "$GATE_TMP"/stability-condition-audit.txt
      return 1
    }
  done
  python3 scripts/check_audit.py "$GATE_TMP"/stability-condition-audit.txt
}

exe_sorry() {
  # The one file the emitter cannot cover: an `lean_exe` root is not part of the
  # environment built from its own imports. CI runs the same loop; see the
  # "No declaration uses sorry" step in .github/workflows/ci.yml.
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
gate trust-guard scripts/test_trust_guard.sh
gate mathlib-style mathlib_style
gate explicit-numerical-data python3 scripts/check_explicit_numerical_data.py
gate foundation-import-boundary python3 scripts/check_foundation_import_boundary.py
gate build lake build
gate algebraic-geometry-audit algebraic_geometry_audit
gate stability-condition-audit stability_condition_audit
gate dg-audit dg_audit

if [ "$MODE" != "fast" ]; then
  gate runLinter lake exe runLinter DerivedAlgGeo
  gate nolints-ratchet python3 scripts/check_nolints.py
  gate lint-style lake exe lint-style
  gate pin python3 scripts/check_pin.py
  gate source-independence python3 scripts/check_source_independence.py
  gate subject-layering python3 scripts/check_layering.py
  gate coherent-families python3 scripts/check_coherent_families.py
  gate coverage-map python3 scripts/check_coverage_map.py
  gate audit-complete audit_complete
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
