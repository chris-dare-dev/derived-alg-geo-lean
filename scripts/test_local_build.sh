#!/usr/bin/env bash
# Does the local-build gate still refuse what it is supposed to refuse?
#
# WHY THIS EXISTS. `scripts/check_local_build.py` is a PreToolUse hook, and a
# hook that has stopped refusing looks exactly like a hook with nothing to
# catch: the agent runs the command, the command works, nothing is printed.
# #837 is that failure twice over. `lake build DerivedAlgGeo` passed the gate
# for as long as the gate existed -- the docstring said "the whole library",
# the code tested for an empty argv -- and on 2026-08-27 it ran for over an
# hour in a worktree that DID have the hook installed.
#
# The allow-list is what makes a test necessary rather than nice. The gate has
# to refuse the umbrella while still permitting `DerivedAlgGeo.Development`,
# which `gates.sh` and `ci.yml` both build BY NAME before the audits. A refusal
# one character wider than intended breaks the audit lanes; one character
# narrower and the hour-long build is back. The cases below pin both edges.
#
# Usage:
#   scripts/test_local_build.sh

set -uo pipefail
cd "$(dirname "$0")/.."

CHECK="scripts/check_local_build.py"
fails=0

# The gate reads LEAN_NUM_THREADS from the ambient environment, so the suite has
# to pin it rather than inherit whatever the runner happens to export. Every
# case below is explicit about which side of the width rule it is testing: this
# default keeps the SIZE cases testing size, and the width cases override it.
export LEAN_NUM_THREADS=2

# refuse|allow <name> -- <argv for the checker, CLI mode>
cli_case () {
  local expect="$1" name="$2"; shift 2
  local out rc want
  out="$(env -u DAG_ALLOW_LOCAL_BUILD python3 "$CHECK" "$@" 2>&1)"
  rc=$?
  [ "$expect" = refuse ] && want=1 || want=0
  if [ "$rc" -eq "$want" ]; then
    printf 'PASS  %-46s (%s)\n' "$name" "$expect"
    return 0
  fi
  printf 'FAIL  %-46s expected %s (rc=%s), got rc=%s\n' "$name" "$expect" "$want" "$rc"
  printf '%s\n' "$out" | sed 's/^/        /'
  fails=$((fails + 1))
}

# The hook path is a different contract from the CLI path: it reads a JSON
# payload on stdin and exits 2 so Claude Code blocks the call. Exercised
# separately because an exit code of 1 there is a silent non-block.
hook_case () {
  local expect="$1" name="$2" command="$3"
  local payload out rc want
  payload="$(COMMAND="$command" python3 -c '
import json, os
print(json.dumps({"tool_name": "Bash",
                  "tool_input": {"command": os.environ["COMMAND"]}}))')"
  out="$(printf '%s' "$payload" \
    | env -u DAG_ALLOW_LOCAL_BUILD python3 "$CHECK" --hook 2>&1)"
  rc=$?
  [ "$expect" = refuse ] && want=2 || want=0
  if [ "$rc" -eq "$want" ]; then
    printf 'PASS  %-46s (%s, hook)\n' "$name" "$expect"
    return 0
  fi
  printf 'FAIL  %-46s expected %s (rc=%s), got rc=%s\n' "$name" "$expect" "$want" "$rc"
  printf '%s\n' "$out" | sed 's/^/        /'
  fails=$((fails + 1))
}

echo "== local-build gate =="

# The original hole: no target at all.
cli_case refuse 'lake build (no target)'          lake build
cli_case refuse 'lake build -R (flag is not a target)' lake build -R

# Hole 2 (#837): the umbrellas ARE the whole library.
cli_case refuse 'lake build DerivedAlgGeo'        lake build DerivedAlgGeo
cli_case refuse 'lake build DerivedAlgGeoSweep'   lake build DerivedAlgGeoSweep
cli_case refuse 'umbrella after a flag'           lake build -R DerivedAlgGeo
cli_case refuse 'umbrella among other targets'    lake build emit DerivedAlgGeo
cli_case refuse 'umbrella with a facet'           lake build DerivedAlgGeo:leanArts
cli_case refuse 'umbrella as a module target'     lake build +DerivedAlgGeo

# The other edge. Refusing any of these breaks gates.sh, ci.yml, or proof work.
cli_case allow  'lake build DerivedAlgGeo.Development' lake build DerivedAlgGeo.Development
cli_case allow  'lake build a leaf module'        lake build DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum
cli_case allow  'lake build the three audits'     lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
cli_case allow  'lake build emit'                 lake build emit
cli_case allow  'lake env lean <file>'            lake env lean scripts/EnumDecls.lean
cli_case allow  'lake exe lint-style'             lake exe lint-style
# `DerivedAlgGeo` appears verbatim here and is NOT a build target. A check that
# scanned the whole token list instead of `lake build`'s own would kill the
# linter gate.
cli_case allow  'lake exe runLinter DerivedAlgGeo' lake exe runLinter DerivedAlgGeo

# gates.sh, in any spelling, because its `build` gate is the bare build.
cli_case refuse 'scripts/gates.sh'                scripts/gates.sh
cli_case refuse 'scripts/gates.sh fast'           scripts/gates.sh fast
cli_case refuse 'bash scripts/gates.sh'           bash scripts/gates.sh

# Compound commands are examined segment by segment, or the gate is one `cd`
# away from being evaded.
cli_case refuse 'cd x && lake build DerivedAlgGeo' cd x '&&' lake build DerivedAlgGeo
cli_case allow  'cd x && lake build a leaf'        cd x '&&' lake build DerivedAlgGeo.Foo

# Hook mode: the exit code is the block.
hook_case refuse 'hook blocks the umbrella'  'lake build DerivedAlgGeo'
hook_case refuse 'hook blocks the bare build' 'lake build'
hook_case allow  'hook passes a leaf module' 'lake build DerivedAlgGeo.Foo'

# == width ==
#
# A targeted build is an allowed SIZE; these pin its WIDTH. The failure being
# prevented is not a slow build, it is the host running out of commit: see
# MAX_LOCAL_THREADS in the checker for the 2026-09-15 incident.

# Cases that run the checker with LEAN_NUM_THREADS removed from the environment,
# to exercise the "unset" branch that the export at the top of this file hides.
nothreads_case () {
  local expect="$1" name="$2"; shift 2
  local out rc want
  out="$(env -u DAG_ALLOW_LOCAL_BUILD -u LEAN_NUM_THREADS \
    python3 "$CHECK" "$@" 2>&1)"
  rc=$?
  [ "$expect" = refuse ] && want=1 || want=0
  if [ "$rc" -eq "$want" ]; then
    printf 'PASS  %-46s (%s)\n' "$name" "$expect"
    return 0
  fi
  printf 'FAIL  %-46s expected %s (rc=%s), got rc=%s\n' "$name" "$expect" "$want" "$rc"
  printf '%s\n' "$out" | sed 's/^/        /'
  fails=$((fails + 1))
}

nothreads_case refuse 'targeted build, no LEAN_NUM_THREADS' lake build DerivedAlgGeo.Foo
nothreads_case allow  'inline assignment supplies it'       LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.Foo
nothreads_case allow  'env prefix supplies it'              env LEAN_NUM_THREADS=4 lake build DerivedAlgGeo.Foo

# The ambient variable is enough on its own: this is the common path, since
# `~/.claude/settings.json` exports it for every agent session.
cli_case allow  'ambient LEAN_NUM_THREADS=2'      lake build DerivedAlgGeo.Foo

# The ceiling. 16 is what the host has cores of, and is the failure mode.
LEAN_NUM_THREADS=4  cli_case allow  'threads at the ceiling'  lake build DerivedAlgGeo.Foo
LEAN_NUM_THREADS=5  cli_case refuse 'threads above the ceiling' lake build DerivedAlgGeo.Foo
LEAN_NUM_THREADS=16 cli_case refuse 'threads = core count'    lake build DerivedAlgGeo.Foo

# `0` is Lean's spelling of "decide for me", which is one per core -- the exact
# thing being refused. A naive `int(v) > MAX` test would let it through.
LEAN_NUM_THREADS=0   cli_case refuse 'threads = 0 means auto'  lake build DerivedAlgGeo.Foo
LEAN_NUM_THREADS=''  cli_case refuse 'threads set but empty'   lake build DerivedAlgGeo.Foo
LEAN_NUM_THREADS=all cli_case refuse 'threads not a number'    lake build DerivedAlgGeo.Foo

# An inline assignment overrides the ambient value, as the shell would.
LEAN_NUM_THREADS=2 cli_case refuse 'inline overrides ambient (up)' \
  LEAN_NUM_THREADS=16 lake build DerivedAlgGeo.Foo

# The width rule must not reach commands that are not `lake build`. `lake env
# lean` is the seconds-long probe proof work depends on, and gating it would
# make every lemma attempt a CI round trip.
nothreads_case allow 'lake env lean is not gated on width' lake env lean scratch.lean
nothreads_case allow 'lake exe is not gated on width'      lake exe lint-style

# A size refusal still wins when both rules would fire, so the message names the
# problem that actually matters.
nothreads_case refuse 'umbrella refused on size, not width' lake build DerivedAlgGeo

# Hook mode carries the width rule too, or the enforcement is CLI-only.
hook_case allow  'hook passes a declared build' 'LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.Foo'

# The documented escape hatch still works, and still has to be set explicitly.
out="$(DAG_ALLOW_LOCAL_BUILD=1 python3 "$CHECK" lake build DerivedAlgGeo 2>&1)"
if [ $? -eq 0 ]; then
  printf 'PASS  %-46s (%s)\n' 'DAG_ALLOW_LOCAL_BUILD=1 overrides' allow
else
  printf 'FAIL  %-46s override did not pass\n' 'DAG_ALLOW_LOCAL_BUILD=1 overrides'
  printf '%s\n' "$out" | sed 's/^/        /'
  fails=$((fails + 1))
fi

echo
if [ "$fails" -eq 0 ]; then
  echo "local-build gate: all cases pass"
  exit 0
fi
echo "local-build gate: $fails case(s) FAILED"
exit 1
