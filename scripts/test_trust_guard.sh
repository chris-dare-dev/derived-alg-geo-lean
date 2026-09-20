#!/usr/bin/env bash
# Does the trust guard still refuse what it is supposed to refuse?
#
# WHY THIS EXISTS. `.github/workflows/trust-guard.yml` is the one check a pull
# request cannot rewrite for its own run, and until #720 it had no test. That is
# a bad combination: the file is edited rarely, by whoever is being blocked by
# it, and a mistake that widens it is invisible -- a guard that has stopped
# guarding looks exactly like a guard with nothing to catch.
#
# The carve-outs are what make a test necessary. Two shapes are deliberately not
# trust surface (the audit record slices, and additive-only umbrella imports),
# and each is one predicate away from letting through an edit that silently
# removes coverage. The cases below pin both directions.
#
# HOW IT WORKS. The `run:` block is extracted from the workflow and both `gh
# api` fetches are replaced by synthetic file/review responses. The
# classification and revision-binding logic under test is therefore byte-for-
# byte the logic that ships. No network, no `gh`, no checkout, nothing from a
# pull request.
#
# Usage:
#   scripts/test_trust_guard.sh [path-to-trust-guard.yml]

set -uo pipefail
cd "$(dirname "$0")/.."

WF="${1:-.github/workflows/trust-guard.yml}"

RAW="$(awk '/^        run: \|$/{f=1;next} f&&/^      - name:/{f=0} f' "$WF" | sed 's/^          //')"

# Swap the one-line API assignments for environment reads.
BODY="$(printf '%s\n' "$RAW" | python3 -c '
import sys
src = sys.stdin.read()
lines = []
for line in src.splitlines():
    if line.startswith("files=\"$(gh api"):
        lines.append("files=\"$FILES_TSV\"")
    elif line.startswith("reviews=\"$(gh api"):
        lines.append("reviews=\"$REVIEWS_JSON\"")
    else:
        lines.append(line)
sys.stdout.write("\n".join(lines))
')"

if ! printf '%s' "$BODY" | grep -q 'files="\$FILES_TSV"' \
   || ! printf '%s' "$BODY" | grep -q 'reviews="\$REVIEWS_JSON"'; then
  echo "harness error: could not substitute the gh api fetch" >&2
  exit 2
fi

b64 () { printf '%s' "$1" | base64 | tr -d '\n'; }

BASE_SHA='a000000000000000000000000000000000000000'
HEAD_SHA='b000000000000000000000000000000000000000'
TRUST_POLICY_VERSION='trust-guard-v2'

review_json () {
  local digest="$1" state="${2:-APPROVED}" association="${3:-OWNER}"
  local review_head="${4:-$HEAD_SHA}" marker_head="${5:-$HEAD_SHA}"
  local marker_base="${6:-$BASE_SHA}" body
  body="trust-review: v1 base=$marker_base head=$marker_head files=$digest policy=$TRUST_POLICY_VERSION"
  jq -cn --arg head "$review_head" --arg state "$state" \
    --arg association "$association" --arg body "$body" \
    '[[{"id":1,"user":{"login":"fixture-reviewer"},
      "author_association":$association,"commit_id":$head,"state":$state,
      "submitted_at":"2026-09-20T00:00:00Z","body":$body}]]'
}

run_case () {
  local name="$1" expect="$2" tsv="$3" mode="${4:-none}"
  local out rc files_value digest reviews='[[]]' approval_tsv="${5:-$tsv}"
  files_value="$(printf '%b' "$tsv")"
  digest="$(printf '%s\n' "$(printf '%b' "$approval_tsv")" | LC_ALL=C sort | sha256sum | awk '{print $1}')"
  case "$mode" in
    exact)        reviews="$(review_json "$digest")" ;;
    old-head)     reviews="$(review_json "$digest" APPROVED OWNER "$BASE_SHA")" ;;
    old-base)     reviews="$(review_json "$digest" APPROVED OWNER "$HEAD_SHA" "$HEAD_SHA" "$HEAD_SHA")" ;;
    changes)      reviews="$(review_json "$digest" CHANGES_REQUESTED)" ;;
    unauthorized) reviews="$(review_json "$digest" APPROVED NONE)" ;;
  esac
  out="$(REPO=x PR=1 LABELS='[]' BASE_SHA="$BASE_SHA" HEAD_SHA="$HEAD_SHA" \
    TRUST_POLICY_VERSION="$TRUST_POLICY_VERSION" FILES_TSV="$files_value" \
    REVIEWS_JSON="$reviews" bash -c "$BODY" 2>&1)"
  rc=$?
  if { [ "$expect" = trip ] && [ "$rc" -ne 0 ]; } \
     || { [ "$expect" = skip ] && [ "$rc" -eq 0 ]; }; then
    printf 'PASS  %-38s (%s)\n' "$name" "$expect"
    return 0
  fi
  printf 'FAIL  %-38s expected %s, rc=%s\n' "$name" "$expect" "$rc"
  printf '%s\n' "$out" | sed 's/^/        /'
  return 1
}

UMB='scripts/StabilityConditionAudit.lean'
GOOD='@@ -1 +1,2 @@
 import StabilityConditionAudit.Families
+import StabilityConditionAudit.CohomologyShortExact'
PROSE='@@ -1 +1,2 @@
 import StabilityConditionAudit.Families
+-- this audit no longer covers the tilting slice'
EXEC='@@ -1 +1,2 @@
 import StabilityConditionAudit.Families
+#eval IO.println "hi"'

fails=0
run_case "umbrella, additive imports only" skip "$UMB\t0\t$(b64 "$GOOD")"  || fails=1
run_case "umbrella, a deletion"            trip "$UMB\t1\t$(b64 "$GOOD")"  || fails=1
run_case "umbrella, added prose line"      trip "$UMB\t0\t$(b64 "$PROSE")" || fails=1
run_case "umbrella, added executable line" trip "$UMB\t0\t$(b64 "$EXEC")"  || fails=1
run_case "umbrella, patch omitted by API"  trip "$UMB\t0\t"                || fails=1
run_case "EnumDecls.lean"                  trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")"                || fails=1
run_case "ci.yml"                          trip ".github/workflows/ci.yml\t0\t$(b64 "$GOOD")"              || fails=1
run_case "milestone delivery policy"        trip ".milestone-pipeline/trust-policy.json\t0\t$(b64 "$GOOD")" || fails=1
run_case "loop specification"               trip ".claude/loop-specs/sf11-pilot.yaml\t0\t$(b64 "$GOOD")"     || fails=1
run_case "reviewer prompt"                  trip ".claude/agents/mathlib-reviewer.md\t0\t$(b64 "$GOOD")"     || fails=1
run_case "loop skill"                       trip ".claude/skills/run-loop/SKILL.md\t0\t$(b64 "$GOOD")"     || fails=1
run_case "openspec change"                  trip "openspec/changes/pilot-change/tasks.md\t0\t$(b64 "$GOOD")" || fails=1
run_case "audit record slice"              skip "scripts/AlgebraicGeometryAudit/Core.lean\t0\t$(b64 "$GOOD")" || fails=1
run_case "ordinary source file"            skip "DerivedAlgGeo/Foo.lean\t0\t$(b64 "$GOOD")"                || fails=1
run_case "trust path without review"       trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")"                  || fails=1
run_case "trust path exact review"         skip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")" exact             || fails=1
run_case "review bound to old head"        trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")" old-head          || fails=1
run_case "review bound to old base"        trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")" old-base          || fails=1
run_case "review requests changes"         trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")" changes           || fails=1
run_case "reviewer lacks authority"        trip "scripts/EnumDecls.lean\t0\t$(b64 "$GOOD")" unauthorized       || fails=1
run_case "review digest is stale"          trip "scripts/EnumDecls.lean\t0\t$(b64 "$PROSE")" exact "$UMB\t0\t$(b64 "$GOOD")" || fails=1
run_case "empty file list"                 trip ""                                                        || fails=1

exit $fails
