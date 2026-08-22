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
# HOW IT WORKS. The `run:` block is extracted from the workflow and only the
# `gh api` fetch is replaced, by a synthetic TSV file list. The classification
# logic under test is therefore byte-for-byte the logic that ships. No network,
# no `gh`, no checkout, nothing from a pull request.
#
# Usage:
#   scripts/test_trust_guard.sh [path-to-trust-guard.yml]

set -uo pipefail
cd "$(dirname "$0")/.."

WF="${1:-.github/workflows/trust-guard.yml}"

RAW="$(awk '/^        run: \|$/{f=1;next} f&&/^      - name:/{f=0} f' "$WF" | sed 's/^          //')"

# Swap the two-line `files="$(gh api ... )"` assignment for an env read.
BODY="$(printf '%s\n' "$RAW" | python3 -c '
import re, sys
src = sys.stdin.read()
out = re.sub(r"files=\"\$\(gh api.*?@tsv.\)\"", "files=\"$FILES_TSV\"", src, flags=re.S)
sys.stdout.write(out)
')"

if ! printf '%s' "$BODY" | grep -q 'files="\$FILES_TSV"'; then
  echo "harness error: could not substitute the gh api fetch" >&2
  exit 2
fi

b64 () { printf '%s' "$1" | base64 | tr -d '\n'; }

run_case () {
  local name="$1" expect="$2" tsv="$3" out rc
  out="$(REPO=x PR=1 LABELS='[]' FILES_TSV="$(printf '%b' "$tsv")" bash -c "$BODY" 2>&1)"
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
run_case "audit record slice"              skip "scripts/AlgebraicGeometryAudit/Core.lean\t0\t$(b64 "$GOOD")" || fails=1
run_case "ordinary source file"            skip "DerivedAlgGeo/Foo.lean\t0\t$(b64 "$GOOD")"                || fails=1
run_case "empty file list"                 trip ""                                                        || fails=1

exit $fails
