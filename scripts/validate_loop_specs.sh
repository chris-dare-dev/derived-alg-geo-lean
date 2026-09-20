#!/usr/bin/env bash
# Validate every loop manifest, including disabled manifests.  A gate that
# validates only the currently remembered pilot lets a newly enabled or
# accidentally malformed manifest bypass the same structural checks.

set -uo pipefail
cd "$(dirname "$0")/.."

found=0
for spec in .claude/loop-specs/*.yaml; do
  [ -f "$spec" ] || continue
  found=1
  echo "validating loop spec: $spec"
  if ! python3 scripts/loop_engine.py validate --spec "$spec"; then
    exit 1
  fi
done

if [ "$found" -eq 0 ]; then
  echo "no loop specifications found under .claude/loop-specs" >&2
  exit 1
fi
