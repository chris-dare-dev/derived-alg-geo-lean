#!/usr/bin/env bash
# Bootstrap a fresh worktree with private, pinned Lake packages and build caches.
# Existing `.lake` trees are verified only when they have a private-cache receipt.
# The old link-producing seeder is intentionally unavailable: it made distinct
# worktrees write through the same `.lake/packages` directory.
#
# Usage: bash scripts/seed_worktree_cache.sh [--dry-run] [--from <donor>]
#        [--private-packages] [--force]
# `--private-packages` is retained for existing callers. `--force` is parsed by
# the helper but refuses until a non-destructive, quiescent migration exists.

set -euo pipefail

usage() {
  sed -n '1,11p' "$0"
}

args=()
while (( $# )); do
  case "$1" in
    --from)
      if (( $# < 2 )) || [[ -z "$2" ]]; then
        echo "--from needs a path" >&2
        exit 2
      fi
      args+=(--donor "$2")
      shift 2
      ;;
    --dry-run|--force)
      args+=("$1")
      shift
      ;;
    --private-packages)
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

target="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}

# A crash after the single atomic rename leaves a complete generation. A
# retry verifies its receipt. An old linked or partial `.lake` fails closed.
if [[ -e "$target/.lake" || -L "$target/.lake" ]]; then
  args+=(--verify)
fi
exec python3 "$target/scripts/private_package_cache.py" --target "$target" "${args[@]}"
