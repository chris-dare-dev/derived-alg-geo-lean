#!/usr/bin/env bash
# Seed a worktree's `.lake/build` from another worktree of this clone.
#
# WHY THIS EXISTS. Every worktree of this repository builds the same ~5850
# modules from scratch. On 2026-09-15 this machine had 36 of them holding 62 GB
# of near-identical `.lake/build`, and a cold targeted build in a fresh worktree
# compiled its whole dependency chain before reaching the one file that had
# changed. That cost is paid in CPU and, far more importantly, in COMMIT: the
# host ran ~60 concurrent `lean` processes that night, the commit limit
# collapsed, and CI `build` jobs on five branches died with no log at all. See
# `MAX_LOCAL_THREADS` in `check_local_build.py` for the incident.
#
# Seeding removes the cold start. Measured on 2026-09-15 in a fresh worktree:
# 1223 modules reused instead of recompiled, and the build reached the changed
# file directly. That is the compile pressure this script is for.
#
# ## Seeding, not sharing -- and the difference is deliberate
#
# The obvious version of this script hardlinks (`cp -l`), which would also
# collapse the 62 GB. It is NOT what this does, and the reason is correctness.
# Lean writes an `.olean` by creating the file at its final path; through a
# hardlink that writes THROUGH the shared inode. Two worktrees on different
# commits share a module's path but not its content, so a rebuild in one would
# silently rewrite the other's cache -- and a concurrent reader there can see a
# half-written file. Lake's trace check would eventually notice and rebuild,
# which makes the damage self-healing but not harmless.
#
# So this copies. It spends disk, which this host has (258 GB free when written)
# to save commit, which it does not. If the duplication ever becomes the binding
# constraint, the fix is a content-addressed read-only store that Lake consults,
# not hardlinks into a live build directory.
#
# `.lake/packages` is a different story and is already shared: it is a symlink
# to a single resolved dependency set. This script creates that symlink when a
# fresh worktree is missing it, which is otherwise a manual step nothing
# documents.
#
# It creates it as a JUNCTION on Windows, and asserts afterwards that what it
# made is a link. `ln -s` to a directory there silently deep-copies instead,
# which cost 6.5 GB and read back as "not a symlink" -- so the NEXT worktree
# seeded from that one was left with no dependency set at all and rebuilt
# Mathlib from cold. See `link_dir` for the whole chain. This script now
# refuses rather than leaving a worktree in that state, because every message
# it printed on the way there was reassuring.
#
# Usage:
#   scripts/seed_worktree_cache.sh                 # seed here from the best donor
#   scripts/seed_worktree_cache.sh --dry-run       # say what it would do
#   scripts/seed_worktree_cache.sh --from <path>   # choose the donor yourself
#   scripts/seed_worktree_cache.sh --force         # overwrite a populated target
#
# Exit codes: 0 seeded or nothing to do, 1 refused, 2 bad usage.

set -uo pipefail

TARGET="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "not inside a git worktree" >&2
  exit 2
}

DONOR=""
DRY_RUN=0
FORCE=0

while [ $# -gt 0 ]; do
  case "$1" in
    --from)    DONOR="${2:-}"; shift 2 || { echo "--from needs a path" >&2; exit 2; } ;;
    --dry-run) DRY_RUN=1; shift ;;
    --force)   FORCE=1; shift ;;
    -h|--help) sed -n '1,48p' "$0"; exit 0 ;;
    *)         echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

olean_count () {
  local dir="$1/.lake/build"
  [ -d "$dir" ] || { echo 0; return; }
  find "$dir" -name '*.olean' 2>/dev/null | wc -l | tr -d ' '
}

# Is a build writing into this worktree right now?
#
# The tempting implementation is to look for `lean`/`lake` processes whose
# command line names the worktree. Two drafts of this script did, and neither
# worked -- which is worth recording, because both FAILED OPEN and so looked
# exactly like a clean check:
#
#   * Git Bash's `ps -W` prints the executable path and no arguments at all, so
#     a `lean.exe` building this worktree is indistinguishable from one building
#     any other; and `wmic`, the usual escape, is gone from Windows 11.
#   * Reading command lines properly (PowerShell `Get-CimInstance Win32_Process`)
#     does work, but they come back with BACKSLASHES while `git rev-parse
#     --show-toplevel` yields forward slashes, so the comparison never matched.
#     Normalising that still leaves `lake env lean some/relative/path.lean`,
#     whose worktree appears nowhere in its argv -- it is the process's working
#     directory, which is not portably readable for another process.
#
# So this measures the hazard itself instead of inferring it from processes: is
# the directory being written? That needs no process introspection, works the
# same everywhere, and is true exactly when copying would tear.
STALE_SECONDS=90

recently_written () {
  local dir="$1/.lake/build"
  [ -d "$dir" ] || return 1
  # `-quit` stops at the first hit, so this stays fast on a 3 GB tree.
  local hit
  hit="$(find "$dir" -type f -newermt "-$STALE_SECONDS seconds" -print -quit 2>/dev/null)"
  [ -n "$hit" ]
}

# Where the donor keeps its dependency set.
#
# A properly made link reads back through `readlink` on every platform here,
# junctions included -- Git Bash resolves a Windows junction as a symlink. So a
# donor whose `.lake/packages` is NOT a link is a donor that was damaged by the
# bug below, and the honest fallback is to point at the donor's own directory:
# still one shared copy, still no cold Mathlib build.
packages_source () {
  local donor="$1" resolved
  resolved="$(readlink "$donor/.lake/packages" 2>/dev/null || true)"
  if [ -n "$resolved" ]; then
    echo "$resolved"
  elif [ -d "$donor/.lake/packages" ]; then
    echo "$donor/.lake/packages"
  fi
}

# Link `$2` to `$1`, as a link and not as a copy.
#
# WHY THIS IS NOT JUST `ln -s`. It was, and on Windows `ln -s` to a DIRECTORY
# silently deep-copies it. The script then printed "linked .lake/packages -> ..."
# over a 6.5 GB copy that was not a link, and the damage only surfaced one hop
# later: seeding a third worktree from that one found a real directory where a
# link should be, took the "leaving yours alone" branch below, and left the new
# worktree with NO dependency set at all -- so its next `lake build` cloned
# Mathlib and compiled it from cold, which is hours. Every message along the way
# was reassuring.
#
# `mklink /J` makes a junction, needs no administrator, and needs
# `MSYS_NO_PATHCONV=1` so MSYS does not rewrite the `/J` switch into a path.
link_dir () {
  local target="$1" link="$2"
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      MSYS_NO_PATHCONV=1 cmd /c "mklink /J $(cygpath -w "$link") $(cygpath -w "$target")" >/dev/null 2>&1
      ;;
    *)
      ln -s "$target" "$link" >/dev/null 2>&1
      ;;
  esac
  # The assertion that was missing. `ln -s` reported success while producing a
  # copy, so success is not what this checks -- being a link is.
  [ -L "$link" ]
}

worktrees () {
  git worktree list --porcelain 2>/dev/null \
    | sed -n 's/^worktree //p'
}

TARGET_HAVE="$(olean_count "$TARGET")"

# --- pick a donor -------------------------------------------------------------

if [ -z "$DONOR" ]; then
  best=""; best_n=0
  while IFS= read -r w; do
    [ -n "$w" ] || continue
    [ "$w" = "$TARGET" ] && continue
    n="$(olean_count "$w")"
    if [ "$n" -gt "$best_n" ]; then best_n="$n"; best="$w"; fi
  done < <(worktrees)
  DONOR="$best"
  if [ -z "$DONOR" ]; then
    echo "no other worktree of this clone has a build cache to seed from." >&2
    echo "Nothing to do; the first build here will be cold." >&2
    exit 1
  fi
fi

if [ ! -d "$DONOR/.lake/build" ]; then
  echo "donor has no .lake/build: $DONOR" >&2
  exit 1
fi

DONOR_HAVE="$(olean_count "$DONOR")"

echo "target: $TARGET  ($TARGET_HAVE modules)"
echo "donor:  $DONOR  ($DONOR_HAVE modules)"

# --- refuse the unsafe cases --------------------------------------------------

if [ "$TARGET" = "$DONOR" ]; then
  echo "refused: donor and target are the same worktree." >&2
  exit 1
fi

if [ "$TARGET_HAVE" -gt 0 ] && [ "$FORCE" -ne 1 ]; then
  echo "refused: target already has $TARGET_HAVE built modules." >&2
  echo "Seeding is for a COLD worktree. Re-run with --force to overwrite." >&2
  exit 1
fi

if [ "$DONOR_HAVE" -eq 0 ]; then
  echo "refused: donor has no built modules." >&2
  exit 1
fi

for w in "$TARGET" "$DONOR"; do
  if recently_written "$w"; then
    echo "refused: $w/.lake/build was written in the last ${STALE_SECONDS}s," >&2
    echo "so a build is probably running there. Copying a build directory out" >&2
    echo "from under a build is a torn read. Wait for it to finish." >&2
    exit 1
  fi
done

# --- report, then do it -------------------------------------------------------

if [ "$DRY_RUN" -eq 1 ]; then
  echo
  echo "would copy $DONOR/.lake/build -> $TARGET/.lake/build  ($DONOR_HAVE modules)"
  if [ ! -e "$TARGET/.lake/packages" ]; then
    pkgs="$(packages_source "$DONOR")"
    echo "would link .lake/packages -> ${pkgs:-<donor has none>}"
  fi
  exit 0
fi

mkdir -p "$TARGET/.lake"

# The dependency set is genuinely shared, so mirror the donor's symlink rather
# than copying several GB of Mathlib oleans that are identical by construction.
if [ ! -e "$TARGET/.lake/packages" ]; then
  pkgs="$(packages_source "$DONOR")"
  if [ -z "$pkgs" ]; then
    echo "refused: donor has no .lake/packages, so there is nothing to share." >&2
    echo "Seeding the build cache alone would leave this worktree without a" >&2
    echo "dependency set, and its next lake build would clone Mathlib and" >&2
    echo "compile it from cold. Seed from a worktree that has one." >&2
    exit 1
  fi
  if link_dir "$pkgs" "$TARGET/.lake/packages"; then
    echo "linked .lake/packages -> $pkgs"
  else
    rm -rf "$TARGET/.lake/packages"
    echo "refused: could not LINK .lake/packages -> $pkgs." >&2
    echo "Refusing to continue rather than copy it: a copy is several GB, and" >&2
    echo "it reads back as not-a-symlink, so the next worktree seeded from this" >&2
    echo "one would get no dependency set at all." >&2
    exit 1
  fi
fi

echo "copying $DONOR_HAVE modules..."
rm -rf "$TARGET/.lake/build.seeding"
if ! cp -r "$DONOR/.lake/build" "$TARGET/.lake/build.seeding"; then
  echo "copy failed; leaving the target untouched." >&2
  rm -rf "$TARGET/.lake/build.seeding"
  exit 1
fi

# Swap last, so an interrupted copy never leaves a half-populated cache that
# Lake would treat as real.
rm -rf "$TARGET/.lake/build"
mv "$TARGET/.lake/build.seeding" "$TARGET/.lake/build"

echo "seeded $(olean_count "$TARGET") modules into $TARGET"
echo
echo "Lake verifies every trace against the source it finds, so anything this"
echo "worktree changes is rebuilt and nothing stale is trusted."
