# Verification history

AGENTS.md states the verification rules briefly, because Codex injects only its
first 32,768 bytes and every loop thread pays for each line. This file keeps the
incidents behind those rules, moved here on 2026-09-27 (verbatim, except the two
measurement notes, which are condensed), so the rules
stay short without losing why they exist. Nothing here is an instruction; the
rules are in AGENTS.md.

## Phantom deletions in a stale pull request's diff

The rule: merge the base branch in before reviewing a diff.

Observed twice on 2026-09-12. #1268 and #1272 each appeared to delete ~84 lines
across five `scripts/*Audit*/*.lean` files; after merging their base, each was a
single file with insertions only and no deletions anywhere. One of the
"deleted" files, `scripts/StabilityConditionAudit/ExpDivisorial.lean`, existed
on neither the branch nor its merge base -- the base created it after the fork.

This matters most for the audit record slices, because deleting a record is a
real defect and the artifact is indistinguishable from it by eye. They are
protected by `check_audit.py` and `check_audit_complete.py`, which run in `ci`
and judge the merged tree, where the artifact does not exist. So a phantom
deletion cannot reach `main`; the cost is a reviewer's time and a wrongly
rejected pull request.

## The local-build hook

The rule: `scripts/check_local_build.py` refuses `scripts/gates.sh` and
untargeted `lake build`, but not reading the gate list.

It refuses RUNNING that file, not reading it: `cat`, `grep`, `diff` and
`git ls-tree` over `scripts/gates.sh` all pass, so you can still read the gate
list. Until 2026-09-16 they did not, which is why the `land-pr` skill's own
tooling probe was blocked by the hook it was probing around.

Advice was what this section used to give, and advice is what failed: on
2026-08-27 an agent read "the normal build stays local", ran a whole-library
`lake build` on a cold tree, and spent three hours of the developer's machine on
work the runners were idle and waiting to absorb.

## `single-instantiation` ran nowhere

The rule: the local precheck and CI each run gates the other does not; say
which gates passed, never "CI is green" for a local run. From the paragraph
that preceded the precheck instructions:

This paragraph used to read "every gate in `gates.sh` runs in CI", and that
sentence is why `single-instantiation` ran nowhere for months: the hook made the
script unrunnable, the summary said CI had it covered, and `bb8a1278` records the
24 abstractions that drifted past its baseline with nothing going red.

## `LEAN_NUM_THREADS` became enforced (2026-09-15)

It used to be advice, and on 2026-09-15 that failed exactly as the size rule had
in #837. The host reached ~60 concurrent `lean` processes across worktrees and
the four self-hosted runners; the commit limit collapsed to 2.9 GB free; CI
`build` jobs on five branches died with **no log and no step records** ("the
self-hosted runner lost communication"), `lean` died mid-build with
`std::bad_alloc` (exit code 3221226505), and `elan` failed to relink `lake.exe`
behind a crashed job's leftovers. None of those failures names memory in its
message, which is what made it expensive to diagnose.

## Pull-request lane timing

The `pull_request` lane, over the 195 commits on which both lanes built: 20.8
min median against 40.2 for the self-hosted lane (measured before 2026-09-19).

## Seeding a worktree's cache

Measured on 2026-09-15: 1556 modules seeded, after which a targeted build
completed 2069 jobs in 43 seconds. A fresh worktree otherwise lacks the shared
`.lake/packages` link, which nothing else documents. Copying rather than
hardlinking spends disk to save commit, which is the right trade on this host
and not a universal one.

## Windows runners and the lake shims (until 2026-09-21)

The self-hosted runners were migrated from Windows to Ubuntu on 2026-09-21. The
text below is what AGENTS.md said while they ran on Windows:

`~/.elan/bin/lake` is not decoration. Each of the four self-hosted runners keeps
its own elan under `C:\actions-runner\<runner>\.elan`, and those `bin`
directories sit on this machine's user PATH **ahead of** `~/.elan/bin` — put
there by CI, not by hand. `lean-action` runs `elan-init` with no
`--no-modify-path`, and `run-runner.cmd` points `HOME` at the runner directory,
so every job re-persists its own shim directory into the user environment.
Deleting the entries does not hold: on 2026-09-16 all four were removed and
three were back within ten minutes.

So a bare `lake` here executes a **runner's** `lake.exe`. Windows will not
replace a running image, so the next CI job on that runner cannot relink its
shims and dies about a second in with

    error: could not create link from 'elan.exe' to 'lake.exe'

That is what took `main` red across three consecutive runs on 2026-09-16
(bc973621, 6217d770, b9e18832), behind one local build that broke none of the
other rules here: named target, `LEAN_NUM_THREADS=2`, gate green.

It costs contention, not correctness. The same declaration sweep run through a
runner's shim and through `~/.elan/bin/lake` came back byte-identical (14589
rows), with audit-completeness reporting the same numbers, so a result already
produced through the wrong tree does **not** need re-running. Check which one
you are using with `which lake`.
