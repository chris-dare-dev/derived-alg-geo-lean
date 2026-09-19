# SF11 loop-engineering notes

This file is the repository-facing memory for the bounded run covering issues
#1060, #1061, and #1062. It records friction and stale statements; it is not a
replacement for a Lean theorem or an issue acceptance criterion.

## Initial observations (2026-09-19)

- `scripts/loop_engine.py` originally rejected every issue labelled `epic`,
  while all three selected SF11 issues are roadmap epics. The manifest now has a
  narrow `eligibility.allow_epic_issues` allow-list. The controller must retain
  rejection for every unlisted epic, blocked, research, and spike issue.
- The loop branch/tooling PR was merged as PR #1399, but a local checkout may
  still have a stale `origin/main`. Fetch before choosing a protected-base ref;
  do not infer merge state from an old local ref.
- `openspec list --all` is not a valid discovery command in the installed CLI;
  `openspec list` (or `openspec list --specs`) is the supported form. The
  generated skill text and CLI affordance should be kept aligned if this recurs.
- The existing SF11 modules are honest about their boundary but easy to
  misread: `BaseChangeCategory.lean`, `BaseChangeData.lean`, and `SLocal.lean`
  construct carriers and closure operators while still leaving geometric
  compactness, coherence, generation, and restriction witnesses supplied.
  Words such as “actual”, “constructed”, and “nothing is inhabited” must be
  read together, not treated as interchangeable evidence of issue completion.
- `SLocal.lean` uses `CompactSpace U.toScheme` to represent the paper's
  quasi-compact opens. This matches the current Mathlib API but is a likely
  source of confusion for agents reading “compact” as a derived-category
  compactness claim.
- `TStructure/Local.lean` now owns the categorical uniqueness half of Remark
  4.6(1), but its docstring still points to `Phase/Transfer/Inducing.lean` as if
  all S-locality were outside the categorical layer. Retire that sentence only
  after the geometric quantifier and at least one inhabitant are genuinely
  proved.
- `stability-families.yaml` revisions 56–67 are useful status history, not
  completion evidence. In particular revision 65 closes only the categorical
  restriction/equivalence shape, revision 67 explicitly says #1061 has no
  inhabitants, and the #1060 summary lists geometric witness obligations still
  open.
- PRs #1336, #1339, #1340, #1344, and #1346 are historical partial advances;
  their bodies explicitly leave geometric inhabitants or coherence open. A
  future agent should read those bodies before assuming a similarly named
  declaration closes an epic.
- `check_roadmap --require-api` exposes an inherited RM-07 defect: issue #854
  is CLOSED even though its merged PR #1392 explicitly says its shift/triangle
  and Ext obligations remain, while `dg-enhancements-e9` remains
  `in_progress`. This SF11 run must not repair that unrelated tracker state by
  changing the mathematics. The controller now scopes the roadmap gate to the
  manifest base ref, so the defect is reported as inherited and any SF11-authored
  roadmap drift still fails closed.
- The controller's original preflight rejected the exact planned issue branch
  that the manifest requires, even when `HEAD` was the clean `base_ref`. Commit
  `9e9f354a` removes that contradictory branch-name rejection; the exact-head,
  clean-worktree, and duplicate-PR checks remain the real safety conditions.
- The local and CI gate scripts originally validated only
  `.claude/loop-specs/sf8-sf9-pilot.yaml`. `scripts/validate_loop_specs.sh` now
  validates every YAML manifest, and the trust surface/CODEOWNERS explicitly
  cover loop specs, reviewer prompts, the run-loop skill, and `openspec/`.
- OpenSpec task 2.3 named a nonexistent `scripts/precheck.py`; the repository's
  actual local contract is `scripts/precheck.sh --no-build` plus a named
  targeted `lake build` invocation. Keep this distinction visible in future
  plans.
- New public declarations in a Families module also require an entry in the
  exact `scripts/AlgebraicGeometryAudit/StabilityConditionFamilies.lean`
  record. The SF11 manifest now includes that audit slice; omitting it lets a
  compiling change fail later in audit-completeness rather than at the frozen
  chunk boundary.

## Time-saving practices

- Use `scripts/precheck.sh` only with a changed-module/targeted Lean selection;
  never run `scripts/gates.sh` locally for this loop. CI remains the full
  repository verdict.
- Run OpenSpec structural/strict validation and the controller unit tests before
  spending time on Lean elaboration. Run the four adversaries on one frozen
  commit, record the ledger, and do not start an unbounded critique loop.
- Keep the protected-base ref explicit after every merge. A branch that is
  “based on main” by intent but not at the exact manifest ref will fail closed.
- Search the roadmap and the source module docstrings together; roadmap
  summaries contain the chronology, while module prose contains the current
  ownership and intentionally uninhabited seams.
- A cold `.lake` cache makes even a narrowly named Families target compile
  thousands of Mathlib prerequisites before reaching the changed modules. The
  first baseline attempt was interrupted after the cache reached roughly
  3,600 targets; treat that as cache warm-up, not as evidence that the whole
  repository target was run, and retain `LEAN_NUM_THREADS=2` for repeatable
  targeted builds.
- The full `StabilityConditionFamilies.lean` audit imports a much larger
  stability graph than the changed base-change modules need. For a local
  completeness check, a generated two-import audit can print only the changed
  declarations and still be passed through `check_audit.py` with its own
  command-count source. Avoid running that slice while another Lake build is
  compiling the same cache: concurrent workers can race on intermediate
  `.olean` paths and report misleading “file not found” failures.
