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
