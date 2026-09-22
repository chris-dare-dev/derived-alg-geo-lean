# Tasks

## 1. Recovery implementation

Frozen chunk: automatic-loop-recovery-core. Files: `scripts/loop_engine.py`,
`scripts/loop_recovery.py`, `scripts/tests/test_loop_recovery.py`,
`scripts/tests/test_loop_engine.py`, `.claude/loop-specs/README.md`,
`.claude/skills/run-loop/SKILL.md`, `.claude/agents/*adversary.md`,
`.claude/agents/mathlib-reviewer.md`, `AGENTS.md`, `CLAUDE.md`,
`CONTRIBUTING.md`, `openspec/config.yaml`, this change's artifacts and
`docs/architecture/loop-recovery.md`. Acceptance: all six requirements and their
negative scenarios pass; legacy tests remain green. Max three formal panels.

- [x] 1.1 Implement bounded recovery, inherited findings and immutable attempt history; verify focused state-machine tests.
- [x] 1.2 Integrate CLI registration, next actions, historical adoption and publication guards; verify end-to-end temporary-repository tests and legacy loop tests.
- [x] 1.3 Align active policy, supervisor and reviewer guidance; verify documented commands and strict OpenSpec validation.

## 2. Review and handoff

- [x] 2.1 Run focused Python tests and applicable static prechecks, and record exact outcomes; no Lean build is needed because no Lean code changes.
- [x] 2.2 Freeze a commit and collect all four independent review lenses, with at most three review/improve rounds; capture verbatim evidence and outcomes.
- [x] 2.3 Deliver a Luna handoff containing branch, commit, verification, review evidence, C3/predecessor inventory and executable continuation commands; record actual PR/CI state rather than assuming local checks imply CI.

Execution evidence is local under `.loop-runs/automatic-recovery-review/`;
the session handoff is this directory's ignored `HANDOFF.md`. C1 completed all
four lenses and required changes; its findings have regressions in the second
candidate. Checklist completion records the work products, not code acceptance:
only a complete passing panel bound to the current SHA permits publication.
