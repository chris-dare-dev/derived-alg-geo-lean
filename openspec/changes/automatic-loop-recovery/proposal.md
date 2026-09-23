# Proposal

## Why

Three failed critique/revise rounds currently stop the entire objective and
require human triage. The owner requests automatic evidence-producing research
and independently checked replanning, preserving adversarial accuracy and all
failed history while enabling AUT1/Serre work to resume under another model.

## What Changes

- Introduce optional bounded recovery for a frozen objective: exhaustion queues
  investigation; independent acceptance of a concrete recovery plan admits a
  successor attempt with the original acceptance and all findings inherited.
- Retain three rounds per attempt and cumulative limits across every attempt,
  including abandoned partial panels, plan revisions, and imported history.
- Persist actionable next steps for the supervising agent, rather than adding
  a status that still needs the user to dispatch research.
- Reconcile active guidance, document migration from C3/#1458 and predecessor
  #1451, record provenance hazards, and provide a Luna handoff.
- Keep provider capabilities separate. Failed attempts and research approvals
  cannot authorize publication. Legacy manifests do not silently opt in.

## Capabilities

### New Capabilities

- `automatic-loop-recovery`: bounded autonomous research and resumption with
  immutable failed history, inherited findings, and independent acceptance.

### Modified Capabilities

None: the canonical main-spec inventory is empty; existing controller deltas
remain historical context.

## Impact

Python controller/state-machine tests, loop manifest documentation, run-loop
and reviewer instructions, AGENTS/CLAUDE/CONTRIBUTING, and OpenSpec configuration.
No Lean declarations, mathematical assumptions, ownership roots, or external
service dependencies change. Repairing C3's production defects is a subsequent
recovery task, not silently included here. This implementation is based on
`origin/main` at `b8306d6b`, not on C3's unpublished controller modifications.
