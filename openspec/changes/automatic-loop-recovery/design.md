# Design

## Context

See proposal.md. The production controller is a CLI; the supervising agent is
the executor. The user explicitly authorizes implementing the researched policy
and eliminating routine permission pauses. Historic C3 remains terminal.

## Goals / Non-Goals

Goals: automatic next actions, bounded retries and research, inherited evidence,
independent recovery acceptance, and an exact handoff usable by Luna.
Non-goals: cryptographic attestations, a remote service, proving a local human
cannot bypass the CLI, mathematical API changes, repairing C3 in disguise, or
implicitly merging this work. No Lean ownership/import/instance changes apply.

## Decisions

- Extend the existing ledger with a recovery envelope; archive exhausted
  attempts inside it when an accepted plan admits a successor. The original
  selected contract is preserved, while each attempt has at most three rounds.
  A pure Python helper owns recovery transitions and validation; loop_engine
  owns filesystem/provider integration. This keeps one review ledger owner.
- The manifest opts in with stable objective identity, implementer identity,
  investigator-reviewer separation, episode/round/plan/time limits, and a
  digest-pinned historical inventory. Defaults are two episodes, nine total
  review allocations, two plan submissions per episode, and one week of wall
  time; all are explicit bounded configuration. Historical rounds are included,
  not discarded. No child task gets a separate allowance: investigations and
  sequential repair subtasks stay within the same objective and frozen scope.
- Register an opted-in objective in the repository's shared Git directory.
  Changing its state directory, worktree, chunk name, or manifest ID cannot
  initialize another copy for the same issue. A recovery manifest has exactly
  one issue and one frozen chunk. Separate issue objectives remain independent.
  The registry owns the canonical ledger; the local state file is an exported
  cache. Reinitialization restores that cache without replenishing budgets.
  Canonical writes precede cache writes, under a shared repository lock.
- A plan captures failure class, reproduction evidence, diagnosis, changed
  strategy, checks and exact inherited finding IDs. Its independent review
  binds the exact plan digest. Rejections permit only the same episode's
  remaining submissions. Source revisions are reviewed normally after resume.
- Use each negative verbatim review and prior lift obligation as an indivisible inherited finding;
  deterministic identities prevent omission of individual criticisms embedded
  in that message. All passing reviewers explicitly account for the inherited
  corpus, with evidence; the controller checks structure and binding while
  independent reviewers judge substance. Machine checks do not prove cognition.
  Fresh passing-panel lifts use the live backlog gate, without requiring earlier
  reviewers to resolve not-yet-submitted messages. All carried lifts require a
  durable backlog disposition, and their scope authorization remains bounded
  by the current original manifest's declared prefixes.
- Reserve a review slot before dispatch using a controller command. Empty or
  incomplete panels keep that slot; retries do not erase genuine negative
  results. Only a full same-commit panel can pass. Persist writes atomically
  and serialize CLI mutations; next actions derive from validated stored state.
- The supervisor consumes next actions (implement, review missing roles, revise,
  investigate, review plan, resume, publish or park). It checks remaining time
  before dispatch and caps worker duration accordingly. Parking affects this
  objective only. There is no background daemon to install.
- Recovery-aware action gates reject failed/partial/unresolved state and bind
  the exact local or remote reviewed head. Existing mutation capabilities
  remain separate. Existing manifests are not retroactively rewritten.

## Risks / Trade-offs

- Local records are not authenticated attestations: preserve provider gates,
  exact commit binding and independent reviews; malicious operators are outside
  the threat model.
- Broad work becomes expensive: prefer smaller diagnosis/probes, bound total
  effort, and record why the prior method failed before granting more attempts.
- Stale five-round prose: reconcile active generic instructions; historical
  changes retain their recorded caps. No fourth round exists within an attempt.
- New recovery code cannot validate itself into publication: review this
  policy/controller change independently, preserving original C3 snapshots.

## Migration Plan

Build on current main without importing unpublished C3 source. Validate the new
state machine, CLI and normal legacy tests. Run mathematical/source,
repository-boundary, abstraction and style adversaries on the same commit,
with at most three review/improve rounds for this implementation. Document
publication/CI state without claiming local checks are CI. Handoff identifies
the C3 and #1451 evidence inventory and the next research task; Luna can adopt
that history explicitly with the new policy, then resume AUT1/Serre work.

## Explicit bootstrap recovery adoption after the initial cap

The preceding migration paragraph and original task checklist imposed three
panels for this implementation. That initial attempt is terminal after C1–C3;
this text does not retroactively reinterpret or erase that narrower wording.
The user's standing instruction separately authorizes exhaustion followed by
automatic research and independently admitted recovery. Applying that policy
here was independently audited in `recovery_admission_audit`, outside the
controller under review. The accepted plan is `recovery-research.md`, raw
SHA-256 `b95deec2072fe8634f6adc991eb1a9f8c21f41c0067c20b7c99e0d0ac760993f`.

The external `.loop-runs/automatic-recovery-review/objective.json` preserves
all twelve verbatim reviews, the three commits and original contract reference.
It records episode 1/submission 1 acceptance and admits attempt 2 without
changing scope or any acceptance requirement. Limits are three panels per
attempt, nine aggregate allocations including the initial three, two episodes,
two plans per episode, and a fixed conservative deadline of
2026-09-29T00:00:00Z (start 2026-09-22T00:00:00Z). No candidate-controller
command grants its own acceptance. Every successor panel reviews the complete
accumulated candidate and inherited findings; publication still needs all four
independent passing lenses on the same exact SHA.

The researched correction separates stored ledger evidence from claims about
shipped artifacts. Recovery backlog checks at adjudication and publication use
one explicit reviewed-commit ordinary Git blob, never HEAD/worktree fallback.
Complete visible exact-target rows distinguish dispositions from prose or
fenced examples. The legacy helper remains unchanged outside recovery mode.
Real Git fixtures cover dirty-only/later-HEAD evidence, missing objects,
symlinks, stale review sources, and all publication paths. A newly discovered
lift needing a new backlog commit requires another charged panel; it cannot
silently alter the frozen SHA. The immutable research report's C1-era start
description is historical; execution uses the tighter conservative bound above.
