# Proposal

> **Superseded by #1473.** That PR delivers this change's goal: a passed ledger survives a
> moved protected base through change-bound review carry-over, with a bounded full-panel
> revalidation when the change or its dependencies move. It also closes #1469. The manifest
> `.claude/loop-specs/passed-ledger-head-revalidation.yaml` is disabled. Do not implement
> the tasks below; this plan is kept as history.

## Why

The loop controller can finish a passing review panel on an exact commit, then leave that work unpublishable when the protected base advances and a required rebase changes the head. The old pass must remain historical evidence, but the controller currently offers no safe, bounded way to review the new head without manually reopening or replacing the ledger.

This surfaced in the DT1 #928 progress chunk: its two-round panel passed on `7a41ba1`, but integration advanced the candidate to `3e0df10`; the active ledger correctly refused further reviews, while the old commit could not be published cleanly. The controller needs a transition that preserves the old panel, spends only an already-authorized remaining round, and grants no mutation authority until the new head passes a complete panel.

## What Changes

- Add an explicit, evidence-preserving transition from a passed ledger to one fresh review round per protected-base advance when a clean candidate is rebased onto the current protected base.
- Bind each round to the exact local HEAD and record the prior reviewed head, new head, base, ancestry, frozen selection, and timestamp without changing the manifest, planning digests, historical reviews, or round cap. Each transition consumes exactly the next pre-existing review slot; repeated transitions stop at the cap.
- Require live repository, protected-base, issue, remote-branch, and PR checks to succeed before changing the ledger; uncertain or malformed provider responses fail without writing.
- Block push and all PR/provider actions while the refreshed round is pending; only its complete exact-head passing panel can restore publication eligibility.
- Add focused state-transition, provider-failure, frozen-scope, and stale-shipping tests, plus workflow documentation and a separate three-round controller manifest.

## Capabilities

### New Capabilities

- `loop-engineering`: Evidence-preserving, bounded revalidation of a passed review ledger after its exact candidate head is replaced.

### Modified Capabilities

None. The repository has no archived main spec for the loop-engineering capability yet; this change establishes its first behavioral contract without modifying a historical delta.

## Impact

The change affects `scripts/loop_engine.py`, its focused tests, and loop-controller workflow documentation and manifest guidance. It does not change Lean mathematics or reopen #1458's already-capped integrity chunk. A separate controller tracking issue and a new frozen manifest are required before implementation review; #928 is the blocked consuming objective, not the controller feature's tracking issue.
