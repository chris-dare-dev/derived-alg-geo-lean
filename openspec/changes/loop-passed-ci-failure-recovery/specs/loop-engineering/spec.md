# Spec Delta

## Purpose

This capability lets the bounded loop controller admit a CI-driven code repair only from exact, live required-check evidence, while preserving prior reviews and consuming the chunk's original critique/revise budget.

## ADDED Requirements

### Requirement: CI-driven repair is admitted from exact required-check evidence

The controller SHALL distinguish a changed implementation review from protected-base-only revalidation. For an ordinary passed ledger, it SHALL admit a CI-driven repair only when the selected manifest and ledger still agree, the selected issue and exactly one matching open non-draft pull request remain in scope, and a check required by both the frozen manifest and live branch protection has a completed `failure` conclusion for the pull request's current full head SHA. The check result, provider pull-request head, and live source-branch head SHALL identify that same commit. Failure to read an unambiguous live protection/check snapshot SHALL reject admission. The controller SHALL read all returned same-head check-run attempts and SHALL NOT treat an older completed failure as current while a newer attempt is pending. The candidate repair commit SHALL descend from that failed-check head and remain within the frozen file scope. Recovery-managed ledgers and changes without qualifying CI evidence SHALL NOT use this transition.

#### Scenario: Required check failed on the current pull-request head
- **WHEN** an ordinary passed ledger's matching pull request is open and its current source head has a completed failure for a check required by both the frozen manifest and live branch protection, and a frozen-scope repair candidate descends from that head
- **THEN** the controller records the failure evidence and admits one full review panel for the repair candidate

#### Scenario: Failure belongs to an older or unrelated head
- **WHEN** a required check failed on a SHA different from the current pull-request head or source-branch head
- **THEN** the controller rejects the repair admission without changing the ledger or allocating a review round

#### Scenario: Check is absent, optional, pending, or cancelled
- **WHEN** no check required by both the frozen manifest and live branch protection has a completed failing result on the exact current pull-request head
- **THEN** the controller rejects the repair admission and does not treat missing, pending, cancelled, or unrelated check results as CI-failure evidence

#### Scenario: Newer check attempt is pending while an older failure completes
- **WHEN** an older required check attempt failed on the current head, but a newer same-head attempt is pending or its start order is ambiguous
- **THEN** the controller rejects repair admission without changing the ledger or allocating a review round

### Requirement: CI repair preserves history and consumes the frozen review cap

When admitting a CI-driven repair, the controller SHALL append an immutable event to the existing ordinary ledger's `ci_failure_repairs` array. The event SHALL identify its sequence number, prior passing round, current failed-check head, exact required-check identity/conclusion/run, matching pull request and source branch, proposed repair commit, recorded time, and disposition (`review_allocated` or `cap_exhausted`). The `rounds` array SHALL remain the sole review history and cap-counting root; every earlier review, finding, verdict, commit, adjudication, and round number SHALL remain unchanged. An allocated repair SHALL append a `ci_failure_repair` round at the next adjacent number, require every configured reviewer on the same full commit, and count against the original `max_review_rounds_per_chunk` cap; it SHALL NOT be classified as uncharged revalidation. If no ordinary slot remains, the controller SHALL still append the failure event with disposition `cap_exhausted`, set the existing ledger's status to `repair_exhausted`, retain the prior passed round as historical evidence, and refuse another panel or replacement ledger for that frozen chunk. `ledger init` SHALL search the repository's canonical `.loop-runs` tree for a ledger with the same frozen issue, issue slug, and chunk identity regardless of nested state directory; for manifests participating in this protocol, a requested state directory outside `.loop-runs` SHALL be rejected. The event SHALL be immutable; whether an allocated repair remains pending or is resolved SHALL be derived from the linked round and the latest ordinary ledger status, not from a second mutable state store.

#### Scenario: Repair consumes the next ordinary slot
- **WHEN** qualifying failure evidence exists and at least one original review slot remains
- **THEN** the controller appends the event, reserves the adjacent next review round for the repair commit, and counts that panel against the original cap

#### Scenario: Cap is already exhausted
- **WHEN** the required check failed after the last permitted ordinary review round passed
- **THEN** the controller records the failure without reopening review, leaves the chunk terminally non-publishable, and rejects a fourth panel or replacement ledger

#### Scenario: Repair round remains a complete adversarial panel
- **WHEN** a repair round is admitted
- **THEN** the four required reviewers must each provide captured, independent evidence for the same exact repair commit before adjudication can pass

### Requirement: Publication waits for a passing repair and green checks on its head

While the latest `ci_failure_repairs` event is `cap_exhausted`, or has an allocated repair round that has not yet been resolved by a passing ordinary round at or after it, the controller SHALL deny push, pull-request creation or attestation, ready-for-review, approval, merge, and issue closure for that chunk before any provider mutation. When no CI-repair event exists, existing initial draft-PR workflow remains available. The selected existing ledger is the canonical authority for these checks: `push` and `close` SHALL accept a required `--ledger`, and all action paths SHALL verify that ledger's manifest digest, frozen issue/chunk, and (for push) current issue branch agree. Missing, stale, mismatched, or ambiguous ledger resolution SHALL fail closed; the controller SHALL NOT add a parallel ledger registry. After a repair panel passes, publication SHALL remain bound to its reviewed full commit and the matching pull request, and merge eligibility SHALL require all current required checks to be green on the live pull-request head. The controller SHALL revalidate the pull-request head and check results immediately before merge. A successful check rerun on an unchanged already-reviewed head SHALL not consume a repair round when no repair transition has been recorded.

#### Scenario: Shipping is attempted before the repair panel passes
- **WHEN** any shipping action is requested while the repair round is pending, incomplete, or adjudicated needs-changes
- **THEN** the controller rejects the action before invoking a provider mutation

#### Scenario: Reviewed repair has green checks on the exact head
- **WHEN** the complete repair panel passes and all current required checks are green for the same live pull-request head
- **THEN** merge eligibility may proceed under the existing manifest mutation and merge policies

#### Scenario: CI rerun succeeds without a source change
- **WHEN** a required check initially failed but a later run succeeds on the same already-reviewed pull-request head and no repair round has been admitted
- **THEN** the existing passing panel remains usable subject to the live green-check and exact-head gates, and no review slot is consumed

#### Scenario: Generic revalidation cannot admit a changed implementation
- **WHEN** a post-pass candidate changes the reviewed implementation rather than only carrying the same reviewed change across a protected-base movement
- **THEN** the generic revalidation path rejects it and requires exact required-check evidence through the charged CI-repair transition

#### Scenario: CI repair has exhausted the original cap
- **WHEN** a qualifying failure is observed after every ordinary review slot has been consumed
- **THEN** the same ledger records a `cap_exhausted` event and `repair_exhausted` status, preserving the prior pass while every publish, close, review, and replacement-ledger path remains denied

#### Scenario: Alternate state directory cannot replace an exhausted ledger
- **WHEN** ledger initialization is attempted for the same frozen issue, issue slug, and chunk under another nested `.loop-runs` state directory, or outside `.loop-runs`
- **THEN** the controller finds and preserves the canonical prior ledger or rejects the unsupported path, and does not create a replacement ledger
