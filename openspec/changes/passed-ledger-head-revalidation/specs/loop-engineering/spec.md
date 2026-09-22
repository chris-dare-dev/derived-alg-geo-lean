# Spec Delta

## Purpose

Preserve bounded review evidence while allowing a passed candidate to be reviewed again when protected-base movement makes its old reviewed head stale. This capability must never turn a stale pass into publication authority.

## ADDED Requirements

### Requirement: New ledgers pin the protected base used for review
When initializing a new ordinary review ledger, the controller MUST record the full protected-base OID resolved from the frozen manifest and bind each ordinary review round to that OID. Initialization MUST fail without writing if the checkout HEAD does not equal the resolved protected base. A revalidation event MUST bind its reserved round to the newly resolved live protected-base OID. The controller MUST NOT silently backfill or rewrite base evidence in an existing ledger.

#### Scenario: Fresh ledger starts from its exact protected base
- **WHEN** a new ledger is initialized from a clean issue branch whose HEAD equals the manifest's resolved protected base
- **THEN** the ledger and its first review round record that full base OID

#### Scenario: Stale initialization checkout
- **WHEN** the manifest's protected-base ref differs from HEAD during ledger initialization
- **THEN** initialization fails without creating or changing a ledger

### Requirement: Refreshing a passed candidate consumes one frozen review slot
The controller MUST permit a revalidation only from a complete passing round when the candidate head has changed, the most recent pass is not already pending revalidation, and at least one review round remains under the original frozen cap. Each accepted revalidation MUST consume exactly the next numbered slot. The controller MUST NOT reset or enlarge the cap, rewrite any prior round, refresh an in-flight round, or refresh after a terminal blocked or needs-changes outcome.

#### Scenario: Revalidation uses the next available slot
- **WHEN** a complete non-final round passes and a clean candidate has been rebased onto a newer protected base
- **THEN** the controller records a new revalidation event and pins exactly the next empty review round to the candidate's current full commit identifier

#### Scenario: No slot remains
- **WHEN** a passed candidate needs revalidation but its frozen review-round cap is exhausted
- **THEN** the controller rejects revalidation without changing the ledger, cap, or review history and denies publication

#### Scenario: Refresh cannot replace an in-flight or terminal round
- **WHEN** a review round is pending, or the last outcome is blocked or needs-changes
- **THEN** the controller rejects revalidation without changing the ledger

### Requirement: Revalidation preserves an append-only evidence chain
The controller MUST preserve all existing manifest bindings, frozen selections, review rounds, verdicts, findings, and timestamps. It MUST append a revalidation event that identifies the prior complete passing round and head, the next round and exact new head, and the protected-base evidence used for admission. At admission, the event MUST point to exactly one adjacent next round that is empty, unadjudicated, and pinned to the new full commit identifier; after that round passes, it may be the prior round of a later event. Every event MUST be adjacent to its prior round, and no event may skip, reuse, or replace a round. The prior and new heads MUST be distinct full commit identifiers; each MUST have exactly one parent, the prior head's parent MUST be a strict ancestor of the newly resolved protected base, and the new head's parent MUST equal that protected base. Ledger validation MUST reject missing, duplicated, out-of-order, or inconsistent revalidation evidence.

#### Scenario: Valid refresh retains prior evidence and reserves an empty round
- **WHEN** revalidation is accepted
- **THEN** every pre-existing review record and frozen binding remains byte-for-byte equivalent in value, and one event plus exactly one adjacent empty, unadjudicated round pinned to the new head are appended

#### Scenario: Forged or inconsistent refresh history
- **WHEN** a ledger contains an event whose prior round did not pass, whose next round is not empty while first reserved, whose full commit identifiers or parent/base ancestry disagree, or whose round numbers/order are inconsistent
- **THEN** the controller rejects the ledger for review and publication actions

#### Scenario: Reserved refreshed round later fails
- **WHEN** a previously empty reserved round is reviewed and adjudicated needs-changes or blocked
- **THEN** the event and failed round remain valid immutable history, the ledger becomes terminal as required by the cap, and no replacement event or round can erase that result

### Requirement: Revalidation admission fails closed on repository or provider uncertainty
Before changing the ledger, the controller MUST establish from live repository and provider evidence that the candidate is a clean checkout at the exact local full head, is a single-parent direct child of the current protected base, remains within the original frozen file scope, and preserves the original issue, repository, remote, branch, and plan bindings. For a ledger that records the prior round's base OID, that OID MUST be a strict ancestor of the current protected base and MUST match the prior head's ancestry evidence. For a legacy ledger without a recorded base OID, the controller MUST mark the base as inferred from the prior head's sole parent and require that parent to be a strict ancestor of the current protected base while the prior head itself is not an ancestor of it; this is a conservative Git-graph admission criterion, not proof of the historical protected-base OID. The issue MUST be open. A complete source-branch pull-request lookup MUST find either no associated pull request or exactly one open, non-draft pull request whose frozen base, body satisfying the manifest's frozen closure mode, source branch, and head OID agree with the ledger's previous passing round; closed, merged, multiple, or differently bound PRs reject the transition. The local protected-base ref MUST equal the live protected-base OID. The remote source ref MUST be absent, equal to the prior reviewed head, or equal to the proposed new head; replacing the prior reviewed head later requires an explicit manifest force-with-lease permission bound to that exact prior SHA. Any absent, malformed, ambiguous, truncated, stale, or failed check MUST reject revalidation without writing to the ledger.

#### Scenario: Eligible rebased candidate
- **WHEN** all local and live checks agree on the open issue, protected base, exact candidate head, source branch, remote repository, and frozen scope
- **THEN** the controller may append the revalidation event and reserve the next round

#### Scenario: Existing pull request is still exactly bound to the previous pass
- **WHEN** exactly one open, non-draft PR is associated with the frozen source branch and its base, body satisfying the manifest's frozen closure mode, and head OID match the prior passing round
- **THEN** revalidation may reserve the next round without changing the PR, and no PR shipping action is allowed until that round passes and the PR's live head is verified against it

#### Scenario: Legacy ledger has no recorded base OID
- **WHEN** a legacy passed round lacks base metadata but its reviewed commit has one parent that is a strict ancestor of the live base, while the reviewed commit itself is not contained in that base
- **THEN** the controller may admit only under the explicitly recorded inferred-base criterion and MUST NOT claim that the old base OID was historically proven

#### Scenario: Provider response is uncertain
- **WHEN** an issue lookup, protected-base lookup, source-branch pull-request lookup, or remote identity check fails or returns malformed or ambiguous data
- **THEN** the controller rejects revalidation and leaves the ledger unchanged

#### Scenario: Source branch cannot be safely reconciled
- **WHEN** the remote source ref differs from both the prior reviewed head and proposed candidate, or it equals the prior reviewed head but the frozen manifest does not authorize an exact expected-head lease
- **THEN** the controller rejects revalidation without consuming a review slot

#### Scenario: Existing pull request is stale, ambiguous, or terminal
- **WHEN** an associated PR is closed, merged, duplicated, draft, or does not match the previous passing head, frozen base, and issue
- **THEN** the controller rejects revalidation and leaves the ledger unchanged

#### Scenario: Candidate has unrelated changes or lacks the required ancestry
- **WHEN** the checkout is dirty, either commit is a merge commit, the candidate's sole parent is not the live protected base, the prior head's parent is not a strict ancestor of that base, or the candidate diff escapes the frozen scope
- **THEN** the controller rejects revalidation and leaves the ledger unchanged

### Requirement: Pending revalidation grants no shipping authority
While a revalidation round is pending, the controller MUST reject push, pull-request creation or attestation, approval, merge, and issue closure before performing any provider mutation. A prior pass MUST NOT authorize any shipping action when local HEAD differs from the latest complete passing round, or when an unaccounted protected-base advance has made that round stale. After a refreshed panel passes, the controller MUST allow push only for the exact reviewed local head and frozen source branch; an existing remote branch may be updated only if absent or still at the immediately prior reviewed head, using an exact expected-head lease, and the resulting remote head MUST be re-read as the new reviewed head. Pull-request creation, attestation, approval, and merge MUST require the live remote branch/PR head to equal the latest passing commit and the protected base to remain the base recorded by that passing round. Issue closure MUST require the matching PR to be merged from the latest passing commit and its merge commit to be reachable from the live protected base; it MUST NOT mistake that exact merge for stale-base drift.

#### Scenario: Shipping is blocked during a refreshed review
- **WHEN** a revalidation round is pending and any shipping action is requested
- **THEN** the action fails before invoking its provider mutation

#### Scenario: Old pass points to a stale local or remote head
- **WHEN** the ledger's last passing commit differs from local HEAD or the source branch's live remote head
- **THEN** pull-request creation, attestation, approval, merge, and issue closure are denied before provider mutation; push is permitted only after a fresh exact-head passing panel and only under the safe remote-update rule above

#### Scenario: Protected base advances after a passing panel
- **WHEN** the protected base advances after the latest panel passes but before merge and the PR is absent or exactly bound to the prior passing head
- **THEN** push, pull-request creation, attestation, approval, and merge fail before mutation until the candidate consumes a remaining review slot and passes a complete panel on a direct child of the new base

#### Scenario: Fresh panel can publish and close only its own merged change
- **WHEN** the refreshed panel passes, the remote branch and any existing PR head equal its reviewed SHA, the protected base has not advanced before merge, and the PR is later merged with that head
- **THEN** publication proceeds under existing provider policy, and closure is allowed only for that issue and PR when its merge commit is reachable from the live protected base

#### Scenario: Previously reviewed remote ref is updated only under its exact lease
- **WHEN** the refreshed panel passes and the remote source ref still equals the immediately prior reviewed SHA
- **THEN** push is allowed only under the frozen manifest's explicit force-with-lease permission naming that exact expected SHA, and the controller verifies the remote ref equals the newly reviewed SHA afterward

#### Scenario: Close is denied for a different or stale merged PR
- **WHEN** issue closure is requested but the supplied merged PR does not have the final passing reviewed SHA, does not close the frozen issue, or its merge commit is not reachable from the protected base
- **THEN** closure fails before invoking the issue-close mutation

### Requirement: Revalidation remains bounded across repeated protected-base advances
After a refreshed round passes, the controller MAY accept another revalidation only if a newer protected-base advance makes that newly reviewed head stale and another original review slot remains. Each such event MUST consume the next adjacent slot. If the cap is reached, or the refreshed round does not pass, the controller MUST stop rather than reopen the ledger or grant publication authority to a stale head.

#### Scenario: A later base advance consumes the next slot
- **WHEN** the latest refreshed round passes and the protected base advances again before publication
- **THEN** the controller may append one further event and reserve exactly the next empty round, subject to the original cap and the same admission checks

#### Scenario: Base advances after the cap is exhausted
- **WHEN** the protected base advances after the final allowed review round has passed
- **THEN** the controller refuses revalidation and all shipping actions remain denied

#### Scenario: The final refreshed round does not pass
- **WHEN** the last available refreshed round is adjudicated needs-changes
- **THEN** the ledger becomes terminal blocked, retains every prior event and finding, cannot reserve a fourth round, and grants no shipping authority
