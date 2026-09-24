# Spec Delta

## Purpose

Collect complete, revision-bound GitHub CI observations so downstream admission logic can distinguish verified required checks from missing work and unhealthy auxiliary checks.

## ADDED Requirements

### Requirement: Current provider identity
The collector SHALL derive the protected base, PR head, tested candidate commit and tree, event, ref, primary workflow run and attempt from authenticated provider responses and immutable Git objects. It MUST recheck the current base and head before returning an admission-capable record and MUST NOT accept caller-supplied revision values as trust anchors.

#### Scenario: Current pull request candidate
- **WHEN** the provider reports a current PR base and head, a completed CI run on a candidate, and Git objects that establish the candidate's required parent relationship
- **THEN** the collected record binds those exact revisions, tree, event, ref, run and attempt for schema v4 validation

#### Scenario: Head or base moves during collection
- **WHEN** the PR head or protected base differs on the final provider read
- **THEN** the collector denies a current required-CI claim and reports which identity moved

#### Scenario: Candidate relationship is unproved
- **WHEN** the tested commit, tree, event/ref or parent relationship cannot be established from provider data and Git objects
- **THEN** the collector fails closed instead of substituting the PR head or a locally synthesized merge commit

### Requirement: Complete and distinct observations
The collector SHALL enumerate every page of candidate check suites, check runs and commit statuses needed by the inventory, preserving each provider ID, producer, workflow run and attempt. It MUST reject incomplete enumeration and ambiguous same-name observations; name or latest timestamp alone MUST NOT select a required result.

#### Scenario: Multiple check-run pages and a commit status
- **WHEN** candidate observations span multiple provider pages and include a commit status whose name matches a check run
- **THEN** all pages are included and the status and check run retain separate provider and run identities

#### Scenario: Truncated or ambiguous provider results
- **WHEN** a page is missing, a provider count disagrees with the collected set, or two observations cannot be disambiguated by verified producer and run attempt
- **THEN** the collector emits no required-CI verified claim

#### Scenario: Rerun supersedes a failure
- **WHEN** two attempts belong to the same verified workflow run on the exact candidate and the later attempt completed successfully
- **THEN** the record identifies the selected attempt and preserves the earlier attempt as non-authorizing history

### Requirement: Protected policy and gate coverage
The collector SHALL read the inventory from the current protected base revision and compare its required contexts with live branch protection. A PR-authored inventory change MUST NOT remove a required gate from the collected policy.

#### Scenario: Required contexts agree
- **WHEN** live protection requires the inventory's declared required contexts and the corresponding candidate observations are successful
- **THEN** the collector may submit the record to the existing schema v4 validator

#### Scenario: Unknown required context
- **WHEN** live protection requires a context absent from the trusted-base inventory, or the provider cannot return protection metadata
- **THEN** the collector denies a required-CI verified claim and names the unaccounted or unavailable policy input

### Requirement: Honest evidence and claims
The collector SHALL produce schema v4 evidence with provider-sourced observation identifiers, candidate pin digests and content hashes for its retained observation payloads. It MUST run the existing validator with independently obtained base, head and inventory anchors. It SHALL report required-CI verification separately from auxiliary health, merge readiness and post-merge health.

#### Scenario: Required CI succeeds while auxiliary check fails
- **WHEN** all required candidate gates pass and an optional security check fails
- **THEN** the record may report required-CI verified while retaining an auxiliary warning and MUST NOT report all pipelines green

#### Scenario: Required work is absent or non-successful
- **WHEN** a required gate is missing, pending, failed, cancelled, timed out or unexpectedly skipped
- **THEN** the collector reports no required-CI verified claim, with the raw provider outcome visible

#### Scenario: Missing pin or observation payload
- **WHEN** a candidate pin blob or the bytes behind a claimed observation hash cannot be obtained
- **THEN** the collector fails closed rather than emitting a placeholder digest

### Requirement: Read-only operation and explicit boundary
The collector SHALL use read-only provider and Git operations. Its output MUST NOT authorize a merge, assert independent reviewer approval, or claim post-merge health.

#### Scenario: Read-only current-PR exercise
- **WHEN** an operator runs the collector against an open PR with suitable read credentials
- **THEN** it returns a validation result and evidence without changing PR, branch-protection, workflow or issue state

#### Scenario: Provider access fails
- **WHEN** authentication, permission, rate limiting, timeout or malformed provider data prevents a complete read
- **THEN** the collector exits unsuccessfully with an actionable error and no passing admission claim
