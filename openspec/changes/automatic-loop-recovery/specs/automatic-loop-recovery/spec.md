# Spec Delta

## Purpose

Continue an authorized objective through bounded research and replanning when
its current attempt exhausts adversarial review, without erasing failed evidence.

## ADDED Requirements

### Requirement: Exhaustion schedules automatic investigation

An opted-in objective SHALL retain a maximum of three review rounds per
attempt. Exhaustion SHALL preserve the failed attempt and expose an actionable
research dependency to the supervising loop agent, without routine user approval.

#### Scenario: Third failed panel
- **WHEN** the third complete panel requires changes
- **THEN** the attempt stays failed and the next action is investigation if budget remains

#### Scenario: Missing reviewer
- **WHEN** a reviewer fails to return on an unchanged candidate
- **THEN** the supervisor retries that missing role within the same reserved round and never invents a passing verdict

### Requirement: Recovery requires independent evidence review

The system SHALL require a structured diagnosis, concrete evidence, a changed
strategy, verification checks, and a complete inherited finding list. An
independent reviewer SHALL accept that exact plan before a successor can start.
Plan revisions SHALL have a finite limit and consume the same episode.

#### Scenario: Rejected plan
- **WHEN** a plan omits a finding or lacks evidence
- **THEN** no successor is admitted

#### Scenario: Plan author tries self-approval
- **WHEN** the researcher or implementer submits the recovery acceptance
- **THEN** acceptance is rejected

### Requirement: Acceptance and findings survive every attempt

Every successor SHALL preserve the original scope, requirements, reviewers and
acceptance. Failed review messages SHALL remain verbatim under stable identities.
Final passing reviews SHALL explicitly account for inherited negative findings.
Research acceptance SHALL NOT authorize publication or satisfy code review.

#### Scenario: Superficial fresh start
- **WHEN** an agent changes the chunk, state path, session or worktree to reset a registered objective
- **THEN** the controller rejects initialization rather than replenishing its budget

#### Scenario: Passing code review omits an old blocker
- **WHEN** a successor panel passes without evidence addressing inherited findings
- **THEN** the objective cannot become publishable

### Requirement: Total recovery effort is finite and durable

An objective SHALL bound recovery episodes, total allocated review rounds,
plan submissions and elapsed execution time. History and abandoned partial
rounds SHALL consume the original allowance. Restarting SHALL preserve counts.
Budget exhaustion SHALL park only this objective and direct the supervisor to
other authorized work.

#### Scenario: Partial panel is abandoned
- **WHEN** investigation starts after a partially reviewed candidate
- **THEN** the reserved panel remains charged

#### Scenario: Budget is exhausted
- **WHEN** no aggregate review, episode, plan or elapsed allowance remains
- **THEN** the next action parks this objective without granting a new allowance

### Requirement: Historical adoption is explicit and preserves provenance

Importing a terminal ledger SHALL preserve its exact snapshot, review evidence
and counted rounds. The manifest SHALL declare the complete supplied historical
inventory by content digest. Unreadable or mismatched history SHALL fail closed.
Fresh policy allowance SHALL be explicit and historical totals remain visible.

#### Scenario: Adopt C3 and predecessor history
- **WHEN** a run declares and supplies their exact historical records
- **THEN** the records remain unchanged and their rounds count before recovery admission

### Requirement: Recovery does not expand provider authority

Existing manifests SHALL retain their current behavior unless explicitly
configured for recovery. Recovery-managed publication SHALL require an exact
current passing commit and inherited finding dispositions, in addition to
existing manifest actions and provider checks. Controller changes SHALL NOT
silently enable a disabled execution manifest.

#### Scenario: Publish during research
- **WHEN** an objective is investigating or its plan alone is accepted
- **THEN** publication is rejected
