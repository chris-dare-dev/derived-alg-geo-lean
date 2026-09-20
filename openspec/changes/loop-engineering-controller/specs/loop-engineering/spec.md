# Spec Delta

## Purpose

This capability makes a small, review-heavy Lean formalization batch auditable,
bounded, and safe to run without pausing for every routine provider action.

## ADDED Requirements

### Requirement: A run has a frozen, OpenSpec-backed scope

The controller SHALL reject a run manifest unless it names two or three issues,
references a valid OpenSpec change with proposal, delta specs, design, and
numbered tasks, and gives every implementation chunk an immutable file list and
acceptance statements.

#### Scenario: Valid disabled pilot is inspectable

- **WHEN** the controller validates a disabled pilot manifest and all referenced
  OpenSpec artifacts exist
- **THEN** it reports the manifest, OpenSpec change, issue count, reviewers, and
  review-round cap without authorizing remote actions

#### Scenario: Scope drift is rejected

- **WHEN** an existing ledger is used after the manifest or referenced OpenSpec
  artifact changes
- **THEN** the controller refuses approval and reports that the frozen scope or
  plan digest no longer matches

### Requirement: Each chunk receives independent bounded review

The controller SHALL require mathematical, repository-boundary, abstraction,
and Lean/mathlib-style reviewers to record verdicts for the same commit before
adjudication, and SHALL allow no more than five review/improve rounds for one
frozen chunk.

#### Scenario: Passing panel

- **WHEN** every required reviewer records `pass` for the same commit
- **THEN** adjudication may mark the chunk passed and the ledger records the
  reviewer identities, findings, commit, and timestamp

#### Scenario: Fifth round still needs changes

- **WHEN** a fifth review round is adjudicated as needing changes
- **THEN** the ledger marks the chunk blocked and refuses to create a sixth
  review round

#### Scenario: A reviewer tries to review a different commit mid-round

- **WHEN** a required reviewer submits a verdict for a different commit before
  the current round is adjudicated
- **THEN** the controller refuses the submission and preserves the open round

### Requirement: Preflight fails closed before remote mutation

The controller SHALL perform a read-only preflight that checks a clean checkout,
the exact protected-base reference, remote repository identity, provider
authentication, open and unblocked issues, dependency order, branch/PR
collisions, and configured repository gates before enabling a run.

#### Scenario: Disabled or stale pilot

- **WHEN** a pilot is disabled or its preflight finds any failure
- **THEN** no provider mutation is attempted and the command exits with a
  machine-detectable non-success status

#### Scenario: A required check is absent

- **WHEN** a pull request lacks one of the manifest's required checks
- **THEN** approval and merge commands refuse to run

### Requirement: Remote actions are independently authorized

The controller SHALL expose comments, issue closure, branch pushes, pull-request
creation, approval, and merge as separate actions controlled by explicit manifest
booleans, and SHALL refuse code-issue closure unless a referenced pull request
is confirmed merged unless non-PR closure was explicitly enabled.

Each frozen chunk SHALL declare either `complete` or `progress` closure mode.
Complete chunks SHALL require a closing keyword for their issue in the PR body.
Progress chunks SHALL require explicit `spec.closure.allow_progress_pr` enablement,
a non-closing issue reference, and no closing keyword.

#### Scenario: Safe code-issue closure

- **WHEN** issue closure is requested with a pull request that the provider
  reports as merged
- **THEN** the controller may close the issue if the close capability is enabled

#### Scenario: Unmerged closure attempt

- **WHEN** issue closure is requested without a merged pull request and non-PR
  closure is disabled
- **THEN** the controller refuses to close the issue

#### Scenario: Progress PR does not close its issue

- **WHEN** an explicitly authorized progress chunk creates a PR whose body says
  `Refs #N` (or another recognized non-closing reference)
- **THEN** the controller permits PR creation but refuses any closing keyword
  and leaves issue #N open for subsequent frozen chunks

#### Scenario: Merge capability is explicitly shaped

- **WHEN** a run requests a merge method, auto-merge, administrator merge, or
  branch deletion
- **THEN** the controller permits that behavior only when the corresponding
  merge-policy setting is enabled, binds the command to the reviewed PR head,
  and never infers an administrator bypass from a failed required check

#### Scenario: Progress dependencies remain blocked

- **WHEN** a downstream issue depends on a passed ledger whose chunk is marked
  `progress`, or whose upstream issue is still open
- **THEN** ledger initialization refuses to start the downstream chunk until a
  complete upstream chunk has merged and the provider reports the issue closed

#### Scenario: Reviewed head accepts a Git revision abbreviation

- **WHEN** the ledger records a valid short or full revision that local Git
  resolves to the provider-reported full PR head SHA
- **THEN** approval and merge treat it as the same reviewed head; an unresolved,
  ambiguous, or different revision is still rejected

### Requirement: OpenSpec remains the planning source of truth

The repository SHALL keep proposals, requirements with scenarios, designs, and
task checklists under `openspec/`, and the loop controller SHALL treat those
artifacts as inputs rather than silently replacing them with chat-only scope.

#### Scenario: Plan-first implementation

- **WHEN** a loop starts applying a change
- **THEN** the implementation is traceable to checked-in OpenSpec artifacts and
  the task ledger can identify the relevant acceptance statements
