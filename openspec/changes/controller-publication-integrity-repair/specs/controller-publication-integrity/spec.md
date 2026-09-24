# Spec Delta

## Purpose

This capability makes loop-controller review evidence reconstructable and makes
publication actions fail closed when their reviewed scope, current repository
authority, or provider snapshots are stale or incomplete.

## ADDED Requirements

### Requirement: Ledger authority is reconstructed from the validated selection

Before using a ledger for review, adjudication, dependency, or publication, the
controller SHALL reconstruct the issue and frozen chunk from the validated
manifest. It SHALL reject a ledger whose copied scope, frozen files, lift
targets, acceptance, closure mode, reviewer roster, review cap, manifest digest,
or OpenSpec digest differs from that selection.

The controller SHALL validate review rounds as a contiguous sequence within
the cap. Each round SHALL have one commit, exactly one authorized review per
required reviewer, captured reviewer evidence bound to that commit, and an
adjudication consistent with the round and terminal ledger status.

#### Scenario: Copied ledger scope is mutated

- **WHEN** a ledger changes its selected issue, chunk, files, reviewer roster,
  cap, or requirement while the validated manifest remains unchanged
- **THEN** every ledger-dependent operation rejects the ledger before relying
  on the copied value

#### Scenario: Forged terminal history is incomplete

- **WHEN** a ledger claims passed but skips a round number, exceeds its cap,
  omits or duplicates a reviewer, mixes reviewed commits, lacks captured
  evidence, or contradicts its last adjudication
- **THEN** the controller rejects the ledger and performs no dependent action

#### Scenario: Complete panel is accepted

- **WHEN** the reconstructed selection and digests match and a contiguous,
  commit-coherent history contains the complete passing panel within the cap
- **THEN** a separately authorized action may consume that ledger

### Requirement: Reviewer evidence has an exact terminal binding

A formal reviewer output SHALL contain exactly one full-SHA
Reviewed commit: <sha> line matching the round commit, immediately followed
by exactly one terminal Close: <verdict> line matching the recorded verdict.
The controller SHALL reject a missing, abbreviated, mismatched, duplicated, or
contradictory marker, a bare verdict without the required markers, and any
text after the terminal close line.

#### Scenario: Review evidence binds to the candidate

- **WHEN** a reviewer supplies one matching full commit marker followed
  immediately by the matching final verdict line
- **THEN** the controller may record the verbatim evidence for that reviewer

#### Scenario: Ambiguous or trailing evidence is submitted

- **WHEN** the output has a second close line, a contradictory verdict,
  a mismatched or shortened SHA, or text after the close line
- **THEN** the controller refuses to record it as review authority

### Requirement: Deferred findings are structured and review-bound

A deferred generalization SHALL count as recorded only when exactly one
parseable tracked record has a globally unique finding identifier and matches
the selected chunk, reviewer, and proposed target in the exact Git blob at the
full commit named by the reviewer's terminal evidence. The ledger SHALL bind
that record digest and identifier to the reviewed commit; the finding block
MUST NOT attempt to embed its own commit SHA. Later append-only lifecycle
transitions SHALL cite the original reviewed commit and SHALL preserve the
finding block unchanged. The controller SHALL reject malformed records and
duplicate identifiers anywhere in the backlog.

Targets SHALL be canonical repository-relative paths with no absolute form,
dot-segment alias, or escape from the declared target. Textual mentions alone
SHALL NOT authorize pass_with_lift.

#### Scenario: Prose or a mismatched record names the target

- **WHEN** the target appears only as prose, or the exact reviewed commit's
  backlog blob has no record for the matching reviewer, chunk, or finding
  identifier
- **THEN** the deferred adjudication is refused

#### Scenario: Duplicate or malformed identity is present

- **WHEN** two records share a finding identifier or a record lacks a required
  provenance or lifecycle field
- **THEN** the controller rejects the backlog as ambiguous

#### Scenario: Exact deferred finding is recorded

- **WHEN** one valid unique record in the exact reviewed commit matches the
  reviewer, chunk, identifier, and canonical target, and the ledger records
  its blob digest beside that full reviewed SHA
- **THEN** the controller may accept that review's deferred finding

### Requirement: Frozen file scope is complete and path-safe

Local and provider-reported changed-file checks SHALL validate every changed
path, including both source and destination paths of renames. Provider file
snapshots SHALL include a valid count witness, and the count SHALL equal the
number of returned, individually well-formed paths before scope classification.

A proposal SHALL satisfy its required Why heading only when that heading is
visible Markdown content in the proposal itself; fenced examples, comments,
HTML-hidden text, and substrings SHALL NOT satisfy the requirement.

#### Scenario: Rename hides an out-of-scope source

- **WHEN** a rename has an allowed destination but an unauthorized source
- **THEN** local and provider scope validation rejects the changed file set

#### Scenario: Provider response is truncated or malformed

- **WHEN** the provider count differs from the returned path count or a file
  entry lacks a string path
- **THEN** the controller refuses the scope snapshot before any dependent
  action

#### Scenario: Fenced heading is mistaken for visible content

- **WHEN** the only Why text is inside a code fence, comment, or hidden
  HTML block
- **THEN** proposal validation reports the required visible heading as absent

### Requirement: Mutation authority is revalidated at the action boundary

Immediately before each non-dry-run push or provider mutation, the controller
SHALL recheck the enabled manifest capability, authenticated actor, configured
repository, fetch remote, and every effective push destination. It SHALL also
revalidate any ledger on which the action depends. A remote action SHALL target
only the repository named by the manifest.

A guarded branch push SHALL name only the selected issue branch and SHALL
disable automatic tag following.

#### Scenario: Remote or push destination changes after preflight

- **WHEN** the selected remote or its effective push URL changes after
  preflight, or multiple push destinations are configured
- **THEN** the controller refuses the push before invoking Git

#### Scenario: Push configuration would publish tags

- **WHEN** Git configuration enables tag following for the guarded branch push
- **THEN** the constructed command disables tag following and names only the
  manifest-authorized branch

#### Scenario: Provider authority has been revoked

- **WHEN** an action is disabled by the live owner policy or the authenticated
  actor/repository no longer matches the manifest
- **THEN** the controller issues no provider mutation

### Requirement: Pull-request creation uses the exact terminal reviewed head

The controller SHALL invoke PR creation only when the ledger is terminally
passed, its terminal reviewed commit is a full SHA exactly equal to local
HEAD, the selected local branch matches the issue, and the live remote issue
branch resolves to that same SHA immediately before provider creation.

After creation, the controller SHALL verify the returned PR head, base, body,
and frozen files still match the reviewed selection before reporting success.

#### Scenario: Local or remote head differs

- **WHEN** local HEAD, the terminal reviewed SHA, or the live remote issue
  branch differ, or the remote branch is absent or malformed
- **THEN** the controller refuses before invoking gh pr create

#### Scenario: Exact reviewed branch creates a PR

- **WHEN** the complete passing terminal ledger, local HEAD, and live remote
  branch all identify the same full SHA and every frozen-scope check passes
- **THEN** the controller may invoke only the configured repository's PR
  creation command and verify the resulting PR binding

### Requirement: Draft readiness is a checked, reviewed-head-bound transition

The controller SHALL expose draft-to-ready as an explicitly authorized action.
Before gh pr ready, it SHALL require a passing validated ledger, a draft PR
whose head carries exactly the reviewed change, the frozen issue branch and
body, the protected base, exhaustive frozen file scope, predecessor evidence,
and green required checks bound to that head.

The controller SHALL capture and compare an initial snapshot, an immediate
pre-action snapshot, and a post-action snapshot. It SHALL revalidate the full
frozen PR scope after the transition and SHALL NOT report verified success if
the provider response is malformed or any binding drifts. This action SHALL
not approve, merge, or close a PR or issue. GitHub provides no conditional
ready transition, so the controller SHALL report that external time-of-check
race as an explicit limitation.

#### Scenario: Ready transition is fully bound

- **WHEN** all snapshots show the same reviewed head, branch, base, body, file
  set, draft/open state, and green required checks
- **THEN** the controller invokes only gh pr ready and reports success only
  after the verified post-action snapshot

#### Scenario: Draft or reviewed scope drifts

- **WHEN** the head, branch, base, body, changed files, checks, open state, or
  draft state differs in a pre-action or post-action snapshot
- **THEN** the controller refuses before acting or reports that the provider
  transition could not be verified

#### Scenario: Ready action is asked to perform another mutation

- **WHEN** readiness is requested while approval, merge, or issue closure is
  not separately authorized
- **THEN** the action performs none of those other mutations

### Requirement: Bootstrap and repository guidance preserve the terminal boundary

The controller-bootstrap manifest SHALL be disabled by default, select only
its own tracking issue, identify its reviewed base and distinct terminal
predecessor, and cap each frozen chunk at three critique/revise rounds. A third
unresolved round SHALL become terminally blocked without a fourth round or
renamed continuation. The one-time publication path for controller-owned
changes SHALL require a passing fresh panel and exact reviewed commit; it SHALL
not self-authorize approval, merge, or issue closure.

The executable controller, OpenSpec artifacts, manifests, root repository
guidance, run-loop instructions, and reviewer prompts SHALL state consistent
issue-count, evidence, mutation, and round-cap rules.

#### Scenario: Predecessor identity is reused

- **WHEN** a bootstrap manifest selects its predecessor issue or OpenSpec
  change as its own identity
- **THEN** manifest validation fails before ledger initialization

#### Scenario: Third review still needs changes

- **WHEN** the third critique/revise round is adjudicated needs_changes
- **THEN** the ledger records a terminal blocked result and refuses another
  round or continuation

#### Scenario: Bootstrap is not self-authorized

- **WHEN** the fresh controller panel has not passed or the reviewed commit
  differs from local HEAD
- **THEN** no bootstrap publication action is attempted

#### Scenario: Guidance is checked against the executable protocol

- **WHEN** a fresh manifest or reviewer follows the repository's current
  guidance for issue count, evidence, or review caps
- **THEN** the guidance agrees with the controller schema and the accepted
  OpenSpec capability
