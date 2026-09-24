# Design

## Context

See proposal.md for motivation and the capability delta for observable
requirements. The implementation is concentrated in scripts/loop_engine.py and
its Python tests. The existing controller has independent provider actions,
review ledgers, PR scope checks, a readiness action, and required-check
validation, but those paths do not yet share one complete trust-boundary
validator.

The selected repository work is control-plane code and guidance only. No
Lean declaration, import, instance, or mathematical object changes. The prior
#1458, #1459, #1460, #1461, and #1462 loop ledgers are terminal historical
evidence. This change starts from current main and uses a new issue, change,
manifest, worktree, and review history.

## Goals / Non-Goals

**Goals:**

- Derive one canonical selected issue/chunk record from the validated manifest
  and route ledger-dependent actions through a single validator.
- Bind every formal verdict and deferred finding to an exact reviewer, full
  commit, frozen chunk, and captured verbatim output.
- Recheck live authority and all remote targets at the last local boundary
  before a push or provider mutation.
- Make PR creation and ready transitions consume the exact reviewed head and
  complete changed-file/check snapshots.
- Make workflow documentation agree with the executable policy and preserve
  terminal caps.

**Non-Goals:**

- Repair or publish any held branch or ignored ledger from #1458 through #1462.
- Make GitHub's draft-to-ready transition atomic; the provider offers no
  reviewed-head compare-and-swap for that operation.
- Replace branch protection, human review, or the separate trust-reviewed
  label.
- Change the Lean library, mathematical APIs, or public declaration audits.
- Add autonomous recovery or a new path around a terminal third review round.

## Decisions

### 1. One canonical selection and ledger-validation gateway

Construct the expected selection from the loaded manifest, requested issue and
chunk, and current OpenSpec digest. Compare it with every scope-bearing ledger
field before review recording, adjudication, dependency checks, or publication.
Validate contiguous round numbers, the manifest cap, one roster-complete panel
per round, unique reviewer identities, the recorded commit, verbatim evidence
digest, verdict tokens, and consistency between adjudication and terminal
status.

Keep the selection derivation pure where possible and put repository reads at
the gateway boundary. This avoids separate partial checks drifting across PR
creation, approval, merge, push, and readiness. A checksum alone is rejected:
the controller must compare copied state to the manifest-derived values.

Review output uses one strict terminal grammar: exactly one full-SHA
Reviewed commit line, immediately followed by one Close line, with no later
content. Existing prose that lacks this evidence remains historical but cannot
satisfy a new panel.

### 2. Parse durable lift records instead of searching prose

Keep the backlog readable Markdown, with machine records inside explicit
HTML-comment blocks that are ignored inside fenced examples. A finding block
contains a stable UUID-based identifier, chunk ID, reviewer, canonical target,
and initial lifecycle state. The captured review and ledger bind that record's
exact blob digest and identifier to the full reviewed commit by reading the
backlog from that commit. The block cannot contain its own commit SHA without
making the commit hash self-referential. Later lifecycle changes are new
append-only transition blocks that cite the original reviewed commit, refer to
one existing identifier, and form an allowed state sequence. Parse the full
file once and reject duplicate finding identifiers, malformed blocks, orphan
transitions, and invalid paths.

Require the reviewer's captured text to name the same lift identifier and
target. The ledger stores that identifier, target, reviewed SHA, and exact
backlog-record digest beside the digest of the verbatim review, so an arbitrary
target substring cannot authorize deferral. Legacy backlog prose remains
visible history but is not evidence for a new lift.

### 3. Validate every changed path, including incomplete provider responses

Use one canonical repository-relative path parser for frozen prefixes and lift
targets. Reject absolute paths, empty or dot segments, parent traversal,
backslashes that create an alias, and paths that leave the repository. Local
name-status parsing preserves both endpoints of renames and copies. Provider
snapshots request changedFiles and files together, require an integer count,
require every entry to contain a string path, and compare the count with the
validated entries before testing frozen scope.

Proposal validation recognizes a visible exact-level Why heading outside
fenced code, comments, and hidden HTML. Keep parsing deliberately fail-closed
for unsupported Markdown constructs rather than treating arbitrary substring
matches as visible sections.

### 4. Re-establish mutation authority immediately before the subprocess

Keep the existing action mapping and owner-controlled grants. Add one shared
last-boundary guard that resolves the current authenticated actor and repository,
reads the selected remote's fetch URL and effective push URL list, rejects
multiple or mismatched push targets, reloads the action grant, and validates
the ledger when required. Every mutation keeps its early authorization check
for clear refusals, then invokes this shared guard immediately before the
subprocess.

The push command uses an explicit source-to-branch refspec and
--no-follow-tags, so push.default and push.followTags cannot widen its effect.
This is a local check immediately before Git starts; GitHub and Git do not
offer one atomic operation combining remote verification and the push.

### 5. Require exact local and remote identity for source-PR creation

For a complete publication, require a fully adjudicated passing ledger and a
lexically full terminal SHA. Resolve local HEAD and require exact equality.
Require the current branch to be the manifest-selected issue branch, the
worktree to be clean, and frozen local file checks to pass. Resolve the live
GitHub branch ref through the manifest repository and require exactly one
valid response naming the same full SHA immediately before gh pr create.
After creation, inspect the created PR and refuse to report success if its head,
base, body, or complete file scope differs.

Do not reuse the content-equivalence helper intended for approval and merge:
the create-PR contract is exact terminal identity, not rebased-content
equivalence.

### 6. Bind readiness to three fresh PR snapshots

Use the existing required-check resolver, but capture each result with the PR
head and a complete frozen binding: state, draft flag, head branch, base,
body, predecessor evidence, changedFiles and validated file paths. First
validate the PR snapshot and checks, re-fetch immediately before the ready
command and compare it to the first snapshot, then fetch and validate again
after the provider mutation. Each check result must refer to the same reviewed
head. A post-action drift is reported as an unverified provider transition,
never as success. The ready action constructs only gh pr ready.

### 7. Keep the controller's own bootstrap disabled

The run manifest selects only #1482, records its reviewed base and terminal
predecessor identities, names all required reviewers and security/workflow/test
adversaries, and caps its one frozen chunk at three rounds. It remains disabled
and grants no provider mutation. Since this PR changes the controller itself,
the one-time publication path is manual only after a passing exact-commit panel,
focused checks, precheck, and a fresh live remote/head check. It can create a
reviewable PR; it cannot approve, merge, or close issues. Ordinary branch
protection and the human trust-reviewed label still apply.

No automatic recovery is enabled. A third unresolved critique/revise round is
terminal and may only lead to a separate, independently authorized issue after
this chunk stops; it does not permit renaming, resetting, or widening this
manifest.

## Risks / Trade-offs

- Provider APIs can change response shapes or pagination behavior → require a
  count witness, strict entry validation, and focused fixtures for truncation
  and malformed responses.
- GitHub has a race between the final read and a ready transition or PR create
  → re-read immediately before, verify afterward, and describe the remaining
  non-atomic provider window.
- Existing local ledgers may have older shapes → fail closed and preserve their
  bytes; do not silently reset review history.
- Root guidance and controller tests touch trust-sensitive paths → require the
  human trust-reviewed label on the eventual PR; do not apply it on the author's
  behalf.

## Migration Plan

1. Freeze the disabled #1482 manifest and this OpenSpec change on a clean
   worktree from the recorded current-main commit.
2. Implement and test the single frozen chunk without Lean changes.
3. Run focused tests, strict OpenSpec and manifest validation, precheck, and
   the exact-commit independent review panel within three rounds.
4. After a passing panel, publish a reviewable PR through the documented
   one-time path. Wait for hosted and self-hosted required checks and the human
   trust-reviewed review before any merge or issue closure.
5. If the third panel is unresolved, record terminal blockage and stop without
   publishing the change.

## Open Questions

None. The issue body and terminal review evidence define the scope and
publication boundary.
