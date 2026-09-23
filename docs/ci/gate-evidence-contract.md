# Decision record: CI gate and evidence contract (CI1.01)

Status: proposed for workflow and controller review. Schema version: 3.

## Decision

`scripts/ci_gate_inventory.json` is the versioned policy inventory. A provider
adapter reads it from the **protected base commit**, not the PR checkout. The
adapter supplies the current protected base SHA and the canonical SHA-256 of
that inventory to `validate_evidence`. The command-line validator reads the
inventory directly from `<trusted-base-commit>:scripts/ci_gate_inventory.json`
through Git. The trusted base SHA must itself come from the provider's current
protected branch metadata; a SHA supplied by the PR is not a trust anchor.
Missing or mismatched anchors deny admission.

The record binds repository, base, PR head, tested commit and tree, event/ref,
run and attempt, producer, toolchain and the SHA-256 of `lean-toolchain`,
`lake-manifest.json` and `pins.json`. Each applicable gate identifies a provider
observation and a hashed artifact with its gate subject. The provider proof
digest detects accidental changes to its normalized fields; it is not a
signature or proof that the fields came from GitHub. The adapter must obtain
them from authenticated provider responses and verify the candidate commit,
tree and parent relation against those responses and Git objects.

Gate identity is `(producer, name)`, so a commit status and a check run may
have the same displayed name. An observation's provider ID, run ID, attempt,
commit, producer and artifact are all required. The adapter must fetch every
page of check runs and commit statuses for the exact candidate and preserve
their provider identities. A name-only or latest-timestamp selection is not
eligible evidence. A rerun supersedes an earlier attempt only when the adapter
has verified the provider's run/attempt relationship and the selected attempt
belongs to the exact candidate.

Only an applicable gate with status `passed` and raw conclusion `success`
satisfies required work. Missing, pending, failed, cancelled, timed-out and
unexpectedly skipped work denies admission. A gate outside its declared event
is explicitly non-applicable with a reason and no artifact. An optional red
check is reported as a warning: it does not become a success claim.

## Current producer map

The checked-in inventory describes the external check contexts on current
`main`: `build` and `roadmap` are CI jobs; `ci` is the required aggregate of
both. Branch protection currently requires only the `ci` context from GitHub
Actions, with strict up-to-date checking. The prior `trust-surface` context was
removed in #1449; its replacement approval policy is separate from this CI
inventory. `cache-warm`, Docs, and GitHub Advanced Security are auxiliary;
their failure must remain visible. `post-merge-health` is a distinct
observation on `main`, not evidence that a PR was merge-ready.

The `build` job contains internal step gates. Its `What changed` step sets
`scope=all` when the diff base cannot be resolved and for merge groups. The
aggregate step prints scoped skips for `Contract gates` and `Emitter
reproducibility`; the latter is conditional on a successful emitter and its
event/diff rule. These internal step outcomes are not separate GitHub check
contexts in the present inventory. A provider adapter must not infer that
every internal gate ran from the `build` context alone. CI1.08 owns the
prerequisite-aware report-all workflow change and its detailed step evidence.

## Admission claims and adapter boundary

The validator establishes consistency of a normalized record against a
trusted inventory and a current base anchor. It does not query GitHub, check
reviewer authority, confirm branch protection, or perform the merge. A
controller may call a candidate **required-CI verified** only after its
provider adapter has checked the producer identity, complete observations,
current base/head, tested candidate/tree, policy commit and all required gate
outcomes. **Merge-ready** additionally requires valid reviews, the live
protection policy and provider merge eligibility. **Post-merge healthy**
requires a successful run on the exact merged `main` revision. These are
separate claims; an optional red check prevents an “all pipelines green”
claim even when required CI is verified.

When the provider cannot supply a field, reports an ambiguous duplicate,
returns a truncated page, or cannot establish the current base/head or tested
candidate, the adapter must produce no admission claim. Final protected merge
remains authoritative. This contract does not authorize changing required
contexts, protection settings or workflow routing.

Workflow and controller owners must independently review this contract at the
final revision before adoption. Operational verification requires a provider
adapter and a real PR/merge-group exercise; the local fixtures establish only
validator behavior.
