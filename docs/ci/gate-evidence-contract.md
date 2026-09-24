# Decision record: CI gate and evidence contract (CI1.01)

Status: proposed for workflow and controller review. Schema version: 4.

## Decision

`scripts/ci_gate_inventory.json` is the versioned policy inventory. A provider
adapter reads it from the **protected base commit**, not the PR checkout. The
adapter supplies the current protected base SHA and the canonical SHA-256 of
that inventory, plus the current PR head SHA, to `validate_evidence`. The
command-line validator reads the
inventory directly from `<trusted-base-commit>:scripts/ci_gate_inventory.json`
through Git. The trusted base SHA must itself come from the provider's current
protected branch metadata; a SHA supplied by the PR is not a trust anchor.
Missing or mismatched base, head or policy anchors deny admission.

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
commit, platform, producer and artifact are all required where applicable.
The gate's platform is separate from the primary CI record's platform.
`run_binding=primary` ties a
gate to the record's CI run; `independent` allows an auxiliary workflow to
have its own run and attempt. `status` represents a commit status, which has
a provider status ID but no workflow run. A check-run artifact must match its
gate's run identity; a commit-status artifact must not invent one. The adapter
must fetch every
page of check runs and commit statuses for the exact candidate and preserve
their provider identities. A name-only or latest-timestamp selection is not
eligible evidence. A rerun supersedes an earlier attempt only when the adapter
has verified the provider's run/attempt relationship and the selected attempt
belongs to the exact candidate.

Only an applicable gate with status `passed` and raw conclusion `success`
satisfies required work. Missing, pending, failed, cancelled, timed-out and
unexpectedly skipped work denies admission. A gate outside its declared event
may be omitted or explicitly non-applicable with a reason and no artifact. A
missing, skipped or red auxiliary check is reported as a warning: it does not
become a success claim. `claims.required_ci_verified` and
`claims.auxiliary_checks_healthy` are separate; `all_pipelines_green` requires
both. Merge readiness and post-merge health remain `not_evaluated` until the
provider adapter checks their additional conditions.

## Current producer map

The checked-in inventory describes the external check contexts on current
`main`: `build` and `roadmap` are CI jobs; `ci` is the required aggregate of
both. Branch protection currently requires only the `ci` context from GitHub
Actions, with strict up-to-date checking. The prior `trust-surface` context was
removed in #1449; its replacement approval policy is separate from this CI
inventory. The independent `warm` check from the Cache warm workflow, the
`check`/`build`/`deploy` jobs from Docs, and GitHub Advanced Security are
auxiliary. Docs may run on a schedule or by manual dispatch; a scheduled run
with no recent commits explicitly skips its build and deploy jobs. These
auxiliary outcomes remain visible without borrowing the CI run ID. There is no
provider check named `post-merge-health`: post-merge health is a later claim
about the exact merged revision's `main` CI, not a synthetic check run.

Manual dispatch selectors include the workflow name. A manual CI run does not
imply that Cache warm or Docs ran, and a manual Docs run does not make the CI
jobs applicable. On a push to `main`, CI and Cache warm are separate runs on
the same revision; the auxiliary run may be pending or absent while required
CI has already passed.

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

## Read-only GitHub collector (CI1.01 progress)

`python3 -m scripts.ci_github_evidence --repo
chris-dare-dev/derived-alg-geo-lean --pr <number> --output <directory>` reads
GitHub through GET requests and writes a local evidence bundle. It obtains the
protected `main` SHA from the branch API, the PR base and head from the pull
request API, and live strict required contexts and app IDs from branch
protection. It reads the inventory from the protected-base Git object, not
from the candidate checkout. Unknown protected contexts, a missing protected
`ci` aggregate, a policy read failure, or a base/head movement deny a current
claim. The same protected branch, PR and protection values are read again
after observation collection.

For a `pull_request` run, GitHub's Actions run and check suite identify the
PR **head** SHA. This repository's protected `ci.yml` uploads a run-scoped
`trust-artifacts-${{ github.sha }}` artifact after checkout. The collector
requires the tested candidate's workflow bytes to equal the protected-base
workflow, takes the merge SHA from exactly one current run artifact, and
checks that Git commit's tree and ordered parents against the protected base
and PR head, and matches the PR API's current `merge_commit_sha`. A missing,
expired, ambiguous or stale-attempt artifact denies
the claim. The artifact name is a run-to-merge-SHA binding under this
workflow's rule; it is not a cryptographic attestation. The collector never
replaces the merge candidate with the run API's head SHA.

The collector traverses all pages of check suites on the head, all runs in
each suite, all commit statuses, and jobs for each attempt of the selected
workflow run. `check_run_url`, check ID, suite app ID, job run ID and attempt
must agree for a primary gate. Earlier attempts and other producers remain
in `source-observations.json`; they cannot authorize the current gate. A
same-named commit status cannot replace a check run. Source observations with
no proven gate mapping remain visible and prevent an all-pipelines-green
claim. A missing or red required gate denies `required_ci_verified`; optional
warnings remain separate.

Separate workflow runs on one head cannot silently supersede an older red
required check: the collector denies a current claim if more than one CI run
exists for that head. It also rechecks the run and attempt after collection.
Failed-jobs-only reruns may reuse a successful job and candidate artifact from
an earlier attempt; schema v4 cannot represent required gates spanning
attempts, so this collector currently denies that case conservatively.

The local bundle contains `evidence.json`, `validation.json`, canonical
`results/check-run-<id>.json` payloads, `source-observations.json`, and
`bundle-manifest.json`. Each schema artifact records the SHA-256 and byte
length of its actual payload, and the manifest hashes the full retained
observation file. `lean-toolchain`, `lake-manifest.json`, and `pins.json`
digests come from the candidate Git tree. These hashes detect a changed
local bundle; they do not authenticate GitHub beyond the authenticated API
response. `ci_contract.validate_evidence` remains the canonical consistency
validator. This collector makes no review, merge, or post-merge health
decision and is not yet called by the controller or CI workflow.
