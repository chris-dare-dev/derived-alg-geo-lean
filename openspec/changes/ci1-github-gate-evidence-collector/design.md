# Design

## Context

See `proposal.md` for the gap. `scripts/ci_contract.py` validates schema v4 records against independently supplied protected-base, PR-head and inventory-digest anchors. `scripts/ci_gate_inventory.json` lists the current GitHub Actions `build`, `roadmap` and `ci` checks and optional workflows. `docs/ci/gate-evidence-contract.md` explicitly leaves GitHub collection and provider eligibility to an adapter. The current `scripts/loop_engine.py` still selects `statusCheckRollup` entries by name and time; #1434 owns its replacement.

GitHub's [check-run API](https://docs.github.com/en/rest/checks/runs) warns that listing by Git ref alone cannot enumerate every possible check run; the collector must traverse [check suites](https://docs.github.com/en/rest/checks/suites) and their runs. [Commit statuses](https://docs.github.com/en/rest/commits/statuses) are a separate paginated surface. Branch protection may require a context that the repository inventory omitted.

## Goals / Non-Goals

**Goals:**

- Emit a schema v4 evidence bundle whose source observations and candidate identity are reproducible from read-only GitHub responses and Git objects.
- Fail closed on moved revisions, incomplete pages, ambiguous producer/run identity, missing pins, and unexplained required contexts.
- Make the collector testable with fixed provider responses and exercise it read-only on a live current PR.

**Non-Goals:**

- No controller merge/admission decision, workflow edit, branch-protection edit, reviewer-approval policy or post-merge health claim.
- No new Lean declaration or mathematical comparison. Mathematical ownership, import, specialization and instance-agreement maps are not applicable to this Python adapter; its canonical contract is the existing `ci_contract.validate_evidence`, not a second validator.
- No assertion that a successful provider API response is a cryptographic attestation. A local bundle hash detects changed collected bytes but does not authenticate GitHub independently of the API connection.

## Decisions

### One adapter downstream of the existing validator

Add `scripts/ci_github_evidence.py` with a narrow read-only provider client and pure normalization functions. The adapter imports `ci_contract`; the validator does not import the adapter. The only normalized output is schema v4 evidence plus a validation result from the existing validator. A bundle contains `evidence.json` and canonical JSON observation files whose actual bytes match the recorded SHA-256, size and candidate subject. Tests inject provider responses instead of calling the live API. A small read-only `loop_engine.py evidence` command consumes the adapter's result and exit code for the live issue demonstration; it does not replace `check_required_checks` in queue admission. #1434 owns durable adoption. This dependency direction avoids duplicate policy logic.

The inventory currently lists GitHub Advanced Security as `run_binding=independent`, but a check app may report a PR-head check without any Actions workflow run. Extend the schema's run binding with `check` for that actual provider shape: no run ID/attempt, `github-checks` platform, and an explicit PR-head commit subject. Reclassify only that optional inventory entry. Applicable independent Actions workflow gates retain their own verified run/attempt; the PR collector does not borrow the primary run for them. No other independent workflow is currently applicable to the PR event. Keep unknown or multiply matching optional observations as warnings/denials rather than fabricating a run.

Alternative considered: teach `ci_contract.py` to query GitHub. Rejected because the provider-neutral validator is already the canonical consistency layer, and combining network reads with validation would obscure which values are trusted external anchors.

### Establish identity before observing gates, then recheck it

Read the configured repository's protected `main` SHA and branch-protection requirements, then the PR's base/head and candidate metadata. The base SHA must equal current `main`; the primary Actions run must identify the expected workflow, PR, event, candidate commit and attempt. Read the candidate Git commit/tree and its parents from immutable Git objects, comparing provider and Git identities. After collecting observations, reread current `main` and PR head; any movement denies a current claim. Inputs such as PR number and repository select what to inspect but never override base/head/candidate anchors.

For this repository's `pull_request` workflow, the Actions run and check suite report the PR **head** SHA, while `github.sha` and the default checkout use the merge ref. The protected-base workflow names its run-scoped upload `trust-artifacts-${{ github.sha }}`. Read that run's artifact list, require one non-expired artifact with this prefix, obtain the merge SHA from its name, compare it with the PR API's current `merge_commit_sha`, and verify its Git commit/tree and both parents against the current base and head. Recheck the merge SHA at the end of collection. Require the candidate's `ci.yml` bytes to match the protected-base workflow so a PR cannot redefine the naming convention and claim a fabricated binding. The collector must deny the claim when this artifact or the workflow comparison is unavailable; it must not substitute `run.head_sha` as the tested tree. The artifact is a binding through the trusted workflow rule and GitHub's run metadata, not a cryptographic attestation. Do not synthesize a candidate from local Git state.

Alternative considered: trust `gh pr checks` or a workflow run's displayed head alone. Rejected because those surfaces omit optional checks or can refer to a different candidate than the one current protection evaluates.

### Enumerate by suites and preserve run identities

Traverse every page of check suites for the exact candidate and every page of check runs per suite; separately traverse all commit-status pages. Verify provider `total_count` where available and reject unknown truncation. Map GitHub Actions check runs to their workflow run and attempt using run/job metadata, including the job's `check_run_url`, not a displayed name or `details_url` alone. Preserve app/producer identity and distinct check-run versus status IDs. For reruns, retain prior observations in the bundle and select an attempt only when the provider proves the same run/candidate relationship; unresolved duplicates deny the claim.

GitHub's failed-jobs-only rerun can reuse a successful build job and its artifact from an earlier attempt while replacing only failed jobs. Schema v4's `run_binding=primary` requires each gate's attempt to equal the record attempt, so the collector denies this mixed-attempt case even when GitHub's latest workflow result is green. A future contract could model a provider-proven effective attempt; this progress change does not claim one.

Alternative considered: one `commits/{sha}/check-runs` request with `per_page=100`. Rejected because it can silently omit observations and cannot safely distinguish same-name producers or reruns.

### Derive policy and pins from immutable sources

Read `scripts/ci_gate_inventory.json` from the current protected-base commit and compare its required GitHub contexts with live branch protection, including any expected app identity. Read `lean-toolchain`, `lake-manifest.json` and `pins.json` from the tested candidate tree and hash their bytes. A missing object, unaccounted required context, unavailable protection response or schema mismatch denies a required-CI claim. Optional red/missing checks remain visible without changing required-CI success into an all-pipelines-green claim.

Alternative considered: use the branch checkout's inventory or pins. Rejected because a PR could edit its own policy or the checkout could move while evidence is collected.

### Protected-code delivery and reviews

The ordinary PR may edit only its OpenSpec directory, `scripts/ci_github_evidence.py`, a read-only `scripts/loop_engine.py` evidence command, `scripts/ci_contract.py`, `scripts/ci_gate_inventory.json`, focused tests and `docs/ci/gate-evidence-contract.md`. The validator/inventory edits are restricted to representing the already inventoried runless security check truthfully. It does not edit `ci.yml` or the controller admission/merge path. The branch-authored unattended controller rejects `scripts/` paths, so no manifest is written to bypass it. Use at most three review/improve rounds on a fixed commit with independent mathematical/source-faithfulness, repository-boundary, abstraction/adoption and mathlib-style lenses. Bounded automatic recovery is **disabled** for this protected-code PR; if the third round fails, preserve findings and stop for a separately reviewed research plan rather than re-chunking or widening scope.

## Risks / Trade-offs

- **Provider pagination or rate limits hide a result** → Check page completeness and counts, bound retries, and deny admission when complete enumeration cannot be proved.
- **GitHub metadata does not prove a job-to-run mapping for a required check** → Reject that required observation; do not infer provenance from its name.
- **Base or head changes between API calls** → Re-read both anchors after collection and let #1434 repeat the check at admission time.
- **Artifact digest is mistaken for provider authentication** → Document that it binds local retained bytes only; GitHub API identity and authenticated transport remain the trust source.
- **Standalone tests are not yet a CI gate** → Report focused local test results and the PR's required `ci` run separately. CI test invocation and controller consumption remain downstream scoped work.

## Migration Plan

Publish the read-only collector, bridge and fixtures in one PR, run focused tests and repository precheck, and record one current-PR read-only controller exercise at an exact revision. Merge normally after exact-head review and required hosted CI, then record the merged revision and close #1430 only when its operational acceptance is demonstrated. Rollback removes the adapter and read-only bridge; the existing validator and protected `ci` requirement remain unchanged. #1434 later adopts the collector for durable queue admission after its own review.
