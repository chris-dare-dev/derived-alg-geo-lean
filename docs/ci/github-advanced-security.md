# GitHub Advanced Security integration diagnosis

The optional `github-advanced-security` check has produced provider failures,
later provider-success runs without coverage proof, and newer PR heads with no
security-check observation. The most recent observed provider failure is from
2026-09-23; absence of a check on newer heads is unknown, not a clean scan or
proof that the integration was retired.

The workflow is provider-generated (`dynamic/agents/github-advanced-security`)
and is not checked into this repository. Repository code cannot grant an
entitlement to the identity used by that external workflow. Do not edit
`ci.yml`, weaken branch protection, suppress provider errors, or change the
provider configuration as a workaround for the failed runs.

## Original provider failures

All four target runs failed during Copilot SDK session initialization with an
HTTP 403 authentication/licensing response, before the scanner could report
findings. They are provider failures, not vulnerability findings and not clean
scans.

| PR | Observed (UTC) | Run / job log | Candidate revision | Classification |
|---:|---|---|---|---|
| [#1415](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1415) | 2026-09-20 18:59:14 | [run 35530799100](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799100) / [job 106130918882](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799100/job/106130918882) | [`e7fc1c1a0c54fe9c5c7316e045faa6b90a75f361`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/e7fc1c1a0c54fe9c5c7316e045faa6b90a75f361) | `provider_failure` before scan |
| [#1419](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1419) | 2026-09-20 18:59:13 | [run 35530798806](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798806) / [job 106130918769](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798806/job/106130918769) | [`23a60f401f3f131b6e30fb12b89df92e124429ca`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/23a60f401f3f131b6e30fb12b89df92e124429ca) | `provider_failure` before scan |
| [#1424](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1424) | 2026-09-20 18:59:14 | [run 35530799092](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799092) / [job 106130918968](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799092/job/106130918968) | [`836c80a308834db9b51dfa2acb02998aca7bfac5`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/836c80a308834db9b51dfa2acb02998aca7bfac5) | `provider_failure` before scan |
| [#1427](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1427) | 2026-09-20 18:59:13 | [run 35530798284](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798284) / [job 106130917005](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798284/job/106130917005) | [`f7a85f60b5833db824e95c2ff55490467dd6b608`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/f7a85f60b5833db824e95c2ff55490467dd6b608) | `provider_failure` before scan |

## Later provider observations

| PR | Observed (UTC) | Run / job log | Candidate revision | Observation |
|---:|---|---|---|---|
| [#1426](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1426) | 2026-09-20 15:38:31 | [run 35520220048](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35520220048) / [job 106102898252](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35520220048/job/106102898252) | [`b434dc682842d1778f7c491af98fe66583347fe9`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/b434dc682842d1778f7c491af98fe66583347fe9) | Provider workflow succeeded and reported a `ccr_security` result to `sweagentd`, but its log says sessions are not supported for code scanning. No bound result artifact or executed negative-fixture proof was found; this is successful-but-unverified execution, not `verified_scan`. |
| [#1427](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1427) | 2026-09-21 23:12:52 | [run 35666505192](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35666505192) / [job 106553349308](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35666505192/job/106553349308) | [`deafef42b66b2f7ea9160247b13f62d2176a184f`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/deafef42b66b2f7ea9160247b13f62d2176a184f) | Provider workflow succeeded, but no bound result artifact or executed negative-fixture proof was found; coverage remains unverified. |
| [#1473](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1473) | 2026-09-23 02:57:40 | [run 35812428038](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35812428038) / [job 107026703282](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35812428038/job/107026703282) | [`edcf0b6213d9e5508ec85381f3d78e64c8d6feae`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/edcf0b6213d9e5508ec85381f3d78e64c8d6feae) | Repeated Copilot SDK HTTP 403 authentication/licensing failure before scan; `provider_failure`. |

## Current open PR-head snapshot

Captured at **2026-09-27 02:03:44 UTC** from PR metadata, check-runs API
responses, and the live `main` required-status-check endpoint. These were all
four PRs open in the repository at capture. Each check-runs request used
`GET /repos/chris-dare-dev/derived-alg-geo-lean/commits/{head_sha}/check-runs?per_page=100&page=1`;
the total counts were below 100, so each complete response fit on the first
page. The snapshot artifact records the exact request URL, head SHA, `total_count`,
returned names/statuses, and result links:
[current-check-runs-2026-09-27T02-03-44Z.json](../../openspec/changes/ci1-1433-security-evidence-refresh/evidence/current-check-runs-2026-09-27T02-03-44Z.json)
(SHA-256 `0c44956a03dfa12136b22f84333c59123072bf143c0060d082312418db9a76d1`).

| PR head | Check-runs response | Returned checks at capture |
|---|---|---|
| [#1566](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1566), [`06079755b65fb71c14d8f655832829e4b8bf65fd`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/06079755b65fb71c14d8f655832829e4b8bf65fd) | [API response](https://api.github.com/repos/chris-dare-dev/derived-alg-geo-lean/commits/06079755b65fb71c14d8f655832829e4b8bf65fd/check-runs?per_page=100&page=1), `total_count: 3` | `ci`, `build`, and `roadmap` all succeeded in [run 36273289044](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36273289044); no security check was returned. |
| [#1568](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1568), [`5364d5bc2c7aaaf81953ef78583c7a7fd192489d`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/5364d5bc2c7aaaf81953ef78583c7a7fd192489d) | [API response](https://api.github.com/repos/chris-dare-dev/derived-alg-geo-lean/commits/5364d5bc2c7aaaf81953ef78583c7a7fd192489d/check-runs?per_page=100&page=1), `total_count: 2` | `roadmap` succeeded and `build` was in progress in [run 36286127013](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36286127013); no security check or required `ci` result had appeared. |
| [#1570](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1570), [`b03e2a5b54b2af28a279049e5803e3ee79d76c8e`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/b03e2a5b54b2af28a279049e5803e3ee79d76c8e) | [API response](https://api.github.com/repos/chris-dare-dev/derived-alg-geo-lean/commits/b03e2a5b54b2af28a279049e5803e3ee79d76c8e/check-runs?per_page=100&page=1), `total_count: 6` | Two `ci`/`build`/`roadmap` runs succeeded, including [run 36284578168](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36284578168); no security check was returned. |
| [#1571](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1571), [`54f7afb99d411fb51dafe2c50175b18a55a71911`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/54f7afb99d411fb51dafe2c50175b18a55a71911) | [API response](https://api.github.com/repos/chris-dare-dev/derived-alg-geo-lean/commits/54f7afb99d411fb51dafe2c50175b18a55a71911/check-runs?per_page=100&page=1), `total_count: 3` | `ci`, `build`, and `roadmap` succeeded in [run 36285293310](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36285293310); no security check was returned. |

For each exact PR revision, the missing check is an API-level observation bound
to the check-runs endpoint, query, capture time, total count, and complete
returned first page in the saved artifact. No provider run/job ID exists for a
missing check, so none is fabricated. These observations do not show that the
provider permanently retired the check, that a scan was clean, or that any
failure should be suppressed. Recheck the exact head before using this dated
snapshot as operational evidence.

The checked-in `scripts/ci_gate_inventory.json` classifies this check as
auxiliary and `required: false`, applicable to PRs. At the same capture time,
the live required-status-check endpoint reported `strict: true` and only `ci`
as a required context. Optional status does not mean invisible: provider
failures remain reportable, and `ci` remains required.

## Owner decision paths

The minimum repair and valid alternatives are:

| Path | Required action | Coverage and authority |
|---|---|---|
| Repair the existing integration | First identify whether the dynamic workflow, GitHub app, or ruleset owner controls the identity. That owner must correct the Copilot SDK authentication/licensing configuration and provide successful runs for the revisions required by the issue, plus a benign negative fixture whose expected finding is observed. | An owner/admin entitlement or account action may be required and could involve a license. No repository change can grant that entitlement. Report `verified_scan` only with the workflow/run/job, candidate revision, scanner scope, hashed result artifact, and executed negative-fixture proof bound together. |
| Replace the integration | The owner selects and names a replacement, then verifies PR and `main` execution where configured and the negative fixture. | Replacement requires a written coverage inventory and owner acceptance of gaps. GitHub documents CodeQL code scanning as available for public repositories and lists Python and GitHub Actions among its supported languages; Lean is not on the supported list, so CodeQL alone would not cover the Lean source. See [Code scanning with CodeQL](https://docs.github.com/en/code-security/concepts/code-scanning/codeql/codeql-code-scanning) and [About GitHub Advanced Security](https://docs.github.com/en/get-started/learning-about-github/about-github-advanced-security). |
| Retire the integration | The owner explicitly approves retirement, records the reason and exact reviewed revision, assigns a follow-up for removed coverage, and retires the provider-owned check through its actual owner. | Retirement is a separate disposition with a coverage loss. It is not a passing scan and must not be normalized to `verified_scan`. |

Until an owner selects and completes one of these paths, keep the issue open and
the provider's errors visible. Do not add `continue-on-error`, fabricate a
success status, weaken required `ci`, or remove the check to make a PR green.

## Evidence contract and validator boundary

For issue-level closure, require separate successful execution records for the
current PR revision and for `main` where configured. Each record must bind its
own workflow, run, job, candidate SHA, scanner scope, hashed result artifact,
and executed negative fixture with its expected finding observed. A single
run's free-form scope list is not evidence of both environments.

The existing `scripts/security_evidence.py` validator checks one JSON execution
record at a time. For `verified_scan`, it checks the run/job and candidate-SHA
bindings, artifact digest fields, negative-fixture fields, and zero findings;
however, it only requires `scope` to be a non-empty string array. It does not
aggregate a PR record with a separate `main` record or enforce which scopes are
supported. Its current test accepts `pull_request` and `push:main` in the scope
array of one run. Therefore a valid single-record result from
`security_evidence.py` is not, by itself, proof of the issue's separate
PR-and-`main` closure requirement.

The labels `successful-but-unverified` and `missing/unknown` in this diagnosis
are documentation classifications. The current JSON validator has no separate
successful-but-unverified or missing-check disposition and requires workflow,
run/job IDs, provider, phase, and conclusion. A missing-check observation is
instead recorded from the check-runs API snapshot above; it is not a validator
input and does not invent a run ID. An unverified success, an absent check, or
an empty proof is not coverage. Replacement or retirement decisions require
an owner, reason, timestamp, exact reviewed revision, and follow-up; they
remain distinct from scan outcomes.
