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

## Current PR-head snapshot

Captured at **2026-09-27 01:43:13 UTC** from PR metadata and the GitHub
check-runs API. These observations are bound to the listed full head revisions.

| PR head | Security check observation | Other check status at capture |
|---|---|---|
| [#1566](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1566), [`06079755b65fb71c14d8f655832829e4b8bf65fd`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/06079755b65fb71c14d8f655832829e4b8bf65fd) | No `github-advanced-security` check run appeared in the three returned check runs; classify this head as missing/unknown. | `build`, `roadmap`, and required `ci` succeeded in [run 36273289044](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36273289044). |
| [#1568](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1568), [`5364d5bc2c7aaaf81953ef78583c7a7fd192489d`](https://github.com/chris-dare-dev/derived-alg-geo-lean/commit/5364d5bc2c7aaaf81953ef78583c7a7fd192489d) | No `github-advanced-security` check run appeared in the two returned check runs; classify this head as missing/unknown. | `roadmap` succeeded and `build` was in progress in [run 36286127013](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/36286127013); required `ci` had not yet appeared. |

The missing observations do not show that the provider permanently retired the
check, that a scan was clean, or that any failure should be suppressed. Recheck
the exact current head before using these entries as operational evidence. The
existing `scripts/ci_gate_inventory.json` classifies this check as auxiliary
and `required: false`, applicable to PRs; the live `main` branch-protection API
listed only `ci` as a required context at capture. Optional status does not
mean invisible: provider failures remain reportable, and `ci` remains required.

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

## Evidence contract

The normalized `verified_scan` disposition is intentionally strict: successful
PR and `main` executions must bind the workflow, run, job, candidate revision,
scanner scope, and a hashed result artifact, and include an executed negative
fixture whose expected finding was observed. An empty proof object, an
unverified provider success, or an absent check is not coverage. Replacement or
retirement decisions require an owner, reason, timestamp, exact reviewed
revision, and follow-up; they remain distinct from scan outcomes.
