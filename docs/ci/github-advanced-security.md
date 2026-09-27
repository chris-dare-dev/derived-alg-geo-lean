# Security scanner decision and evidence

The optional `github-advanced-security` check was GitHub's provider-generated
**AI Scan for pull requests**, not a checked-in workflow or a separate check
app. Its workflow ID was `360047049`, path
`dynamic/agents/github-advanced-security`, event `dynamic`, and actor
`github-advanced-security[bot]`. Its check-run app was `github-actions` (ID
`15368`). Matching the check name alone, or expecting an app slug of
`github-advanced-security`, misidentifies it.

As observed on 2026-09-27, `GET /code-scanning/ai-scan` reported
`pr_scan: disabled`; CodeQL default setup reported `state: not-configured`
with `actions` and `python` detected. These are dated settings observations,
not a present scan or an owner-approved retirement. AI Scan's last observed
run was [35812428038](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35812428038)
on 2026-09-23. No later absent check is a passing scan. The protected branch
requires `ci`; this scanner is optional, so its failure remains visible but
does not become a required-check failure.

At 2026-09-27 17:24 UTC, the setting was still `disabled`. A paginated read
of **all five then-open PR heads** found no dynamic AI Scan run and no
`github-advanced-security` check on [#1601](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1601),
[#1602](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1602),
[#1603](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1603),
[#1604](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1604), or
[#1605](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1605).
The head SHA, run/check counts, setting response and request interval are in
the owner-only archive's `probes/1433-security/open-pr-heads-2026-09-27T1724Z.json`
(SHA-256 `558ac56cc9f3234700987352caf7f75a9b34e8779fb8507c96a359c98b647172`).
This is a bounded snapshot, not a claim about later PRs.

## Historical diagnosis

The four target runs all constructed a prompt, then failed while creating a
Copilot session with HTTP 403 `SessionModelError: You are not licensed to use
Copilot` (`errorType: authentication`). They stopped before analysis and did
not report vulnerability findings.

| PR | Provider run | Check/job | Classification |
| --- | --- | ---: | --- |
| [#1415](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1415) | [35530799100](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799100) | 106130918882 | Entitlement failure before analysis |
| [#1419](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1419) | [35530798806](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798806) | 106130918769 | Entitlement failure before analysis |
| [#1424](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1424) | [35530799092](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530799092) | 106130918968 | Entitlement failure before analysis |
| [#1427](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1427) | [35530798284](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/35530798284) | 106130917005 | Entitlement failure before analysis |

The owner-only archived recount at
`~/.loop-runs/transcripts/analysis/2026-09-27-m54-recovery/probes/1433-security/`
classifies all 237 dynamic runs from September 16–23: 201 failed at that
Copilot entitlement step; 36 succeeded only after all changed files matched
the provider exclusion list and no prompt or model session was opened. That
green state is **vacuous**. The apparent #1426 and #1427 successes do not
demonstrate analysed clean changes; #1426 also predates the four target
failures. The archived redacted logs and `t4_classification.tsv` support the
counts; GitHub check colours alone do not.

Current check absence must be bound to a PR head SHA, a complete paginated
check/run query, a request time and the provider setting response. A missing
run has no run or job ID. A disabled setting plus no run means
`disabled_by_setting`; an enabled setting plus no run means `missing`; an
unavailable setting means `provider_state_unknown`. A failed dynamic run is
`unclassified_failure` from check colour alone; the archived four 403
diagnoses use redacted logs. It is not automatically a security finding. A
raw green dynamic run does not prove analysis or zero findings. Keep the raw
conclusion and evidence separately.

## Decision record for the owner

No path has been selected or applied. The minimum legitimate choices are:

| Choice | Owner action and evidence needed | Coverage |
| --- | --- | --- |
| Repair AI Scan | Confirm the GitHub Advanced Security and Copilot entitlements and AI-credit implications; re-enable `pr_scan`; run an eligible disposable PR through analysis and show a benign finding in a provider-defined, head/run-linked result channel. If only a green check or prompt build is visible, the result remains unknown. | [GitHub documents AI Scan](https://docs.github.com/en/code-security/concepts/code-scanning/ai-powered-security-detections) as PR-only and advisory during preview. Neither a `main` scan nor Lean/Markdown coverage is established here. |
| Replace with CodeQL | Approve default setup or a separately chosen advanced setup; observe its actual check identity and successful analyses on the selected PR and `main` revisions; prove an expected finding on a disposable unmerged fixture. Retire the old optional gate only after recording the replacement and its scope. | [CodeQL lists Python and GitHub Actions](https://codeql.github.com/docs/codeql-overview/supported-languages-and-frameworks/) but not Lean. [Default setup](https://docs.github.com/en/code-security/concepts/code-scanning/setup-types) can scan PRs, default-branch pushes and on a schedule, subject to its configured eligibility. |
| Retire AI Scan without replacement | Explicitly approve the loss of code-analysis coverage, preserve the historical 403/vacuous record and name a follow-up. Do not call retirement a scan success. | Secret scanning and push protection remain distinct; neither proves code analysis. |

The existing `scripts/security_evidence.py` validates one normalized execution
observation. It cannot by itself prove distinct PR and `main` analyses for a
replacement or establish a provider-defined zero-findings result. The first
progress slice fixes evidence classification only. Issue #1433 remains open
until a selected path is applied and its own closure evidence is verified.
