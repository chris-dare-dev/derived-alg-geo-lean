# GitHub Advanced Security integration diagnosis

The optional `github-advanced-security` check is currently failing before a
scanner can produce a result. The four observed failures are provider/account
failures, not reported repository findings:

| PR | run | job | observed failure |
|---:|---:|---:|---|
| #1415 | 35530799100 | 106130918882 | Copilot SDK session initialization returned HTTP 403/authentication: not licensed to use Copilot |
| #1419 | 35530798806 | 106130918769 | Copilot SDK session initialization returned HTTP 403/authentication: not licensed to use Copilot |
| #1424 | 35530799092 | 106130918968 | Copilot SDK session initialization returned HTTP 403/authentication: not licensed to use Copilot |
| #1427 | 35530798284 | 106130917005 | Copilot SDK session initialization returned HTTP 403/authentication: not licensed to use Copilot |

The dynamic workflow is provider-generated (`dynamic/agents/github-advanced-
security`) and is not a checked-in workflow in this repository. Repository code
cannot grant the missing Copilot entitlement. The checked-in observation
fixture and `scripts/security_evidence.py` deliberately reject classifying this
failure as a verified clean scan.

## Closure decision

The repository may claim this issue resolved only after one of these exact
evidence paths is recorded:

1. Provider configuration is repaired, the scanner runs successfully on a PR
   and on `main`, and a benign negative fixture proves that a real finding is
   surfaced.
2. The owner approves a named replacement scanner, its PR/main execution and
   negative fixture are verified, and the old optional check is retired or
   replaced without weakening the required `ci`/`trust-surface` contract.
3. The owner explicitly approves retirement of this optional integration, with
   the security coverage it removes documented and a follow-up issue/milestone
   assigned. Retirement is not a passing scan and must not be represented as
   one.

Until one path is evidenced, keep the failure visible and classify it as
`provider_failure`; do not add `continue-on-error`, fabricate a success
status, or silently remove the check.
