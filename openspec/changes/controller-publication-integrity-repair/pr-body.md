## Scope

Complete the controller safeguards requested by #1458, #1459, and #1460 using
a fresh, bounded run tracked by #1482. The implementation reconstructs ledger
authority from the validated manifest, binds reviews and deferred findings to
exact evidence, checks all changed paths, revalidates mutation authority at
the action boundary, and requires exact reviewed-head snapshots for PR
creation and draft readiness.

## Verification

- Focused controller tests cover the previously reported bypasses and refusal
  paths.
- Strict OpenSpec validation, manifest validation, and `scripts/precheck.sh
  --no-build` are reported separately from hosted CI.
- Seven independent reviewers review the same frozen candidate commit within
  the three-round cap.
- Hosted pull-request CI and the separately dispatched self-hosted CI lane must
  pass before merge.

## Publication and closure

This controller-owned change uses the documented one-time manual publication
path after a passing exact-commit panel and fresh remote checks. Its manifest
stays disabled and grants no provider mutations. The PR does not authorize
self-approval, merge, or application of the `trust-reviewed` label.

Closes #1458
Closes #1459
Closes #1460
Closes #1461
Closes #1462
Closes #1482
