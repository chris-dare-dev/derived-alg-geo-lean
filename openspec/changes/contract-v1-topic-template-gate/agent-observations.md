# Agent Observations

## 2026-09-23

- The live acceptance criteria are #182 (zero Bridgeland-specific template strings, optional anchor, Copier answers and update path) and #183 (one ingested paper, five sourced entries, one exact Mathlib binding). #137 is the parent epic. The user explicitly authorized the full batch.
- Contact email is optional metadata, not an arXiv API prerequisite. The analytic paper was parsed through ar5iv after the raw `/e-print/` endpoint returned 406, and ingested into the notebook.
- The analytic adopter has exactly five registry entries. Four quote digests bind to ingested paper chunks; the Iwaniec–Kowalski row is explicitly a publisher contents locator and does not claim inspection of the textbook theorem text.
- Registry validation passed (13 passed, 0 failed, 0 not-run). The adopter build passed. External emission contains `Nat.infinite_setOf_prime` with `scope: external` and `relation_claimed: exact`; MFC bundle, lint, and coverage commands passed. The environment digest and trust evidence were recorded against the exact template commit.
- MathFormalContract PR #24, `https://github.com/chris-dare-dev/math-formal-contract-lean/pull/24`, merged as `495c67d8752dcb5455eca876178c835b510e2bac` after all five hosted checks passed. Its contract suite passed locally (632 passed, 3 skipped).
- Issues #182 and #183 were closed after that merge; parent issue #137 was closed after both children.
- The optional-email change in arXMCP passes Ruff and the full test suite (5,551 passed, 147 skipped, 1 xfailed). It remains staged but unpublished because the repository requires GPG-signed commits and this host has no secret signing key. That change was not an acceptance prerequisite for the completed gate.
- The issue-first procedure is documented for active user-started Codex work; the manifest controller remains available for standalone unattended runs. Its DerivedAlgGeo PR is still to be opened and reviewed.
