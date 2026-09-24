# Agent Observations

## 2026-09-23

- The live acceptance criteria are #182 (zero Bridgeland-specific template strings, anchor optional, Copier answers and update path) and #183 (one fetched/ingested paper, five entries, one exact Mathlib binding). #137 is the parent epic. The user explicitly authorized the full batch.
- The old arXMCP email gate was incorrect. A neutral application User-Agent works with ar5iv; email is now optional contact metadata. Raw arXiv `/e-print/` returned 406, while the parsed ar5iv paper was fetched and ingested into the notebook.
- The analytic adopter has exactly five registry entries. Four quote digests bind to ingested paper chunks; the Iwaniec–Kowalski row is explicitly a publisher contents locator and does not claim inspection of the textbook theorem text.
- Registry validation passed (13 passed, 0 failed, 0 not-run). The adopter build passed after fixing the generated emitter to import and qualify `Lean.Name`. External emission contains `Nat.infinite_setOf_prime` with `scope: external` and `relation_claimed: exact`; MFC bundle, lint, and coverage commands passed. The environment artifact still needs a clean committed source revision before the final digest/trust update.
- Full arXMCP validation initially exposed two tests that still enforced mandatory email. Those expectations were corrected to match optional contact behavior; the full suite is running again.
- The MFC template change adds the missing `Lean` import/qualification in the generated emitter and a scaffold regression assertion. MFC contract tests, final generated adopter update, and PR publication remain.
