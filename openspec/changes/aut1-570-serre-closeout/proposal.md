# Proposal

## Why

Issue #570 is still open even though its implementation was completed in the
landed S2-A/S2-B/S2-C work and the follow-on tensor-inverse change. The current
remote baseline already contains the general coproduct epimorphism theorem and
the `Pⁿ` coherent short-exact presentation, but the issue text and two nearby
module docstrings still describe the old `Γ_*` route and the former blocker.

This closeout makes the completed mathematics auditable, removes those stale
directions from the repository guidance, records the operational friction for
future agents, and closes the parent issue through the bounded controller.

## What Changes

- Capture the exact #570 acceptance contract in an OpenSpec capability, tied to
  `exists_epi_coproduct_twistingSheaf_ge` and
  `exists_shortExact_coproduct_twist`.
- Correct the stale route description in `TwistSection.lean` and the final
  theorem pointer in `Glue.lean` so future agents distinguish section
  extension, global generation, and the untwisted coproduct epimorphism.
- Correct the projective-space presentation theorem's typeclass boundary so
  finite nonempty index types include `P⁰`; retain `[Nontrivial ι]` only on
  the separate negative-twist cohomology-finiteness declarations.
- Record repository and controller inconsistencies in
  `agent-observations.md` and in the loop ledger/issue handoff.
- Do not add a second Serre carrier, a global-generation instance, a
  `\Gamma_*` correspondence, or any new mathematical axiom. The mathematical
  API being reconciled is already on `origin/main`.

## Capabilities

### New Capabilities

- `projective-serre-quotient`: the verified theorem-level contract that a
  coherent sheaf on projective space has a finite negative-twist coproduct
  presentation, with the general Proj module theorem as its source.

### Modified Capabilities

- `projective-serre-quotient`: the existing projective presentation is exposed
  under the correct finite-nonempty hypothesis, including the singleton
  projective space, without adding a second theorem or API.

## Impact

- Lean source: two module docstrings and one typeclass-context correction in
  the existing projective presentation file; no imports or new declarations
  change.
- OpenSpec and loop metadata: one closeout change and one enabled independent
  loop manifest for issue #570.
- Provider state: the controller will create, verify, merge, and use the PR to
  close #570 after the four-role adversarial panel and required CI checks pass.
- Verification: OpenSpec strict validation, loop validation/preflight,
  targeted Proj theorem builds, `scripts/precheck.sh`, the review ledger, and
  the remote required checks. No whole-repository local build is in scope.
