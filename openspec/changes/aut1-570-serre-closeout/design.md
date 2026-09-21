# Design

## Existing mathematical surface

The completed route is already split along the repository's mathematical
owners:

1. `ProjectiveSpectrum/Modules/ChartGeneration.lean` obtains finitely many
   local chart generators from coherence.
2. `ProjectiveSpectrum/Modules/GlueUniform.lean` extends all chart generators
   with one common exponent.
3. `ProjectiveSpectrum/Modules/GlobalGeneration.lean` proves
   `free I ↠ F ⊗ O(N)` by local combinations; it does not assume global
   generation.
4. `ProjectiveSpectrum/Modules/TwistInverse.lean` uses the proved inverse of
   `O(N)` to obtain `∐ O(-N) ↠ F`.
5. `Cohomology/Finiteness/Projective.lean` specializes that result to the
   polynomial grading and lifts it to a coherent short exact sequence. The
   presentation theorem needs only `[Fintype ι] [Nonempty ι]`, while the
   separate negative-twist cohomology-finiteness theorems correctly retain
   `[Nontrivial ι]`.

The source-of-truth declarations are reused directly. This closeout introduces
no carrier, class, instance, comparison map, or alternate `Γ_*` presentation.
The direct route is also why the final statement is stronger and more honest
than treating the initial issue sketch as an unfinished graded-module
construction.

## Repository ownership and boundaries

The affected source docstrings remain under
`AlgebraicGeometry/ProjectiveSpectrum/Modules/`, where the Proj and module
objects are owned. No generic tensor API is copied into the projective lane,
and no cohomology theorem is moved into the module layer. The audit records for
the existing declarations remain the authoritative trust surface.

The source edits remain in files that already own the claims: explanatory
docstring corrections and the typeclass-boundary correction identified by the
mathematics reviews. The final documentation-hygiene chunk also qualifies the
alternative-twist and degree-one-generation prose without changing a theorem.
OpenSpec artifacts and each fresh manifest are frozen alongside the source so
the review panel evaluates the corrected closeout evidence and not a later
expansion.

## Closeout evidence

- Strict OpenSpec validation and controller validation/preflight.
- Targeted builds of the existing Proj presentation and inverse modules, with
  `LEAN_NUM_THREADS=2`; never the all-library umbrella.
- `scripts/precheck.sh`, whose local verdict is explicitly not a CI verdict.
- Four independent reviewers on one immutable commit:
  `mathematics-adversary`, `repository-boundary-adversary`,
  `abstraction-adversary`, and `mathlib-reviewer`.
- At most three review/improve rounds for this frozen chunk. A third failing
  adjudication is terminal; no speculative fourth pass or scope widening is
  permitted.
- Required remote `ci` and `trust-surface` checks before controller merge.
- The first review round is preserved as evidence for the superseded manifest;
  the corrected source scope starts a fresh bounded chunk, with the same
  three-round maximum and the same four independent reviewer roles.
- The prior scope-correction chunk reached its hard cap and is intentionally
  terminal; the documentation-hygiene chunk has its own digest-bound ledger
  and must pass its own panel before provider actions.

## Known non-goals

- Do not re-prove the already-landed S2-A/S2-B/S2-C declarations.
- Do not construct `Γ_*(F)` or assert the full Serre correspondence merely
  because the original issue suggested that route.
- Do not generalize `IsInvertible L` to a chosen tensor inverse for every line
  bundle; #806's broader question remains separate.
- Do not run the whole repository locally or weaken a failing repository gate.
