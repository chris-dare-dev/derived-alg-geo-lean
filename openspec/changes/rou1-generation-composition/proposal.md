# Proposal

## Why

Rouquier dimension and generation time already measure finite extension stages, but the API needs a composition law that describes what happens when generation passes through an intermediate object property. Generation time itself is not additive; the useful invariant is generation time plus one, which is submultiplicative, and the same envelope argument gives the bounded object-property form of Stacks 0FXA.

## What Changes

- Prove the stage-zero fixed-point, iterated-envelope composition, and transfer bounds for Mathlib's existing `triangEnvelopeIter` operation.
- Derive the `ℕ∞` generation-time-plus-one inequality, record why the additive inequality is false, and state the bounded strong-generator transfer and its single-object classical-generator corollary.
- Derive the finite Rouquier-dimension consequences for classical generators, while preserving the distinction between objectwise finite stages and a uniform bound for an arbitrary object property.

## Capabilities

### New Capabilities

- `triangulated-generation-composition`: Composition and transfer laws for iterated triangulated envelopes, generation-time consequences, and the bounded object-property form of Stacks 0FXA.

### Modified Capabilities

None.

## Impact

Issue #920 in milestone ROU1. The Mathlib `ObjectProperty.triangEnvelopeIter` extensions belong beside the pinned generator API in `DerivedAlgGeo/CategoryTheory/Triangulated/Generators/Composition.lean`; generation-time and Rouquier consequences belong in `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Composition.lean`. The existing `Triangulated/Generators.lean` and `Triangulated/Dimension.lean` umbrellas and the dimension audit are extended. No new closure carrier is introduced, and these generic results import neither algebraic geometry nor stability conditions.
