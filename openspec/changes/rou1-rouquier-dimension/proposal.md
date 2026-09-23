# Proposal

## Why

The library now measures extension steps for an object property, but it lacks the category-level invariant that minimizes this count over single objects. Rouquier dimension is the natural next API and gives a precise way to state when a triangulated category has a strong or classical generator.

## What Changes

- Define Rouquier dimension as the infimum of the existing generation time from singleton object properties.
- Prove finite-bound, finite-dimension, classical-generator, and zero-dimension characterisations, with the `⟨G⟩_{n+1}` indexing convention stated explicitly.
- In a successor chunk, transport envelope membership and generation time along triangulated functors, then prove the target-dimension inequality for essentially surjective functors and invariance under equivalence.

The successor transport work is issue #921 and remains separate from the core definition in issue #919. This plan does not include issue #920's composition law or Stacks 0FXA.

## Capabilities

### New Capabilities

- `triangulated-generation-dimension`: Rouquier dimension and its generator characterisations, followed by forward transport through triangulated functors.

### Modified Capabilities

None.

## Impact

Issues #919 and #921 in milestone 39. The code belongs under `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/`; the existing `Dimension.lean` umbrella and `scripts/StabilityConditionAudit/Dimension.lean` audit slice are extended in issue order. The new files remain generic and import neither algebraic geometry nor stability conditions.
