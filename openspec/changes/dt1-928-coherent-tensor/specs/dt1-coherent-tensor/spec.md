# Spec Delta

## Purpose

This capability makes a supplied coherent exact tensor on an ambient coherent
derived category available on its bounded coherent full subcategory without
claiming unproved boundedness or ambient-comparison theorems.

## ADDED Requirements

### Requirement: Full-subcategory two-variable exactness transfer

The library SHALL transfer a supplied two-variable exact functor to a full
subcategory whenever the stated closure, shift, and triangulated hypotheses
hold. The transferred structure MUST retain both-variable shift naturality and
the Koszul compatibility, not merely separately selected fixed-variable data.

#### Scenario: Closed exact bifunctor restricts

- **WHEN** an ambient exact bifunctor preserves a full subcategory satisfying
  the required closure and triangulated hypotheses
- **THEN** the restricted bifunctor carries complete two-variable shift
  coherence and exactness in both variables

#### Scenario: Closure or coherence is absent

- **WHEN** the required closure or ambient two-variable coherence is not
  supplied
- **THEN** the library does not infer a restricted exact bifunctor or hide the
  missing obligation in a new instance

### Requirement: Conditional coherent bounded tensor assembly

The library SHALL assemble a coherent bounded tensor only from separately
supplied monoidal and exact tensor data on the ambient coherent derived category
and an explicit boundedness-closure hypothesis. The assembly MUST expose named
fixed-kernel additive, shift, and triangulated consequences and MUST preserve
the existing one-way projection to the raw bounded tensor capability.

#### Scenario: Ambient coherent tensor is supplied

- **WHEN** the ambient coherent derived category has the required monoidal and
  two-variable exact tensor data and bounded coherent objects are closed under
  that tensor
- **THEN** the bounded coherent category receives the existing coherent tensor
  interface and its existing raw-tensor projection

#### Scenario: Module-sheaf tensor has no coherent-ambient comparison

- **WHEN** only a tensor on the derived category of all module sheaves is
  available and no comparison to the coherent ambient category is supplied
- **THEN** the bounded coherent assembly remains unavailable and no comparison
  or preservation theorem is asserted

#### Scenario: Boundedness closure is absent

- **WHEN** bounded coherent objects are not explicitly known to be closed under
  the ambient tensor
- **THEN** no coherent bounded tensor structure is inferred
