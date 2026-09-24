# Spec Delta

## Purpose

This capability completes the remaining abstract and geometric Serre-duality obligations in milestone SRF1 while preserving the repository’s explicit finiteness, representability, and supplied-data boundaries.

## ADDED Requirements

### Requirement: A right Serre functor is fully faithful under finite Hom hypotheses

The library SHALL prove full faithfulness of a Serre functor when every Hom space is finite-dimensional. It SHALL derive essential surjectivity only from a separate co-Serre duality input; a right Serre functor alone does not imply an equivalence.

#### Scenario: Finite Hom spaces give full faithfulness
- **WHEN** a `k`-linear category has finite-dimensional Hom spaces and carries Serre duality data
- **THEN** the Serre endofunctor is proved fully faithful using the finite-dimensional double-dual map

#### Scenario: Co-Serre data supplies the missing equivalence direction
- **WHEN** the same category also carries natural co-Serre duality data
- **THEN** the duality data yields an adjunction, the co-Serre functor is proved fully faithful, and the Serre endofunctor is proved an equivalence

#### Scenario: Full faithfulness alone does not claim an equivalence
- **WHEN** only right Serre duality and finite Hom spaces are available
- **THEN** the API provides full faithfulness without claiming essential surjectivity or an equivalence

### Requirement: Autoequivalence and shift transport use valid Serre data

The library SHALL derive transport of Serre duality along a `k`-linear autoequivalence by conjugating the Serre functor and applying uniqueness. When a compatible triangulated structure is available, it SHALL derive shift commutation, its additive coherence, the supported triangulated equivalence, and the resulting Hom-built Euler-form symmetry under the stated finiteness hypotheses.

#### Scenario: A linear autoequivalence transports the Serre functor
- **WHEN** a `k`-linear autoequivalence acts on a category with Serre data
- **THEN** the conjugated functor is shown to carry Serre data and uniqueness gives the natural transport isomorphism

#### Scenario: Shift compatibility yields the triangulated consequences
- **WHEN** the Serre functor is an equivalence on a pretriangulated category with linear shifts
- **THEN** shift commutation and its coherence are proved, the available exactness obligations are discharged, and the Hom-built Euler form has the specified Serre symmetry

#### Scenario: The invalid shifted-Serre shortcut is rejected
- **WHEN** one attempts to prove shift commutation by treating either composite of the shift with the Serre functor as a Serre functor
- **THEN** the implementation does not apply uniqueness to those composites and instead uses conjugation or the exported representability result

### Requirement: Geometric Serre duality remains explicit supplied data

The library SHALL represent the smooth-proper geometric bridge as supplied data carrying derived-category duality, both naturality laws, Hom-finiteness, and compatibility with the existing sheaf-level duality only in its stated range. It SHALL repackage this input as categorical Serre data without claiming an inhabitant or deriving the missing comparison from sheaf-level data alone.

#### Scenario: Supplied geometric data projects to categorical Serre data
- **WHEN** a smooth proper variety, canonical-sheaf input, and a supplied geometric Serre-duality witness are available
- **THEN** its twist-and-shift functor and supplied duality fields repackage as categorical Serre data

#### Scenario: Sheaf compatibility stays within its supported range
- **WHEN** the geometric compatibility field compares derived duality to the existing bilinear sheaf data
- **THEN** it is restricted to sheaf objects and degrees `0 ≤ i ≤ n`, through explicit Ext-to-derived-Hom comparison data

#### Scenario: Missing geometric inputs are not inferred
- **WHEN** only the existing sheaf-level `BilinearData` is available
- **THEN** the API does not infer derived-category naturality, Hom-finiteness, or an Ext-to-derived-Hom comparison, and documents why the geometric structure is presently uninhabited
