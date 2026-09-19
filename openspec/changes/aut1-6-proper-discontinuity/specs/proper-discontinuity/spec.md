# Spec Delta

## Purpose

This capability records the external geometric input for a properly
discontinuous compatible-autoequivalence action and exposes only the
point-stabilizer, local-topology, quotient-separation, and free-locus covering
consequences justified by that input.

## ADDED Requirements

### Requirement: Proper discontinuity is supplied as external data

The formalization SHALL expose a proposition-valued data boundary for a class
map `v : K₀ C →+ Λ` with fields asserting proper discontinuity of the
`AutPairQuot v` action, surjectivity of `v`, and local compactness of the
stability space with class map.  The data boundary MUST not claim that these
fields are inhabited in the generic stability API.

#### Scenario: A consumer supplies the geometric hypotheses

- **WHEN** a consumer has a properly discontinuous action, a surjective class
  map, and a locally compact stability space
- **THEN** the consumer can package exactly those facts as the external data
  required by this capability.

### Requirement: Proper discontinuity gives finite point stabilizers

The formalization SHALL derive that the stabilizer of every individual
stability condition under `AutPairQuot v` is finite using only the supplied
proper-discontinuity field.  Surjectivity and local compactness MUST NOT be
required for this consequence.

#### Scenario: Point stabilizer is queried

- **WHEN** proper discontinuity is supplied for the action and a stability
  condition is chosen
- **THEN** the corresponding point-stabilizer set is proved finite without
  using the other two data fields.

### Requirement: Proper discontinuity gives the two local neighborhood consequences

The formalization SHALL provide both standard neighborhood consequences: a
neighborhood whose translate can meet it only when the acting element fixes the
chosen point, and a neighborhood disjoint from every translate by an element
that does not fix that point.  These results MUST use all hypotheses actually
needed by the underlying topology: proper discontinuity, local compactness,
the Hausdorff result supplied by surjectivity, and continuity of the constant
scalar action.

#### Scenario: A local action neighborhood is requested

- **WHEN** all four topological/action hypotheses are available at a stability
  condition
- **THEN** both local neighborhood conclusions are available with the acting
  group quantified explicitly.

### Requirement: The compatible-autoequivalence orbit space is Hausdorff

The formalization SHALL derive a `T2Space` instance for the orbit space of the
`AutPairQuot v` action from proper discontinuity, local compactness,
surjectivity-induced Hausdorffness, and continuous constant scalar action.

#### Scenario: Orbit-space separation is used downstream

- **WHEN** a consumer supplies the external data
- **THEN** the compatible-autoequivalence orbit space can be used as a
  Hausdorff topological space without an additional unproved separation axiom.

### Requirement: The covering claim is restricted to the free locus

The formalization SHALL provide a covering-map-on statement for the orbit
projection restricted to the image of the free locus, where the point
stabilizer is trivial.  It MUST NOT assert an unrestricted quotient covering
map for an action that may have nontrivial stabilizers.

#### Scenario: A free orbit is covered

- **WHEN** a point lies in the image of the trivial-stabilizer locus
- **THEN** the orbit projection satisfies the covering-map-on conclusion over
  that image.

#### Scenario: A point has nontrivial stabilizer

- **WHEN** an orbit contains a point with nontrivial stabilizer
- **THEN** this capability makes no unrestricted covering-map claim at that
  orbit.

### Requirement: Missing geometric consequences remain explicit non-goals

The formalization SHALL document that no generic inhabitant of the external
data is constructed.  In particular, it MUST NOT claim arithmetic control of
the compatible image in lattice isometries, local finiteness of the relevant
walls, finite-dimensionality or local compactness from absent hypotheses, or
finiteness of a chamber's setwise stabilizer merely from point-stabilizer
finiteness.

#### Scenario: A consumer asks for a generic witness

- **WHEN** no arithmetic, wall-local-finiteness, and finite-dimensionality
  inputs have been supplied
- **THEN** the capability exposes no witness and does not turn the requested
  geometric construction into an interface field.

#### Scenario: A consumer asks for chamber stabilizer finiteness

- **WHEN** only proper discontinuity of the point action is available
- **THEN** no chamber-stabilizer finiteness theorem is claimed.
