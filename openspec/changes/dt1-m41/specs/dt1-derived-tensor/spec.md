# Spec Delta

## Purpose

This capability records the construction and bounded-transfer obligations for
the first inhabited derived tensor in milestone #41 while preserving the
repository's mathematical and architectural trust boundary.

## ADDED Requirements

### Requirement: The tensor-derived left derived interface is inhabited

The implementation SHALL provide a localization-based left-derived tensor
bifunctor for the supported scheme derived category, a
`TensorAcyclicResolution` contract for its construction, an explicit counit
against the degreewise module-sheaf tensor, and a fixed-argument
`Functor.IsLeftDerivedFunctor` universal-property witness. The exact/identity
resolution case SHALL be available from explicit inversion or exactness data.

#### Scenario: Supported resolution constructs the bifunctor

- **WHEN** a tensor-acyclic resolution supplies its comparison quasi-isomorphism
  and localization inversion obligations
- **THEN** the implementation produces a derived tensor bifunctor and a
  counit whose factors agree with the existing degreewise tensor after
  localization

#### Scenario: Fixed argument has the derived universal property

- **WHEN** one argument is fixed in the supported derived tensor bifunctor
- **THEN** the corresponding functor carries a proved
  `Functor.IsLeftDerivedFunctor` witness, rather than only a named functor or
  an existence marker

#### Scenario: Exact identity case

- **WHEN** the left tensor factor is covered by the explicit exact/inversion
  hypothesis
- **THEN** the identity resolution yields the canonical exact comparison with
  the degreewise tensor-derived functor

#### Scenario: Missing acyclicity data

- **WHEN** a proposed resolution lacks a comparison quasi-isomorphism or the
  required inversion proof
- **THEN** the API does not manufacture a left-derived tensor or universal
  property from a marker class

### Requirement: The coherent bounded derived tensor structure is assembled

The implementation SHALL transfer the ambient additive, commutative-shift,
and triangulated exactness data along the existing bounded coherent inclusion
and SHALL provide a `HasCoherentDerivedTensor.ofUnbounded` constructor. The
constructor SHALL reuse the existing bounded monoidal restriction and expose
all ambient exactness and closure hypotheses explicitly.

#### Scenario: Ambient structure transfers to bounded coherent objects

- **WHEN** the ambient derived category has the required monoidal and
  per-kernel exactness data and the bounded property is monoidal
- **THEN** the bounded coherent tensor class has named additive,
  commutative-shift, and triangulated transfer witnesses

#### Scenario: Constructor produces the existing coherent interface

- **WHEN** `HasCoherentDerivedTensor.ofUnbounded` is applied to the explicit
  ambient hypotheses
- **THEN** it produces the repository's existing coherent tensor class and
  its `HasDerivedTensor` projection, without a duplicate bounded monoidal root

#### Scenario: Missing closure or exactness hypothesis

- **WHEN** the bounded property is not monoidal or an ambient exactness proof
  is absent
- **THEN** the constructor is unavailable and no bounded coherent tensor
  structure is inferred by an unproved instance
