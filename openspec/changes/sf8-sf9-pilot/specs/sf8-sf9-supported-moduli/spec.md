# Spec Delta

## Purpose

This capability records the construction and algebraicity obligations needed to
advance the supported SF8/SF9 relative-perfect moduli chain without weakening
the repository's mathematical trust boundary.

## ADDED Requirements

### Requirement: Supported arbitrary derived pullbacks are constructed

The implementation SHALL construct the supported arbitrary derived pullback
objects required by SF8.5 (#554), including the stated K-flat/resolution,
inhabitation, preservation, coherence, comparison, and non-flat nonidentity
obligations, rather than merely adding an interface that names them.

For this pilot, "supported" means the explicitly named input class and
hypotheses already accepted by the SF8.5 issue contract and the repository's
derived-category interfaces. The required hypotheses SHALL be explicit in the
Lean statement or supplied by a proved instance; they SHALL NOT be inferred
from an unproved marker typeclass introduced by the chunk.

#### Scenario: Nontrivial supported pullback

- **WHEN** the supported non-flat, nonidentity example is instantiated
- **THEN** the construction produces the claimed derived pullback data and the
  relevant comparison maps are proved, with no sorry or postulated existence

#### Scenario: Progress witness before the full issue contract

- **WHEN** a frozen progress chunk instantiates the supported non-flat,
  nonidentity affine witness
- **THEN** the witness and its supported pullback data are actual Lean terms,
  the PR uses a non-closing reference to #554, and the controller leaves #554
  open until the remaining preservation and coherence obligations pass

#### Scenario: Nonzero derived effect in the supported affine lane

- **WHEN** the two-term free resolution of `ZMod 2` is pulled back along
  `ℤ → ZMod 2`
- **THEN** the resulting affine bounded-projective derived object has a
  proved nonzero degree-minus-one homology/Tor witness, while the result stays
  explicitly restricted to that affine lane and makes no general
  scheme-level or relative-perfect preservation claim

#### Scenario: Preservation obligation is tested

- **WHEN** a supported object satisfies the declared pseudo-coherence, finite
  Tor, and negative-Ext hypotheses
- **THEN** the implemented pullback construction proves the corresponding
  universally-gluable relative-perfect preservation statement

#### Scenario: Missing hypothesis

- **WHEN** the input lacks a required preservation hypothesis
- **THEN** the API does not silently manufacture the preservation conclusion or
  expose it as an unproved field

#### Scenario: Unsupported input class

- **WHEN** an input falls outside the explicitly supported class or lacks a
  proved required hypothesis
- **THEN** the construction remains unavailable or returns only the weaker
  data justified by the available hypotheses

### Requirement: Algebraicity is proved for the supported moduli stack

The implementation SHALL prove the supported relative-perfect moduli stack's
algebraicity obligations in SF9.2 (#522), including actual atlas, diagonal,
and local-finiteness morphism statements for the supported case.

Here "supported" means the moduli problem whose input and preservation data
come from the accepted SF8.5 construction and the concrete supported case
named by the SF9.2 issue contract; it does not mean the arbitrary moduli
problem or a general representability theorem.

#### Scenario: Supported atlas

- **WHEN** the supported moduli problem is instantiated
- **THEN** the atlas is an actual scheme morphism with the required coverage
  and compatibility statements, not a representability postulate

#### Scenario: Supported diagonal and local finiteness

- **WHEN** the algebraicity proof is assembled
- **THEN** the diagonal and local-finiteness claims are stated and proved at the
  required morphism layer

### Requirement: Semistable reduction and quasi-properness are proved for the supported moduli stack

The implementation SHALL construct the supported semistable-reduction data for
SF9.3 (#525), including DVR/Dedekind test diagrams, permitted base change,
semistable replacement, the uniqueness/S-equivalence boundary, and the
quasi-properness adapter. The implementation SHALL not mark this requirement
ready until the accepted SF8.5 and SF9.2 obligations, relative-HN inputs,
repository audits, and required CI checks are complete.

#### Scenario: Dependency or relative-HN input is not complete

- **WHEN** #554, #522, or the required relative-HN input remains open, blocked,
  or without passing review
- **THEN** the controller refuses to start the #525 chunk

#### Scenario: Supported semistable replacement

- **WHEN** a supported family over a DVR or Dedekind base is supplied
- **THEN** the implementation produces the permitted-base-change and
  semistable-replacement data without accepting a valuative conclusion directly
  from callers

#### Scenario: Quasi-properness adapter

- **WHEN** the supported algebraic moduli stack and relative-HN structures are
  available
- **THEN** the quasi-properness adapter is stated at the actual moduli layer and
  does not introduce a duplicate algebraicity root or an opaque existence field
