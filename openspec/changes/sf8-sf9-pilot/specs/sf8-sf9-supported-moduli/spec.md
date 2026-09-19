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

### Requirement: Downstream SF9.3 work respects the dependency boundary

The pilot SHALL not mark SF9.3 (#525) ready for implementation until the
accepted SF8.5 and SF9.2 obligations, repository audits, and required CI checks
are complete.

#### Scenario: Dependency not complete

- **WHEN** #554 or #522 remains open, blocked, or without passing review
- **THEN** the controller refuses to start the #525 chunk

#### Scenario: Dependency complete

- **WHEN** the preceding issues are closed by merged pull requests and their
  ledgers pass
- **THEN** the #525 plan may be preflighted as a new frozen chunk
