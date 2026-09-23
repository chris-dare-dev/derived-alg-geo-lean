# Spec Delta

## Purpose

Keep hand-maintained axiom audit records aligned with the repository's authored
declaration sweep, preserving real declarations while excluding compiler
artifacts that the sweep intentionally omits.

## ADDED Requirements

### Requirement: Filtered compiler artifacts are absent from the axiom audits

The reviewed audit records whose names the declaration sweep deliberately
filters SHALL be removed from the DGCategory, AlgebraicGeometry, and
StabilityCondition audit lanes. A reviewed record whose declaration is present
in the sweep SHALL remain audited.

#### Scenario: Generated congruence and constructor records

- **WHEN** a reviewed record names a generated `.congr_simp` lemma or `.mk`
  constructor omitted by the sweep
- **THEN** the audit lane omits that record and its unresolved count decreases

#### Scenario: Authored equation declarations

- **WHEN** a reviewed `eq_*` record names an authored declaration included by
  the current sweep
- **THEN** the audit lane retains the record and the sweep counts it as audited

#### Scenario: Unrelated unresolved records remain visible

- **WHEN** audit entries outside this reviewed artifact set remain unresolved
- **THEN** the completeness report continues to show them, and this cleanup
  does not claim they were resolved
