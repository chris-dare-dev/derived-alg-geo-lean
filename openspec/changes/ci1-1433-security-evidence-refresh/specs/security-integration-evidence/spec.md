# Spec Delta

## Purpose

This capability records current evidence about the optional security integration so maintainers can distinguish provider availability, scan execution, and verified security coverage without inferring a clean result from a missing or failed check.

## ADDED Requirements

### Requirement: Security integration reports SHALL bind observations and distinguish outcomes

The report SHALL bind every observation to a full candidate revision, provider run/check identity, observation time, and source link when available. It SHALL classify provider/authentication failure, successful execution without coverage proof, and missing provider observation separately. None of these states SHALL be reported as a verified clean scan.

#### Scenario: Provider authentication fails before scanning
- **WHEN** a provider run fails during Copilot session initialization with an authentication or licensing error
- **THEN** the report classifies it as `provider_failure`, records the failed run and revision, and makes no claim about scanner findings

#### Scenario: Check is absent on a current PR head
- **WHEN** the current PR-head check-runs response contains no security observation
- **THEN** the report records the check as missing/unknown for that exact head and does not treat absence as a clean result or permanent retirement

#### Scenario: Provider job succeeds without coverage evidence
- **WHEN** the provider job succeeds but the run has no verified result artifact and no executed negative fixture proof
- **THEN** the report records provider execution as successful but does not classify the scan as `verified_scan`

### Requirement: Verified scan reports SHALL require complete coverage evidence

A report SHALL use `verified_scan` only when successful PR and `main` executions bind the exact candidate revisions, scanner scope, run/job identities, hashed result artifact, and an executed negative fixture whose expected finding was observed. Replacement or retirement SHALL be represented as a separate owner-approved disposition, not as a passing scan.

#### Scenario: Coverage proof lacks a negative fixture
- **WHEN** a successful run has a result artifact but no executed negative fixture with an observed expected finding
- **THEN** the report withholds `verified_scan` and identifies the missing coverage evidence

#### Scenario: Owner approves a replacement or retirement
- **WHEN** the owner selects replacement or retirement after reviewing its coverage tradeoff
- **THEN** the report records the exact reviewed revision, decision, reason, timestamp, and follow-up separately from scan results
