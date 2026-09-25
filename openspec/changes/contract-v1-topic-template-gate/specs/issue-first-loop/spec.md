# Issue-first Loop

## Purpose

Make user-named GitHub issues sufficient to start and carry out scoped repository work without duplicate planning or per-repository setup steps.

## ADDED Requirements

### Requirement: Named issues are sufficient to start

A user-initiated task that names one or more GitHub issues MUST be able to start from the live issue bodies and repository guidance. It MUST NOT require a separate manifest, an OpenSpec root in every participating repository, or a second authorization step before implementation.

#### Scenario: A batch spans multiple repositories
- **WHEN** a user asks to complete named issues whose files live in more than one repository
- **THEN** the agent works in each owning repository under the same task and tracks acceptance against the named issues without creating duplicate planning roots

### Requirement: A real blocker does not stop unrelated issues

The loop MUST continue independent issue work when one issue encounters an external credential, required-check, branch-protection, or contradictory-acceptance blocker. It MUST report and stop only the affected action when no safe continuation exists.

#### Scenario: One issue needs an unavailable external credential
- **WHEN** that credential is not required by another selected issue
- **THEN** the agent records the specific blocker and continues the independent work

### Requirement: Issue completion uses repository checks

Code issues MUST be closed only after their accepted implementation is merged. The loop MUST honor required checks and branch protection; planning artifacts MUST NOT substitute for implementation evidence.

#### Scenario: The issue implementation is ready to publish
- **WHEN** relevant local checks pass and the hosted required checks pass
- **THEN** the agent may merge when repository rules permit and close the issue after merge
