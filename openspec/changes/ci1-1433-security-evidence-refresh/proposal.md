# Proposal

## Why

#1433 already records the original Copilot authentication failures and has a strict offline evidence classifier, but its current disposition predates later successful check runs, repeated 403 failures, and newer PR heads with no matching check at all. Refreshing the evidence now lets the repository owner choose an entitlement repair, a replacement with a disclosed coverage tradeoff, or retirement without treating missing or failed scans as clean.

## What Changes

- Update the existing security integration diagnosis with exact, revision-bound run links and a dated snapshot of recent failed, successful, and missing check observations.
- Distinguish a successful provider workflow from a verified scan with a bound result artifact and negative fixture.
- Record the minimum entitlement repair and a replacement/retirement decision matrix, including CodeQL's public-repository availability and its lack of Lean language support.
- Keep the required `ci` context and optional security warning contract unchanged; make no workflow, branch-protection, provider-configuration, or scanner-coverage change in this progress chunk.
- Leave #1433 open until an owner selects a disposition and its current PR/main execution and negative-fixture evidence are supplied.

## Capabilities

### New Capabilities

- `security-integration-evidence`: Truthful, revision-bound reporting for security scanner outcomes, provider failures, missing checks, and coverage evidence.

### Modified Capabilities

None.

## Impact

The implementation scope is a refresh to `docs/ci/github-advanced-security.md` plus the OpenSpec change artifacts. Existing evidence validation and tests are inputs; this chunk changes no workflow, action, repository setting, branch protection, scanner configuration, or Lean source. A later owner decision may authorize a separate implementation change.
