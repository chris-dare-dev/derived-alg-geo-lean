# Design

## Context

See proposal.md for motivation and spec.md for the report contract. The existing `docs/ci/github-advanced-security.md`, `scripts/security_evidence.py`, and its tests already distinguish provider failure from verified coverage. The provider-generated workflow at `dynamic/agents/github-advanced-security` is absent from the checkout, so this progress chunk can document current provider observations but cannot repair its entitlement or configuration.

## Goals / Non-Goals

**Goals:**

- Bind refreshed observations to exact PR heads, run/job IDs, dates, and source links.
- Preserve the difference between a provider failure, a successful workflow execution without verified coverage, and a missing check.
- Present the entitlement repair, replacement, and retirement paths with their coverage and owner-decision requirements.

**Non-Goals:**

- Changing workflow routing, `ci.yml`, branch protection, the gate inventory, provider settings, secrets, or scanner configuration.
- Claiming a clean scan from a green provider job or from an absent check.
- Choosing or implementing a replacement, assigning a paid Copilot seat, or retiring the integration.

## Decisions

- Use the repository's authenticated GitHub CLI/API observations: workflow runs and job logs for existing outcomes, current PR metadata for exact head SHAs, PR-head check-run pagination for present/absent checks, live branch protection, and the protected-base gate inventory.
- Record the latest observed successful execution separately from the latest observed failed execution. A provider success is not promoted to `verified_scan` unless the existing coverage proof is complete, including a hashed result artifact and an executed negative fixture.
- Preserve absent observations as unknown for the named SHA. Do not infer that the check was retired or that scanning succeeded.
- Keep the current optional status inventory and required `ci` contract unchanged in this progress PR. A later selected disposition must use a separate implementation change and satisfy the issue's PR/main execution and negative-fixture evidence.
- Present CodeQL only as a possible partial replacement: GitHub documents code scanning availability for public repositories and supports Python and GitHub Actions, but its supported-language list excludes Lean. It therefore cannot be described as equivalent coverage for this repository without an owner-approved coverage plan.

## Risks / Trade-offs

- Provider logs can show successful result submission without exposing a bound scan artifact or negative-fixture result. Mitigation: classify such execution as successful-but-unverified and leave #1433 open.
- The current PR sample has missing check observations after earlier runs. Mitigation: identify each exact head and the observation date; do not call absence permanent retirement.
- Repairing the Copilot entitlement may require an owner/admin action or paid seat. Mitigation: document the actor/entitlement question and wait for the owner's selected disposition before changing provider settings.
- A replacement may leave Lean-specific coverage gaps. Mitigation: record supported-language limits and require an explicit coverage tradeoff and negative fixture before adoption.

## Migration Plan

This progress chunk updates the existing diagnosis only. It leaves required CI, optional status policy, and provider configuration unchanged. Any provider repair, replacement, or retirement is a separate owner-directed change with rollback and PR/main verification described in that change.
