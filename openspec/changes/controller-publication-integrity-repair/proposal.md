# Proposal

## Why

**Mathematical motivation.** This change adds no Lean theorem, declaration, or mathematical existence claim.

**Repository motivation.** The capped runs for #1458, #1459, and #1460 ended without publication. Their final reviews identified concrete trust-boundary gaps in ledger evidence, deferred findings, PR readiness, PR creation, and controller guidance. This fresh issue repairs those behaviors on current `main` without reusing any terminal ledger or branch.

## What Changes

- Add one controller-integrity capability covering manifest-derived ledgers, exact reviewer evidence, durable deferred findings, live mutation authority, exact-head PR creation, and reviewed draft-to-ready transitions.
- Make remote changed-file validation exhaustive and reject malformed responses, noncanonical lift paths, and renames whose source lies outside the frozen scope.
- Add a disabled bootstrap manifest and a documented one-time publication path for this controller-owned change. The path cannot authorize approval, merge, or issue closure.
- Align repository guidance and reviewer prompts with the executable issue, evidence, and round-cap rules.
- Preserve #1458, #1459, #1460, #1461, and #1462 histories as terminal evidence; this change is a new issue and review budget.

## Capabilities

### New Capabilities

- `controller-publication-integrity`: make loop-controller review evidence and publication endpoints fail closed against stale or ambiguous authority.

### Modified Capabilities

- None. `openspec list --specs` reports no canonical inventory; `loop-engineering-controller` is an in-flight delta, not an archived capability.

## Impact

The change affects `scripts/loop_engine.py`, its focused tests, loop manifests and workflow guidance, reviewer prompts, the generalization backlog format, and the root `AGENTS.md`/`CLAUDE.md` protocol. It changes no Lean source, API, dependency, or mathematical ownership decision.
