# Proposal

## Why

Milestone 13 tracks three connected outcomes: parent issue #137, the reusable Copier topic template in #182, and the reduced second-topic falsifiability gate in #183. The old gate estimate assumed a much larger ingest and formalization; the revised scope is one analytic-number-theory paper, five registry entries, and one direct binding to a theorem already in Mathlib, with the generalization claim held false until that evidence exists.

## What Changes

- Add a Copier template to MathFormalContract with an optional upstream anchor, an exact topmost package pin, honest generated metadata, and a full source-commit answer so later schema updates can be applied reproducibly.
- Demonstrate the template in an anchor-free analytic-number-theory adopter using the exact Mathlib pin.
- Establish the reduced second-topic gate: one fetched and ingested arXiv paper, five sourced entries including an Iwaniec–Kowalski textbook entry using `digest_only`, and at least one Mathlib external declaration whose claimed relation is `exact`.
- Keep `generalization_validated: false` until the corpus, registry, Lean emission, environment binding, and contract checks all pass; record evidence and date the transition if they do.
- Keep the Derived issue plan, the MathFormalContract implementation, and the arXMCP notebook as separate repository-scoped work. Do not use one loop manifest to claim control of all three repositories.

## Capabilities

### New Capabilities

- `topic-template-gate`: Reproducible generation and evidence requirements for a second mathematical topic.

### Modified Capabilities

- None.

## Impact

The implementation target for #182/#183 is the separate MathFormalContract repository and its generated topic adopter; the real source corpus is stored in arXMCP. This Derived repository owns the milestone plan and issue tracking only. No public `DerivedAlgGeo` Lean API or mathematical declaration changes. The current loop controller can validate and preflight Derived issues, but it cannot freeze files in another repository; separate repository-local plans and runs are required before provider actions.

Issue #137 and #183 carry `gate:owner`; no issue closure, publication, approval, or merge is authorized by this plan. The plan records the two-week budget requested by the issue while keeping the gate's acceptance criteria fixed.
