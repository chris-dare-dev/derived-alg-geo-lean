# Proposal

## Why

Issue #1394 identified 63 `#print axioms` records across the DGCategory,
AlgebraicGeometry, and StabilityCondition audit lanes whose names are
deliberately excluded by `scripts/EnumDecls.lean` or no longer exist. These
records inflate the unresolved count and make later stale audit entries harder
to notice. The `eq_*` filter was corrected in #998, so those records need to be
checked against the current sweep individually rather than removed by suffix
alone.

## What Changes

- Compare each record named by #1394 with the declaration names emitted by the
  current `EnumDecls` sweep.
- Remove records for generated artifacts deliberately excluded by the sweep,
  while retaining authored declarations that the current sweep includes.
- Include the two equivalent generated `.mk` records added to the current audit
  files after #1394 was filed, so the same known artifact does not remain.
- Confirm the unresolved counts after cleanup. Keep the existing completeness
  ratchet while unrelated unresolved records remain; only consider a zero-only
  gate after all three lane baselines actually reach zero.

## Capabilities

### New Capabilities

- `audit-record-integrity`: the hand-maintained axiom audit records agree with
  the declarations selected by the repository's authored-declaration sweep.

### Modified Capabilities

None.

## Impact

- Audit records in `scripts/DGCategoryAudit.lean`,
  `scripts/AlgebraicGeometryAudit/`, and
  `scripts/StabilityConditionAudit/`.
- The unresolved report from `scripts/check_audit_complete.py`; the checker
  itself remains unchanged because the expected post-cleanup count is nonzero.
- No public Lean API or mathematical declaration changes.
