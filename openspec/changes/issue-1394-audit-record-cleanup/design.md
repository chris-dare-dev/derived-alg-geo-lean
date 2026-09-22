# Design

## Context

See proposal.md for motivation and specs/audit-record-integrity/spec.md for the
behavior contract. On the current `origin/main`, the declaration sweep reports
35 unresolved AlgebraicGeometry records, 26 StabilityCondition records, and 4
DGCategory records. The issue's 24/25/4 snapshot is older than this checkout
and will not be used as the post-cleanup target.

The current audit inventory contains 36 `.congr_simp` records and 9 `.mk`
records that the sweep filters, including two `.mk` records added in the
current main after #1394 was filed. The 20 `.eq_` records are authored names
accepted by the #998 classifier fix and resolve in the current sweep; they
remain. Removing the filtered records is expected to leave 19, 1, and 0
unresolved records respectively. Those remaining records are outside this
cleanup's suffix-classified set and stay visible in the report.

## Goals / Non-Goals

**Goals:**

- Remove the 45 currently filtered generated records: 36 `.congr_simp` and 9
  `.mk` entries.
- Preserve all 20 authored `.eq_` records that the current sweep includes.
- Confirm the post-change unresolved counts against a fresh enumeration.

**Non-Goals:**

- Change the declaration filter or rename authored declarations.
- Resolve unrelated existing audit gaps or update their baseline.
- Make nonzero unresolved counts fail globally; the post-cleanup baseline is
  still nonzero.
- Change Lean declarations, imports, namespaces, public APIs, or mathematical
  ownership.

## Decisions

1. **Use current sweep membership for each candidate.** `scripts/EnumDecls.lean`
   is the source of truth for which authored declarations the audit ratchet can
   count. A textual `.eq_` match alone is not evidence of a generated equation
   lemma: the 20 names in this inventory are authored and present in the
   current enumeration. Conversely, `.congr_simp` and `.mk` candidates are
   excluded and are removed from the audit lists.
2. **Keep changes in the existing audit lanes.** DGCategory records remain in
   `scripts/DGCategoryAudit.lean`; AlgebraicGeometry and StabilityCondition
   records remain in their existing audit modules. No new audit root, duplicate
   declaration, import, projection, comparison map, or instance is introduced.
   The ownership boundary is the existing enumeration in `EnumDecls.lean` and
   its three consuming audit lanes; dependency direction and imports do not
   change.
3. **Do not tighten the unresolved gate yet.** The current report is expected
   to retain 19 AlgebraicGeometry and 1 StabilityCondition unresolved entries.
   `check_audit_complete.py` therefore stays a ratchet and keeps those entries
   visible; setting a zero-only rule would reject this honest remainder.
4. **Freeze one bounded review chunk.** The manifest names only the planning
   artifacts and the audit files that contain the removed records. The
   mathematics/source-faithfulness reviewer checks sweep membership and
   preservation of authored names; the repository-boundary reviewer checks
   that no unrelated audit or generated baseline is changed; the
   abstraction/adoption reviewer confirms that no competing API or ownership
   root was introduced; the mathlib reviewer checks style. All four review the
   same commit. The cap is three review/improve rounds; a third unsuccessful
   adjudication is terminal, with no fourth or fifth round.
5. **Disable bounded recovery.** If the three-round cap is exhausted, stop the
   run, retain the failed ledger and its findings, and hand back a focused
   research summary. Any later attempt needs a new, independently reviewed plan
   before it reuses those findings; until then, park the issue. No automatic
   chunk splitting or provider action follows exhaustion.

## Risks / Trade-offs

- **The issue's old counts may be mistaken for current totals.** Use the fresh
  current-main enumeration and report residual counts instead of claiming the
  lanes are fully resolved.
- **A generated-looking suffix can be authored.** Compare each candidate with
  the sweep and preserve the 20 resolving `eq_*` names; remove only the
  filtered generated entries.
- **The DGCategory file also contains its umbrella.** Its four record deletions
  are intentional; leave imports and all other lines unchanged.

## Migration Plan

No data migration is required. Remove the selected `#print axioms` lines,
rerun the focused audit enumeration and completeness checks, then run the
repository's approved local precheck. Remote checks remain CI work.
