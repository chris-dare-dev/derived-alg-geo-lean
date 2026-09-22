# Tasks

## 1. Audit record cleanup

- [ ] 1.1 Compare the 63 candidates named by #1394 and the two equivalent `.mk`
  records added on current `origin/main` with the emitted declaration sweep;
  remove only the 36 filtered `.congr_simp` and 9 filtered `.mk` records, while
  retaining all 20 resolving authored `.eq_` records. Verify with a focused
  inventory and `git diff --unified=0` that exactly those 45 audit records are
  deleted and no other record is changed.
- [ ] 1.2 Run `LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean scripts/EnumDecls.lean > /tmp/issue1394-enum-after.txt` and `python3 scripts/check_audit_complete.py /tmp/issue1394-enum-after.txt`; verify the unresolved counts are 19 AlgebraicGeometry, 1 StabilityCondition, and 0 DGCategory, with unrelated unresolved entries still reported.
- [ ] 1.3 Run `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit` and `scripts/precheck.sh`; verify the focused audit targets and every precheck gate pass. The hosted `ci` check remains required before a pull request can merge.

## 2. Independent review

- [ ] 2.1 Have the mathematics/source-faithfulness, repository-boundary,
  abstraction/adoption, and mathlib-style reviewers independently review the
  same frozen commit. Record every review in the loop ledger and verify the
  chunk is adjudicated `passed` within the three-round cap.
