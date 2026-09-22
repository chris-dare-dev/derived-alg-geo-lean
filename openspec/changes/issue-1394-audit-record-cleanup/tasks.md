# Tasks

## 1. Audit record cleanup

- [x] 1.1 Compare the 63 candidates named by #1394 and the two equivalent `.mk`
  records added on current `origin/main` with the emitted declaration sweep;
  remove only the 36 filtered `.congr_simp` and 9 filtered `.mk` records, while
  retaining all 20 resolving authored `.eq_` records. Verify with a focused
  inventory and `git diff --unified=0` that exactly those 45 audit records are
  deleted and no other record is changed.
- [x] 1.2 Run `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit` and `scripts/precheck.sh` before enumerating, so the imported build artifacts reflect current source. The focused audit targets and all 19 precheck gates pass.
- [x] 1.3 Run `LEAN_NUM_THREADS=2 ~/.elan/bin/lake env lean scripts/EnumDecls.lean > /tmp/issue1394-enum-after.txt` and `python3 scripts/check_audit_complete.py /tmp/issue1394-enum-after.txt`; verify 10 AlgebraicGeometry, 0 StabilityCondition, and 0 DGCategory unresolved records, with all three audit counts at their recorded ceilings. The hosted `ci` check remains required before a pull request can merge.

## 2. Independent review

- [x] 2.1 Have the mathematics/source-faithfulness, repository-boundary,
  abstraction/adoption, and mathlib-style reviewers independently review the
  same frozen commit. Record every review in the loop ledger and verify the
  chunk is adjudicated `passed` within the three-round cap. All four reviews
  passed the synchronized issue commit in round 2; their outputs and
  adjudication are preserved in the loop ledger.
