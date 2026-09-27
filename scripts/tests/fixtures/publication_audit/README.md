# Publication audit examples

These receipts were collected read-only from the public GitHub API on 2026-09-27.
They are historical observations, not merge authorization or authenticated
technical reviews. Each `--reviewed-commit` below supplies a revision to compare;
`review_provenance` remains `not_evaluable`. The whole-tree SHA includes Git
modes, symlinks, names and deletions. `--verify` re-fetches GitHub and rejects
any receipt that differs from the provider's current observations, including a
self-rehashed forged edit. A later rerun can legitimately make a snapshot stale.

Run from the repository root with an authenticated read-only `gh` session:

```sh
python3 scripts/publication_audit.py chris-dare-dev/derived-alg-geo-lean 1577 \
  --reviewed-commit 847c33d1d17e26c79c21b0c8bd23c7a5cf6d440d \
  --verify scripts/tests/fixtures/publication_audit/pr1577.json
python3 scripts/publication_audit.py chris-dare-dev/derived-alg-geo-lean 1554 \
  --reviewed-commit be178b1bbd3813a3491569447b719c0acf608292 \
  --verify scripts/tests/fixtures/publication_audit/pr1554.json
python3 scripts/publication_audit.py chris-dare-dev/derived-alg-geo-lean 1580 \
  --reviewed-commit c1d5e19771ce72406d900d5c35b4bea89e4e0c09 \
  --verify scripts/tests/fixtures/publication_audit/pr1580.json
```

| PR | Published commit | Observation |
| --- | --- | --- |
| [#1577](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1577) | `788f89a56793377a9d09b07a35799446f1e6a975` | Published and supplied trees match; `ci` succeeded on the head before merge; postmerge `ci` passed. Tested candidate, final review provenance and historical required policy remain unknown. |
| [#1554](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1554) | `8e44470b48f3f9e72c3f0e68795219ea0b793d0d` | Published and supplied trees differ; the PR's recorded base differs from the published parent despite an observed premerge `ci` success on the head. |
| [#1580](https://github.com/chris-dare-dev/derived-alg-geo-lean/pull/1580) | `349ea8a0e08d5d42bfca859aac65abb17f66d12a` | Trees match, but the observed `ci` check completed after the merge. This does not establish applicable required CI at merge time. |

The 60-merge replay and transcript extracts remain in the owner-only
`~/.loop-runs/transcripts/analysis/2026-09-27-m54-recovery/` archive. No agent
transcript is committed here.
