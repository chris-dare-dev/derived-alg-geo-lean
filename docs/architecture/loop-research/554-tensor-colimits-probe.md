# Scratch probe for the #1574 R&D alternative

Status: local research only, 2026-09-27. No commit, push or edit to the parked
PR branch. The scratch worktree is detached at its frozen head
`7e19074188697d8c810905687ac5a9029759f06a`, under
`/home/chris-dare/.codex-accounts/account-2/worktrees/sf8-rd-tensor-probe/derived-alg-geo-lean`.

The probe restored `Tensor/Invertible.lean` and `Tensor/Monoidal.lean` from
the PR base `84d8aa97c75c0acfd5f826667927b764633284d7`. It removed only
the generic historical-functor instances and `tensorLeftFreeIso` migration
from the scratch `Tensor/Colimits.lean`, keeping its two generic colimit
theorems on canonical `tensorLeft`. The scratch diff changes these three
source files and remains uncommitted. It is a counterfactual architecture
experiment, not a fourth revision of the frozen PR.

The donor cache seeded 1496 project modules. With `LEAN_NUM_THREADS=2` and
`~/.elan/bin/lake`, the named `Tensor.Colimits` build completed successfully
(2594 jobs), then the named `DerivedCategory.Tensor.LeftDerivedTensor` build
completed successfully (3276 jobs). A targeted invocation of
`~/.elan/bin/lake exe runLinter
DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.LeftDerivedTensor`
reported linting passed. The unrelated replay warning in
`LinearAlgebra/ExteriorPower/Top.lean` was already present and did not fail
either build. The scratch diff passed `git diff --check`.

This supports the R&D diagnosis: retaining the historical additive instance
gives `singleLeftTensorIso` a genuine use for invertibility, while the generic
canonical tensor theorem still compiles. It does not test the repository-wide
environment linter, audits, the merged-base contribution, or required PR CI.
Those remain obligations for any separately admitted successor attempt. The
full twelve-message review inventory is preserved in
[554-tensor-colimits-review-history.md](554-tensor-colimits-review-history.md).
