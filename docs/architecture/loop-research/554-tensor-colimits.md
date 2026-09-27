# R&D handoff: #554 sheaf tensor colimits, PR #1574

Status: research only. The implementation attempt is terminal after three
frozen critique/revise rounds. This report does not approve source revision,
PR readiness or merge.

## Frozen evidence and contract

- Issue: #554, arbitrary derived pullback and preservation of the relative
  perfect locus. This progress chunk concerns sheaf tensor colimits only; all
  remaining general derived-pullback obligations in the issue remain open.
- Draft PR: #1574, base `84d8aa97c75c0acfd5f826667927b764633284d7`,
  final reviewed head `7e19074188697d8c810905687ac5a9029759f06a`.
  `origin/main` was `ceae23f170d837628f199ffdb902d405bc918077`
  at the first R&D read and had advanced to
  `788f89a56793377a9d09b07a35799446f1e6a975` by independent review.
  The PR is behind; recheck the live base before any successor work.
- Frozen rounds: `1a774282c221540639da1447ab39250842d41ce1`
  (four passes), `fbc39e11223f7805168c2372d2762a9b761e7487`
  (abstraction and style requested removal of unnecessary `[Finite I]`),
  and `7e19074188697d8c810905687ac5a9029759f06a` (four passes).
  The PR body preserves the round table and summarized findings; its comments
  and reviews do not contain the complete verbatim messages. They were not
  found in the worktree's `.loop-runs` inventory. A successor attempt requires
  the full raw review inventory. The PR summary cannot substitute, and this
  report does not reconstruct missing transcripts.
- Required CI run 36295085080 on the final head failed its repository-wide
  `environment_linters` gate: `[L.IsInvertible]` is unused in
  `AlgebraicGeometry.DerivedCategory.singleLeftTensorIso` at
  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Tensor/LeftDerivedTensor.lean`.
  The Lean build, audits, contract gates and emitter reproducibility passed.
  The required `ci` check failed. The draft remains open and #554 remains open.

## Diagnosis and alternatives

The change makes fixed-left sheaf tensor additive for arbitrary `L`.
`singleLeftTensorIso` appears to construct a bare complex natural isomorphism
from that generic functor, without using invertibility. The PR body attributes
the unused premise to `tensorLeftFreeIso`; the proof of `singleLeftTensorIso`
does not call that declaration directly. Compiler probes must settle the exact
dependency before source revision.

1. **Preferred rearchitecture:** keep the historical invertible-only
   `tensorLeftFunctor`, its additive/finite-colimit instances and finite-free
   comparison in `Tensor/Invertible.lean`, as they stood on the PR base. Prove
   generic colimit preservation only for the canonical monoidal
   `tensorLeft (C := X.Modules) L` in a new `Tensor/Colimits.lean`. Do not
   replace the historical functor with an abbreviation or register generic
   instances under its existing names in this progress chunk. The old
   `singleLeftTensorIso` then continues to use its invertibility premise
   through the old additive instance. This changes the architecture that
   caused a cross-module linter cascade, while still supplying the sheaf-level
   colimit input needed by later total-tensor work. The generic theorem's
   comparison proof already compiles at #1574's reviewed head; the experiment
   must show it still compiles when the historical API is restored.
2. Generalize the bare `singleLeftTensorIso` and migrate all callers to a
   generic complex comparison, retaining invertibility only where preservation
   of quasi-isomorphisms or exactness is used. This is mathematically plausible
   but changes a wider derived API and may cascade through consumers. Merely
   removing its unused premise on the frozen PR is a fourth repair, not an
   admitted recovery. A genuinely broader migration would need its own
   acceptance case and an environment-wide dependency inventory.

The first approach is preferred because its boundary is the existing canonical
monoidal tensor and it avoids changing the invertible derived API at all. It is
not an edit to #1574's terminal branch: an independently admitted successor
would retain the same issue, frozen scope and all findings, and require four
fresh same-commit reviews plus required CI.

## Falsification and checks

- On a scratch checkout, restore `Tensor/Invertible.lean` and the historical
  functor-related edits in `Tensor/Monoidal.lean` from the PR base while keeping
  only the generic `tensorLeft` colimit theorems. Compile `Colimits.lean` and
  `LeftDerivedTensor.lean` without modifying the frozen branch. Failure of the
  generic proof or persistence of the unused premise falsifies option 1.
- Search all consumers and named audits; run named builds of
  `LeftDerivedTensor`, `Tensor.Colimits`, `Tensor.Invertible`, and the affected
  projective-spectrum consumer, then the repository-wide Lean environment
  linter, focused audits and `scripts/precheck.sh`. Local checks are not CI.
- A successor freeze would be reviewed by the independent mathematics,
  boundary, abstraction and style roles on one exact SHA. Required PR CI must
  pass on that head before readiness or merge.

## Friction to retain

Focused leaf lint did not exercise the downstream environment linter. A broad
local lint attempt hit a missing cold-worktree olean. The PR description's
causal attribution was too specific. Main advanced while this research was
reviewed; the root checkout and PR base differ. Complete verbatim review
transcripts are not present in the located worktree records. None of these
facts may be treated as a passing CI or a new review allowance.
