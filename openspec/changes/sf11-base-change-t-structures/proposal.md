# Proposal

## Why

Issues #1060, #1061, and #1062 are the remaining SF11 chain for the base-change
categories and t-structures of arXiv:1902.08184v4 §§3–5. The repository now
has substantial categorical scaffolding, but its own roadmap still marks the
geometric witnesses, local inhabitants, and Ind-extension reconciliation as
supplied or uninhabited; this batch makes those claims executable and reviewable
while the new bounded loop controller is available.

## What Changes

- Complete the construction of `D_T` and `(Dqc)_T` from the repository's
  model-free and K-flat base-change layers, including the functors and the
  source-faithful hypotheses required by Proposition 3.15, Theorem 3.17, and
  Lemma 3.18.
- Put S-local t-structures and the corresponding slicing vocabulary inside the
  formalized layer, with actual affine-base inhabitants and the required local
  finiteness and filtration-lifting statements.
- Prove the supported form of Theorem 5.3, including the flat/fpqc descent
  formulas and t-exactness clauses, by reusing the existing Ind-extension data.
- Remove or rewrite comments and roadmap entries that claim these layers are
  outside the categorical layer once the corresponding declarations are truly
  inhabited; record any remaining external theorem boundary explicitly.
- Extend the loop manifest/controller only as needed to authorize this exact
  three-issue epic batch explicitly; an `epic` label must never become eligible
  implicitly.

## Capabilities

### New Capabilities

- `sf11-base-change-t-structures`: source-faithful base-change categories,
  S-local t-structures/slicings, and the base-changed quasi-coherent
  t-structure required by issues #1060, #1061, and #1062.

### Modified Capabilities

None.

## Impact

The affected Lean modules are under
`DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Families`,
`DerivedAlgGeo/CategoryTheory/Triangulated/TStructure`, and the existing
Ind-extension/phase-transfer consumers. The batch also touches the roadmap,
repository notes, and the Python loop-controller manifest/schema tests. Every
mathematical result must compile without `sorry`, `admit`, or a new axiom; a
targeted module build and the repository's no-sorry/audit gates are required,
but the full repository build is deliberately not part of the local loop.
