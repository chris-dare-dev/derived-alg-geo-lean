# Tasks

## 1. Envelope composition and generator transfer

- [x] 1.1 Record the pinned-API reconnaissance for retract, shift, and binary-product closure on issue #920; verify the verdict against the issue discussion.
- [x] 1.2 Prove stage-zero containment, the `m * n + m + n` composition bound, and transfer through an intermediate property; verify with `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.CategoryTheory.Triangulated.Generators.Composition`.
- [x] 1.3 Add the bounded strong-generator transfer and singleton/classical-generator corollary, export them from the existing umbrella, and audit every public declaration; verify with the targeted `Generators` build and the dimension audit.

## 2. Generation-time and Rouquier consequences

- [x] 2.1 Prove the generation-time-plus-one inequality and finite-Rouquier-dimension consequences using the existing APIs; verify with `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Composition DerivedAlgGeo.CategoryTheory.Triangulated.Dimension`.
- [x] 2.2 Document the false additive law with its `k[t]/(t^6)` example, the single-object/uniform-stage boundary for Stacks 0FXA, and retain the generalization backlog entry; verify by reviewing both docstrings and the appended backlog record.

## 3. Final run evidence

- [ ] 3.1 Reconcile the candidate with current `origin/main`, then run the focused precheck and strict OpenSpec validation on the final branch head; record the exact commit and results.
- [ ] 3.2 Obtain all four independent reviews on one exact commit and pass the required hosted CI checks before merging PR #1570; verify the reviewed SHA, check conclusions, merge commit, and issue closure.
