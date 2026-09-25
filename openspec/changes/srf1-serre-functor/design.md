# Design

## Context

See `proposal.md` for the SRF1 motivation and scope. The current main branch already owns `SerreFunctorData`, Hom-finiteness, uniqueness, the Serre pairing, and trace in `CategoryTheory/Linear/SerreFunctor/`. `SerreCategoryData` already packages a chosen Serre functor with its equivalence proof. The triangulated subtree contains shift-dependent applications. On the geometry side, `BilinearData` supplies sheaf-level Ext duality but has no naturality in either variable and no comparison from `Abelian.Ext` to derived-category Hom. Varieties are represented by an existing scheme `X` with instances such as `IsSmoothProperVariety k X`; `SmoothProperVariety` is a namespace, not a bundled carrier.

## Goals / Non-Goals

**Goals:**

- Add the missing full-faithfulness and co-Serre equivalence results without changing the existing right Serre root.
- Separate ordinary linear conjugation from shift-dependent triangulated consequences.
- Provide the geometric duality bridge as explicit data with one-way projections and an honest uninhabitedness note.
- Complete issues #897, #898, and #899 in dependency order with independent review of frozen chunks.

**Non-Goals:**

- Proving that every right Serre functor is essentially surjective.
- Constructing derived tensor by the canonical sheaf, Hom-finiteness of `Dᵇ(Coh X)`, or the missing Ext-to-derived-Hom comparison.
- Changing the existing sheaf-level `BilinearData`, its consequences, or spherical-object fields.
- Adding a second derived-category carrier, a global geometric instance, or a projection from categorical Serre data back to geometric data.

## Decisions

1. **Respect the completed MO1.07 ownership cutover.** #897 has no shift hypothesis, so its extensions and the new `CoSerreFunctorData` belong in `DerivedAlgGeo/CategoryTheory/Linear/SerreFunctor/Equivalence.lean`; add that leaf to the existing linear umbrella. Reuse `SerreFunctorData`, `HomFinite`, and `SerreCategoryData`. Derive the adjunction between the co-Serre and Serre functors from their two duality isomorphisms, prove the co-Serre functor fully faithful using finite-dimensional double duality, and obtain essential surjectivity of the right adjoint. Construct the existing `SerreCategoryData` from that result; do not add another equivalence package.

2. **Split #898 at its mathematical boundary.** Put conjugated Serre data and `transportIso` in a linear transport leaf (planned as `CategoryTheory/Linear/SerreFunctor/Transport.lean`) and re-export it from the linear umbrella. Put the shift case, `CommShift ℤ` coherence, triangulated exactness/`TriEquiv`, and `chiHom_symm` in `CategoryTheory/Triangulated/SerreFunctor/Shift.lean` and re-export it from the triangulated umbrella. The shift result is the `Φ = shiftEquiv C n` instance of the general conjugation theorem. Prove coherence with the exported uniqueness-compatibility theorem; do not add shift commutation as a field or an axiom. Do not treat either `[1] ⋙ S` or `S ⋙ [1]` as Serre data.

3. **Join the geometric presentation downstream.** Put `GeometricSerreData` in `DerivedAlgGeo/AlgebraicGeometry/Duality/Serre/Categorical.lean`, and add only its import to the existing `Duality/Serre.lean` umbrella. State it on the existing scheme `X`, its `IsSmoothProperVariety` instance, dimension `n`, and `CanonicalSheafData`; do not introduce the bundled `SmoothProperVariety` type suggested by the older issue wording. Its supplied fields include the derived twist functor, duality equivalence, both naturality laws, Hom-finiteness, the existing `BilinearData`, and explicit comparison data sufficient to state compatibility only on sheaves and `0 ≤ i ≤ n`. The projection to categorical Serre data is a repackaging with `S := canonicalTwistFunctor ⋙ shiftFunctor _ (n : ℤ)`. Keep the reasons the structure is uninhabited today visible: the bounded-derived Hom-finiteness chain is incomplete, derived tensor by the canonical sheaf is not constructed, and no Ext-to-derived-Hom comparison exists.

4. **Keep projections and instance use one-way.** The co-Serre witness supplies the missing equivalence direction; it does not alter the definition of right Serre data. `GeometricSerreData` retains the existing bilinear witness and projects to `SerreFunctorData`; categorical data does not recover geometric structure. Carry finiteness and supplied witnesses explicitly and use local instances only at the consumer that needs them. The linear files import neither triangulated nor algebraic geometry, the triangulated files import the linear root, and the geometric file imports both the linear Serre root and existing geometric bilinear data.

5. **Keep the geometrically unsupported comparison as an explicit field.** Compatibility uses the current `BilinearData.extComparison` only after supplying whatever Ext-to-derived-Hom map its type requires. Do not infer naturality or extend compatibility to arbitrary complexes or degrees outside the sheaf range. State the one-way recoveries of `finrank_hom_eq` and `chiHom_symm` in the K3/surface range without editing `Surface/Spherical.lean`.

6. **Stage live dependencies as successor runs.** The OpenSpec change plans the whole three-issue chain, but the active manifest initially selects only #897. The controller rejects issues with a live `blocked` label or open predecessors; after verifying #895 and #896 are closed, the stale `blocked` label on #897 was removed, while #898 and #899 remain blocked by their open predecessors. The #897 source manifest emits a controller-derived predecessor attestation after its passing ledger and before merge; its successor binds that attestation, reviewed head, and merge commit. Re-read labels and dependencies after each predecessor closes, and do not pre-invent predecessor metadata for #898 or #899. The owner grant on `main` must cover the actions required by the reviewed manifest, including the PR comment used for attestation. Once read-only preflight passes, local ledger work and implementation may proceed; provider actions remain denied by the controller until the grant is merged to `main`.

7. **Use bounded independent review without hidden retries.** Each new attempt has at most three critique/improve rounds. The mathematics/source-faithfulness, repository-boundary, abstraction/adoption, and mathlib/style reviews are independent and review the same commit. Recovery is disabled for this batch: on exhaustion preserve the attempt and all findings, research a concrete repair within the frozen scope, obtain independent review of that plan before any separate one-issue recovery objective, inherit every finding, and park the issue when the bounded recovery allowance is exhausted. No re-chunking resets the budget.

## Risks / Trade-offs

- **Essential surjectivity is accidentally inferred from full faithfulness** → require co-Serre data for the adjunction and derive the existing equivalence package only from that witness.
- **Shift uniqueness is applied to functors that do not satisfy Serre duality** → establish conjugation first and derive every shift comparison from it.
- **Sheaf data is presented as a derived theorem** → keep naturality, Hom-finiteness, and the Ext-to-Hom comparison as explicit supplied fields and state the current obstruction.
- **A stale blocked label or absent provider grant makes the pilot appear ready** → recheck live issue eligibility before ledger initialization; provider actions remain separately denied until the owner grant reaches `main`.
- **A cutover path from an old issue description is reused** → preserve declaration namespaces but follow the current path owner in the placement policy and cutover ledger.

## Migration Plan

1. Validate this OpenSpec change and the one-issue #897 manifest; run the manifest's read-only preflight and preserve its exact result.
2. Start local #897 ledger work only after its blocked label is resolved and a fresh preflight passes. Keep push, PR creation, attestation comments, and merge behind the owner grant on `main`.
3. After #897 merges, create the #898 successor manifest using the exact predecessor attestation and current branch state. After #898 merges, repeat for #899.
4. Build only named Lean targets during implementation, add public declarations to the existing audits, run `scripts/precheck.sh` and required runner checks, and archive only after the full review ledger and repository gates pass.

## Review and Exhaustion

Advisors may scout altitude and hypotheses but do not vote. Every required reviewer records a separate finding for the same commit; no supervisor rewrites review text. If three rounds do not pass, preserve the failed ledger and findings. The researcher then produces a concrete repair plan, a distinct reviewer judges that exact plan, and any later one-issue recovery attempt inherits the full contract and findings. Research and plan acceptance never count as implementation review or provider permission. Exhausted recovery is parked with its reason; it does not authorize a new scope.
