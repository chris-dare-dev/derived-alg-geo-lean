# MO1: mathematical ownership and abstraction boundaries

Planning date: 13 September 2026. Source: the [directory review](2026-09-13-mathematical-ownership-review.md), at repository snapshot `9edfb9d6a6b01556ac203a755666b91f46984a99`.

This plan creates a structural companion to CA1–CA3. The charge track already owns the mathematical formulas and comparison theorems; MO1 owns their placement and independent importability, together with the other ownership defects found across the repository. The planning PR changes documentation and roadmap data only. It neither moves Lean declarations nor marks the proposed source work completed.

[Milestone 52: MO1 — Mathematical ownership and abstraction boundaries](https://github.com/chris-dare-dev/derived-alg-geo-lean/milestone/52). The machine-readable owner is `.claude/roadmap/mathematical-ownership.yaml`.

## Integration with the existing milestones

The standing [ownership policy](../architecture/mathematical-ownership.md)
codifies the review's general rules, with matching `CLAUDE.md`/`AGENTS.md`
instructions and reconciled placement, abstraction and dependency guidance.
This is partial progress on MO1.01. The complete declaration-level cutover map
and affected issue path contracts still need reconciliation; no source move
or new import gate is completed by codifying the policy.

- [CA1, milestone 49](https://github.com/chris-dare-dev/derived-alg-geo-lean/milestone/49) retains the exponential kernel, correction inhabitant, discriminant, twist and fourfold constructions. Closed #1219–#1221 are reused. MO1 extracts charge roots, removes parent-to-specialization imports and organizes numerical models. #1223 is a native prerequisite of the lattice move.
- [CA2, milestone 50](https://github.com/chris-dare-dev/derived-alg-geo-lean/milestone/50) retains rotation, the (3,2) tilt node and adjudication of tilt/nu spellings (#1226–#1228). MO1 gives charge families an owner upstream of walls and separates the wall notions. The tilt-dependent rotation comparison stays downstream of the neutral core.
- [CA3, milestone 51](https://github.com/chris-dare-dev/derived-alg-geo-lean/milestone/51) retains bridge-first #1229 and conditional root review #1230. The lattice move waits for #1229 and #1223, preserves the public Mukai.pairing root and the weighted/factor-of-two comparisons, and creates no competing graded root. Fin-indexed and product coordinates require the actual equivalence, not an assumed definitional equality.

Existing issues retain their milestones, states and native prerequisites. Their bodies and milestone descriptions have reciprocal integration notes. MO1 tasks depend on relevant CA outputs; no blanket reverse dependency prevents ongoing CA proofs. The optional graded-root decision may conclude that no new root is justified, as CA3 already permits.

## Adjacent theorem owners

- SRF1 #897–#899 still owns full faithfulness, equivalence/shift transport and geometric Serre-duality obligations. MO1 moves the independent linear foundation and Yoneda helpers.
- SF1 #192/#208 still owns weak stability and tilting. MO1 extracts the abelian root and separates slope/Gieseker ownership.
- DG3 #854/#855 still owns the classical seam and linear/exact H⁰ proofs. MO1 owns intrinsic dg placement and the distinction between an ordinary presentation and an exact enhancement.
- DT1 #892/#928–#931 still owns construction and inhabitation of derived tensor. MO1 extracts existing operations from Fourier–Mukai. #795/#796 retain their transform/adjoint obligations.
- SF8 #517/#554/#723 still owns relative-perfect construction, preservation and compact-perfect results. MO1 gives the foundational predicates their own owner, preserving the non-Noetherian pseudo-coherence caveat.

The issue bodies link these owners. Path-specific contracts are reconciled in MO1.01; neither a stale path nor this proposal authorizes duplicate definitions or a missing theorem supplied as an instance.

## Issue series and finding coverage

Each task has a concrete outcome, source links at the review commit, acceptance criteria, mathematical qualifications and the structural completion contract. Tasks are milestone-direct, with no artificial parent epic.


### MO1.01 — Agree canonical owners and a coordinated cutover map

[#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312); review findings 14.

Record the definition owner, neutral core, application adapter and comparison owner for each confirmed finding before moving source. Amend the placement policy where it currently conflates a new subject with an extension of an existing Mathlib API.

No native prerequisite; start here.

### MO1.02 — Make charge construction upstream of walls and separate neutral pairing lemmas

[#1313](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1313); review findings 01, 04.

Split the linear-algebra functional/kernel/bounds API from its stability interpretation, and move the existing ChargeFamily and exponential/divisorial constructors to their agreed owners upstream of Walls.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.03 — Separate positive frames, positive planes and the different wall loci

[#1314](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1314); review findings 02.

Give the current period-domain and wall APIs names and owners matching what they actually define, with explicit maps between frame, plane, numerical-locus and stability interpretations.

Native prerequisites: [#1313](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1313).

### MO1.04 — Separate hyperbolic-extension algebra from geometric Mukai realizations

[#1315](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1315); review findings 03.

Extract reusable extension, reflection and Gram-form algebra from Lattice/Mukai while retaining geometric Mukai terminology for the realization and its geometric consequences.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312), [#1223](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1223), [#1229](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1229).

### MO1.05 — Remove numerical parent-to-specialization import inversions

[#1316](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1316); review findings 07.

Split generic numerical/Todd/transport foundations from K3, dimension-specific and cross-surface comparison files.

Native prerequisites: [#1313](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1313).

### MO1.06 — Distinguish numerical models, named surface cases and geometric realizations

[#1317](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1317); review findings 12.

Organize reusable Numerical/Examples material as mathematical models and put variety-specific realizations beneath the common numerical construction.

Native prerequisites: [#1316](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1316).

### MO1.07 — Move linear Serre duality and Yoneda helpers to their independent owners

[#1318](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1318); review findings 05.

Make the basic Serre-functor and linear representability theory importable without triangulated categories.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.08 — Separate abelian stability foundations and make slope theory independent of Gieseker

[#1319](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1319); review findings 06.

Extract abelian stability functions/HN foundations from the triangulated weak-stability application and organize geometric slope and Gieseker theories as siblings.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.09 — Own H⁰ constructions with DGCategory and make enhancement exactness explicit

[#1320](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1320); review findings 15.

Separate DGCategory’s intrinsic H⁰/shift/triangle/functor theory from the data comparing it with a chosen triangulated category.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.10 — Extract derived tensor and pushforward capabilities from Fourier–Mukai

[#1321](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1321); review findings 10.

Give general derived operations their own geometry-level owners, leaving Fourier–Mukai files to assemble kernels, convolution and transforms.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.11 — Move flatness and relative-perfect predicates out of the moduli consumer

[#1322](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1322); review findings 11.

Make geometric flatness, pseudo-coherence and Tor-amplitude predicates usable independently of the relative-perfect moduli problem.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.12 — Separate the GL⁺(2,ℝ) cover from its stability action

[#1323](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1323); review findings 08.

Extract the standalone covering-group/topological construction currently owned by stability symmetry.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.13 — Make mass a sibling of metric and extract planar convex geometry

[#1324](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1324); review findings 09.

Give mass its own stability-theoretic owner and move neutral planar perimeter/convexity lemmas out of a mass-subadditivity proof directory.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.14 — Repair direct Mathlib-owner mismatches in module and sheaf APIs

[#1325](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1325); review findings 13.

Perform the small, independently reviewable owner corrections where the current path disagrees with the API being extended.

Native prerequisites: [#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312).

### MO1.15 — Verify the completed ownership graph and close the migration ledger

[#1326](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1326); review findings 14.

Close MO1 on evidence that the extracted foundations are reusable and every review finding has a completed or explicitly adjudicated disposition.

Native prerequisites: [#1314](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1314), [#1315](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1315), [#1317](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1317), [#1318](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1318), [#1319](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1319), [#1320](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1320), [#1321](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1321), [#1322](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1322), [#1323](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1323), [#1324](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1324), [#1325](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1325).


## Sequencing and closure

1. MO1.01 settles the owner map and updates the policy/cutover contracts. This is the only initially ready MO1 issue.
2. MO1.02 and independent foundations MO1.07–MO1.14 can then proceed independently. MO1.04 additionally waits for CA #1223/#1229.
3. MO1.02 feeds the wall/period split MO1.03 and the numerical inversion repair MO1.05; MO1.05 feeds model organization MO1.06. These are separate reviewable cuts, not one repository-wide rename PR.
4. MO1.15 collects import-boundary, canonical-root, comparison and CI evidence from the implementation PRs. It closes only after the accepted repairs land or a specific proposal is rejected with recorded mathematical/import evidence.

No due dates, assignees or estimates of calendar time are imposed. Sizes describe reviewable scope; an issue may use multiple small PRs. Only MO1 blockers are newly installed. The native dependency graph and each `blocked_by` list must remain synchronized.

Every source move updates imports, umbrellas, audits, source/registry bindings, relevant gates and CI paths in the same PR. Keep historical declaration names through the repository’s existing executable-only bridge; do not create import shims for retired paths. Strengthen focused component rules without imposing a total subject order. Keep all hypotheses and supplied/proved boundaries explicit.

## Tracker synchronization and validation

The new issues are all on the newly created milestone 52. Before this planning PR merges, existing main does not own milestone 52, so RM-06 is not made red by adding issues to milestones 49–51. This PR introduces the milestone and all fifteen references together. No existing CA native blocker is changed, avoiding an RM-05 mismatch on other branches.

Validate the roadmap against the live API with `python3 scripts/check_roadmap.py --require-api`. Planning validation does not certify any proposed Lean move. The implementation PRs must obtain the prescribed full runner CI, and each issue-closing PR advances its roadmap status. The planning PR closes none of the implementation issues.
