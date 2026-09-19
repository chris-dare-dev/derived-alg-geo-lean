# Design

## Context

See `proposal.md` for the motivation. The current tree has a model-free
`DerivedBaseChangeData` root and a K-flat producer, then builds external-product
generators, their triangulated envelope, the coproduct closure, and the
bounded-coherent inverse image. It also has the one-functor t-structure
restriction API and the `TStructure.IndExtensionData` family. The missing work is
at the boundary between those formal constructors and the geometric witnesses
needed by the paper.

The repository's contract forbids `sorry`, `admit`, bypass axioms, and turning a
theorem or preservation result into a structure field. Local verification must
use targeted Lean module builds; the full repository build is left to CI.

## Goals / Non-Goals

**Goals:**

- Make the three issue outcomes source-faithful and usable by downstream
  consumers, with every comparison map and theorem hypothesis visible.
- Preserve one ownership chain: model-free base change at the root, K-flat
  resolutions as a producer, component restrictions as lifts, and local
  t-structures/slicings as consumers of those components.
- Give each implementation chunk a small frozen file set and run the four
  independent adversarial reviews on the same commit, with a hard three-round
  cap.
- Record repository inconsistencies and avoidable agent friction in a checked-in
  note rather than relying on chat history.

**Non-Goals:**

- Inventing a new derived-category carrier, a second Ind-extension hierarchy,
  or a generic representability/algebraicity interface.
- Claiming §3–§5 for morphisms outside the stated source theorem hypotheses.
- Hiding an unproved geometric theorem behind a proposition-valued field or
  closing an issue merely because its declarations compile.
- Running the full repository build locally.

## Decisions

1. **Keep `DerivedBaseChangeData` as the root.** `BaseChangeData.lean` owns the
   model-free projections and all category/functor definitions. `KFlatBaseChange`
   only supplies those projections. This prevents the open-immersion and future
   non-K-flat producers from duplicating the carrier. The ambient functor and
   restricted functor are connected by the existing inclusion comparison
   isomorphisms; no second functor is introduced just to state a theorem.

2. **Discharge §3 at the existing seams.** The concrete external-product
   Hom-vanishing, compactness, presentable linearity, projection formula,
   approximation, finite amplitude, bounded/coherent preservation, and Lemma
   3.18 detection proofs belong beside the corresponding `BaseChange*` APIs.
   Generic sequence and object-property lemmas remain generic. A geometric
   theorem is proved in the geometry owner and consumed by the sequence layer,
   rather than copied into a convenience structure.

3. **Make local structures consume base-change functors.** `TStructure/Local`
   owns uniqueness and one-functor restriction. `Families/SLocal` owns the
   quantification over quasi-compact opens and the affine examples. The slicing
   analogue belongs with the existing phase-transfer/slicing owner and must
   reuse the local t-structure data. The restriction comparison maps always
   point from the base category to the open-base category, avoiding an instance
   diamond between ambient and bounded-coherent inclusions.

4. **Reuse Ind extension rather than translate it by parallel definitions.**
   Theorem 5.3 adapters consume `TStructure.IndExtensionData`; a single bridge
   theorem relates its coproduct closure to the paper's filtered-colimit
   presentation. The affine closure, descent equations, and t-exactness clauses
   are theorems over that bridge. A failed bridge is a real blocker, not a
   reason to introduce a duplicate carrier.

5. **Authorize only the selected epic issues.** Add a manifest field
   `eligibility.allow_epic_issues` and require it to list exactly the selected
   issue numbers that carry `epic`. Preflight continues to reject epic labels
   for every other issue, as well as blocked, research, and spike labels. This
   is safer than weakening the label gate globally and makes the exception
   auditable in the manifest digest.

6. **Review frozen chunks, not an amorphous milestone.** The chunks are ordered
   #1060 → #1061 → #1062. Each chunk has a fixed directory/file-prefix list,
   explicit acceptance statements, targeted build commands, and the same four
   reviewers. After a commit is frozen, a finding either produces one revised
   commit in the next round or is adjudicated; a third unsuccessful round
   records `blocked` and terminates that chunk.

7. **Treat notes as a repository artifact.** `notes/loop-engineering-sf11.md`
   records stale roadmap/comments, controller mismatches, build practices, and
   confusing naming discovered during the run. It does not substitute for a
   theorem or silently broaden a frozen file scope.

8. **Scope the roadmap gate to the manifest base.** The repository already has
   inherited RM-07 disagreements that are not authored by this batch. The
   controller invokes `check_roadmap.py --scope-to-diff=<base_ref>` so those
   disagreements remain visible in the output but do not make an unrelated
   branch claim ownership of their repair; any roadmap entry changed by the
   SF11 branch still fails closed.

## Risks / Trade-offs

- **[Geometric witnesses exceed the current library]** → Keep the exact paper
  hypotheses at the call site and stop the affected ledger after three review
  rounds; do not replace them with postulates.
- **[A broad Families directory causes accidental scope drift]** → Freeze
  changed-file prefixes before implementation, run the repository-boundary
  review, and let the controller reject any changed path outside the chunk.
- **[Ind and coproduct presentations disagree]** → Prove the comparison once and
  have the math adversary check the quantifiers against Lemma 5.1 and Theorem
  5.3 before downstream use.
- **[CI takes longer than local work]** → Use targeted module builds and let the
  controller bind approval/merge to the reviewed head and required checks; do
  not start a second dependent issue on an unmerged predecessor.
- **[Epic opt-in becomes a blanket bypass]** → Validate the allow-list as a
  subset of the selected issue numbers and report the admitted exception during
  preflight.
- **[An inherited roadmap defect is silently ignored]** → Keep the scoped gate's
  inherited-disagreement report in the preflight output and the SF11 note; only
  branch-authored roadmap entries can be admitted by this run.

## Migration Plan

1. Add the OpenSpec artifacts, the explicit epic eligibility validation, and the
   SF11 notes/tests on the dedicated loop branch.
2. Validate the plan and run controller unit tests without remote mutation.
3. Implement and review #1060, push and merge it through the controller, then
   refresh the protected base before starting #1061; repeat for #1062.
4. Run targeted Lean checks, `scripts/precheck.sh` where applicable, and the
   required CI/trust-surface checks for every reviewed head.
5. Close each code issue only after the controller confirms the merged PR
   contains its closing keyword. Archive the OpenSpec change only after all
   three ledgers, gates, and issue closures pass.

## Open Questions

None. The external theorem boundary and the order of the three issues are
deliberate parts of the contract; if a required witness cannot be proved, the
bounded ledger must record the blocker rather than change the scope.
