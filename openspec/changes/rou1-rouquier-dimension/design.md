# Design

## Context

See [proposal.md](proposal.md) for motivation. `Dimension/GenerationTime.lean`
already defines the `ℕ∞` extension-step invariant for object properties, and
Mathlib provides the iterated triangulated envelope and the strong/classical
generator predicates. The two issues add a category-level infimum first, then
transport results through triangulated functors.

## Goals / Non-Goals

**Goals:**

- Add Rouquier dimension using the existing single-object singleton property
  and envelope machinery.
- Expose the finite, strong-generator, classical-generator, and zero-stage
  characterisations required by #919.
- Add forward envelope transport, generation-time monotonicity, essential
  surjectivity monotonicity, and equivalence invariance for #921.
- Keep both modules generic and independently importable from geometry and
  stability theory.

**Non-Goals:**

- Prove the multiplicative envelope law or Stacks 0FXA (#920).
- Reconcile the repository's `ExtensionClosure` presentation (#918).
- Prove geometric bounds, semiorthogonal decomposition bounds, or statements
  involving `CompactlyGenerated/`.
- Add an arbitrary-property version of Rouquier dimension, a new closure
  operation, or an equivalence claim for a general functor.

## Decisions

### Ownership and canonical root

Rouquier dimension is a new invariant of an abstract triangulated category,
so its canonical declaration belongs to `CategoryTheory.Triangulated` under
`DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Rouquier.lean`. This
follows the Tier 2 triangulated-category subject rule in
`docs/architecture/mathematical-ownership.md` and
`docs/architecture/placement.md`. The already existing generation-time API
remains owned by `CategoryTheory.ObjectProperty`; functor transport of object
properties remains there, while category-level dimension results remain in
`CategoryTheory.Triangulated`.

### Reuse and comparison maps

The new numerical definition takes the infimum of the existing generation
time at `ObjectProperty.singleton G`. It introduces no competing generator
predicate or envelope carrier. The finite-dimension equivalence projects to
Mathlib's strong-generator predicate, and the classical-generator corollary
uses Mathlib's existing strong-to-classical implication. The zero case is the
zeroth envelope comparison, whose existing Mathlib definition is the shift,
binary-product, and retract closure.

The finite-witness proof uses `ENat.exists_eq_iInf`, whose index must be
nonempty. Derive a local `Nonempty C` witness from
`HasZeroObject.zero.choose`; do not strengthen the public category hypotheses
with a new `[Nonempty C]` assumption. The zero-stage theorem can use
`ENat.iInf_eq_zero` without that side condition.

For #921, the pointwise envelope-transport lemma extends Mathlib's
`ObjectProperty.triangEnvelopeIter`, defined under the `CategoryTheory/Triangulated`
API path. Its Lean namespace remains `CategoryTheory.ObjectProperty`, and the
downstream module is
`DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/Functor.lean` because the
lemma is part of the generation-dimension feature. Category-level results use
`CategoryTheory.Triangulated` in that same module. This keeps API namespace,
subject owner, and file placement explicit.

Transport is proved pointwise through the existing closure construction in its
defining order: shifts, binary products, distinguished extensions, then
retracts. It uses `[F.CommShift ℤ] [F.IsTriangulated]`; Mathlib supplies the
additivity and binary-product preservation consequences. The public map lemma
uses `ObjectProperty.map F`, Mathlib's essential image property that includes
objects isomorphic to images, and records only the forward inclusion. The
generation-time comparison uses the existing order characterisation.
Essential surjectivity `[F.EssSurj]` supplies target objects up to
isomorphism. For an equivalence, use `Equivalence.IsTriangulated.mk'` and the
pinned instances that make its inverse and symmetric equivalence
triangulated. No reverse-inclusion theorem is stated for arbitrary functors.

### Imports and instances

The Rouquier file imports the existing generation-time module and only the
narrow Mathlib APIs needed for `ℕ∞` infima and generator predicates. The
functor file imports the Rouquier and generation-time APIs plus the pinned
triangulated-functor interfaces. Neither file imports
`AlgebraicGeometry/**`, `StabilityCondition/**`, or
`CompactlyGenerated/**`. The work adds no global instance. Any local
specialization must agree with Mathlib through the existing singleton,
envelope, and exact-functor APIs; it must not create a second carrier or
instance diamond.

### Index convention

Mathlib's `triangEnvelopeIter G n` is Rouquier's `⟨G⟩_{n+1}`. In particular,
its zeroth stage is exactly the closure generated without extensions, and
`triangEnvelopeIter_succ` confirms the recursive successor indexing without
requiring `[IsTriangulated C]`. Therefore the infimum is Rouquier's numerical
dimension with no offset. The module docstring will state both the convention
and the reason the zero-offset choice is intentional. It will also state that
the infimum ranges over single objects rather than arbitrary object properties
and does not supply a preselected object attaining its value; finite witness
theorems remain separate existential statements. It will also cite
`triangEnvelopeIter_add` as the extension-composition compatibility with this
same `n + 1` convention, explicitly noting that this auxiliary equation
requires `[IsTriangulated C]`; neither the Rouquier dimension API nor its
zero-offset proof adds that stronger class.

### Audit and review

New public declarations append to `scripts/StabilityConditionAudit/Dimension.lean`;
the `Dimension.lean` umbrella imports each new direct child. Every frozen
chunk receives independent mathematical/source-faithfulness,
repository-boundary, abstraction/adoption, and Mathlib-style reviews on the
same commit. The altitude and hypothesis-elimination advisors run before
ledger initialization. Reviewers must assess the envelope index, actual
functor hypotheses, import boundaries, and reuse of the canonical roots.

Each attempt is limited to three review/improve rounds. Bounded recovery is
disabled for this plan: a third unsuccessful round leaves its ledger terminal
and preserves the evidence. Any continuation then requires a separately
reviewed recovery plan that reuses the same objective history; it cannot
rename or re-chunk the work to reset the allowance. This avoids automatic
scope changes to these two issue chunks.

### Bootstrap and execution order

Publish this plan and its enabled #919 manifest first as a planning-only PR
from a separate plan branch. Because the controller cannot initialize a ledger
until its manifest is on the exact base, this one-time bootstrap publication
uses the direct `git push` and `gh pr create` actions the user explicitly
authorized; it contains only planning artifacts and the execution manifest,
no Lean changes. Use no issue-closing syntax in its title, body, or commit
messages, use only plain references to #919 and #921, and verify that GitHub
reports no closing issue references. This exception applies only to that
plan-only PR. After it merges, fetch the protected base and start the
implementation on a fresh, clean issue branch whose HEAD is exactly
`origin/main`. Run manifest validation and live preflight there. Only after
preflight passes, run both declared altitude advisors, inspect their findings
against the generalization backlog, then initialize the digest-bound ledger.
All implementation-phase provider actions use the loop controller. The source
chunk's frozen file list contains only the Rouquier module, umbrella, audit
slice, and append-only generalization backlog; it cannot edit this plan or
change its own execution authority.

## Risks / Trade-offs

- **Off-by-one error in the numerical invariant** → State the `⟨G⟩_{n+1}`
  correspondence in the public docstring and check both the zeroth stage and
  finite-bound theorem.
- **Accidentally stronger functor hypotheses or reverse transport** → Check
  each closure step against Mathlib's exact APIs and review the public binder
  list and implication direction.
- **Accidental application-layer import or duplicate abstraction** → Check
  transitive imports, audit routing, and the canonical-root decision in the
  independent boundary and abstraction reviews.
- **Stale milestone dependency state** → Do not start #921 until #919 is
  merged and closed, the stale blocked label is removed, and a fresh live
  preflight passes.
