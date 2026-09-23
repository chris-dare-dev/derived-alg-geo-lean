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

For #921, transport is proved pointwise through the existing closure
construction in its defining order: shifts, binary products, distinguished
extensions, then retracts. The public map lemma records only the forward
inclusion. The generation-time comparison uses the existing order
characterisation. Essential surjectivity supplies the target objects up to
isomorphism, and equivalence equality uses the functor and a proved
triangulated quasi-inverse if Mathlib does not already provide that fact.
No reverse-inclusion theorem is stated for arbitrary functors.

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
`triangEnvelopeIter_add` confirms the successor indexing. Therefore the
infimum is Rouquier's numerical dimension with no offset. The module
docstring will state both the convention and the reason the zero-offset
choice is intentional.

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
  merged, its controller attestation is recorded, the blocked label is
  removed, and a fresh live preflight passes.
