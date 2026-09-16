# Mathematical ownership and abstraction boundaries

This is the repository policy for separating reusable mathematics from its
applications. Read it before adding a public root, extending a known mixed
module, or moving declarations. It complements the decision procedure in
[placement.md](placement.md), the reuse contract in
[abstraction-tree.md](abstraction-tree.md), and the implemented import rules in
[layers.md](layers.md). `CLAUDE.md` and `AGENTS.md` carry the same short checklist.

The policy applies to new work. Existing violations are tracked in the
[cutover ledger](cutover-ledger.md) and
[MO1 plan](../reviews/2026-09-13-mathematical-ownership-plan.md). A target owner
is not a claim that its module already exists. Verify the checkout and the
linked issue before changing imports. A discussion, issue, or dated review may
propose a policy change; record the resulting decision in these versioned
documents and update the affected issue contracts in the same change.

## Three relationships to record separately

1. **Ownership:** the subject that defines and studies the object. Direct
   extensions of an existing Mathlib API follow that API's owner at the pinned
   revision. A new subject merely using that API needs its own ownership
   decision: a stability condition uses additive maps but is not an
   additive-group lemma.
2. **Dependency:** the modules required to state and prove the declarations.
   Consumers import foundations. A generic foundation does not import its
   specializations, realizations, paper applications, or their comparisons,
   including transitively through an umbrella.
3. **Specialization or realization:** the actual Lean map connecting a leaf
   with the root: direct reuse, an instance, projection, abbreviation, or
   proved comparison. A directory name establishes none of these.

There is no total ordering of algebra, category theory, topology and geometry.
Nesting is mathematical navigation, not a claim about inheritance or import
direction. Preserve the single `DerivedAlgGeo` library, Mathlib owners for its
direct extensions, and the site/topological-space/scheme distinctions.

## Decide at declaration boundaries

Search the pinned Mathlib and repository definitions before introducing a
name. Read the public types and imports; a filename, namespace, motivating
paper, or first consumer is insufficient evidence of ownership.

- Keep independently useful elementary theory with its mathematical object.
  A quadratic coercivity lemma remains quadratic-form theory even if a wall
  argument first needed it. A theorem about quasicoherent modules remains with
  those modules even if its proof uses cohomology.
- Split a mixed file into its neutral foundation, application adapter and
  comparison declarations. A comparison imports both presentations downstream;
  do not make a generic root import a special case to state their agreement.
- Share the construction, not just its name. Prefer an existing root and a
  specialization map to copying fields into a new record. Follow the
  independent-consumer and instance-agreement obligations in
  [the root review](abstraction-tree.md#root-review-before-a-new-structure).
- Generalize only across hypotheses for which the construction actually works.
  Record failed unifications and preserve separate branches. A false proposed
  generalization is not repaired by adding its conclusion as a structure field.
- When a misplaced root already exists, move or split that root and update its
  consumers. Do not leave it in place and add a second owner at the target path.
  A ledger entry records deferred work; it does not permit growing the defect.

## Charges, walls and Mukai theory

**Abstract charge first; characteristic classes are constructors.** The
primitive charge is an additive map `Λ →+ ℂ`, often pulled back along a class
map from a Grothendieck group. A heart, positivity, HN filtrations, a slicing
and support conditions are additional data or properties. Do not require a
Chern character, a Todd class or a scheme in every abstract charge.

Reuse `ChargeFamily` and the existing `Exp.ofMoments` kernel for their supported
families. Keep truncation degree `m`, geometric dimension `n`, and correction
class `κ` separate. In particular `(n,m) = (3,2)` is a valid tilt construction;
`κ = 1` and `κ = √td` are distinct choices. An arbitrary-divisor-rank input
must not be forced through lossy scalar polarization degrees. A new charge
formula must either reach the existing root by a proved comparison or explain
the mathematical obstruction to doing so.

**Construction precedes walls.** Place neutral paired complex functionals and
their linear-algebra lemmas with bilinear/quadratic algebra. Place charge
families and stability-facing adapters upstream of wall equations. Place
scheme Chern/Todd realizations with geometry. Ordinary rotation operations
may be neutral; their comparison with a tilted heart belongs downstream.
Preserve the existing canonical declarations required by CA1–CA3, including
the option to withdraw an unjustified new graded root.

**Implemented by #1313.** The canonical stability-facing owner is
`StabilityCondition/CentralCharge/`; determinant-alignment loci remain below
`Walls/`, and full quadratic support statements remain below `Support/`.
Neutral paired-functional, continuity, coercivity and Hodge-index owners are
below `LinearAlgebra/`. Issue #1230 has not supplied its conditional
`Lattice.pairCharge`, so the established paired functional and its existing
bridges remain the root for this cutover.

**Name the locus that was defined.** Distinguish `Z(δ) = 0`, determinant
alignment, a signed ray condition, and an actual destabilization wall.
Charge-zero loci are generically real codimension two; alignment loci are
generically codimension one only with appropriate nondegeneracy. Equal-phase
claims need nonzero/sign conditions. Smoothness and codimension theorems need
their own regularity hypotheses. Do not make all these loci instances of a
codimension-one-submanifold parent. Numerical alignment alone proves no
categorical destabilization.

**Frames, planes and support are separate.** An ordered positive frame and
the unoriented positive plane it spans are different objects, related by a
forgetful map. The canonical neutral owners are `QuadraticForm/PositiveFrame.lean`
and `PositivePlane.lean`; orthogonality arrangements live in the separate
`Orthogonality*.lean` modules. General positive-plane/signature theory belongs in linear
algebra; a geometric period-domain identification belongs with its
realization. Negative definiteness on `ker Z` alone is not the full quadratic
support condition: nonnegativity on relevant semistable classes is also needed.

**The Mukai application does not own all lattice theory.** General hyperbolic
extensions, reflections and Gram-form results have neutral algebraic owners.
Geometric Mukai vectors, Euler-pairing identifications, integrality,
spherical-object interpretations and expected dimensions belong to the
appropriate applications. Preserve the single fixed-arity pairing generalized
over its coefficient ring; do not replace it by a dimension-indexed
self-pairing. Comparisons must account for coordinate equivalences,
polarization weights, normalization factors and odd-degree parity.

K3, Enriques and abelian surface models are siblings specializing shared
surface constructions. A numerical coordinate model is not an actual surface
or its full lattice. Name polarization slices as slices; Picard rank one in
higher dimension does not by itself identify the entire numerical ring with
powers of the polarization. Reusable models belong to their subject, with
`Examples` reserved for demonstrations and realizations stated explicitly.

**Implemented by #1317.** `Numerical/Models/` owns the formal
rank-degree-coordinate models; `Numerical/Examples/` owns the realization maps,
charges and walls demonstrated on them, and every module there reaches the
stability tree. The four named surface models share `Models/Surface/RankOne.lean`
and import no sibling. The Enriques model is titled as the polarisation slice
it is, and the dimension-general ring is `Models/MonogenicRing.lean`, named for
the generated-by-`H` hypothesis it actually uses rather than for Picard rank
one. K3-only charge adapters carry a `K3` suffix. Layering rule 12 keeps all of
that true.

## Independent foundations in the other subjects

- **Linear Serre theory and Yoneda:** basic Hom-duality and linear
  representability need no triangulated category. Shift, Ext and exactness
  results are downstream. Full faithfulness needs its finiteness hypothesis;
  essential surjectivity is an additional obligation. **Done** (#1318):
  `CategoryTheory/Linear/SerreFunctor/` owns the duality data and its
  uniqueness, `CategoryTheory/Linear/Yoneda.lean` owns the three
  representability helpers and needs Mathlib alone, and layering rule 9 keeps
  both of those true.
- **Abelian stability and slope:** abelian stability functions and HN theory
  precede their triangulated applications. Geometric slope and Gieseker
  stability have independent owners and downstream comparisons. Retain
  `StabilityCondition/Weak` as the legitimate weakened-concept nesting.
  **Done** (#1319): `CategoryTheory/Abelian/Stability/` owns the stability
  functions, their Harder--Narasimhan theory and the `Weak/` variants below
  them, and reaches no triangulated module; `AlgebraicGeometry/Stability/`
  carries `Slope/` and `Gieseker/` as siblings over shared Hilbert-polynomial
  data with a `Comparison.lean` above them; and layering rule 13 keeps all of
  that true. The μ-Harder--Narasimhan existence theorem moved directory and
  kept its statement: it is not a Gieseker HN theorem.
- **dg H⁰:** intrinsic H⁰, shift, cone and functor theory belongs with the
  implemented `DGCategory` on `HomComplex`. Comparison with a chosen
  triangulated target belongs to enhancement theory. An ordinary equivalence
  with H⁰ is not an exact enhancement without shift/triangle compatibility.
  A placement correction does not change the dg encoding or prove uniqueness.
  **Done** (#1320): `Algebra/Homology/DGCategory/Pretriangulated/H0/` owns the
  intrinsic theory and reaches no enhancement consumer, scheme realization or
  stability module; `CategoryTheory/Triangulated/DGEnhancement/` keeps the
  comparisons and names two carriers -- `Enhancement`, the underlying H⁰
  presentation, and `Enhancement.Exact`, the refinement carrying `CommShift` and
  `Functor.IsTriangulated` as supplied data with `Cdg.enhancementExact` as its
  one inhabitant. The dg encoding is unchanged (ADR-0010 / ADR-0011), the seam
  and exactness obligations remain #854's and #855's, and layering rule 13 keeps
  the import claim true.
- **Derived operations:** general tensor and pushforward capabilities belong
  with the relevant derived-category object; Fourier–Mukai consumes them to
  construct transforms and convolution. Preserve the distinction between
  unbounded, bounded-coherent and relative operations. Bounded coherent tensor
  closure needs hypotheses and is not automatic on singular schemes.
- **Perfectness before moduli:** module flatness belongs with modules;
  pseudo-coherence, Tor amplitude and perfect-complex predicates belong with
  derived objects. Moduli constructions consume them. Preserve the existing
  one-way perfectness comparisons and the warning that the current
  cohomological pseudo-coherence criterion is not automatically the standard
  notion on arbitrary non-Noetherian bases.
- **Covering groups and convex geometry:** the independent GL-cover
  construction precedes its stability action. Neutral planar perimeter lemmas
  precede HN-polygon applications. Mass is a stability invariant consumed by
  the metric, rather than a definition owned by its metric proof.
- **Direct Mathlib extensions:** distinguish `ModuleCat` from arbitrary linear
  categories, presheaf modules from sheaf modules, and scheme-module exterior
  powers from their divisor applications. Use the actual API owner at the pin.

## Record the decision in the issue or PR

For a new or moved public root, use this compact record. Ordinary theorem
additions need only the entries affected by their change.

```text
Object and placement tier:
Existing root: declaration, module, and searched Mathlib pin
Current owner -> target owner (implemented, or pending cutover):
Consumers and exact specialization/comparison maps:
Imports: consumer -> root; downstream comparison -> both presentations
Hypotheses and supplied/proved boundaries preserved:
Independent consumers or justified statement-layer exception:
Instance agreement, including coordinate/normalization comparisons:
Verification: focused import checks, audit/registry coverage, runner CI
Tracking: issue, roadmap entry, and cutover-ledger disposition
```

A review should be able to trace a claimed abstraction to a declaration, an
import path and a map. A renamed directory, empty parent module or prose-only
inheritance claim does not satisfy this record.

## Complete and verify the cutover

Update imports, umbrellas, audit routing and declaration baselines, registry
bindings, source-owner assertions, documentation and relevant CI paths in the
same source PR. Preserve required historical names through the existing
executable-only mechanism; add no retired-path import shims.

A neutral core umbrella must not pull its applications back in transitively.
If it omits a child, document the exact umbrella/child exception, update the
coverage gate in that PR, and retain a stable export/build route for the child.
Never weaken coverage globally to allow a single move.

The current scripts enforce only their named rules. The stability exemption is
named by subcomponent rather than by top-level subtree since 2026-09-13, with
regression fixtures for the first named component edge; even so, neither it nor
the hard-coded divisorial owner certifies that every numerical root is
independent or well placed. Five of the nine exempt subcomponents mixed
modules that reach the stability tree with modules that do not; after MO1.05
and MO1.06 two still did, and MO1.08 (#1319) resolved one of those two by
removing `Stability/Gieseker/` from the list rather than narrowing it -- the
sheaf-stability subtree instantiates an abelian slope theory and reaches no
stability condition. `Numerical/Stability/` is the remaining mixed entry, and
that component boundary is a review obligation until its source cutover adds
the focused checks and regression fixtures. `check_single_instantiation.py` has a scoped search;
absence of a finding is not the two-consumer justification.

Run the relevant focused checks, then the prescribed runner CI for source
moves. Keep GitHub membership, native blockers and roadmap entries synchronized;
advance the entry when the issue closes. Policy documentation alone closes
neither a source migration nor an unresolved mathematical comparison.
