# Declaration placement by signature

This is the operational placement test for new declarations and structural
moves. The canonical owner is determined by the weakest mathematical
vocabulary needed to state a declaration after irrelevant local notation is
expanded. The motivating theorem, current filename, first consumer, and proof
technique do not determine ownership.

## Signature test

Read the complete public type of the declaration and choose the first row that
can express it without importing a row below it.

| Minimal vocabulary in the public type | Canonical owner |
| --- | --- |
| Rings, ideals, ordinary modules, localization, additive subgroups | `Algebra/` |
| Linear maps, bases, lattices, matrices, bilinear or quadratic forms, exterior powers | `LinearAlgebra/` |
| Bicategories, 1- and 2-morphisms, adjunctions between 1-morphisms, mates, modifications | `CategoryTheory/Bicategory/` |
| Ordinary categories, functors, adjoint functors, limits, abelian or triangulated structure | the nearest `CategoryTheory/` subject root |
| Pseudofunctors, their coherence transport, and fiberwise object loci | `CategoryTheory/Pseudofunctor/` |
| Grothendieck topologies, sites, sheaves, or descent | `CategoryTheory/Sites/` |
| Topological spaces but no schemes | `Topology/` |
| Schemes, varieties, geometric fibers, scheme morphism properties, `Dqc(X)`, `QCoh(X)`, or `Coh(X)` | `AlgebraicGeometry/` |
| Registration of a geometric construction as a generic categorical interface | the interface's `Instances/AlgebraicGeometry/` leaf |

A generic declaration does not become geometric because its only current use
is geometric. Conversely, a theorem remains geometric when its signature
intrinsically contains a scheme even if its proof is entirely algebraic or
categorical. When `Algebra/` and `LinearAlgebra/` overlap, follow the nearest
Mathlib hierarchy: module localization and ring operations are algebra;
linear-map, basis, lattice, matrix, and multilinear constructions are linear
algebra.

## Root and consumer test

Before adding or moving a public declaration:

1. Search Mathlib and this repository for the carrier or concept.
2. Name the canonical root module and the concrete consumer module.
3. State the Lean relationship between them: direct reuse, `extends`, an
   instance, an `abbrev`, or a proved comparison.
4. Verify that the root imports no consumer, paper-specific file, or instance
   bridge.
5. Import the root directly from the consumer. Do not add a compatibility shim
   merely to preserve the old motivational path.
6. Update the nearest umbrella, axiom audit, declaration baseline, architecture
   gate, and this documentation in the same change.

If a file contains both a generic block and its geometric use, split the block
at the first declaration whose signature no longer needs the consumer's
vocabulary. Namespace alone is not evidence of correct ownership: declarations
inside `LinearMap`, `Module`, `Submodule`, `Matrix`, or similar namespaces must
still live with their most general mathematical source.

An adjunction in its most general implemented form is
`CategoryTheory.Bicategory.Adjunction`. Mathlib identifies ordinary functor
adjunctions with its `Cat` specialization. A theorem that merely assumes an
ordinary adjunction is placed by the other vocabulary in its signature:
preservation results belong with limits, `Ext` comparisons with derived `Ext`,
and kernel packages with Fourier--Mukai theory.

Comparison data of type
`(DerivedCategory C)ᵒᵖ ≃ DerivedCategory Cᵒᵖ` uses only abelian and derived
categories, so its canonical owner is
`CategoryTheory/Triangulated/DerivedCategory/Opposite.lean`. Exact algebraic
linear duality on `ModuleCat` and its derived lift are the categorical
specialization in `LinearDual.lean`. A Serre-duality statement that mentions a
scheme imports those roots and the canonical coherent-derived specialization;
its geometric motivation does not move the generic functors into duality.

The comparison `Dᵇ(Coh X) ≃ Dᵇ_coh(Dqc X)` intrinsically mentions a scheme,
so its statement and conditional consumer API belong under
`AlgebraicGeometry/DerivedCategory/Dqc/`. The existence proposition is not an
instance: `Dqc/Comparison.lean` accepts it explicitly and produces a coherent
representative and comparison isomorphism. The same rule applies to the
conditional equality of the perfect and compact-object properties. A moduli
consumer adds its relative-perfect and bounded-cohomology hypotheses without
becoming the owner of either comparison.

Classify categorical dimension before applying the table. A declaration whose
essential data are associators, unitors, pentagons, triangles, or other
2-morphisms is not ordinary-category infrastructure merely because its `Cat`
specialization is written with functors and natural isomorphisms. Its root is
the corresponding bicategory or pseudofunctor module. Thus conjugating a
Cat-valued pseudofunctor presentation through objectwise equivalences is rooted
at `CategoryTheory/Pseudofunctor/Transport.lean`; affine derived and geometric
models import that root as consumers.

The module-localization kernel chain is rooted at
`Algebra/Module/Localization/Kernels.lean`. Its linear-map, `ModuleCat`, and
finite-limit-preserving natural-transformation forms are one algebraic chain:
the first constructs the map on module kernels and the remaining declarations
prove its localization behavior, without mentioning a site or scheme.
`AlgebraicGeometry/CoherentSheaf/Abelian/Kernels.lean` is a direct consumer and
owns only the scheme restriction, affine comparison, and coherence steps.

Weight-indexed spans of basis vectors and the resulting independence,
spanning, internal-direct-sum, and multiplicativity lemmas are rooted at
`LinearAlgebra/GradedBasis.lean`. The numerical consumer imports that module
and adds the geometric `NumericalRingData.ofGradedBasis` constructor; it does
not own another copy of the decomposition.

Theorems stated only using `Finsupp`, `MvPolynomial`, homogeneity, and
`divMonomial` are rooted at `Algebra/MvPolynomial/DivMonomial.lean` in the
established `Finsupp` and `MvPolynomial` namespaces. The standard polynomial
grading and generation by variables over degree zero belong in
`Algebra/MvPolynomial/Grading.lean`. Representative-independent maps on
polynomial degree-zero localizations—including Laurent sign and block
projections, their one-localization homotopies, and full-block finiteness—also
belong under `Algebra/MvPolynomial/`. Polynomial-variable Čech denominators,
graded-localization terms, the canonical `p / 1` variable-localization element,
face maps, block homotopies, primitives, and finite-block assembly belong under
`Algebra/MvPolynomial/Cech/`. Comparison of that diagram with projective basic
opens, sheaf sections, or cohomology is the geometric consumer.

Internally graded modules are algebra, not projective geometry. Extend
Mathlib's `GradedModule` namespace under `Algebra/Module/GradedModule/` for
degree-zero homogeneous localizations, natural or integer graded shifts,
localization trivializations, and equality transport between denominator
power submonoids. Pure exponent-vector arithmetic uses `Algebra/Finsupp/`, and
polynomial specializations use `Algebra/MvPolynomial/`. A projective sheaf,
basic-open comparison, or cohomology module imports these roots and adds only
the scheme, section, or cohomological consumer.

## Moduli and subprestacks

`CategoryTheory.Moduli.BoundednessProblem` is the neutral boundedness root. A
stability-family package may require it and a geometric moduli package may
realize it with finite-type parameter data, but neither consumer owns the
predicate.

Mathlib's `Pseudofunctor.ObjectProperty` is the canonical fiberwise locus for a
Cat-valued pseudofunctor:

- `IsClosedUnderIsomorphisms` makes the locus replete;
- `IsClosedUnderMapObj` makes it stable under restriction;
- `fullsubcategory` and `ι` construct the sub-pseudofunctor and its inclusion.

Repository extensions to that mechanism live under
`CategoryTheory/Pseudofunctor/ObjectProperty/`. Do not introduce a parallel
`Subprestack` carrier in algebraic geometry. An indexed collection of
isomorphism-closed fiber predicates is not yet a subprestack until restriction
stability is supplied.

Concrete finite-type witnesses, atlases, scheme presentations, relative-perfect
objects, semistable loci, and Harder--Narasimhan filtrations remain under
`AlgebraicGeometry/Moduli/` because their signatures intrinsically mention
geometry.

`AlgebraicGeometry.RelativePerfectModuliSelector` is the canonical name for
the weaker geometric input used by finite-type boundedness: it stores the
independent replete `familyLocus` and `geometricLocus` over each actual scheme
base change. It is not a pseudofunctor object property and provides no
restriction functors. The affine construction first places its locus on an
actual Cat-valued pseudofunctor, applies `universallyStable`, and only then
calls `fullsubcategory`; that is the root-to-consumer relationship required
for a genuine subprestack.

## Review evidence

Every structural pull request must include:

- the signature-test row for each moved or new public root;
- the root-to-consumer import direction;
- the specialization map or a statement that the consumer directly reuses the
  root;
- any adjacent misplaced declarations discovered while editing, recorded in
  `docs/architecture/cutover-ledger.md` if they are not part of the same slice.
