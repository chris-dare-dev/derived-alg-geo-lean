# Structural cutover ledger

This ledger records known ownership defects that have been confirmed by the
signature test in `placement.md`. It is a migration queue, not an allowlist:
new code must use the canonical owner immediately, and touching one of these
blocks should normally move it rather than add more declarations beside it.

## Completed roots

- Generic moduli boundedness: `CategoryTheory/Moduli/Boundedness.lean`.
- Generic replete subprestack machinery:
  `CategoryTheory/Pseudofunctor/ObjectProperty/`, reusing Mathlib's
  `Pseudofunctor.ObjectProperty.fullsubcategory`.
- Ordinary ring/module helpers already extracted to `Algebra/Module/`.
- Generic sheaves and ringed-site module sheaves:
  `CategoryTheory/Sites/Sheaves/`.
- Generic abelian and derived-category infrastructure:
  `CategoryTheory/Abelian/` and
  `CategoryTheory/Triangulated/DerivedCategory/`.
- Canonical scheme-derived specializations:
  `AlgebraicGeometry/DerivedCategory/Basic.lean` registers the shared
  module-sheaf derived-category instance, while
  `AlgebraicGeometry/DerivedCategory/Coherent.lean` owns `D(Coh X)`,
  `Dᵇ(Coh X)`, `Perf(X)`, and the structure-sheaf perfect object without
  importing scheme-family, pullback, determinant, or moduli consumers.
  `Families/BoundedGeometry.lean` now begins with base-change fiber aliases and
  pullback-preservation contracts.
- Derived opposites and exact linear duality:
  `CategoryTheory/Triangulated/DerivedCategory/Opposite.lean` owns the generic
  `DerivedCategory.OppositeComparison`, while `LinearDual.lean` owns the exact
  ModuleCat linear-dual functor and its derived lift. Canonical and Serre
  duality consume those roots together with
  `AlgebraicGeometry/DerivedCategory/Coherent.lean`; the former geometric
  `Duality/Serre/LinearDual.lean` path and its ModuleCat-specific comparison
  carrier are retired.
- Bounded-coherent and compact/perfect comparison consumption:
  `AlgebraicGeometry/DerivedCategory/Dqc/Comparison.lean` converts the
  explicit `HasBoundedCoherentDqcIdentification` and
  `PerfectObjectsAreCompactInDqc` propositions into coherent representatives,
  comparison isomorphisms, and membership equivalences without registering
  global instances. The relative-perfect category is the first geometric
  consumer and states bounded coherent cohomology at the use site.
- Perfect-complex notion reconciliation:
  `schemePerfect` remains the absolute thick envelope in `D(Coh X)`,
  `schemeRelativePerfect` remains the base-dependent pseudo-coherent finite-Tor
  locus in `Dqc(X)`, and `TwoTermPerfectDeterminantData` remains explicit
  presentation data. `Moduli/PerfectComplex/Comparison.lean` proves the valid
  two-term-to-absolute-to-Dqc direction without asserting a reverse or
  absolute/relative equivalence. The canonical `Dqc(X)` zero now lives in
  `DerivedCategory/Dqc.lean` for every scheme; the moduli consumer only proves
  its additional relative properties.
- Ordinary semilinear and top exterior-power algebra:
  `LinearAlgebra/ExteriorPower/`.
- Exterior powers of presheaves of modules over an arbitrary ring presheaf:
  `CategoryTheory/Sites/Sheaves/Modules/ExteriorPower.lean`; scheme
  sheafification and restriction comparisons remain geometric consumers.
- Higher-categorical adjunctions: Mathlib's
  `CategoryTheory.Bicategory.Adjunction`, extended under
  `CategoryTheory/Bicategory/Adjunction/`; ordinary adjoint functors are the
  `Cat` specialization through `Adjunction.bicategoricalEquiv`.
- Pseudofunctor-presentation transport:
  `CategoryTheory/Pseudofunctor/Transport.lean` owns conjugation through
  objectwise equivalences together with transported units, compositors,
  pentagon, and triangle equations. Both affine bounded-projective derived
  realizations consume this root; the former
  `CategoryTheory/EquivalenceTransport.lean` path and the private geometric
  duplicate are retired.
- Pseudofunctorial triangulated families:
  `CategoryTheory/Triangulated/Families/TriangulatedFiberFamily` now owns a
  Cat-valued pseudofunctor on `LocallyDiscrete Bᵒᵖ`, exposes its pullback unit
  and compositor, and derives the `K₀` identity and composition laws through
  those isomorphisms. Ordinary `Bᵒᵖ ⥤ Cat` families enter through
  `TriangulatedFiberFamily.ofFunctor`. Pre-stability base change transports
  its iterated preimage witness through the pseudofunctor compositor.
- Generic preservation through composition and reflective transport:
  `CategoryTheory/Limits/Preserves/`. The former repository
  `CategoryTheory/Adjunction/` root is retired.
- Module-localization kernel maps:
  `Algebra/Module/Localization/Kernels.lean`. This owns `LinearMap.kerMap` and
  the `IsLocalizedModule.{kerMap,kernelMap,kernelNatTrans}` chain; the
  coherent-sheaf kernel theorem imports and directly reuses that root.
- Relative-perfect moduli selectors are explicitly fiberwise:
  `AlgebraicGeometry.RelativePerfectModuliSelector` exposes `familyLocus` and
  `geometricLocus`, each closed under isomorphisms but with no claimed
  restriction maps. The genuine affine relative-perfect subprestack is built
  separately by `AffineFamilyRelativePerfectPseudofunctor.lean` through the
  generic `universallyStable` and `fullsubcategory` APIs.
- Weighted-basis decompositions:
  `LinearAlgebra/GradedBasis.lean` owns `gradedPiece`, its spanning and
  independence results, and multiplicativity promoted from basis vectors.
  `AlgebraicGeometry/Numerical/Core/GradedBasis.lean` retains only
  `NumericalRingData.ofGradedBasis` and its smoke test.
- Division by multivariate monomials:
  `Algebra/MvPolynomial/DivMonomial.lean` owns the `Finsupp.degree` bridge,
  homogeneous-degree result, factor-commutation identities, and
  `MvPolynomial.divMonomial_pow_mul`, exact division by a variable power, and
  cross-variable cancellation. Projective Laurent and section comparisons
  import that root directly.
- Graded-module localization and shifts:
  `Algebra/Module/GradedModule/` extends Mathlib's `GradedModule` namespace with
  `DegreeZeroLocalization`, natural and integer shifts, twist
  trivializations, and transport along equal power denominators. Proj sheaves
  and Čech complexes import these roots as geometric consumers.
- Laurent monomial bases:
  `Algebra/Finsupp/LaurentExponent.lean` owns the exponent-vector arithmetic,
  while `Algebra/MvPolynomial/{Grading,LaurentBasis}.lean` owns the standard
  polynomial grading, polynomial twists, and the monomial spanning and
  independence API for degree-zero localizations. The former
  `AlgebraicGeometry/Proj/Modules/LaurentBasis.lean` path is retired.
- Laurent localization projections and blocks:
  `Algebra/MvPolynomial/{LaurentProjection,LaurentBlock,LaurentHomotopy,LaurentFinite}.lean`
  owns representative-independent sign projections, negative-support block
  projections, the one-localization contracting map, and full-block
  finite-generation results. The corresponding former Proj module paths are
  retired; the polynomial Čech algebra and its geometric consumers import the
  algebraic leaves directly.
- Polynomial variable Čech algebra:
  `Algebra/MvPolynomial/Cech/{Basic,Homotopy,Primitive,Finite}.lean` owns the
  denominator diagram, graded-localization terms and faces, canonical `p / 1`
  variable-localization element, block homotopy, cocycle primitive, and
  finite-block assembly. The former
  `AlgebraicGeometry/Proj/Modules/Cech{Homotopy,Primitive,Finite}.lean` paths
  are retired. `Proj/Modules/ProjectiveSpace.lean` now begins at comparison
  with projective basic opens and sections; geometric cohomology files import
  the algebraic leaves directly.
- Polynomial projective-space algebraic prefix:
  `Algebra/MvPolynomial/Grading.lean` owns generation by the variables over the
  degree-zero homogeneous submodule; `DivMonomial.lean` owns the exact-division
  and cross-variable cancellation lemmas; and `Cech/Basic.lean` owns the
  canonical localized fraction. `Proj/Modules/ProjectiveSpace.lean` now keeps
  only the generic-point, basic-open, section, and cohomology comparisons that
  introduce geometric vocabulary.
- Negative-twist arithmetic prefix:
  `Algebra/Module/GradedModule/Shift.lean` owns triviality of an integer-shifted
  piece below degree zero, while `Algebra/MvPolynomial/DivMonomial.lean` owns
  the homogeneous variable-power divisibility vanishing theorem and its
  cross-variable corollary. `AlgebraicGeometry/Cohomology/Cech/NegativeTwist.lean`
  now begins with the Čech overlap and projective-cohomology plumbing.
- Relative numerical algebra:
  `Algebra/RelativeNumerical/Basic.lean` owns indexed direct sums, saturated
  family-relation quotients, and their universal properties, while
  `Overlattice.lean` owns additive-map images, factorizations, and
  finite-relative-index predicates. The former
  `AlgebraicGeometry/Numerical/GrothendieckGroup/Relative{,Overlattice}.lean`
  paths are retired; a future geometric adapter must introduce actual scheme
  data and import the algebra root directly. `FamilyRelationSystem` is
  deliberately recorded by the single-instantiation ratchet as statement-layer
  input: downstream applications supply admissible families, so this slice
  does not fabricate a second library-owned inhabitant merely to satisfy a
  count.

## Confirmed next lanes

1. Generic triangulated `K₀` realization and descent, together with the
   categorical Euler carrier, currently have public signatures using only
   categories, Grothendieck groups, and additive groups. Move that block to
   `CategoryTheory/Triangulated/GrothendieckGroup/`; retain only the geometric
   Riemann--Roch and numerical-pairing transfer consumers below
   `AlgebraicGeometry/Numerical/`.
2. The generic `ZLattice` class and its finite-torsion-free construction use
   only finite free abelian groups. Move that root to
   `LinearAlgebra/Lattice/`; retain the numerical-quotient theorem as its
   geometric consumer.

Take these lanes one per pull request. Remove the old path rather than retaining
an import-only shim, update audits and umbrellas in the same pull request, and
add a focused layering guard preventing the declaration from returning to its
consumer.
