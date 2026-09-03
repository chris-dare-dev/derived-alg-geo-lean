# Structural cutover ledger

This ledger records known ownership defects that have been confirmed by the
signature test in `placement.md`. It is a migration queue, not an allowlist:
new code must use the canonical owner immediately, and touching one of these
blocks should normally move it rather than add more declarations beside it.

## Completed roots

- Orthogonal exceptional blocks and residual projections:
  `CategoryTheory/Triangulated/SemiorthogonalDecomposition/Blocks.lean`
  owns positive-length mutually orthogonal exceptional blocks, their
  triangulated spans, decomposition type, and residual right orthogonal;
  `Projection.lean` owns a chosen right adjoint to a full-subcategory
  inclusion and its universal Hom equivalence; `Mutation.lean` constructs the
  objectwise counit triangle and proves the generic projection-chain theorem.
  Ext profiles and their bidirectional transport remain generic in
  `SerreFunctor/`, while the one-step and finite kernel-extension result
  interfaces live in `FourierMukai/ExceptionalExtension.lean`.
  `AlgebraicGeometry/Surface/Enriques/PaperBlocks.lean` and
  `PaperExtension.lean` are geometric consumers: they identify the block
  members with the ten selected line bundles, record the numerical
  `(-2)`-chains, and specialize the projection and classification results.
  Constructing the divisor triangles and functorial kernel cones remains
  supplied data pending the dg enhancement lane.
- Generic moduli boundedness: `CategoryTheory/Moduli/Boundedness.lean`.
- Generic replete subprestack machinery:
  `CategoryTheory/Bicategory/Functor/Cat/ObjectProperty/`, reusing Mathlib's
  `Pseudofunctor.ObjectProperty.fullsubcategory`.
- Ordinary ring/module helpers already extracted to `Algebra/Module/`.
- Generic sheaves and ringed-site module sheaves:
  `Algebra/Category/ModuleCat/Sheaf/`.
- Generic abelian and derived-category infrastructure:
  `CategoryTheory/Abelian/` and
  `Algebra/Homology/DerivedCategory/`.
- Canonical scheme-derived specializations:
  `AlgebraicGeometry/DerivedCategory/Basic.lean` names the derived categories
  of module sheaves (the standard localization is a local instance in each
  consumer, never a global one), while
  `AlgebraicGeometry/DerivedCategory/Coherent.lean` owns `D(Coh X)`,
  `Dᵇ(Coh X)`, `Perf(X)`, and the structure-sheaf perfect object without
  importing scheme-family, pullback, determinant, or moduli consumers.
  `Families/BoundedGeometry.lean` now begins with base-change fiber aliases and
  pullback-preservation contracts.
- Derived opposites and exact linear duality:
  `Algebra/Homology/DerivedCategory/Opposite.lean` owns the generic
  `DerivedCategory.OppositeComparison`;
  `CategoryTheory/ModuleCat/LinearDual.lean` owns the bare contravariant
  ModuleCat linear-dual functor,
  `Algebra/Category/ModuleCat/LinearDual.lean` proves its exactness, and
  `Algebra/Homology/DerivedCategory/LinearDual.lean` owns the derived lift.
  Canonical and Serre duality consume those roots together with
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
  `Algebra/Category/ModuleCat/Sheaf/ExteriorPower.lean`; scheme
  sheafification and restriction comparisons remain geometric consumers.
- Higher-categorical adjunctions: Mathlib's
  `CategoryTheory.Bicategory.Adjunction`, extended under
  `CategoryTheory/Bicategory/Adjunction/`; ordinary adjoint functors are the
  `Cat` specialization through `Adjunction.bicategoricalEquiv`.
- Pseudofunctor-presentation transport:
  `CategoryTheory/Bicategory/Functor/Cat/Transport.lean` owns conjugation through
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
- Graded-ring homogeneous-localization domain properties:
  `RingTheory/GradedAlgebra/HomogeneousLocalization/Domain.lean` owns the five
  `HomogeneousLocalization` declarations proving nontriviality, domain, and
  reducedness from nonzerodivisor hypotheses. Their complete signatures use no
  projective spectrum or scheme. `AlgebraicGeometry/ProjectiveSpectrum/Integral.lean` imports
  this owner directly and adds the geometric chart and integrality results;
  the former Proj-owned source path is retired without a compatibility shim.
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
- Triangulated Grothendieck-group realizations and Euler forms:
  `CategoryTheory/Triangulated/GrothendieckGroup/Realization.lean` owns the
  canonical `K₀.Realization` alias and exact-functor descent squares, while
  `EulerForm.lean` owns `K₀.EulerForm`, its canonical linear-category form, and
  preservation by exact functors. Numerical Riemann--Roch, Euler-pairing, and
  Mukai-vector transfer remain in `AlgebraicGeometry/Numerical/` as consumers.
  The former geometry-owned one-field carriers `NumericalRealization` and
  `CategoricalEulerForm`, together with their parallel descent and preservation
  APIs, are retired rather than retained as compatibility wrappers.
- Finite free integral lattices: there is no repository lattice class. The
  interface is Mathlib's pair of instances `Module.Finite ℤ` and
  `Module.Free ℤ`, the latter from `Module.free_of_finite_type_torsion_free'`
  in `Mathlib/LinearAlgebra/FreeModule/PID.lean`.
  `NumericalVarietyData.instFiniteNumericalQuotient` remains in
  `AlgebraicGeometry/Numerical/GrothendieckGroup/Lattice.lean` because it
  introduces the Euler radical and numerical quotient. The former
  `AlgebraicGeometry.Numerical.ZLattice` namespace and the former
  `LinearAlgebra/Lattice/Basic.lean` are retired rather than retained as
  compatibility aliases.
- Numerical polynomials and mixed finite differences:
  `Algebra/NumericalPolynomial/Basic.lean` owns integer-lattice numerical
  functions, mixed differences, degree bounds, Newton coefficients, and top
  multilinear coefficients. `AlgebraicGeometry/IntersectionTheory/Snapper.lean`
  imports that root and begins with Picard powers, coherent twists, Euler
  characteristics, and the geometric induction certificate. The former
  `AlgebraicGeometry/IntersectionTheory/NumericalPolynomial.lean` and
  `AlgebraicGeometry/IntersectionTheory/NumericalPolynomial/` paths, together
  with the `AlgebraicGeometry.IntersectionTheory.NumericalPolynomial`
  namespace, are retired rather than retained as compatibility shims.
- Coverwise local equivalences of additive presheaves:
  `CategoryTheory/Sites/Sheaves/CoversTop.lean` owns detection of local
  injectivity, local surjectivity, and `J.W` membership on a family covering
  the terminal object. Scheme tensor, divisor, associated-sheaf, and Proj
  modules import that arbitrary-site root directly; the declarations no
  longer live inside the scheme tensor consumer.
- Over-site restriction infrastructure:
  `CategoryTheory/Sites/Over.lean` owns cocontinuity of `Over.post`,
  `Algebra/Category/ModuleCat/Sheaf/Over.lean` owns the module-sheaf
  restriction API, and `CategoryTheory/Sites/CoversTop.lean` owns
  transport of a terminal-covering family through a cover-preserving
  equivalence. `AlgebraicGeometry/Modules/Restriction/OpenImmersion.lean`
  imports these roots and now begins at the scheme/open-site equivalence; the
  three declaration names are preserved without a compatibility shim.
- Ringed-site presentation restriction:
  `Algebra/Category/ModuleCat/Sheaf/Presentation/Over.lean` owns
  restriction of `Presentation`, `GeneratingSections`, and
  `QuasicoherentData` to over sites, including preservation of a finite
  generating index. `AlgebraicGeometry/Modules/Affine/{BasicOpen,Finiteness}.lean`
  import that root directly and now begin with `Spec R`, distinguished opens,
  and affine finiteness. The seven declaration names are preserved without a
  compatibility shim.
- Ringed-site finite-presentation invariance and locality:
  `CategoryTheory/Sites/Sheaves/Modules/Presentation/{Isomorphism,Locality}.lean`
  own transport across isomorphisms, closure of the finite-presentation object
  property, restriction to over sites, and descent from a `CoversTop` family.
  `AlgebraicGeometry/Modules/Coherent/Basic/Isomorphism.lean` now contains only
  the `coherent X` instance, while `Descent/Locality.lean` contains only
  scheme open-immersion and affine-cover consumers. The seven declaration
  names are preserved without compatibility shims, and unnecessary hypotheses
  are removed from five declarations in the presentation transport/locality chain.
- Ringed-site finite-presentation closure:
  `CategoryTheory/Sites/Sheaves/Modules/Presentation/{Zero,Extensions}.lean`
  own the empty finite presentation of the zero module sheaf and the finite
  horseshoe construction proving closure under short-exact extensions.
  `AlgebraicGeometry/Modules/Coherent/Abelian/Extensions.lean` now contains only
  the resulting `coherent X` extension instance, while `Abelian/Basic.lean`
  retains the geometric zero, finite-product, abelian, and exact-inclusion
  instances. Public declaration names are preserved without compatibility
  shims.
- Generic invertible module sheaves and tensor/sheafification descent:
  `Algebra/Category/ModuleCat/Sheaf/Invertible.lean` owns rank-one local
  generator data, intrinsic `SheafOfModules.IsInvertible`, transport, finite
  presentation, and local trivializations. The adjacent `Tensor.lean` owns
  preservation of local equivalences by tensoring with a rank-one factor on an
  arbitrary site. `Topology/Sheaves/ModuleTensor.lean` owns the stalkwise
  arbitrary-factor strengthening. Scheme tensor objects, tensor closure,
  associativity, and Picard classes remain direct geometric consumers.
- Stalk tensor products of module presheaves:
  `Topology/Sheaves/ModuleTensor/StalkTensor.lean` owns the comparison between
  the stalk of a tensor product and the tensor product of stalks, together with
  its open-neighbourhood, germ, and stalk-map infrastructure. The parent
  `Topology/Sheaves/ModuleTensor.lean` imports that root to prove the
  arbitrary-factor stalkwise local-equivalence theorem. The former
  `Algebra/Category/ModuleCat/StalkTensor.lean` path and its export from the
  algebra umbrella are retired without a compatibility shim.
- Basiswise detection of topological sheaf isomorphisms:
  `Topology/Sheaves/Basis.lean` owns surjectivity of stalk maps detected on a
  basis and the resulting criterion that a sheaf morphism is an isomorphism.
  `AlgebraicGeometry/Modules/Affine/Comparison.lean` imports that root and now
  begins with scheme modules, distinguished opens, and localization. Both
  declaration names are preserved without a compatibility shim.
- Finite products of prime-spectrum basic opens:
  `RingTheory/Spectrum/Prime/BasicOpen.lean` owns
  `PrimeSpectrum.basicOpen_prod_eq_pi`, while
  `AlgebraicGeometry/Cohomology/Cech/Affine.lean` imports it and retains only
  the private localization machinery and public affine Čech exactness
  theorems. The declaration name and full signature are preserved without a
  compatibility shim. The earlier queue classified this under `Algebra/` from
  its ring input alone; the complete signature instead contains
  `Opens (PrimeSpectrum R)` and a categorical finite product supplied by
  `Topology/Category/TopCat/Opens/Limits`, so `RingTheory/Spectrum/Prime/` is the first valid
  owner without a forbidden `Algebra -> Topology` edge.
- Generating sections from free epimorphisms:
  `Algebra/Category/ModuleCat/Sheaf/GeneratingSections.lean` owns
  `SheafOfModules.GeneratingSections.ofFreeEpi`, its finite-index instance,
  and the lemma recovering the original epimorphism. The full signatures use
  only a ring sheaf on an arbitrary site. The affine coherent-chart module
  imports this owner directly and now retains only its scheme/open/coherence
  theorem; the declaration names and signatures are preserved without a
  compatibility shim.
- Alternating finranks along long exact sequences: restated on Mathlib's API
  (2026-09-02). `Algebra/Homology/EulerCharacteristic.lean` owns
  `GradedObject.eulerChar_eq_add_of_exact`, the `ℤ`-indexed balance stated on
  Mathlib's `GradedObject.eulerChar` with the signs of `ComplexShape.up ℤ`;
  `Algebra/Exact/Sequence.lean` owns the bounded zig-zag companion
  `Module.sum_neg_one_pow_finrank_eq_zero_of_longExact` beside Mathlib's
  `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`; and
  `LinearAlgebra/FiniteDimensional/Lemmas.lean` owns their shared rank--nullity
  lemma `Function.Exact.finrank_eq_finrank_range_add_finrank_range`. The former
  `LinearAlgebra/AlternatingFinsum.lean` with its parallel `altDim` vocabulary,
  and `LinearAlgebra/AlternatingSum.lean`, whose single-sequence theorem is
  Mathlib's, are retired.
- Geometric realizations live with the geometric object (2026-09-01): the
  seven former `CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves
  moved to
  `AlgebraicGeometry/DerivedCategory/Stability/{BoundedCoherentBaseChange,DerivedPullback,FourierMukaiAction}.lean`,
  `AlgebraicGeometry/Moduli/Semistability/{SchemeProbes,LocusProbes,FiniteType}.lean`,
  and `AlgebraicGeometry/Moduli/HarderNarasimhan/DedekindProblem.lean`, and the
  `IsCompatibleWithTriangulation` instance for `Dᵇ(Coh X)` merged into
  `DerivedCategory/FourierMukai/DerivedTensorCoherence.lean` beside the class
  it registers. The eight instance umbrellas, the `GeometryInstances` layer,
  the subject rank order, and the reverse-edge allowlist are retired;
  `scripts/check_layering.py` now enforces the six policy edges in
  `layers.md`. Declaration names and namespaces are unchanged.
- Homological algebra at Mathlib's paths (2026-09-01):
  `CategoryTheory/Triangulated/DerivedCategory/` and
  `Triangulated/CohomologyObjectProperty.lean` moved to
  `Algebra/Homology/DerivedCategory/`; `Triangulated/BoundedHomotopyCategory.lean`
  to `Algebra/Homology/HomotopyCategory/Bounded.lean`;
  `Triangulated/DGEnhancement/Instances/HomotopyCategory/` to
  `Algebra/Homology/HomotopyCategory/DGEnhancement/`;
  `CategoryTheory/SpectralSequence/` to `Algebra/Homology/SpectralSequence/`;
  and `CategoryTheory/Enriched/DGCategory/` to `Algebra/Homology/DGCategory/`
  (ADR-0010 amendment). The `CategoryTheory/Enriched` umbrella and the
  `DGEnhancement/Instances` umbrella are retired. Declaration names and
  namespaces are unchanged; the declaration sweep routes the moved subtrees
  to the audit lanes that already hold their records.
- Sheaves of modules at Mathlib's path (2026-09-01):
  `CategoryTheory/Sites/Sheaves/Modules/` moved to
  `Algebra/Category/ModuleCat/Sheaf/`, where Mathlib defines `SheafOfModules`.
  `Algebra/Category`, `Algebra/Category/Grp`, and `Algebra/Category/ModuleCat`
  gained the umbrellas the tree never had. Declaration names and namespaces
  are unchanged; the sweep routes the subtree to the audit lane that holds its
  records.
- Site, bicategory, abelian, simplicial, ring-theoretic, and topological
  extensions at Mathlib's paths (2026-09-01): site-level Čech theory moved to
  `CategoryTheory/Sites/SheafCohomology/Cech/` and its topological half
  (compact-open bases, boundedness, the free abelian Yoneda stalk, global
  sections, injective and flasque acyclicity) to `Topology/Sheaves/Cech/`;
  stacks in groupoids to `CategoryTheory/Sites/Descent/StackInGroupoids/`;
  pseudofunctor loci and transport to `CategoryTheory/Bicategory/Functor/Cat/`;
  weak Serre classes to `CategoryTheory/Abelian/SerreClass/Weak.lean`; the
  extra-codegeneracy contraction to `AlgebraicTopology/`; basic-open products
  to `RingTheory/Spectrum/Prime/BasicOpen.lean`; and the opens category to
  `Topology/Category/TopCat/Opens/`. Umbrellas exist at every new level, the
  public root exports the two new subjects, and the sweep routes each moved
  subtree to the audit lane that holds its records. Declaration names and
  namespaces are unchanged.
- Geometry organized by Mathlib's object names (2026-09-01):
  `AlgebraicGeometry/Proj/` moved to `AlgebraicGeometry/ProjectiveSpectrum/`,
  Mathlib's name for the directory whose `Proj` it extends, and
  `AlgebraicGeometry/CoherentSheaf/` to `AlgebraicGeometry/Modules/Coherent/`
  with its `Quasicoherent/` child beside it as `Modules/Quasicoherent/`, since
  both are subcategories of the `X.Modules` that Mathlib defines in
  `AlgebraicGeometry/Modules/Sheaf.lean`. Declaration names and namespaces
  (`AlgebraicGeometry.Proj`, `Scheme.Modules`, `SheafOfModules`) are
  unchanged.
- Stability nested by name (2026-09-01): `CategoryTheory/Triangulated/WeakStabilityCondition/`
  became `CategoryTheory/Triangulated/StabilityCondition/` with weak stability
  as the child `Weak/`, following Mathlib's `MetricSpace/Pseudo/`: the
  directory is named for the canonical concept and the variant by its
  adjective, while the dependency still runs from Bridgeland to weak. The
  strong umbrella imports its weak child, so the former explicit umbrella
  boundary is gone; the layering gate still rejects any import from `Weak/`
  into the Bridgeland theory and still requires `PreStabilityCondition` to
  extend `WeakPreStabilityCondition`. Declaration namespaces are unchanged.
- The `ZLattice` class is retired (2026-09-02): `LinearAlgebra/Lattice/Basic.lean`
  bundled `Module.Finite ℤ` and `Module.Free ℤ` into a class whose name is
  Mathlib's `ZLattice` namespace. The interface is Mathlib's pair of instances;
  `NumericalVarietyData.numericalZLattice` became the instance
  `instFiniteNumericalQuotient`, and freeness of the torsion-free quotient is
  Mathlib's `Module.free_of_finite_type_torsion_free'`.
- The bundled variety types are retired (2026-09-02): `SchemeOverField`,
  `Variety k`, `SmoothProperVariety k`, `ProjectiveVariety k`, `K3Surface`,
  and `EnriquesSurface` were second carriers for objects Mathlib already has.
  A variety is now `X : Scheme` with `[X.Over (Spec (CommRingCat.of k))]`,
  whose structure morphism is `X ↘ Spec (CommRingCat.of k)`, and the
  `Prop` classes `IsVariety k X` (integral, locally of finite type over `k`),
  `IsSmoothProperVariety k X`, `Variety.IsProjective k X`,
  `SmoothProperVariety.IsK3Surface k X C`, and
  `SmoothProperVariety.IsEnriquesSurface k X C` state the properties, as
  `IsProper` does for a morphism. The base field is an `outParam` so that
  `Variety.isLocallyNoetherian`, whose conclusion mentions no `k`, is found
  by instance search. Data that was reached through the bundle takes the
  field explicitly: `FiniteCohomology k X`, `FiniteDimensionalCohomology k X`,
  `LinearCohomology k X`, `SmoothProperVariety.CanonicalSheafData k X n`,
  `NumericalData k X n A N`, `SurfaceChernCharacter k X`,
  `ProjectivePresentation k X`, `EulerRealization k X V`, and the relative
  differentials `Variety.relativeDifferentials k X` with their derivation and
  descent API. Projective space carries `instOverProjectiveSpace`,
  `isVariety_projectiveSpace`, and `isProjective_projectiveSpace` in place of
  `projectiveSpaceVariety`; the point `Spec k` carries
  `isSmoothProperVariety_point`. The `Variety` and `SmoothProperVariety`
  namespaces remain as the homes of the API; they are no longer types.
  Unbundling exposed hypotheses the bundle had hidden: the base-field scalar
  action on coherent cohomology, the relative differentials with their
  descent API, and the twisting sheaf on projective space need only the
  structure morphism; additivity of derived coherent cohomology holds on any
  scheme; the projective-space scalar files no longer assume a finite
  nonempty index, which only the finiteness theorems use as `[Fintype ι]`;
  and the two Euler-additivity exactness lemmas assume
  `IsLocallyNoetherian X`, which is what they use.
- Adjacent placement defects found by the 2026-09-02 review of the restructure
  (landed 2026-09-02). Generic t-structure retract closure moved from
  `Algebra/Homology/DerivedCategory/TStructure.lean` to
  `CategoryTheory/Triangulated/TStructure/Retracts.lean`; `QuasiAbelian.lean`
  moved from `Triangulated/` to `CategoryTheory/Abelian/`;
  `Triangulated/LinearOpposite.lean` split into `CategoryTheory/Linear/Opposite.lean`
  and `Triangulated/Opposite/Linear.lean`; `DerivedCategory/LinearDual.lean` split,
  with the ordinary `ModuleCat` duality at `Algebra/Category/ModuleCat/LinearDual.lean`;
  `Ext/InjectiveResolutionNaturality.lean` split, with
  `CategoryTheory/Localization/SmallShiftedHom.lean` and
  `Algebra/Homology/HomotopyCategory/HomComplexPostcomp.lean`;
  `Triangulated/CompactlyGenerated.lean` split, with the generic compact-object
  vocabulary at `CategoryTheory/Preadditive/CompactObject.lean`; and
  `CategoryTheory/StabilityCharge.lean` moved to
  `Triangulated/StabilityCondition/Weak/Charge.lean`. Declaration names and
  namespaces are unchanged; the old paths are retired in the layering gate; the
  audit sweep routes all of `Algebra/Category/ModuleCat/` to the StabilityCondition
  lane. The four upper-half-plane facts in `Weak/Charge.lean` remain an upstream
  candidate for `Analysis/Complex/UpperHalfPlane/` under the `Complex` namespace,
  deferred by the name-stability rule.
- The global `HasDerivedCategory.standard` registrations are retired
  (2026-09-02). `AlgebraicGeometry/DerivedCategory/Basic.lean` (module sheaves,
  in both spellings, with a priority hack), `Coherent.lean` (`Coh X`), and
  `Algebra/Homology/DerivedCategory/LinearDual.lean` (`ModuleCat k` and its
  opposite) registered Mathlib's standard localization as global instances,
  against Mathlib's own guidance that a chosen localization be introduced
  locally. Every consumer that spells a derived category now declares
  `attribute [local instance] HasDerivedCategory.standard` after
  its preamble, the idiom fifteen files already used; the instance term in every
  signature is literally `HasDerivedCategory.standard _`, so definitions agree
  across files and across the reducibly equal spellings `X.Modules` and
  `SheafOfModules X.ringCatSheaf` without the priority hack. A consumer that
  wants a different localization takes `[HasDerivedCategory C]` as a hypothesis,
  as `SemiorthogonalDecomposition/DerivedField.lean` already does.
- The alternating-finsum vocabulary is retired (2026-09-02) in favour of
  Mathlib's `Algebra/Homology/EulerCharacteristic.lean`: see the owner entry
  above. The Euler form `chiHom` is now `GradedObject.eulerChar` of the shifted
  Hom family by `rfl`, and its additivity on distinguished triangles applies
  `GradedObject.eulerChar_eq_add_of_exact` directly.

## Confirmed next lanes

Every path lane confirmed by the 2026-09-01 audit has landed.

- `CategoryTheory/Triangulated/TStructure/Restriction.lean` carries a
  five-declaration purely categorical `ObjectProperty` block with no
  t-structure in its types: `preimageLift` (with its `Additive`, `CommShift`,
  and `IsTriangulated` instances), `inverseImageLift`, `liftToInverseImage`,
  and the restricted adjunctions `Adjunction.restrictInverseImageLeft` and
  `restrictInverseImageRight`. Its canonical owner is
  `CategoryTheory/ObjectProperty/`, where Mathlib defines `ObjectProperty.lift`,
  `inverseImage`, and `fullyFaithfulι`; move the block there in one pull
  request and leave the t-structure restriction theorems behind (recorded
  2026-09-02, projective-families lane).

No confirmed type-level hazard remains: the `ZLattice` class, the bundled
variety types, and the alternating-finsum vocabulary are all retired above
(2026-09-02).

Take these lanes one per pull request. Remove the old path rather than retaining
an import-only shim, update audits and umbrellas in the same pull request, and
add a focused layering guard preventing the declaration from returning to its
consumer.
