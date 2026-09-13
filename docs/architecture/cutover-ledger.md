# Structural cutover ledger

This ledger records known ownership defects that have been confirmed by the
signature test in `placement.md`. It is a migration queue, not an allowlist:
new code must use the canonical owner immediately, and touching one of these
blocks should normally move it rather than add more declarations beside it.

## Completed roots

- Bounded-derived `K₀` comparison and geometric class-map transport
  (2026-09-12): `DerivedCategory.boundedHeartToAmbient` is the direct
  standard-heart map `K₀Ab(A) →+ K₀(Dᵇ(A))`, and bounded cohomological
  dévissage proves that it is inverse to `boundedEulerClassHom`.  The proof
  handles shifted single objects with the parity formula for `K₀`, lifts the
  truncation triangles into the bounded full subcategory, and uses triangle
  additivity; it does not assume the comparison.  Consequently
  `boundedDerivedClassMap` canonically transports any supplied additive class
  map on `K₀Ab(A)` to `K₀(Dᵇ(A))`.  For coherent sheaves,
  `K3MukaiTilt.derivedMukaiClass` applies this construction to the existing
  numerical-realization Mukai class and proves the former ambient restriction
  obligation automatically.  The canonical tilt constructor therefore no
  longer asks for an arbitrary ambient map or compatibility proof.  It still
  exposes exactly the geometric inputs not proved here: Grothendieck slope
  boundedness (the remaining `MuHNInput` field on a Noetherian scheme), the
  Hilbert/numerical normalization, dimension-zero Mukai-class classification,
  Hodge positivity, and the boundary Mukai decomposition.
- Bounded-derived cohomological Euler classes (2026-09-12):
  `K₀Ab.of_exact` expresses the middle term of an exact pair through its two
  image classes, and `K₀Ab.eulerClass_add_of_exact` telescopes those identities
  over a finitely supported integer-indexed long exact sequence. For every
  abelian category `A`, `DerivedCategory.boundedEulerClassHom` then gives the
  canonical map `K₀(Dᵇ(A)) →+ K₀Ab(A)` by alternating bounded cohomology.
  This file constructs only the cohomological direction; the separate
  comparison entry above supplies the inverse by dévissage rather than
  assuming a Grothendieck-group equivalence.
- Degreewise ambient coherent Ext-finiteness on projective varieties
  (2026-09-12):
  `ProjectivePresentation.module_finite_ambientExt` combines unconditional
  restricted-twist presentations, finite Ext from restricted twists, and the
  long exact Ext sequence to prove `Module.Finite k` for every
  `Ext^n_{X.Modules}(F, G)`. The result deliberately asserts no uniform or
  pairwise degree bound: finite support still requires a genuine regularity or
  finite-global-dimension theorem, and internal Ext in `Coh X` still requires
  `Dqc.CoherentExtComparison X`.
- Closed-immersion counit epimorphism and restricted-twist presentations
  (2026-09-12): `Scheme.Modules.pushforward_faithful_of_isInducing` detects
  equality of module-sheaf morphisms on the canonical target open attached to
  each source open. Closed immersions therefore have faithful pushforward, so
  the general adjunction theorem makes every component of
  `pullbackPushforwardAdjunction` counit epic. The projective-presentation lane
  now gives unconditional finite restricted-negative-twist quotients of
  coherent sheaves. This does not assert the stronger counit isomorphism or
  exactness of closed-immersion pullback; neither is needed for the quotient.
- Scheme-module stalk and pullback comparison (2026-09-12):
  `AlgebraicGeometry/Modules/Pullback/Stalk.lean` now owns the local-ring-valued
  module-stalk functors, their finite-limit and joint-reflection theorems, the
  private module-skyscraper construction, and the canonical presheaf and sheaf
  pullback-to-stalk isomorphisms. These declarations previously lived in
  `DerivedCategory/Families/FlatPullback.lean` despite mentioning neither
  derived categories, families, nor flatness. The families file now contains
  only the flat local-ring calculation and its exact-pullback consequence;
  open-immersion and relative-perfect consumers use the canonical neutral API.
  The transitional comparison records are removed rather than retained as a
  compatibility shim.
- Finite-biproduct calculus in triangulated `K₀` (2026-09-12):
  `Triangulated/GrothendieckGroup/Biproduct.lean` owns the reusable identities
  `[X ⊞ Y] = [X] + [Y]` and `[⨁ i, X i] = ∑ i, [X i]`, together with
  the constant-family `nsmul` specialization.  The binary law is exactly
  Mathlib's distinguished split triangle; the finite law uses Mathlib's
  finite-type induction and biproduct comparison maps.  This is generic
  triangulated `K₀` infrastructure, not a copower- or twist-specific
  formula.  It makes no Euler-characteristic, formality, or scalar-evaluation
  assertion; those remain downstream consumers.
- Finite cohomology presentation and scalar-linear copower transport
  (2026-09-12):
  `Homotopy.FiniteCohomologyPresentation` owns the coefficient-side data of an
  explicit homotopy equivalence to a finite biproduct of single homology
  objects.  Its shifted normal form reuses Mathlib's `singleFunctors.shiftIso`,
  with a degree-`i` single identified as a degree-zero single shifted by `-i`.
  `DGEnhancement.FiniteCohomologyCopower` transports this presentation through
  `linearCopowerFunctor`: generic additivity of `DGFunctor.h0` and `Cdg.toH0`
  lets Mathlib supply finite-biproduct preservation, and
  `SingleFunctors.postcomp` supplies the coherent shifted family.
  `DGCategory.LinearCopowerUnit` proves directly from the representing
  property that the scalar unit copower is `X`, using the strict canonical
  `IsLinearCopowerOf.compareIso`.
  `DGEnhancement.LinearCopowerFiniteFree` owns the generic `H⁰` leaf: a
  supplied finite basis expands a degree-zero copower as a finite biproduct of
  copies of `X`, with arbitrary finite index universe handled by Mathlib's
  categorical biproduct reindexing.  `Module.finBasis` gives the finite-free
  `finrank` specialization.  The finite-presentation consumer composes these
  interfaces into its nested finite-biproduct normal form.  No new direct-sum
  or shift interface is introduced.  This root still assumes the actual
  `HomotopyEquiv`; it proves no automatic formality, quasi-isomorphism
  invariance, Hom-cohomology comparison, Euler/K₀ formula, cone preservation,
  basis independence, or concrete `HasLinearCopowers` instance.
- Supplied-presentation scalar-copower `K₀` class (2026-09-12):
  `DGEnhancement.FiniteCohomologyCopowerK0` owns the numerical leaf
  `FiniteCohomologyPresentation.linearCopowerK₀Of`.  For an explicitly
  supplied finite cohomology presentation whose displayed homology modules
  are finite free, it combines `linearCopowerFinrankIso`, the generic finite
  biproduct law in triangulated `K₀`, and `K₀.of_shift_int` to identify the
  selected scalar-linear copower class with Mathlib's
  `HomologicalComplex.homologyEulerChar` times `[X]`.  The support reduction
  comes only from the supplied presentation; the theorem assumes a nontrivial
  base ring and infers neither a presentation nor formality from bare
  finiteness.  It introduces no
  parallel Euler-characteristic definition and supplies no comparison between
  scalar-linear `LinearEvaluationData` and additive `EvaluationData`.
- Rank-one `K₀` interface and scalar-linear Euler evaluation (2026-09-12):
  `Triangulated/GrothendieckGroup/RankOne` owns the reusable factorization
  `K₀ C →+ ℤ →+ K₀ D` and the objectwise `K₀.IsRankOne` predicate.
  Natural isomorphisms preserve that predicate without exactness; only the
  separate `map_eq_rankOne` theorem assumes the existing hypotheses needed to
  form `K₀.map`.  Both additive `EvaluationData.IsEulerCopower` and the new
  generic-H⁰ scalar-linear specialization reuse this root.  The H⁰
  Hom-cohomology Euler bridge identifies Mathlib's homological Euler
  characteristic with `chiHom` without a boundedness hypothesis.
  `HomotopyCategory/DGEnhancement/LinearEvaluationK0` owns the realization:
  with `HomFiniteBounded`, all linear copowers, and a supplied finite
  cohomology presentation for every `DGLinear.homComplex k E X`, it derives
  the required finite/free homology witnesses and proves the rank-one formula.
  It does not infer presentations or formality, make the evaluation functor
  exact, or compare the additive and scalar-linear universal properties.
- Scalar-linear copower DG functor and homotopy invariance (2026-09-12):
  `DGCategory.LinearCopowerFunctor` packages the universal property as a
  degreewise `homComplexIso`, then uses it to define the homogeneous
  `coefficientMap`.  Differential, identity, and composition compatibility
  assemble the selected objects into the `k`-linear dg functor
  `linearCopowerFunctor k X : Cdg (ModuleCat k) ⟶ C`.  The standard complex
  model's `DGLinear` instance is only a bridge to Mathlib's existing
  pointwise module action and its `δ_smul`/cochain-composition laws.
  Chain homotopies give coboundary differences, and homotopy equivalences give
  isomorphic witnessed copowers in `H⁰ C`.  The selected-object wrapper is
  owned by `HomotopyCategory.DGEnhancement.LinearCopower`, where it is
  transported through the existing `Cdg.h0Functor` seam rather than a new
  quotient construction.  This
  proves neither quasi-isomorphism invariance nor a finite cohomology
  decomposition, Euler formula, cone-preservation theorem, or concrete
  `HasLinearCopowers` instance.
- Scalar-linear evaluation root (2026-09-12):
  `DGCategory.LinearEvaluation` assembles the `IsLinearCopowerOf` family at an
  object `E` into `LinearEvaluationData k E`.  Fixed-source right composition
  is exposed once as `DGLinear.postcompCochain`; the evaluation action is its
  composite with the target universal chain map, followed by the source
  copower's linear representing inverse.  The result is a `k`-linear dg
  functor, a closed evaluation transformation to the identity, and a coherent
  canonical `Z⁰` isomorphism between any two choices which commutes strictly
  with evaluation.  `HasLinearEvaluationData` stores only existence and is
  supplied at low priority by `HasLinearCopowers`.
  This is parallel to, not a refinement of, additive `EvaluationData`: there
  is no adapter between their incompatible universal properties.  The
  coefficient-complex homotopy result is owned by the copower DG-functor root;
  this evaluation root itself asserts no cone, exactness, Euler/K₀,
  finite-presentation, or concrete existence result.
- Scalar-linear dg Hom and copower root (2026-09-12):
  `DGCategory.Linear` repackages the existing Hom-complex of a `DGLinear k C`
  as `DGLinear.homComplex`, a `ModuleCat k`-valued cochain complex.
  `DGCategory.LinearCopower` defines `IsLinearCopowerOf` by a bundled linear
  equivalence with Mathlib's existing `HomComplex.Cochain`.  Its
  lift, closed canonical comparison, strict comparison laws, and
  `HasLinearCopower(s)` choice-free existence capabilities follow the same
  universal-property pattern as the additive root.  There is deliberately no
  projection to `IsCopowerOf`: that interface represents all additive
  cochains, so forgetting scalar structure would strengthen rather than
  preserve the linear contract.  Scalar-linear evaluation data and the
  coefficient DG-functor/homotopy root now consume this universal property
  separately; no Euler-class or finite-presentation result is asserted here.
- Scalar-linear dg Hom-cohomology comparison (2026-09-12):
  `DGCategory.Pretriangulated.ShiftIso` now packages the degreewise
  bijectivity in `IsShiftBy` as an actual isomorphism of Hom-complexes, and
  `LinearShiftIso` supplies its `ModuleCat k` refinement through the existing
  `DGLinear.postcompCochain` and Mathlib cocycle-to-shift equivalence.
  `DGCategory.LinearH0Homology` owns the intrinsic degree-zero quotient
  comparison, and `Pretriangulated.LinearShiftHomology` combines it with
  Mathlib's shifted-homology isomorphism for an explicit `IsShiftBy` witness.
  `DGEnhancement.H0.HomCohomology` only selects the existing `HasShift` object,
  giving
  `Hⁿ(DGLinear.homComplex k X Y) ≃ₗ[k] Hom_{H⁰ C}(X, Y⟦n⟧)`, both for an
  explicit shift witness and for the selected `HasShift` object.  Public
  representative laws identify the maps with `H0.homMk` and right composition
  by the shift element.  The `+n` target convention follows from the `-n`
  shift of Hom-complexes.  This is a pointwise linear comparison only: no
  naturality package, finite-dimensional transfer, formality, Euler
  characteristic, `K₀`, or sphericality statement is inferred.
- Object-twist `K₀` action and Euler-realization boundary (2026-09-12):
  `DGEnhancement.H0.NaturalTransformationConeK0` owns the reusable theorem
  that a functorial cone acts on `K₀` by target endpoint minus source
  endpoint, both on generators and, under endpoint cone preservation, as a
  homomorphism.  The object twist specializes this to identity minus its
  evaluation functor.  `DGEnhancement.H0.ObjectTwistK0` owns the explicit,
  choice-invariant `EvaluationData.IsEulerCopower` capability saying exactly
  when that evaluation class is the Euler multiple of `[E]`.  Together with
  chosen-cone preservation, the spherical consumer proves that the induced
  object-twist map equals the existing numerical `twistK₀`.
  This capability is supplied realization input, not a consequence of the
  present additive `IsCopowerOf`, which represents ℤ-additive rather than
  `k`-linear cochains.  The separate scalar-linear copower and evaluation
  roots now exist, coefficient-complex homotopy invariance is closed, and
  supplied finite cohomology presentations now transport to shifted finite
  biproducts and finite-free homology expands these into `finrank` copies.
  The scalar-linear Hom-cohomology comparison is now closed, generic
  triangulated `K₀` computes finite biproduct classes, and the supplied
  finite-presentation scalar-copower class is Mathlib's homological Euler
  characteristic times the object class.  The shared `K₀.IsRankOne`
  interface and its direct linear-evaluation consumer are now closed as well.
  Any passage to additive `EvaluationData` remains explicit, and automatic
  formality remains a separate later lane.
- `K₀` actions of enhanced adjunction cones (2026-09-12):
  `SphericalTwist.EnhancedFunctorK0` derives the four generator identities
  directly from the distinguished adjunction triangles and lifts them, under
  the existing endpoint chosen-cone hypotheses, to equalities of `K₀`
  homomorphisms.  Each conventional twist or cotwist acts as the identity
  minus its corresponding adjunction composite.  This does not identify an
  object-twist evaluation composite with an Euler multiple of the object;
  that copower computation remains the next seam toward `twistK₀`.
- Exact twist and cotwist equivalences on `H⁰` (2026-09-12):
  `twistH0EquivalenceIsTriangulated` and
  `cotwistH0EquivalenceIsTriangulated` combine the separately proved ordinary
  equivalences and exact forward functors using Mathlib's canonical
  `Equivalence.CommShift` and `Equivalence.IsTriangulated` interfaces.  The
  compatible shift structure and triangulatedness of each inverse are derived,
  not assumed or duplicated in a repository-owned record.  This packaging
  still proves no `K₀` action formula, cone relation, or sphericality.
- Sign-correct exactness of shifted dg functors (2026-09-12):
  `DGFunctor.shiftedFunctorH0CommShift` composes the canonical comparison on
  `H⁰(F)` with the signed integral-shift package and transports it across
  `shiftedFunctorH0Iso`; `shiftedFunctorH0IsTriangulated` transports exactness
  by the same route.  Both are explicit interfaces, not global instances.
  The underlying `H⁰` capability transport now also keeps independent source
  and target object universes, matching the shifted-functor comparison API.
  The conventional `[-1]` dual twist and cotwist now reuse this root, so their
  exactness asks only for the same endpoint chosen-cone preservation as their
  unshifted cones.  This proves no dg quasi-equivalence, cone relation, or
  sphericality.
- Sign-correct exactness of integral shift functors (2026-09-12):
  `Triangulated.ShiftFunctor` now owns the explicit Koszul-signed `CommShift`
  on `[n]`, its comparison with `Triangle.shiftFunctor`, and
  triangulatedness for every `n : ℤ`.  The unsigned `CommShift` remains
  available as explicit data for object-only uses, but neither package is a
  global instance.  The stability-action `[±2]` implementation is reduced to
  compatibility wrappers over this root.  This closes the odd-shift sign
  seam; composing it with an already exact functor is a downstream operation,
  not another shift-functor abstraction.
- Exactness of the four stored dg adjunction cones (2026-09-12):
  `EnhancedAdjunctionCones` now exposes shift preservation, chosen-cone
  preservation, the induced `H⁰` `CommShift`, and triangulatedness for the
  twist, dual cotwist, and the unshifted cones underlying the dual twist and
  cotwist.  Every result reuses the generic adjunction-cone 3-by-3 theorem and
  asks only for preservation of chosen cones by the relevant adjoint pair.
  Exactness for the two conventional `[-1]` shifted functors is obtained in
  the separate shifted-dg-functor root above.  No cone relation, equivalence,
  or sphericality follows.
- Conventional shifted dg twists on `H⁰` (2026-09-12):
  `DGFunctor.shiftedFunctor_h0_eq` and `shiftedFunctorH0Iso` package the
  objectwise and morphism computations as a functor-level comparison
  `H⁰(F[n]) ≅ H⁰(F) ⋙ [n]`.  Equivalence of `H⁰ F` therefore transports to
  every shifted dg functor without asserting a dg quasi-equivalence or
  exactness.  `EnhancedAdjunctionCones` now names the conventional
  `dualTwistFunctor` and `cotwistFunctor`, and `cotwistH0Equivalence` applies
  that bridge to the recorded unshifted cotwist condition.  This introduces
  no second shift structure and proves no relation among the four adjunction
  cones or sphericality.
- Generic twist kernels and left-adjunction Fourier--Mukai dual cotwists
  (2026-09-12): `CounitKernelConeData.twistKernel` now names the ordinary image
  of the selected enhanced cone, with its definitional transform isomorphism
  and the correspondingly narrow `IsKernelFunctor` conclusion.
  `DualCotwistKernelData` and its enhanced form then swap the correspondences
  through `LeftAdjointKernelData.toRightAdjointKernelData` and reuse that
  counit/twist construction for the left-adjunction counit.  The semantic API
  names `dualCotwist`, presents it by `dualCotwistKernel`, and exposes the
  source-natural triangle
  `Φ_P ⋙ Φ_Q ⟶ 𝟭 X ⟶ dualCotwist ⟶ (Φ_P ⋙ Φ_Q)⟦1⟧`, pointwise
  distinguished under the existing exactness hypotheses.  No new cone or
  normalization is introduced, and no exactness, invertibility, canonicity,
  dual-kernel identity, or sphericality is asserted.
- Left-adjunction Fourier--Mukai dual twists (2026-09-12):
  `DualTwistKernelData` and its enhanced cone form read
  `LeftAdjointKernelData.toRightAdjointKernelData` with the correspondences
  swapped, so the left-adjunction unit reuses the generic unit-kernel,
  normalization, inverse-rotation, and shifted-kernel machinery.  The semantic
  API names the resulting functor `dualTwist`, presents it by
  `dualTwistKernel`, and exposes the target-natural triangle
  `dualTwist ⟶ 𝟭 Y ⟶ Φ_Q ⋙ Φ_P ⟶ dualTwist⟦1⟧`, pointwise
  distinguished under the existing exactness hypotheses.  This is not a new
  adjunction, cone choice, or normalization construction, and it asserts no
  exactness, invertibility, dual-kernel identity, or sphericality.
- Shifted Fourier--Mukai cone kernels (2026-09-12):
  `KernelConeNormalizationData` names the ordinary kernel represented by its
  selected enhanced cone and, for every integer shift, the kernel obtained by
  shifting that cone in the enhancement's homotopy category.  The enhancement
  comparison and the kernel family's existing Mathlib `CommShift` component
  give the reusable isomorphism from its transform to the pointwise-shifted
  cone transform.  `AdjunctionUnitKernelConeData.cotwistKernel` specializes
  this at `-1`, so the conventional cotwist is now explicitly a kernel functor.
  No second shift structure is installed, and the statement does not make the
  selected kernel canonical, exact, invertible, or spherical.
- Fourier--Mukai cotwist inverse rotation (2026-09-12):
  `AdjunctionUnitKernelConeData.cotwist` is the pointwise functor-category
  `[-1]` shift of the selected unshifted cone transform, and
  `cotwistTriangleInSource` reuses Mathlib's `invRotate` to produce the
  source-natural family
  `cotwist ⟶ 𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧`.  Its three projection functors
  are identified strictly, its second map is literally the adjunction unit as
  a natural transformation, and every value is distinguished.  The result is
  choice-dependent and ordinary-categorical.  Its shifted-kernel presentation
  is now constructed downstream; exactness, invertibility, comparison with a
  dg adjunction cone, and sphericality remain separate seams.
- Right-adjunction unit kernels and literal unit triangles (2026-09-12):
  `FourierMukai.AdjunctionUnitKernelData` and its enhanced cone form are
  definitional specializations of the generic kernel-transformation roots,
  providing their second consumer without a parallel record or normalization
  proof.  They package the supplied kernel arrow `O_Δ ⟶ P ⋆ Q`, its exact
  transform equation, and the source-natural triangle
  `𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟭 X)⟦1⟧`, pointwise distinguished under
  the existing exactness hypotheses.  The third functor is the unshifted
  cotwist-cone candidate; its `[-1]` shift and inverse-rotated triangle are now
  constructed downstream, while exactness, autoequivalence, and sphericality
  remain separate seams.
- Generic enhanced kernel-transformation cones (2026-09-12):
  `Enhancement.liftedCocycle` and `Enhancement.conePresentation` own the
  noncanonical lift of an ordinary morphism to a closed representative and dg
  cone.  `FourierMukai.KernelTransformationData` packages a kernel morphism
  whose transform is a named natural transformation in supplied endpoint
  presentations; `KernelTransformationConeData` adds the enhanced choices and
  forgets back one way.  Its `normalizationData` feeds the reusable
  `Correspondence.KernelConeNormalizationData`, which owns transport to a
  source-natural triangle with literal endpoints and first map.  The counit
  kernel records now delegate to these generic owners without changing their
  public contracts, with inverse adapters and simp round trips proving the two
  presentations equivalent.  Fullness remains only a sufficient constructor,
  choices remain noncanonical, and the normalized result is only pointwise
  distinguished: no exactness, functor-category distinguishedness,
  autoequivalence, or sphericality is inferred.
- Literal Fourier--Mukai counit triangles (2026-09-12):
  `CounitKernelConeData.counitTriangleInSource` transports the raw transform
  triangle of an enhanced counit-kernel cone to a source-natural triangle with
  vertices `Φ_Q ⋙ Φ_P`, `𝟭 Y`, and the kernel-presented twist, and with
  first map literally the supplied adjunction counit.  The construction reuses
  Mathlib's `Triangle.functorMk` and `Triangle.functorIsoMk`; the natural
  comparison exposes all three components, and exact kernel evaluation makes
  every value of the normalized family distinguished.  This is pointwise
  distinguishedness only: it does not assert a distinguished triangle in the
  functor category, exactness or autoequivalence of the twist, or independence
  from the selected enhancement representative and cone.
- Ordinary counit-kernel data and enhanced cone selection (2026-09-12):
  `FourierMukai.CounitKernelData` separates the geometric kernel morphism and
  its exact transform equation from any enhancement or cone choice.
  `CategoryTheory.Z0.toH0_full` records the reusable quotient-surjectivity fact,
  so `CounitKernelData.toConeData` uses Mathlib's `Functor.preimage` to choose a
  closed representative and pretriangulated cone in any enhancement.  The
  forgetful map recovers the ordinary datum, but no selected representative or
  cone is claimed canonical.  `CounitKernelData.ofFull` is only a constructor
  under the explicit strong hypothesis `E.kernelTransform.Full`; the geometric
  counit-trace realization remains open.
- H⁰ cone-triangle comparison across strict isomorphism squares (2026-09-12):
  `Algebra/Homology/DGCategory/FunctorCategoryH0.lean` owns the canonical
  `DGFunctor.h0Iso`, including identity and composition coherence.
  `DGEnhancement/H0/NaturalTransformationCone.lean` upgrades the existing
  strict-square natural transformation to `ConeData.triangleIsoOfStrictSquare`
  when both endpoint maps are isomorphisms. Its third component is the `H⁰`
  image of the canonical dg cone-functor comparison, not a second comparison
  construction. `DGEnhancement/H0/ObjectTwist.lean` specializes this interface
  to `TwistConeData.twistTriangleIsoOfEvaluation` across both evaluation and
  cone choices, with component, identity, and composition laws, while retaining
  the original `twistTriangleIso` definition for same-evaluation callers. This is
  choice-independence of the full triangle functor; it does not assert that the
  twist itself is an autoequivalence or that the object is spherical.
- DG cone comparison and preservation transport (2026-09-12):
  `Algebra/Homology/DGCategory/Pretriangulated/Functor.lean` proves that
  `DGFunctor.PreservesChosenCones` transports across an isomorphism in
  `Z⁰ (DGFunctor C D)`.  Consequently the exactness hypothesis for an object
  twist is independent of the chosen evaluation data once the evaluation
  functors are compared.  `Pretriangulated/Lift.lean` owns the reusable
  `IsConeOf.isoOfStrictSquare`: endpoint isomorphisms in a strictly commuting
  square lift to an isomorphism between arbitrary chosen cones.
  `Pretriangulated/NaturalTransformationCone.lean` specializes it to cone dg
  functors, and `Pretriangulated/ObjectTwist.lean` gives the resulting
  `TwistConeData.compareIso`, strict compatibility with `id ⟶ T_E`, and strict
  identity/composition coherence.  This identifies the twist dg functor
  independently of both evaluation and cone choices; it does not assert
  autoequivalence or sphericality.
- DG copower and evaluation-data existence packaging (2026-09-12):
  `Algebra/Homology/DGCategory/Copower.lean` owns the Mathlib-style
  `HasCopower` and `HasCopowers` mere-existence capabilities, their
  noncomputable `copowerData` selector returning a `CopowerData` witness, and
  the narrower `HasEvaluationData E` capability consumed by object twists. It
  also proves
  that canonical copower comparisons are closed and compose strictly, then
  assembles these into `EvaluationData.compareIso` in
  `Z⁰ (DGFunctor C C)` with strict compatibility with evaluation. No
  concrete dg category is asserted to have all copowers, and no cone-
  preservation claim is derived from the mapping-out universal property.
- Exact functor-family shift coherence (2026-09-12):
  `CategoryTheory/Triangulated/ExactFunctorFamily.lean` now makes
  `Functor.ExactFamily F` extend Mathlib's `F.CommShift ℤ` for the pointwise
  shift on the target functor category, and adds only pointwise
  triangulatedness. The parallel `FamilyCommShift` record and its manually
  stored evaluation naturality are removed. The generic extensionality
  theorem for `CommShift` lives at the mirrored Mathlib definition site in
  `CategoryTheory/Shift/CommShift.lean`; the explicit, non-instance adapters
  from `CommShift₂` and their evaluation-agreement theorems live in
  `CategoryTheory/Shift/FunctorCategory.lean`. Thus `ExactBifunctor` retains
  Mathlib's two-variable Koszul contract while its two family projections use
  the canonical one-variable interface, with complete shift-data agreement
  rather than an isolated comparison at shift one.
- Bounded dévissage for the derived functor of an exact functor
  (2026-09-10, #1069/#1070/#1071):
  `Algebra/Homology/DerivedCategory/CohomologyObjectProperty/Bounded.lean` owns
  `DerivedCategory.bounded_induction` and the truncation stability of
  `cohomologyIn`; `Algebra/Homology/DerivedCategory/ExactFunctor/Bounded.lean`
  owns `Functor.mapDerivedCategory_map_bijective_of_bounded` and
  `Functor.exists_bounded_iso_mapDerivedCategory_obj`. For an exact
  `F : A ⥤ B` between abelian categories that is bijective on every `Ext`
  group, the derived functor is fully faithful on bounded objects and hits
  every bounded object whose cohomology lies in the essential image of `F`;
  that is `Dᵇ(A) ≌ Dᵇ_{F(A)}(B)`, stated in Mathlib's namespace with no
  geometry, and it is an upstream candidate. The one geometric consumer,
  `AlgebraicGeometry/DerivedCategory/Dqc/Identification.lean`, reduces
  `BoundedCoherentDqcIdentification X` on a locally noetherian scheme to the
  single proposition `CoherentExtComparison X`: `Coh.ι X` is bijective on
  `Ext^n(F, G)` for coherent `F`, `G`. The `comparison` field is `Iso.refl _`.
  Three decisions are recorded here so the sub-issues do not reopen them.
  1. *The #1069 formulation fork is settled as: neither form is on the path.*
     The identification as typed lands in `D(X.Modules)`, not in a derived
     category of quasi-coherent sheaves, and `Dqc.lean` pins the functor to
     `mapDerivedCategory (Coh.ι X)`. Once full faithfulness is known,
     essential surjectivity is the formal cone argument above, so the
     dévissage that classically consumes coherent subsheaves (subobject form,
     Stacks 01PG) is not consumed, and the Ind form is not either. The
     scheme-level approximation statement becomes relevant only for a route
     through an abelian category of quasi-coherent sheaves, which the
     repository does not have; it stays unwritten until such a route exists.
  2. *The #1070 route taken is the general root, not the special case.* The
     route not taken, a direct proof for `Coh ⊂ QCoh`, would not have reached
     the stated target anyway: the surjection-lifting hypothesis of Stacks
     0FCL fails for `Coh X ⊆ X.Modules`. On `X = 𝔸¹`, the module sheaf
     `F := ⨁_{U ⊊ X open} j_{U!}𝒪_U` surjects onto `𝒪_X`, but `Γ(X, F) = 0`
     because a nonzero section of `𝒪_U` on a proper open of an integral scheme
     has support `U`, which is not closed; so `Hom(M~, F) = Hom(M, Γ(X, F)) = 0`
     for every quasi-coherent `M~`, and no coherent sheaf maps onto `𝒪_X`
     through `F`. The Ext comparison is therefore genuine geometric content.
  3. *What supplies `CoherentExtComparison X` remains open, and the affine
     case is not a shortcut.* The classical proofs pass through
     `D(QCoh X) ≌ D_qc(X)` (Stacks 08DB, the coherator) or through
     quasi-coherent injectives being injective in `X.Modules` (Hartshorne,
     *Residues and Duality* II.7.18); neither is available at this Mathlib
     pin. Mathlib's own sufficient conditions,
     `Functor.mapExt_bijective_of_preservesProjectiveObjects` and
     `…_of_preservesInjectiveObjects`, do not apply to `Coh X`: it has neither
     enough projectives nor enough injectives. For `X = Spec R` with `R`
     noetherian, scoping on 2026-09-10 found that a finite-free-resolution
     argument needs `Ext^i_{X.Modules}(𝒪_X, N~) = 0` for `i > 0`, and the
     affine vanishing in `Cohomology/Derived/AffineVanishing.lean` is stated
     for `Sheaf.H`, the `Ext` of *abelian* sheaves out of the constant sheaf.
     Bridging the two needs either injective module sheaves to be flasque
     plus flasque abelian sheaves to be `Sheaf.H`-acyclic (the Čech
     comparison in `Sites/SheafCohomology/Cech/Comparison.lean` gives
     acyclicity only from Čech exactness), or `tilde` of an injective module
     to be an injective module sheaf (Hartshorne III.3.4, which needs
     Artin--Rees, absent from Mathlib). `tilde` is also not yet known to be
     exact in the tree. Each of these is its own lane; the first was taken, see 4.
  4. *Affine noetherian schemes satisfy `CoherentExtComparison`* (2026-09-10,
     same lane). `AlgebraicGeometry/DerivedCategory/Dqc/AffineIdentification.lean`
     proves `coherentExtComparison_spec` for `Spec R`, `R` noetherian, by
     `Functor.bijective_mapExtAddHom_of_generators`
     (`Algebra/Homology/DerivedCategory/Ext/AcyclicGenerators.lean`: dimension
     shifting in the first variable along a class of generators acyclic on both
     sides, the mirror of `extComparisonAddEquiv` in `Ext/AcyclicComparison.lean`)
     with generators `𝒪^k` (`Modules/Coherent/Affine/Free.lean`): projective in
     `Coh (Spec R)` through `Coh.affineEquivalence`, and acyclic in `X.Modules`
     because `Ext_{X.Modules}(𝒪_X, G) ≅ H(G)` vanishes by affine vanishing. That
     bridge is `SheafOfModules.extUnitAddEquivH` in
     `Algebra/Category/ModuleCat/Sheaf/Cohomology.lean`, stated for sheaves of
     modules on a site with a terminal object under an acyclicity hypothesis on
     injectives, discharged on a space by flasqueness
     (`Topology/Sheaves/Flasque.lean`, `Topology/Sheaves/ModulesCohomology.lean`)
     and reassembled for the `X.Modules` wrapper in
     `AlgebraicGeometry/Cohomology/Derived/UnitExt.lean`. The general-scheme
     comparison is still open; the affine proof uses that `𝒪^k` present every
     coherent sheaf, which fails off the affine case, so it is not a shortcut.
- Divisorial charge block (2026-09-09):
  `CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/` owns the
  central-charge arithmetic that `Walls/Numerical/` performs in three
  compressed real coordinates, carried out instead on an uncompressed real
  divisor space. `Coordinates.lean` owns `ChargeCoordinates` and the charge
  polynomial, `Charge.lean` owns `DivisorSpace`, `ChernCharacter`,
  `StabilityParameters` and the intrinsic charge, `Slice.lean` owns
  `fullChargeFamily` and `OrthogonalSlice`, `Discriminant.lean` owns the
  Macri--Schmidt quadratic forms and the `DivisorSpace.HodgeIndex` certificate,
  and `Circle.lean` owns the identification of a fixed-`u` slice with the
  `(s,t)` model. None of the five needs a scheme, a sheaf, or a numerical
  intersection ring. The precedent for the placement is
  `Walls/Numerical/Basic.lean`, which is the same kind of pure arithmetic, and
  `Walls/Spherical/Basic.lean`, which already consumes `LinearAlgebra/` from
  this subtree rather than living in it.

  The geometric adapters stay under `AlgebraicGeometry/Numerical/Stability/`:
  `SurfaceChargeNumerical.lean`, `DivisorialChargeNumerical.lean`,
  `DivisorialChargeScalarExtension.lean`, `DivisorialWallTransport.lean`, and
  the numerical-realization halves of `DivisorialDiscriminant.lean` and
  `DivisorialWallCircle.lean`. The old paths are removed rather than shimmed.
  `SurfaceChargeNumerical.lean` declares its adapters into
  `Wall.Divisorial.ChargeCoordinates` so dot notation keeps working on the
  coordinates they produce, which the placement rule permits; its module is
  still under `AlgebraicGeometry/`, so its records stay in the
  algebraic-geometry audit lane, while the 177 moved declarations are audited
  in `scripts/StabilityConditionAudit/Divisorial.lean`. Rule 8 of
  `scripts/check_layering.py` pins the six structures to the Walls subtree and
  fails if a geometric module declares them again.

  **The candidate entry for this lane overstated its payoff.** It said the move
  would let `Wall.stChargeFamily` be defined as a reindexing of
  `ChernCharacter.fullChargeFamily`, leaving one formula owner. That is not
  what the move buys. `reZ` and `imZ` in `Walls/Numerical/Basic.lean` remain
  the definition the circle, line, disjointness and nesting theorems are stated
  against, and redefining them would rewrite that whole development. The two
  presentations stay related by the proved bridges
  `ChargeCoordinates.stCharge_toNumClass` and
  `OrthogonalSlice.chargeFamily_reindex_ofST`. What the move buys is the
  placement itself, and that a future threefold or BMT charge family, or the
  spherical wall lane, can now consume the divisorial layer without importing
  geometry.

- Mukai stability-condition specialization (2026-09-08):
  `CategoryTheory/Triangulated/StabilityCondition/Mukai/` is the sibling
  consumer of generic weak stability and tilting. `Charge.lean` owns the
  categorical Mukai class map and its additive charge, `Slope.lean` owns weak
  slope compatibility, `NumericalCases.lean` owns the four numerical
  half-plane adapters, `Ambient.lean` owns restriction from `K₀ C` to a heart,
  and `Tilting.lean` owns the HN-tilt consumers. The generic
  `Weak/Foundation/StabilityFunction` and `Weak/Tilting/TorsionPair` umbrellas
  no longer import this specialization. At the lower layer,
  `LinearAlgebra/Lattice/Mukai/CentralCharge.lean` now exposes
  `Mukai.expChargeHom`, so heart and ambient charges compose additive
  homomorphisms instead of reproving additivity. The canonical
  numerical lemmas are `Mukai.expCharge_zero`, `expCharge_add`, and
  `expCharge_neg`; their historical `CategoryTheory.Triangulated` names remain
  stable as aliases in `Mukai/Charge.lean`. `GeometricInput.lean` now isolates
  the two remaining geometric obligations as independent propositions:
  classification of rank-and-degree-zero torsion classes and a factorwise
  boundary Mukai decomposition. The boundary contract
  `HasBoundaryMukaiDecompositionWith` is parameterized by a predicate on the
  factors; the exact-Hodge-margin contract and the uniform `realForm ≥ -δ`
  contract are its abbreviations, the historical K3 contract is only `δ = 1`,
  and the theorems turning each predicate into `Re Z > 0` live in
  `Tilting.lean` rather than in the contract.
  `Assembly.lean` carries the same hierarchy through
  `tiltStabilityFunctionOfMargin`, `tiltStabilityFunctionOfLowerBound`, and the
  legacy `tiltStabilityFunction`. Todd normalization remains upstream in the
  additive class map, so this categorical construction has no surface-type
  flag. Its extension argument is not Mukai-specific: the reusable constructor
  lives at
  `Weak/Tilting/TorsionPair/HnTiltStabilityFunction.lean` and consumes any
  additive ambient charge positive on nonzero torsion and shifted-free
  generators.
- Left orthogonals are closed under colimits (2026-09-04):
  `CategoryTheory/ObjectProperty/Orthogonal.lean` owns
  `instIsClosedUnderColimitsOfShapeLeftOrthogonal`, beside Mathlib's own
  `Mathlib/CategoryTheory/ObjectProperty/Orthogonal.lean`. It is the one
  hypothesis of `ObjectProperty.coprodClosure_le` that neither Mathlib file
  supplied: `IsClosedUnderIsomorphisms` and `ContainsZero` come from
  `ObjectProperty/Orthogonal.lean` and `IsTriangulatedClosed₂` from
  `Triangulated/Orthogonal.lean`. `CompactlyGenerated/Coaisle.lean` and
  `CompactlyGenerated/IndExtension.lean` each hand-rolled the same induction
  over `coprodClosure` with verbatim identical `of_iso`, `of_coproduct`, and
  `of_extension` branches; both now apply `coprodClosure_le` and prove only
  their own generator case, which is 42 lines deleted for 29 added. The
  instance is stated for an arbitrary colimit shape, not just `Discrete ι`,
  because `IsColimit.hom_ext` is the entire proof; no dual for
  `rightOrthogonal` under limits was added, as no consumer needs one.
- Restricting a functor to the subcategories an `ObjectProperty` cuts out
  (2026-09-04): `CategoryTheory/ObjectProperty/Lift.lean` owns
  `liftOfLE` with its `Additive`, `CommShift ℤ`, and `IsTriangulated`
  instances, `preimageLift` with the same three, `inverseImageLift`,
  `liftToInverseImage`, and `Adjunction.restrictInverseImageLeft` and
  `restrictInverseImageRight`. Mathlib defines `lift`, `ι`, `ιOfLE`,
  `liftCompιIso`, and `fullyFaithfulι` in
  `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`, so the file
  mirrors that directory; it is named `Lift.lean` and not `FullSubcategory.lean`
  because the latter is one of the two paths `check_source_independence.py`
  keeps retired. The block needs Mathlib alone and imports nothing from
  `DerivedAlgGeo`, which is what makes it generic rather than t-structure
  theory. `CategoryTheory/Triangulated/TStructure/Restriction.lean` keeps
  Steps 2--4 of Theorem A.17 and now imports the root; `Polishchuk.lean`,
  `Phase/Transfer/Inducing.lean`, and `Phase/Transfer/BaseChange.lean` import
  it directly rather than through the t-structure file, and no compatibility
  shim was left behind. The twelve `#print axioms` entries moved from
  `StabilityConditionAudit/TStructureCore.lean` to the new
  `StabilityConditionAudit/ObjectPropertyLift.lean`. Rule 7 of
  `scripts/check_layering.py` keeps the block at that path: the root must
  import no `DerivedAlgGeo` module, must declare all six, and no other module
  may redeclare any of them.
- Orthogonal exceptional blocks and residual projections:
  `CategoryTheory/Triangulated/SemiorthogonalDecomposition/Blocks.lean`
  owns positive-length mutually orthogonal exceptional blocks, their
  triangulated spans, decomposition type, and residual right orthogonal;
  `Projection.lean` owns a chosen right adjoint to a full-subcategory
  inclusion and its universal Hom equivalence; `Mutation.lean` constructs the
  objectwise counit triangle and proves the generic projection-chain theorem.
  Ext profiles, their bidirectional transport, and classification-induced
  candidate matching remain generic in `SerreFunctor/`; adjacent Ext shift
  rigidity and bidirectional ordered block-length comparison live in
  `SemiorthogonalDecomposition/AdjacentExt.lean`.  The one-step criterion and
  result interface live in `FourierMukai/ExceptionalExtension.lean`, while
  `ExceptionalInduction.lean` owns dependent finite extension and derives
  ambient generation from right admissibility.
  `AlgebraicGeometry/Surface/Enriques/PaperBlocks.lean` and
  `PaperExtension.lean`, `PaperMatching.lean`, and `PaperTorelli.lean` are
  geometric consumers: they identify the block members with the ten selected
  line bundles, record the numerical `(-2)`-chains, and specialize projection,
  classification matching, shift rigidity, and ambient kernel extension.
  `Divisors/EffectiveLineBundle.lean` and
  `DerivedCategory/DivisorSequence.lean` now construct the line-bundle-twisted
  divisor triangles; `PaperExtension.lean` transports them to the chosen block
  representatives and derives the projection-chain maps. Curve-quotient
  residual orthogonality remains supplied geometric data.
- Functorial dg cones and kernel-variable transforms:
  `Algebra/Homology/DGCategory/Pretriangulated/ConeCategory.lean` owns the
  category of chosen dg cones and homotopy-coherent cone morphisms;
  `DGEnhancement/H0/ConeFunctor.lean` maps it functorially into distinguished
  `H⁰` triangles.  `FourierMukai/Basic.lean` owns the functor from kernels to
  transforms and its objectwise evaluation, while `FourierMukai/KernelCone.lean`
  maps dg cones of an enhanced kernel category to pointwise transform
  triangles and packages an exact kernel evaluation as a functor valued in
  distinguished triangles.  The kernel category enters through an
  `Enhancement`, never as an `H⁰` on the nose; the cone lift has one owner
  (`homogeneousLift`, with `lift` and `HomotopySquare` its degree-zero case);
  and cone morphisms carry the shift-free `fst` square, so the cone category
  needs no pretriangulated instance.  The enhancement of the geometric kernel
  category with an exact comparison, the paper's actual enhanced kernel
  morphism, and the exactness instance for its evaluation remain realization
  tasks; the generic cone itself is no longer a supplied paper-layer seam.
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
  the coherent pullback contract; the perfect lift is in
  `Families/PerfectPullback.lean` and the pullback identity/composition laws in
  `Families/CoherentPullbackCoherence.lean`.
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

Every path lane confirmed by the 2026-09-01 audit has landed, and so have
both lanes recorded after it: the `ObjectProperty` lift block (2026-09-02)
and the left-orthogonal colimit closure (2026-09-03). Both are entries under
"Completed roots" above.

The divisorial charge block recorded here as a candidate on 2026-09-08 landed
on 2026-09-09 and is now an entry under "Completed roots" above; the entry
also records where that candidate's stated payoff was wrong.

When a lane is added here, take it one per pull request. Remove the old path rather than retaining
an import-only shim, update audits and umbrellas in the same pull request, and
add a focused layering guard preventing the declaration from returning to its
consumer.
