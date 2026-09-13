# Canonical roots and specialization trees

This document is the repository contract for reusable abstractions.  The
dependency contract in `layers.md` decides which imports are forbidden
between subjects.  This document decides the finer question: when
two constructions share mathematical structure, where does that structure
live and how do the specializations relate to it?

## The rule

Every reusable concept has one canonical root in the lowest natural owner.
Specialized geometry supplies instances, refinements, subobjects, quotients,
or equivalences at the leaves.  A leaf must not copy the carrier or fields of
its root.

In Lean, "inheritance" means the narrowest of the following that expresses the
mathematics:

1. reuse an existing typeclass or structure directly;
2. add a small capability typeclass whose parent is already an instance;
3. use `extends` when there is a canonical forgetful projection;
4. use an `abbrev` for a genuine specialization;
5. use a proved equivalence or agreement theorem for two independently useful
   presentations.

It does **not** mean putting a theorem, algebraicity claim, preservation result,
or other unfinished conclusion into a structure field.  It also does not mean
forcing unlike formulas into one record merely because their carriers look
similar.

## Canonical spine

This is the ownership target. Existing reverse edges are tracked defects to
burn down, not exceptions that authorize more leaf-to-root imports.

```text
Bicategory                              Mathlib higher-categorical root
├─ Adjunction of 1-morphisms
│  ├─ adjoint equivalences and mates
│  └─ Cat specialization ≃ ordinary functor adjunction
└─ Pseudofunctor
   ├─ equivalence transport of Cat presentations
   └─ fiberwise object properties / full subpseudofunctors

Category
├─ Limits and colimits
│  ├─ preservation through composition
│  └─ reflective transport using an ordinary adjunction
├─ Preadditive
│  ├─ Triangulated category              Mathlib root
│  │  ├─ signed integral-shift exactness explicit CommShift + IsTriangulated
│  │  ├─ ObjectProperty.OnTriangle       objectwise subcategory witness
│  │  │  └─ liftTriangle / liftTriangleMap
│  │  │     full-subcategory lift, comparison iso, functorial laws
│  │  ├─ Semiorthogonal decomposition
│  │  │  ├─ ExceptionalCollection
│  │  │  ├─ OrthogonalExceptionalBlocks  positive blocks and residual
│  │  │  ├─ RightProjectionData          chosen adjoint and universal Hom
│  │  │  └─ mutation / projection chains objectwise cones and iteration
│  │  └─ Wall.ChargeFamily P N           parameterized charges; wall loci
│  │     ├─ reindex / pullback           change of chart / of class map
│  │     ├─ smul / phaseRotate β         wall_smul; a unit modulus fixes wallValue
│  │     │  └─ = phaseTiltRotation       proved comparison, never a copy
│  │     ├─ Wall.Exp.ofMoments m         one polynomial, indexed by truncation m
│  │     │  ├─ scalar moments            compressed H-degrees of a polarised n-fold
│  │     │  │  ├─ m = 1, m = 2           SlopeData.charge / stChargeFamily
│  │     │  │  ├─ m = 3                  Threefold.chargeFamily
│  │     │  │  ├─ m = 4                  free; no new polynomial
│  │     │  │  └─ (n,m) = (3,2)          the tilt charge; Ku(cubic threefold)
│  │     │  │     rotated by 1/i         ν is α · its unrotated chargeSlope
│  │     │  └─ form moments              Picard rank ≥ 2; no compression
│  │     │     ├─ centralCharge          Divisorial; proved instance of the kernel
│  │     │     ├─ StabilityParameters    the (B,ω) chart; w = β + iα fixed here
│  │     │     ├─ mukaiCharge / κ        κ is a pullback, never a coefficient
│  │     │     │  SqrtTodd               the image of κ, not a truncation of it
│  │     │     └─ quadric, ℙ², blow-up   rank-one slice reaches the scalar branch
│  │     ├─ Wall.Exp.twist / discr       the e^{-βH} action and Δ_H, stated once
│  │     └─ Spherical half-wall          a wall against the point class, cut by a
│  │                                     sign; inclusion plus sign, never equality
│  └─ Linear k C                         Mathlib root
│     └─ SerreFunctorData                duality on Hom spaces
│        ├─ SerreCategoryData            chosen Serre autoequivalence
│        │  └─ EnriquesCategoryData      square-to-shift refinement
│        ├─ IsSphericalObject            two-degree self-Hom profile
│        ├─ IsPseudoprojectiveObject     interval self-Hom profile
│        ├─ Ext profiles / transport     Serre-compatible equivalences
│        └─ classification data          supplied paper conclusions
├─ Abelian                               Mathlib typeclass
│  ├─ CochainComplex.homologyModel       generic zero-differential model
│  │  └─ ModuleCat/division-ring formality
│  │     noncanonical and unbounded; no finiteness/naturality
│  ├─ CochainComplex.finiteCohomologyModel
│  │  ├─ finiteCohomologyModelHomologyIso  homology preserves the finite biproduct
│  │  └─ finiteCohomologyModelIsoShifted degree i becomes degree zero shifted by -i
│  ├─ CochainComplex.FiniteCohomologyPresentation
│  │  ├─ pullback                        transport along an explicit HomotopyEquiv
│  │  ├─ isZero_homology_of_not_mem      finite homology support consequence
│  │  ├─ homologyModelIsoFiniteCohomologyModel
│  │  │                                   generic finite-support comparison
│  │  ├─ ofFiniteSupport                 ModuleCat/division-ring constructor
│  │  └─ shiftedHomotopyEquiv            presentation in the shifted normal form
│  ├─ weak-Serre exactness               repository generic extension
│  └─ DerivedCategory C                  generic construction
│     ├─ ShortExact.singleTriangle       Mathlib triangle construction
│     │  └─ map identity/composition     neutral functoriality laws
│     └─ OppositeComparison C            explicit derived/opposite bridge
│        └─ exact ModuleCat linear dual  categorical specialization
├─ FiniteExactTower
│  └─ FiniteFiltration                    zero-to-object endpoint refinement
│     └─ almost-disconnected witness       scheme-geometric leaf
├─ HasShift C A                          Mathlib root
│  └─ HasShift (X ⥤ Y) A                 pointwise, from the target's shift
│     └─ evaluation commutes strictly    identity comparison, both laws free
├─ DGCategory C
│  ├─ IsShiftBy X n Y                    representable dg shift witness
│  │  └─ homIso                         dgHom W X ≅ (dgHom W Y)⟦-n⟧
│  ├─ DGLinear k C                       scalar refinement
│  │  ├─ homComplex                     existing Hom-complex repackaged in ModuleCat k
│  │  ├─ IsShiftBy.linearHomIso          target shift as a shifted Hom-complex iso
│  │  │  ├─ H⁰ homComplex ≃ₗ Hom in H⁰  intrinsic quotient comparison
│  │  │  └─ Hⁿ homComplex ≃ₗ Hom in H⁰  target is the selected same-sign shift Y⟦n⟧
│  │  ├─ homComplexFiniteCohomologyPresentation
│  │  │                                   HomFiniteBounded support + field formality
│  │  ├─ postcompCochain                fixed-source right composition, linear chain-map law
│  │  ├─ homFunctor k E                 Hom(E,-) as a k-linear dg functor to Cdg(ModuleCat k)
│  │  ├─ Cdg (ModuleCat k)             standard model inherits Mathlib's k-linear structure
│  │  │  └─ linearTensorObj K X       Mathlib total tensor product, same universe
│  │  │     ├─ tensorCochainLinearEquiv   degreewise tensor--Hom adjunction
│  │  │     └─ HasLinearCopowers       concrete scalar-linear copower instance
│  │  └─ IsLinearCopowerOf k K X Z      represents k-linear cochains only
│  │     ├─ homComplexIso               representing equivalence, compatible with differentials
│  │     ├─ coefficientMap              homogeneous coefficient action, strict in composition
│  │     ├─ lift / lift_unique           linear cochains are morphisms out of Z
│  │     ├─ compare / compareIso         strict comparison, packaged as a Z⁰ isomorphism
│  │     ├─ scalar-unit witness         single⁰(k) ⊗ X represents X itself
│  │     ├─ HasLinearCopower(s)          Mathlib-style mere-existence capabilities
│  │     │  └─ linearCopowerFunctor    Cdg(ModuleCat k) ⟶ C, k-linear dg functor
│  │     │     ├─ linearCopowerAdjunction  (- ⊗ E) ⊣ Hom(E,-), strict at the dg level
│  │     │     │  ├─ unit                 selected universal copower chain map
│  │     │     │  └─ counit               exactly selected scalar-linear evaluation
│  │     │     ├─ selected H⁰ invariance is a HomotopyCategory/DGEnhancement leaf
│  │     │     │  └─ LinearCopowerFiniteFree
│  │     │     │     ├─ basis expansion of a degree-zero copower
│  │     │     │     └─ finite-free finrank specialization
│  │     │     └─ finite presentation transport
│  │     │        ├─ finite biproduct of shifted degree-zero copowers in H⁰ C
│  │     │        └─ nested finite biproduct of shifts of X with finrank multiplicity
│  │     │           └─ K₀ class = homologyEulerChar • [X] for supplied finite-free data
│  │     └─ LinearEvaluationData k E     scalar-linear Hom(E,-) ⊗ E assembly
│  │        ├─ functor                   k-linear dg functor
│  │        ├─ evaluation                closed degree-zero map to the identity
│  │        ├─ compareIso                coherent choice independence, strict over evaluation
│  │        ├─ IsEulerCopower            generic H⁰ rank-one K₀ predicate
│  │        │  ├─ realization from supplied finite presentations
│  │        │  └─ automatic realization from HomFiniteBounded
│  │        └─ TwistConeData             direct cone of scalar-linear evaluation
│  │           ├─ compareIso / exactness  delegated to generic strict-square and cone APIs
│  │           ├─ twistTriangleFunctor    H⁰ C ⥤ Triangle (H⁰ C), all distinguished
│  │           ├─ adjunctionTwistIso      canonical Z⁰ identification with the copower--Hom counit cone
│  │           ├─ adjunctionTwistTriangleIso
│  │           │                           coherent identification of the full H⁰ triangle functors
│  │           └─ K₀ action             identity minus evaluation; HomFiniteBounded numerical twist
│  ├─ DGFunctor C D
│  │  ├─ HomogeneousNatTrans             all degrees, differential, dg-functor category
│  │  │  ├─ IsClosed                     shared cocycle predicate for transformations
│  │  │  ├─ whiskerLeft / whiskerRight   both sign-free, additive, degree-preserving
│  │  │  │  ├─ interchange               Godement, with the Koszul sign (-1)^(m n)
│  │  │  │  └─ hcomp                     the product itself; graded Leibniz, strict assoc
│  │  │  ├─ h0                           closed degree zero becomes an ordinary NatTrans
│  │  │  │  └─ h0Comparison             H⁰(DGFunctor C D) ⥤ (H⁰ C ⥤ H⁰ D); no fullness claimed
│  │  │  │     └─ h0Iso                 Z⁰ isomorphisms descend, coherently
│  │  │  └─ ConeData                     functorial objectwise cones
│  │  │     └─ K₀ action                 target endpoint minus source endpoint
│  │  ├─ IsQuasiEquivalence               Hom-complex quasi-isos plus essential surjectivity
│  │  │  └─ h0Equivalence                 induces an equivalence H⁰ C ≌ H⁰ D
│  │  ├─ shiftedFunctor n                objectwise shift with the sign (-1)^(n p)
│  │  │  ├─ shiftedFunctorAdd / Zero     degree coherence, closed and invertible
│  │  │  ├─ HasShift Z⁰(DGFunctor C D) ℤ standard Mathlib packaging, all unit/assoc laws
│  │  │  ├─ shiftedFunctor_h0_obj/_map   the dg shift computes the H⁰ shift
│  │  │  ├─ shiftedFunctorH0Iso          functor-level comparison; transports H⁰ equivalences
│  │  │  └─ shiftedFunctorH0CommShift / IsTriangulated
│  │  │                                 transports exactness with the signed shift package
│  │  ├─ PreservesShifts                 free: every dg functor preserves shifts
│  │  └─ PreservesChosenCones            free: mapped fst/snd split every image cone
│  │     ├─ ofIso                        invariant under Z⁰ dg-functor isomorphism
│  │     └─ h0CommShift / h0IsTriangulated automatic non-instance H⁰ exactness
│  │        └─ transportedH0             ordinary equivalence conjugate
│  │           ├─ CommShift / IsTriangulated  composed from canonical packages
│  │           └─ Equivalence            under explicit equivalence of H⁰ F
│  ├─ IsCopowerOf K X Z                   `Z = K ⊗ X`, by its universal property
│  │  ├─ lift / lift_unique              cochains out of `K` are morphisms out of `Z`
│  │  ├─ compare                         closed canonical comparison, strict composition
│  │  ├─ HasCopower / HasCopowers        Mathlib-style mere-existence capabilities
│  │  │  └─ copowerData                  a noncomputably selected CopowerData witness
│  │  ├─ HasEvaluationData E             the narrower existence capability object twists need
│  │  │  └─ chosenEvaluationData         a noncomputably selected EvaluationData E
│  │  └─ EvaluationData E                selected directly or through HasEvaluationData
│  │     ├─ functor                      the dg functor `RHom(E,-) ⊗ E`
│  │     ├─ evaluation                   its degree-zero map to the identity
│  │     ├─ compareIso                   canonical Z⁰ isomorphism between any two choices
│  │     │  └─ compare_comp_evaluation  strict compatibility with evaluation
│  │     └─ TwistConeData                the object twist Cone(evaluation)
│  │        ├─ compareIso                coherent Z⁰ iso across evaluation/cone choices
│  │        │  └─ inclusion compatibility is strict
│  │        ├─ twistTriangleFunctor      H⁰ C ⥤ Triangle (H⁰ C), all distinguished
│  │        ├─ twistTriangleIso          original same-evaluation cone-choice comparison
│  │        ├─ twistTriangleIsoOfEvaluation  coherent across evaluation and cone choices
│  │        ├─ twistH0IsTriangulated    automatic exactness; no caller-supplied cone witness
│  │        ├─ K₀ action                 generic cone formula: identity minus evaluation
│  │        └─ IsEulerCopower           choice-invariant realization input for numerical twistK₀
│  ├─ DGAdjunction L R                    closed unit/counit plus triangle identities
│  │  └─ DGAdjunction.h0                  an ordinary adjunction between the H⁰ functors
│  │     └─ H0Presentation                supplied endpoint isos after equivalence transport
│  │        ├─ presentedCounitTriangle     generic normalization of the transported dg counit cone
│  │        │  └─ transportedTwist        unchanged third vertex; pointwise distinguished
│  │        ├─ presentedUnitTriangle       generic normalization of the transported dg unit cone
│  │        │  └─ transportedUnitCone     unshifted third vertex; pointwise distinguished
│  │        ├─ presentedCotwistTriangle    Mathlib inverse rotation of the presented unit triangle
│  │        │  ├─ transportedCotwist      pointwise `[-1]` shift of the transported unit cone
│  │        │  └─ transportedCotwistH0Iso transport of the actual shifted dg cone agrees up to iso
│  │        │     └─ exact equivalence     exact for every cone under supplied triangulated transport;
│  │        │                                equivalence from explicit H⁰ input
│  │        └─ Fourier--Mukai adapters     existing left/right adjoint-kernel data
│  ├─ HomogeneousSquare                  arbitrary-degree vertical maps and homotopy
│  │  ├─ HomotopySquare                  degree zero with closed vertical maps
│  │  │  └─ strict                      a commuting square with zero homotopy
│  │  └─ IsConeOf.homogeneousLift        all-degree cone maps, d/id/add/comp laws
│  │     ├─ IsConeOf.lift                the degree-zero case, not a second owner
│  │     │  └─ IsConeOf.Morphism         cone map with strict `inr` and `fst` squares
│  │     │     └─ ConePresentation category  composes without a shift witness
│  │     ├─ IsConeOf.isoOfStrictSquare   endpoint isos lift canonically to cone isos
│  │     └─ HomogeneousNatTrans.ConeData objectwise cones assemble to a dg functor
│  │        ├─ fst / snd                 cone projections, graded-natural
│  │        ├─ isConeOf                  a cone in the dg category of dg functors
│  │        ├─ isoOfStrictSquare         the generic lift in Z⁰(DGFunctor C D)
│  │        ├─ preservesShifts           automatic for the assembled dg functor
│  │        ├─ preservesChosenCones      retained endpoint-based 3-by-3 witness; existence automatic
│  │        ├─ triangleFunctor           H⁰ C ⥤ Triangle (H⁰ D), values distinguished
│  │        │  ├─ triangleNatTrans       natural in a STRICT square of transformations
│  │        │  ├─ triangleIsoOfStrictSquare  endpoint isos give a NatIso
│  │        │  └─ compareIso             the cone choices do not matter, canonically
│  │        └─ DGAdjunction.CounitConeData  counit-cone twist candidate
│  │           └─ twistTriangleFunctor   H⁰ D ⥤ Triangle (H⁰ D), all distinguished
│  ├─ H0 C
│  │  └─ coneTriangleFunctor             functor to distinguished triangles
│  └─ IsPretriangulated C
│     └─ Enhancement T                   comparison data, not a class
│        ├─ liftedCocycle                noncanonical closed representative of an ordinary map
│        ├─ conePresentation             representative plus a noncanonical dg cone
│        └─ coneTriangleFunctor          dg cones read in `T` through the equivalence
├─ Triangle.FirstMapNormalizationData     raw endpoint isos plus a named first-map square
│  ├─ normalizedTriangle                 literal first two vertices and literal first map
│  ├─ rawIsoNormalized                   natural triangle comparison; third component identity
│  └─ ComparisonData                     third-vertex iso + remaining squares over identity endpoints
├─ Fourier--Mukai correspondence
│  ├─ kernelTransform                     functor from kernels to transforms
│  ├─ kernelEvaluation                    one source object's kernel-variable functor
│  ├─ ExactFamily                         extends Mathlib CommShift; pointwise exactness only
│  ├─ ExactBifunctor                      extends Mathlib CommShift₂Int; Koszul-compatible
│  │  ├─ first/secondFamilyCommShift      explicit adapters, evaluation agreement
│  │  └─ firstFamily / secondFamily       exact-family projections through those adapters
│  ├─ kernelConeTransformTriangleFunctor  pointwise image of dg cones of an enhanced kernel category
│  ├─ KernelConeNormalizationData         FM cone/shift data plus generic-normalization adapter
│  │  ├─ firstMapNormalizationData       categorical endpoint/first-map normalization
│  │  ├─ coneKernel                      ordinary image of the selected enhanced cone
│  │  └─ shiftedConeKernel               enhanced shift with transform/shift comparison
│  └─ KernelTransformationData            ordinary kernel arrow realizing a named transformation
│     ├─ KernelTransformationConeData     noncanonical enhanced representative and dg cone
│     │  └─ normalizationData             reusable literal endpoint/first-map transport
│     ├─ CounitKernelData                 equivalent adjunction-counit specialization; stable API
│     │  └─ CounitKernelConeData          enhanced counit specialization
│     │     ├─ twistKernel                           ordinary image of the selected dg cone
│     │     ├─ kernel-presented twist candidate       exact image of its dg cone
│     │     ├─ counitTriangleInSource                literal counit triangle, pointwise distinguished
│     │     └─ presented dg comparison               objectwise choice or supplied natural contract
│     ├─ AdjunctionUnitKernelData         definitional right-adjunction-unit specialization
│     │  └─ AdjunctionUnitKernelConeData  selected enhanced unit arrow and dg cone
│     │     ├─ unshifted cotwist-cone candidate       exact image of its dg cone
│     │     ├─ unitTriangleInSource                  literal unit triangle, pointwise distinguished
│     │     ├─ cotwist = cotwistCone⟦-1⟧             pointwise functor-category shift
│     │     ├─ cotwistKernel                         shifted enhanced cone presenting cotwist
│     │     ├─ cotwistTriangleInSource               inverse rotation, pointwise distinguished
│     │     └─ presented dg comparison               objectwise choice or supplied natural contract
│     ├─ DualTwistKernelData              left-adjunction unit specialization after swapping
│     │  └─ DualTwistKernelConeData       reuses the unit/cotwist cone and normalization
│     │     ├─ dualTwistKernel                        shifted enhanced cone presenting dual twist
│     │     └─ dualTwistTriangleInTarget             inverse rotation, pointwise distinguished
│     └─ DualCotwistKernelData            left-adjunction counit specialization after swapping
│        └─ DualCotwistKernelConeData     reuses the counit/twist cone and normalization
│           ├─ dualCotwistKernel                      selected enhanced cone presenting dual cotwist
│           └─ dualCotwistTriangleInSource           literal counit triangle, pointwise distinguished
├─ Enhanced spherical-functor lane
│  ├─ EnhancedAdjunctionCones             four adjunction-map cone choices
│  │  ├─ dualTwistFunctor / cotwistFunctor conventional shifted cone functors
│  │  ├─ cotwistH0Equivalence             spends the unshifted condition after `[-1]`
│  │  ├─ H⁰ exactness                     automatic for every dg functor; no endpoint cone hypotheses
│  │  ├─ triangulated equivalences         canonical Mathlib package for twist and cotwist
│  │  └─ K₀ action                        identity minus the corresponding adjunction composite
│  └─ TwistCotwistEquivalenceConditions   explicit sufficient-condition input only
│     └─ full sphericality                 pending Morita/adjoint-comparison theorem
├─ Derived-category extensions
│  └─ Ext adjunction / dimension shift / resolution naturality
├─ filtered-complex spectral sequences
├─ Moduli
│  └─ BoundednessProblem                 neutral boundedness predicate
├─ GrothendieckPresentation
│  ├─ K₀Ab                               short-exact relations
│  ├─ K₀                                 triangle relations
│  │  ├─ finite biproduct calculus         [⨁ Xᵢ] = Σ [Xᵢ], constant family = n·[X]
│  │  ├─ rankOne / IsRankOne                factorization through ℤ; objectwise before exactness
│  │  ├─ Realization := K₀ C →+ A        additive target
│  │  │  └─ Descends                    commuting realization square
│  │  └─ EulerForm := K₀ C →+ K₀ C →+ ℤ
│  │     ├─ ofLinear                    canonical linear-category pairing
│  │     └─ Preserves                   exact-functor compatibility
│  └─ K₀dg := K₀ (H0 C)                 reuse, not a third presentation
└─ Sites / descent / stacks in groupoids
   ├─ over-site functoriality
   │  └─ cocontinuity of `Over.post`
   ├─ `CoversTop` equivalence transport
   ├─ Sheaves
   │  ├─ coverwise detection of local equivalences
   │  ├─ constant pullback and cohomology pushforward
   │  └─ module sheaves on a ringed site
   │     ├─ restriction to an over site
   │     ├─ exact forgetful functor
   │     ├─ finite-presentation transport
   │     │  ├─ isomorphism invariance / cover locality
   │     │  └─ zero objects / short-exact extensions
   │     └─ intrinsic IsInvertible
   │        ├─ rank-one local trivializations
   │        ├─ arbitrary-site tensor descent
   │        └─ topological specialization
   │           ├─ stalk/tensor comparison
   │           └─ stalkwise arbitrary-factor strengthening
   ├─ site-theoretic Čech complexes and derived comparison
   │  └─ compact-basis and finite-cover boundedness
   └─ scheme-site realizations

LinearAlgebra
├─ finite free integral lattices          Mathlib: [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
│  └─ NumericalVarietyData.NumericalQuotient finite by Module.Finite.quotient; free, once
│                                            torsion-free, by Module.free_of_finite_type_torsion_free'
├─ weighted-basis graded pieces
│  ├─ internal direct-sum decomposition
│  └─ NumericalRingData.ofGradedBasis        geometric numerical consumer
├─ bilinear form on a lattice
│  └─ Lattice.pairCharge b x y v         ⟪x,v⟫ + i⟪y,v⟫; b not symmetric
│     ├─ PeriodDomain.centralCharge      the quadratic-space presentation
│     │  ├─ support property             ker Z is the plane's negative-definite ⊥
│     │  ├─ signature additivity         gives HasSignatureTwo on a complement
│     │  ├─ Mukai.expCharge              Bridgeland Z(β,ω), the exponential plane
│     │  ├─ Ku(X) charge                 on H̃_alg; NOT a child of expCharge
│     │  └─ Ku(X) period domain          on A₂^⊥ ⊆ H̃; a different lattice
│     └─ Mukai.Graded.pairing n          ⟪v,w⟫ = (-1)ⁿ⟪w,v⟫; odd n alternating
│        n = 2 is realPairing            so n = 2 owes a comparison, not a def
└─ Mukai.pairing / selfPairing           Lattice/Mukai/Basic.lean:56,143
   ARITY IS FIXED AT THREE               generalise over the coefficient ring only
   root of the discriminant              pairing 3 v v = 0 identically

Algebra
├─ ordinary ring and module theory
│  └─ module localization
│     └─ kernel maps                       consumed by coherent-sheaf geometry
├─ numerical polynomials on integer lattices
│  ├─ mixed finite differences and degree
│  └─ top multilinear coefficients
│     └─ Snapper polynomiality             geometric Picard/coherent consumer
├─ multivariate polynomials
│  └─ division by monomials                consumed by projective localization
├─ saturation of an additive subgroup
│  └─ saturated quotient and torsion-free universal property
└─ relative numerical algebra
   ├─ indexed sums and saturated family-relation quotients
   └─ additive-map images and finite-index-overlattice predicates

AlgebraicGeometry
├─ SheafOfModules(X)
│  ├─ QuasicoherentSheaf(X)
│  │  └─ CoherentSheaf(X)
│  │     ├─ Abelian instance under geometric hypotheses
│  │     └─ DerivedCategory (Coh X)     consumes the generic construction
│  ├─ sheafified tensor / MonoidalCategory X.Modules
│  │  ├─ intrinsic IsInvertible as ObjectProperty.IsMonoidal
│  │  │  ├─ InvertibleSheaf              inherited full monoidal subcategory
│  │  │  └─ pullback preservation        theorem inherited by every consumer
│  │  ├─ Picard classes                  consume intrinsic IsInvertible
│  │  └─ Functor.Monoidal pullback input standard tensor/unit comparison surface
│  └─ LineBundleData                     invertible sheaf plus chosen tensor inverse
│     ├─ determinant and Picard interpretations
│     ├─ monoidal pullback and projection formula
│     ├─ CartierDivisor.lineBundleData   associated-sheaf/Picard agreement leaf
│     │  ├─ coherent, derived, bounded-derived canonical objects
│     │  └─ effective-divisor sequences twisted by arbitrary line bundles
│     └─ almost-disconnected graded pieces   scheme-geometric leaf
├─ scheme-derived category                     `DerivedCategory/`
│  ├─ Dqc                                      neutral geometric locus
│  │  ├─ canonical zero                        owned by Dqc, all schemes
│  │  └─ explicit comparison evidence          representatives, not instances
│  ├─ bounded coherent locus                   consumes generic triangle lift
│  │  ├─ Cartier-divisor objects            consume canonical line-bundle bridge
│  │  └─ short-exact triangles/maps         includes arbitrary line-bundle twists
│  ├─ scheme pullback and geometric kernels
│  └─ absolute perfect locus                   thick envelope in `D(Coh X)`
│     └─ essential image in Dqc
│        └─ compact objects                    only with explicit evidence
├─ relative-perfect locus over `p : X ⟶ S`     `Moduli/PerfectComplex/Relative`
│  └─ pseudo-coherent + finite Tor amplitude   not absolute perfection by definition
├─ two-term determinant presentation           explicit finite-locally-free resolution
│  └─ absolute perfect degree-zero object       proved comparison adapter
├─ numerical K-theory
│  ├─ Euler quotient
│  │  └─ future scheme-specific relation generators consume Algebra root
│  ├─ Riemann--Roch and Mukai transfer
│  │  └─ consume categorical K₀ realizations and Euler forms
│  └─ Polarised.wallChargeFamily         one transport for every (n, m, κ)
│     ├─ n = 2, 3 exist; n = 4 free      K3, ℙ², quadric, ℙ³, quintic, ℙ⁴, sextic
│     ├─ κ = √td is inhabited            = mukaiCharge at sqrtTodd on rankOne
│     │  any surface                     no K3 hypothesis is needed
│     └─ κ = 1 and κ = √td               two pullbacks; different walls, not one
├─ moduli
│  ├─ fiberwise replete locus selector     not a subprestack
│  ├─ finite-type boundedness witness      consumes selector + generic predicate
│  ├─ affine stable subprestack            consumes pseudofunctor object property
│  ├─ stack presentation
│  └─ perfect-complex specialization
└─ stability-consuming children                `DerivedCategory/Stability/`, `Moduli/`,
                                               `Numerical/`, `Stability/` — four, not one
```

The arrows implied by this tree point downwards from consumers to roots.  In
particular:

- do not introduce a second adjunction hierarchy: reuse Mathlib's
  `Bicategory.Adjunction`, and recover ordinary adjoint functors through the
  bicategory `Cat`; place results that merely assume an adjunction with their
  actual conclusion, such as limit preservation or derived `Ext`;
- do not add `KLinearCategory`; use Mathlib's `Preadditive` and `Linear` and
  bridge `DGLinear` to them;
- do not add a coherent, derived, dg, projective-space, or relative sibling of
  the Grothendieck group presentation; specialize the canonical presentation
  and prove comparison maps;
- represent additive K₀ targets and categorical Euler pairings by the canonical
  `K₀.Realization` and `K₀.EulerForm` aliases. Their descent and preservation
  laws stay with the triangulated Grothendieck-group root; geometric
  `IsRiemannRoch`, Euler-transfer, and Mukai-pairing theorems consume them;
- keep indexed additive-group sums, additive-subgroup saturation,
  family-relation systems, additive-map images, and finite-index-overlattice
  predicates in `Algebra/RelativeNumerical`; a geometric consumer must
  introduce actual schemes, connectivity, relative perfection, or other
  geometric data and import this root directly;
- keep integer-lattice numerical functions, mixed forward differences,
  finite-difference degree, Newton coefficients, and top multilinear
  coefficients in `Algebra/NumericalPolynomial`; Snapper's theorem imports
  that root and adds the Picard, coherent-sheaf, and Euler-characteristic data;
- do not add a class for finite free abelian groups: Mathlib's `Module.Finite ℤ`
  and `Module.Free ℤ` instances are the interface, and freeness of a finitely
  generated torsion-free group is Mathlib's instance
  `Module.free_of_finite_type_torsion_free'`; the numerical Euler-radical
  quotient supplies those hypotheses and nothing else;
- keep ordinary module theory under `Algebra`, generic sheaves under
  `CategoryTheory/Sites/Sheaves`, module sheaves on ringed sites under
  `Algebra/Category/ModuleCat/Sheaf` where Mathlib defines `SheafOfModules`,
  and only the scheme-indexed `SheafOfModules(X) -> QCoh(X) -> Coh(X)`
  refinements under algebraic geometry; in particular, coherent-sheaf kernels directly reuse
  the module-localization kernel maps rather than owning them;
- keep detection of additive-presheaf local equivalences on a `CoversTop`
  family under the generic site/sheaf root; scheme charts and sheafified
  tensor constructions only consume that theorem chain;
- keep cocontinuity of `Over.post`, module-sheaf restriction to over sites,
  and equivalence transport of `CoversTop` families under the generic site and
  sheaf roots; open-immersion geometry consumes them only after introducing
  schemes and their open-set sites;
- keep restriction of presentations, generating sections, and quasicoherent
  presentation data under the generic ringed-site presentation root; affine
  geometry consumes that API only when it introduces `Spec R` and basic opens;
- keep isomorphism invariance, over-site preservation, and covering-family
  descent of finite presentation under the same generic presentation root;
  coherent-sheaf geometry consumes them only for `coherent X` and affine-open
  criteria;
- keep stalk/tensor comparisons for module presheaves under
  `Topology/Sheaves/ModuleTensor/`: their use of open neighbourhoods, germs,
  and stalk functors makes them topological specializations of arbitrary-site
  sheaf theory, not ordinary module algebra;
- keep the braided transfer between the two sheafification whiskering
  comparisons under `Algebra/Category/ModuleCat/Sheaf/Tensor.lean`: conjugating
  `M ◁ toSheafify` into `toSheafify ▷ M` uses only symmetry of the objectwise
  presheaf tensor, so it holds on an arbitrary site and must not be restated
  inside the scheme consumer that supplies its stalkwise hypothesis;
- put the sheafified tensor and its coherence on all scheme-module sheaves;
  invertible sheaves inherit that root through `ObjectProperty.IsMonoidal`, and
  pullback monoidality uses Mathlib's `Functor.Monoidal` rather than a parallel
  capability class;
- keep basiswise detection of topological sheaf isomorphisms under
  `Topology/Sheaves/Basis.lean`; affine comparison consumes it only after
  introducing `Spec R`, distinguished opens, and module localization;
- keep identities involving the lattice and categorical products of
  prime-spectrum opens under `RingTheory/Spectrum/Prime/`, where Mathlib
  defines `basicOpen`; neither the ring input nor the topological output
  moves them;
- extend Mathlib's abelian-category hierarchy under `CategoryTheory/Abelian`
  and make the geometric proof that `Coh(X)` is abelian an input to the generic
  derived-category construction;
- generic stacks, replete subprestacks, and boundedness predicates do not
  import stability-condition or geometric modules; scheme presentations and
  finite-type witnesses remain geometric consumers;- a paper-specific module may instantiate these roots but never becomes a root
  imported by them.
- keep exceptional blocks, residual right orthogonals, chosen right-adjoint
  projections, objectwise mutation and projection-chain arguments, Serre
  duality, Enriques-category relations, and spherical or pseudoprojective
  self-Hom profiles and transport under the generic triangulated-category
  root.  Kernel-presented exceptional-block extension remains under the
  Fourier--Mukai root.  A surface-specific residual category reuses those
  structures and binds the candidates to projections of its actual line
  bundles; the numerical curve chain is geometric, its derived triangles and
  successive block maps consume the reusable Cartier-sequence roots, and only
  quotient orthogonality remains an explicit geometric input.  Functorial dg
  cones and their pointwise transform triangles now have generic roots, and
  the kernel category enters through an `Enhancement` rather than as an `H⁰`
  on the nose; the enhancement of the geometric kernel category with its
  exact comparison, the actual kernel morphism, and exactness of kernel
  evaluation remain explicit realization inputs.
- keep every central charge under one root. A charge is an additive map to `ℂ`
  built from a complex parameter and a numerical class, and the surface, threefold
  and slope charges are the same polynomial at three truncation degrees, not three
  theories. Truncation degree `m` is the index, never the ambient dimension `n`:
  the cubic-threefold tilt charge is `(n, m) = (3, 2)`, so a root indexed by `n`
  cannot state it. A new dimension supplies a `Polarization` and inherits the
  polynomial; if a lane finds itself writing a fourth charge polynomial, the
  placement is wrong.
- a correction class `κ` is a pullback, never a coefficient. `κ = 1` and `κ = √td`
  give genuinely different walls, so they are two pullbacks of one transport and
  must not be fused into a single family. `SqrtTodd` is the image of `κ` under a
  numerical realization, not a truncation of it.
- the Mukai pairing has fixed arity three. Generalise it over the coefficient
  ring, never over dimension: a dimension-indexed self-pairing vanishes
  identically in odd degree, so it cannot be the root of the Bogomolov
  discriminant. The graded pairing is a separate object that declares nothing new
  at `n = 2`, where it is `Mukai.realPairing` and owes a comparison theorem.
- noncommutative varieties add no carrier. A Kuznetsov component reaches the tree
  by restriction along its inclusion, so there is no `KuznetsovChargeData` and
  must not become one. The two cases differ and the difference is forced by
  parity, not by taste: for the cubic threefold the dimension is odd, the pairing
  is alternating, no period domain exists, and the charge is induced from the
  rotated tilt charge; for the cubic fourfold the charge lives on the algebraic
  Mukai lattice while the period domain lives on the orthogonal complement of an
  `A₂` sublattice, and those are two different lattices that must not be fused.

Bicategories are the first implemented higher-categorical stage. A future
general `n`-category or `(∞,1)`-category layer must name its formal model and
its comparison with this spine; an empty directory does not establish an
abstraction relationship.

## Recorded negative results

Clause 6 below requires a falsified generalization to be recorded rather than
forgotten. These were each established against the tree, and each one is a
unification that looks right in the literature and is false here.

- **A dimension-indexed Mukai self-pairing is not the root of the discriminant.**
  It vanishes identically in odd degree, so the threefold leaf cannot reach it.
  The root is the fixed-arity pairing generalized over its coefficient ring.
- **The multi-divisor charge does not factor through the compressed H-degrees.**
  The compression is not injective once the Picard rank exceeds one, so the
  intersection-form branch is a genuine sibling of the scalar branch and not a
  specialization of it.
- **The graded pairing declares nothing new at `n = 2`.** It is
  `Mukai.realPairing` there, on the nose. Shipping it as a definition rather than
  a comparison would add a second spelling of an existing form.
- **Parity of the compressed pairing says nothing about a Kuznetsov component.**
  The compressed form lives on a space of dimension `n + 1`; the Mukai lattice of
  the component does not. Symmetry there is automatic for an unrelated reason, so
  the parity argument is vacuous even on the correct space.
- **The rotation that induces the cubic-threefold charge is not cosmetic.** It
  leaves every wall fixed but changes phases, so a construction that drops it is
  wrong about semistability even where it is right about walls.
- **The tilt charge is not a chart change of the threefold charge.** Their wall
  loci genuinely differ; the tilt family is the surface family pulled back along a
  truncation, which is a different operation.
- **A geometric Serre functor is not a new structure.** The categorical root
  already exists and the geometric side owes it a bridge; a parallel structure
  fails the adoption clause below and would add a third duplicate twist.
- **The Fourier--Mukai convolution classes are not pseudofunctor data.** They
  resemble compositor and unitor data without being an instance of it, so that
  lane cannot own them and the resemblance must not be used to place them.

## Root review before a new structure

Every issue or pull request that introduces a public `structure`, `class`,
quotient carrier, or category must answer these questions before implementation.

1. **Canonical owner.** What existing root is closest?  Give its declaration
   and module.  If none exists, name the proposed neutral module.
2. **Adoption.** Name two independent consumers, or say explicitly that this is
   statement-layer data whose purpose is to compare multiple inhabitants.
3. **Projection.** How does a specialization forget to, refine, or compare with
   the root?  The answer must be an existing instance, a projection, an
   `abbrev`, or a theorem—not prose.
4. **Diamond.** If both the root and leaf synthesize inherited instances, add a
   compile-time or equality test showing that the paths agree.
5. **Dependency direction.** Confirm that the root imports no leaf or
   paper-specific module.
6. **Negative result.** If the apparent generalization is false, record the
   counterexample and keep the leaves separate.  A falsified unification is a
   successful architecture result.

Moving declarations is not complete until imports, umbrellas, audit records,
registry bindings, and compatibility reexports are updated together, as
required by `CONTRIBUTING.md`.

## Agreement is part of the feature

If the target already carries the structure being constructed, agreement is
an acceptance criterion, not follow-up cleanup.  The dg enhancement of the
homotopy category is the model: its transported shift and distinguished
triangles are compared with Mathlib's existing instances.  The same rule
applies to exact versus triangulated K-groups, ordinary versus dg linearity,
and classical versus derived moduli truncations.

## Enforcement

The policy is partly mechanical and partly a review obligation:

- `scripts/check_layering.py` enforces the policy edges in `layers.md`;
- `scripts/check_umbrella_coverage.py` keeps every specialization in the public
  tree;
- `scripts/check_single_instantiation.py` rejects new thin abstractions in the
  generic subjects;
- `scripts/check_roadmap.py` keeps materialized lanes synchronized with their
  tracker issues;
- the pull-request template records the non-mechanical root, projection, and
  agreement decisions.

The projective-families roadmap carries the first finer-grained burn-down:
generic stack roots move out of scheme geometry, moduli-to-stability reverse
imports are removed, and geometric relative numerical K-theory consumes the
indexed quotient machinery rooted in ordinary algebra.
