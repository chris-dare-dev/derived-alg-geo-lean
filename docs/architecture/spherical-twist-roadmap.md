# Enhanced spherical twists: conventions and remaining seams

This note records the mathematical convention implemented by the dg-cone and
Fourier--Mukai layers.  It is a dependency and claim ledger, not an assertion
that the repository already constructs a spherical twist for a geometric
Enriques surface.

## Primary references and convention

- Seidel--Thomas, *Braid group actions on derived categories of coherent
  sheaves*, [arXiv:math/0001043](https://arxiv.org/abs/math/0001043).  For an
  object `E`, the twist is the functorial cone of the evaluation
  `RHom(E,-) ⊗ E ⟶ id`.  In the smooth-projective Fourier--Mukai realization,
  its kernel is `Cone(E^∨ ⊠ E ⟶ O_Δ)` (Lemma 3.2).
- Anno--Logvinenko, *Spherical DG-functors*,
  [arXiv:1309.5035v2](https://arxiv.org/abs/1309.5035v2).  For a functor `S`
  with left and right adjoints `L` and `R`, their convention uses the four
  functorial triangles
  `SR ⟶ id_B ⟶ T`, `T' ⟶ id_B ⟶ SL`,
  `F ⟶ id_A ⟶ RS`, and `LS ⟶ id_A ⟶ F'`.
  Full sphericality includes twist/cotwist equivalences and two maps identifying
  the adjoints.  Their main theorem derives all four conditions from any two in
  a Morita-enhanced dg setting; it is not merely a theorem of triangulated
  categories.

The repository therefore calls `Cone(SR ⟶ id_B)` a **twist candidate**, not a
spherical twist, until the remaining equivalence and comparison conditions
have been discharged.

## Implemented dependency tree

```text
DGFunctor.HomogeneousNatTrans
├─ all integer degrees and Koszul naturality
├─ pointwise differential and vertical composition
├─ h0Comparison: H⁰(DGFunctor C D) ⥤ (H⁰ C ⥤ H⁰ D), no fullness or faithfulness
│  └─ h0Iso: a Z⁰ dg-functor isomorphism descends canonically, with unit/composition laws
├─ whiskerLeft / whiskerRight (both sign-free) and additive-hom packaging
│  ├─ interchange: the Godement sign (-1)^(m n) is naturality of the second
│  └─ hcomp: the Godement product, graded Leibniz, strictly associative
└─ DGCategory (DGFunctor A B)
   └─ IsClosed

IsConeOf
└─ homogeneousLift (one owner of the cone lift)
   ├─ arbitrary-degree squares with homotopy: differential law
   ├─ additivity, identity, composition laws for strict squares
   ├─ projection and inclusion formulas
   ├─ lift := homogeneousLift 0, HomotopySquare := degree-zero square + closedness
   │  ├─ HomotopySquare.strict: a commuting square with zero homotopy
   │  └─ IsConeOf.Morphism with the shift-free `fst` square
   │     └─ ConePresentation category, no pretriangulated instance needed
   ├─ isoOfStrictSquare: endpoint isomorphisms in a strict square induce a
   │  canonical Z⁰ isomorphism of arbitrary chosen cones
   └─ HomogeneousNatTrans.ConeData
         ├─ objectwise cone choices
         ├─ assembled cone DGFunctor
         ├─ canonical inr/inl transformations and boundary equation
         ├─ fst / snd: the cone projections, graded-natural in degrees 1 and 0
         ├─ isConeOf: a cone in the dg category DGFunctor C D itself, so the
         │  twist candidate is a cone OF FUNCTORS, the form in which
         │  Anno--Logvinenko state SR ⟶ Id_B ⟶ T
         ├─ isoOfStrictSquare: the generic cone isomorphism in Z⁰(DGFunctor C D)
         └─ triangleFunctor: H⁰ C ⥤ Triangle (H⁰ D), every value distinguished;
            the third square is the connecting map, carried by IsConeOf.Morphism
            ├─ triangleNatTrans: natural in a STRICT square of closed
            │  degree-zero transformations; the cone lifts are natural on the
            │  nose.  The homotopy-coherent case needs uniqueness of the lift
            │  up to homotopy, which the repository does not have.
            ├─ triangleIsoOfStrictSquare: endpoint isomorphisms upgrade the
            │  comparison to a natural isomorphism of triangle functors
            └─ compareIso: two ConeData for one transformation give canonically
               isomorphic triangle functors, so the cone choices do not matter

DGAdjunction
├─ closed unit and counit
├─ dg triangle identities
├─ h0 : an ordinary Mathlib adjunction between the H⁰ functors
└─ CounitConeData
   ├─ twist candidate Cone(LR ⟶ id)
   └─ twistTriangleFunctor: H⁰ D ⥤ Triangle (H⁰ D), every value distinguished,
      first two maps the counit and the canonical inclusion.  This is
      Anno--Logvinenko's twist triangle as a triangle OF FUNCTORS on H⁰.  It
      does not say the twist is an autoequivalence, does not call the
      adjunction spherical, and does not relate it to the other three
      triangles; UnitConeData carries the unshifted unit side.

HasCopower K X / HasCopowers C
└─ copowerData: a noncomputably selected CopowerData witness

HasEvaluationData E
├─ chosenEvaluationData: a noncomputably selected EvaluationData witness
└─ supplied automatically by HasCopowers C

EvaluationData E
├─ functor = RHom(E,-) ⊗ E, evaluation : functor ⟶ id, closed in degree zero
├─ compareIso: canonical Z⁰ isomorphism between any two choices, strictly
│  compatible with evaluation
└─ TwistConeData: the object twist T_E = Cone(evaluation)
   ├─ compareIso: canonical coherent Z⁰ isomorphism across both evaluation and
   │  cone choices, strictly compatible with id ⟶ T_E
   ├─ twistTriangleIsoOfEvaluation: coherent natural isomorphism of the full triangles
   │  across both evaluation and cone choices
   ├─ triangle functor H⁰ C ⥤ Triangle (H⁰ C), every value distinguished
   ├─ H⁰(T_E) triangulated as soon as RHom(E,-) ⊗ E preserves chosen cones
   │  (shifts are free for every dg functor)
   └─ no adjunction, no autoequivalence, no sphericality

EnhancedAdjunctionCones
├─ twist and dual-cotwist cones
├─ the twist is EXACT on H⁰ (twistH0IsTriangulated), as soon as S and R preserve
│  shifts and chosen cones.  A cone functor preserves both when its two ends do;
│  the cone half is the 3-by-3 lemma, whose proof is block diagonal in the four
│  coordinates of the two splittings rather than merely triangular.
├─ unshifted cones underlying dual twist and cotwist
├─ dualTwistFunctor and cotwistFunctor name their conventional `[-1]` shifts;
│  shiftedFunctorH0Iso compares their H⁰ functors with pointwise shift
├─ the four triangles as functors on H⁰, every value distinguished, each first
│  map the corresponding unit or counit.  The dual twist and the cotwist are
│  the INVERSE ROTATIONS of their unshifted cone triangles: invRotate applies
│  the ⟦-1⟧ shift and reorders in one step, and the first vertex is the value
│  of the dg shifted cone functor on the nose (DGFunctor.shiftedFunctor_h0_obj).
│  The unshifted forms are kept, since TwistCotwistEquivalenceConditions is
│  stated against the unshifted cone functors.  No sphericality, and no relation
│  among the four.
└─ TwistCotwistEquivalenceConditions
   └─ cotwistH0Equivalence spends the unshifted condition on the actual cotwist

Enhancement W (kernel category W ≃ H⁰ of a pretriangulated dg category)
├─ liftedCocycle / conePresentation: noncanonical enhanced lift of any ordinary map
└─ coneTriangleFunctor: dg cones read in W through the comparison equivalence
   └─ FourierMukai.KernelCone: pointwise and source-natural transform triangles
      ├─ KernelConeNormalizationData: literal endpoints and named first map
      │  └─ shiftedConeKernel: enhanced shift whose transform is the shifted cone transform
      └─ KernelTransformationData: a kernel arrow realizes any named transformation
         ├─ KernelTransformationConeData: enhanced representative and chosen dg cone
         │  └─ normalizationData: feeds the generic endpoint transport
         ├─ FourierMukai.CounitKernelData: adjunction-counit specialization
         │  ├─ ordinary kernel arrow conv Q P ⟶ O_Δ whose transform is the counit
         │  │  (conv Q P represents Φ_Q ⋙ Φ_P diagrammatically; Huybrechts writes P ∘ Q)
         │  └─ toConeData: choose a closed representative and dg cone in any enhancement
         │     └─ FourierMukai.CounitKernelConeData
         │        ├─ twistKernel presents the selected enhanced cone
         │        └─ exact kernel evaluation gives a source-natural counit triangle
         │           Φ_Q ⋙ Φ_P ⟶ 𝟭_Y ⟶ twist, pointwise distinguished
         ├─ AdjunctionUnitKernelData: definitional right-adjunction-unit specialization
         │  ├─ ordinary kernel arrow O_Δ ⟶ conv P Q whose transform is the unit
         │  └─ AdjunctionUnitKernelConeData
         │     ├─ exact kernel evaluation gives the unshifted unit triangle
         │     │  𝟭_X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟭_X)⟦1⟧,
         │     │  pointwise distinguished
         │     ├─ cotwist = cotwistCone⟦-1⟧, pointwise functor-category shift
         │     ├─ cotwistKernel: shifted enhanced cone presenting cotwist
         │     └─ inverse rotation gives
         │        cotwist ⟶ 𝟭_X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧,
         │        pointwise distinguished
         ├─ DualTwistKernelData: left-adjunction unit specialization after swapping C and C'
         │  └─ DualTwistKernelConeData reuses the unit/cotwist construction
         │     ├─ dualTwistKernel presents the pointwise shifted left-unit cone
         │     └─ dualTwist ⟶ 𝟭_Y ⟶ Φ_Q ⋙ Φ_P ⟶ dualTwist⟦1⟧,
         │        pointwise distinguished
         └─ DualCotwistKernelData: left-adjunction counit specialization after swapping C and C'
            └─ DualCotwistKernelConeData reuses the counit/twist construction
               ├─ dualCotwistKernel presents the selected left-counit cone
               └─ Φ_P ⋙ Φ_Q ⟶ 𝟭_X ⟶ dualCotwist ⟶ (Φ_P ⋙ Φ_Q)⟦1⟧,
                  pointwise distinguished
```

The kernel category is never required to *be* an `H⁰`: the comparison
equivalence of an `Enhancement` carries a geometric kernel category such as
`Dᵇ(Coh(Y × Y))` to the dg side, and the shift and exactness compatibility of
that comparison are instance hypotheses to be discharged by the realization.

## Deliberately open seams

1. `IsPretriangulated (DGFunctor C D)` is registered whenever `D` is
   pretriangulated (`DGFunctor.isPretriangulated_dgFunctor`), so a cone of dg
   functors is now a cone in a pretriangulated dg category rather than a
   pointwise construction.  The shift is `DGFunctor.shiftedFunctor`, whose
   action on a degree-`p` morphism carries the sign `(-1)^(n * p)`; the
   Leibniz rule forces it (`IsShiftBy.shiftMap_d`) and no constant sign works.

   The comparison data is now there too.  `IsShiftBy.shiftMap_compare` makes
   the objectwise comparison of two chosen shifts natural in every degree, and
   `IsShiftBy.comp'_shiftMap` says transport across a composite shift is the
   two transports in turn.  On top of those, `DGFunctor.shiftedFunctorAdd` and
   `DGFunctor.shiftedFunctorZero` are the two coherences -- shifting by `n`
   then `m` agrees with shifting by `n + m`, and shifting by `0` changes
   nothing -- each closed and invertible, so each is an isomorphism in the dg
   category of dg functors rather than merely a map.

   This family is now assembled into Mathlib's shift interface at the first
   ordinary categorical boundary where that statement makes sense:
   `DGFunctor.z0HasShift` is a `HasShift (Z0 (DGFunctor C D)) ℤ` instance.
   Its functors are `DGFunctor.z0ShiftFunctor`; they act on closed degree-zero
   transformations by `HomogeneousNatTrans.shiftedDegreeZero`, whose identity
   and composition laws are explicit.  Its zero and addition isomorphisms are
   `z0ShiftFunctorZeroIso` and `z0ShiftFunctorAddIso`.  The latter uses
   `shiftedFunctorAddInv` as its `hom`, because Mathlib points from the total
   shift to the iterated shift, and `shiftedFunctorAdd` as its `inv`.

   `DGFunctor.z0ShiftMkCore` proves all three standard coherences.  Its
   associativity law reuses `DGFunctor.shiftedFunctorAdd_assoc`: the inverse
   paths of the two categorical composites are exactly
   `shiftedFunctorAddAssocLeft` and `shiftedFunctorAddAssocRight`.  The two
   unit laws identify addition by zero with, respectively, the shifted inverse
   zero comparison and the inverse zero comparison on the shifted functor.
   Nothing parallel is installed on `H0 (DGFunctor C D)`: that category
   already receives the generic `H0.hasShift` from its pretriangulated dg
   structure, so a second instance would duplicate an existing abstraction.
   The dg-functor shift packaging seam is therefore closed.
2. The repository has strict dg functors, not the Morita quasi-functor and
   bimodule framework used by the spherical-functor theorem.  Consequently it
   does not claim that the two recorded equivalence conditions imply full
   sphericality.  `DGAdjunction.h0` now compares a dg adjunction with an
   ordinary one on `H⁰`, but the dg notion is the strict one: Anno--Logvinenko
   work with homotopy adjunctions of bimodules, and no comparison with those
   exists.

   The conditions are no longer inert, though.  `DGFunctor.h0Equivalence`
   (`dg-enhancements-e10`) turns a quasi-equivalence into an equivalence on
   `H⁰`, so `twistH0Equivalence` and `cotwistConeH0Equivalence` make the twist
   and the unshifted cotwist cone autoequivalences of `H⁰`.
   The conventional dg functors are now named `dualTwistFunctor` and
   `cotwistFunctor`.  The functor equality
   `DGFunctor.shiftedFunctor_h0_eq` and its natural-isomorphism wrapper compare
   `H⁰(F[n])` with `H⁰(F) ⋙ [n]`; the reusable
   `shiftedFunctorH0Equivalence` transports ordinary equivalences through that
   comparison.  Consequently `cotwistH0Equivalence` spends the recorded
   unshifted condition on the actual `[-1]` cotwist.  It does not infer a dg
   quasi-equivalence or triangulatedness.  This is the first
   categorical invertibility statement about a twist here; everything earlier
   was numerical, on `K₀`, or a construction with no invertibility attached.
   Exactness is separate, and now supplied: `DGFunctor.PreservesShifts` and
   `PreservesChosenCones` are instantiated for a cone functor whenever its two
   ends carry them, so `twistH0IsTriangulated` makes `H⁰` of the twist a
   triangulated functor.  The shift half of that is free for every dg functor
   (`DGFunctor.preservesShifts`), so `twistPreservesShifts` and
   `cotwistConePreservesShifts` take no arguments and `twistH0IsTriangulated`
   asks only for the two `PreservesChosenCones` witnesses.  Together with
   `twistH0Equivalence` above, that makes the twist an exact autoequivalence --
   which is still not sphericality, since that needs all four Anno--Logvinenko
   conditions and the Morita framework the first paragraph rules out.
3. `CategoryTheory/Shift/FunctorCategory.lean` now supplies the pointwise
   shift on a functor category, and `Functor.ExactFamily` is now built on that
   canonical structure: it extends Mathlib's `F.CommShift ℤ` and adds only
   pointwise triangulatedness.  The former `FamilyCommShift` record, its
   separately stored evaluated comparisons, and its manual naturality field
   have been removed.

   The bifunctor projection is coherent at the data level, not only at the
   level of comparison maps.  `Functor.CommShift₂.firstFamilyCommShift` and
   `secondFamilyCommShift` assemble the two functor-valued `CommShift`
   structures explicitly from Mathlib's `CommShift₂`; they are not global
   instances.  After composition with the strict evaluation comparison,
   `firstFamilyEvaluationCommShift_eq` and
   `secondFamilyEvaluationCommShift_eq` identify them with the partial
   structures already selected by `CommShift₂`.  Thus `ExactBifunctor`
   still retains the Koszul compatibility between its two variables, while
   its two `ExactFamily` projections transport triangulatedness across an
   equality of the complete `CommShift` data.  Evaluation of
   `ExactFamily.mapTriangle` is consequently proved against Mathlib's
   ordinary `mapTriangle`; no parallel triangle-map interface remains.  This
   seam is closed.
4. `EvaluationData.functor` is the generic `RHom(E,-) ⊗ E` dg functor and
   `EvaluationData.evaluation` its degree-zero transformation to the identity,
   both in `Algebra/Homology/DGCategory/Copower.lean`.  They are built on
   `IsCopowerOf`, which states the tensoring the way `IsShiftBy` states the
   shift -- by its universal property, as data plus a bijectivity condition --
   because `HomologicalComplex.HasTensor` does not synthesize for the
   `ℤ`-indexed shape at the pin, so there is no tensor product of complexes to
   build the object with.  `HasCopower K X` and `HasCopowers C` now package
   mere existence in Mathlib's `HasLimit` style: the classes contain no
   preferred object, while `copowerData` makes a noncomputable selection for
   consumers.  The narrower `HasEvaluationData E` is exactly the capability
   needed here, and follows automatically from `HasCopowers C`.

   This choice is coherent rather than merely available.  The canonical
   comparison between two copowers is closed and composes strictly, so any two
   `EvaluationData E` choices determine a canonical isomorphism
   `EvaluationData.compareIso` in `Z⁰ (DGFunctor C C)`.  The theorem
   `compare_comp_evaluation` says that this isomorphism commutes strictly with
   their evaluation transformations.  Thus later consumers may depend on the
   existence capability without treating a selected evaluation family as
   mathematically significant.  Moreover,
   `DGFunctor.PreservesChosenCones.ofIso` transports strong cone preservation
   across any such dg-functor isomorphism, so the cone-preservation hypothesis
   used for exactness is independent of the selected evaluation data.

   The functor is not inert.  `evaluation_isClosed` gives the transformation
   objectwise cones, so `EvaluationData.TwistConeData` is the Seidel--Thomas
   twist `T_E = Cone(RHom(E,-) ⊗ E ⟶ id)` of an *object*, and its
   `twistTriangleFunctor` is a functor `H⁰ C ⥤ Triangle (H⁰ C)` with every
   value distinguished.  This is a second twist, not a duplicate of the
   adjunction one: `CounitConeData.twist` is the cone of an adjunction counit,
   this one is attached to a single object with no adjunction in sight.  The
   two agree when `RHom(E,-)` and `- ⊗ E` are the adjoint pair of a spherical
   functor out of `Perf(k)`, which is exactly what cannot be stated here.

   `twistH0IsTriangulated` makes `H⁰(T_E)` a triangulated functor on one
   hypothesis: that `RHom(E,-) ⊗ E` preserves chosen cones.  The shift half is
   free.  `DGFunctor.preservesShifts` holds for *every* dg functor, because a
   shift element is a closed two-sided invertible element (`IsShiftBy.inv`,
   `hom_inv`, `inv_hom`) and a dg functor preserves composition and identities.
   That retires the shift half of every exactness hypothesis in this tree, not
   just the object twist's.

   The cone half stays open, and for a structural reason worth recording:
   `PreservesChosenCones` asks that maps *into* the cone split, while
   `IsCopowerOf` is a *mapping-out* property -- it controls degree-`p` morphisms
   out of `V.obj X` and says nothing about maps in.  So it does not follow from
   the universal property the copower is given by, and a cone, unlike a shift,
   is not an invertible element that functoriality carries over.

   What is open is *concrete existence*: no dg category in the repository yet
   supplies a `HasCopowers` instance.  The generic existence/choice interface
   and its independence theorem are closed, as is choice-independence of the
   cone-preservation capability.  The comparison seam is closed at both
   dg-functor and full H⁰-triangle levels.  `IsConeOf.isoOfStrictSquare` lifts
   endpoint isomorphisms in a strict square,
   `ConeData.triangleIsoOfStrictSquare` carries the result to a natural
   isomorphism of triangle functors, and
   `EvaluationData.TwistConeData.twistTriangleIsoOfEvaluation` applies it to
   the evaluation square while preserving the original same-evaluation
   `twistTriangleIso` wrapper.  These comparisons commute with all three
   triangle components, are
   identities on one choice, and compose coherently.  No theorem relates the
   object twist to a spherical object: that comparison needs `Perf(k)` as a dg
   category, which the repository does not have, so nothing here calls `E`
   spherical or claims `T_E` is an autoequivalence.
5. `KernelTransformationData` now owns the reusable statement that an ordinary
   kernel arrow realizes a named natural transformation between functors in
   supplied endpoint presentations.  `KernelTransformationConeData` owns its
   noncanonical enhanced representative and cone, while
   `KernelConeNormalizationData` owns transport to literal endpoints and first
   map.  `CounitKernelData` and `CounitKernelConeData` retain their public
   contracts as equivalent adjunction-counit presentations, with inverse
   adapters and simp round trips to those interfaces.
   In particular, `CounitKernelData.arrow` and its exact transform equation are
   supplied.
   Once they are available, `Z0.toH0_full` and pretriangulated cone existence
   choose a noncanonical closed representative and dg cone in any enhancement;
   forgetting those choices recovers the original ordinary datum.  The strong
   hypothesis `E.kernelTransform.Full` is one sufficient abstract constructor,
   not a theorem proved here.  Producing the ordinary arrow geometrically still
   needs convolution, the diagonal unit kernel, the adjunction trace, and proof
   that its transform is the counit.  Given those supplied data,
   `CounitKernelConeData.counitTriangleInSource` specializes the generic
   normalization interface:
   Mathlib's triangle transport identifies the raw enhanced-cone triangle with
   a source-natural triangle whose first two vertices are literally
   `Φ_Q ⋙ Φ_P` and `𝟭 Y`, and whose first map is literally the
   adjunction counit.  Every value is distinguished under the existing exactness
   hypotheses.  This is not a distinguished triangle in the functor category,
   does not make the twist exact or an autoequivalence, and does not make the
   selected enhancement representative or cone canonical.  `CommShift` and
   `IsTriangulated` for the enhancement comparison remain supplied where these
   pointwise distinguished triangles are consumed.  The right-adjunction unit
   kernel is now the second generic consumer: `AdjunctionUnitKernelData`
   realizes `O_Δ ⟶ P ⋆ Q`, and its enhanced form normalizes the unshifted
   triangle `𝟭_X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟭_X)⟦1⟧`.
   `AdjunctionUnitKernelConeData.cotwist` then uses the pointwise
   functor-category shift and `cotwistTriangleInSource` inverse-rotates the
   family to `cotwist ⟶ 𝟭_X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧`.  This is still only a
   choice-dependent ordinary functor and a pointwise distinguished family.
   The generic normalization root now also transports a shifted enhanced cone
   through the enhancement and kernel-family `CommShift` comparisons.
   Specializing at `-1` gives `cotwistKernel`, an explicit kernel whose
   transform is naturally isomorphic to the cotwist, and hence proves only
   that the cotwist is a kernel functor.
   The left-adjunction unit is now a third consumer:
   `DualTwistKernelData` swaps the two correspondences and reuses
   `LeftAdjointKernelData.toRightAdjointKernelData`, so its enhanced form names
   the kernel-presented dual twist and the pointwise distinguished family
   `dualTwist ⟶ 𝟭_Y ⟶ Φ_Q ⋙ Φ_P ⟶ dualTwist⟦1⟧` without a second
   cone or normalization construction.  The corresponding left-adjunction
   counit is a fourth consumer: `DualCotwistKernelData` performs the same swap
   through the generic counit/twist interface, names the selected cone kernel,
   and exposes
   `Φ_P ⋙ Φ_Q ⟶ 𝟭_X ⟶ dualCotwist ⟶ (Φ_P ⋙ Φ_Q)⟦1⟧` pointwise,
   again without new cone machinery.  Pointwise distinguishedness cannot
   supply `CommShift` or `IsTriangulated` for either shifted cone functor, and
   no comparison with the corresponding dg-adjunction cone is available;
   those later seams remain explicit.
6. No theorem currently identifies a categorical spherical object with a
   spherical functor from `Perf(k)`, or derives the Seidel--Thomas
   autoequivalence from `SerreFunctor.IsSphericalObject`.
7. The Enriques classification layer supplies categorical spherical objects
   and paper-level Fourier--Mukai conclusions through explicit seams.  It does
   not yet provide the dg evaluation functor, counit kernel arrow, or a
   concrete Enriques surface needed to instantiate this tree.

These seams should remain below any Enriques-specific adapter.  In particular,
an Enriques leaf must consume a generic evaluation/counit-kernel theorem; it
must not add a second paper-specific cone or spherical-twist structure.
