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
   │  └─ IsConeOf.Morphism with the shift-free `fst` square
   │     └─ ConePresentation category, no pretriangulated instance needed
   └─ HomogeneousNatTrans.ConeData
         ├─ objectwise cone choices
         ├─ assembled cone DGFunctor
         ├─ canonical inr/inl transformations and boundary equation
         ├─ fst / snd: the cone projections, graded-natural in degrees 1 and 0
         ├─ isConeOf: a cone in the dg category DGFunctor C D itself, so the
         │  twist candidate is a cone OF FUNCTORS, the form in which
         │  Anno--Logvinenko state SR ⟶ Id_B ⟶ T
         └─ triangleFunctor: H⁰ C ⥤ Triangle (H⁰ D), every value distinguished;
            the third square is the connecting map, carried by IsConeOf.Morphism
            ├─ triangleNatTrans: natural in a STRICT square of closed
            │  degree-zero transformations; the cone lifts are natural on the
            │  nose.  The homotopy-coherent case needs uniqueness of the lift
            │  up to homotopy, which the repository does not have.
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

EvaluationData E
├─ functor = RHom(E,-) ⊗ E, evaluation : functor ⟶ id, closed in degree zero
└─ TwistConeData: the object twist T_E = Cone(evaluation), with its triangle
   functor H⁰ C ⥤ Triangle (H⁰ C), every value distinguished, and H⁰(T_E)
   triangulated as soon as RHom(E,-) ⊗ E preserves chosen cones (shifts are
   free for every dg functor).
   No adjunction, no invertibility, no sphericality.

EnhancedAdjunctionCones
├─ twist and dual-cotwist cones
├─ the twist is EXACT on H⁰ (twistH0IsTriangulated), as soon as S and R preserve
│  shifts and chosen cones.  A cone functor preserves both when its two ends do;
│  the cone half is the 3-by-3 lemma, whose proof is block diagonal in the four
│  coordinates of the two splittings rather than merely triangular.
├─ unshifted cones underlying dual twist and cotwist
├─ the four triangles as functors on H⁰, every value distinguished, each first
│  map the corresponding unit or counit.  The dual twist and the cotwist are
│  the INVERSE ROTATIONS of their unshifted cone triangles: invRotate applies
│  the ⟦-1⟧ shift and reorders in one step, and the first vertex is the value
│  of the dg shifted cone functor on the nose (DGFunctor.shiftedFunctor_h0_obj).
│  The unshifted forms are kept, since TwistCotwistEquivalenceConditions is
│  stated against the unshifted cone functors.  No sphericality, and no relation
│  among the four.
└─ TwistCotwistEquivalenceConditions

Enhancement W (kernel category W ≃ H⁰ of a pretriangulated dg category)
└─ coneTriangleFunctor: dg cones read in W through the comparison equivalence
   └─ FourierMukai.KernelCone: pointwise and source-natural transform triangles
      └─ FourierMukai.CounitKernelConeData
         ├─ convolution kernel conv Q P, the kernel of Φ_Q ⋙ Φ_P (diagrammatic;
         │  Huybrechts writes P ∘ Q)
         ├─ closed dg arrow between the enhancement's lifts of conv Q P and O_Δ
         ├─ equality identifying its transform with the adjunction counit
         └─ dg cone kernel
            └─ exact kernel evaluation gives pointwise distinguished twist triangles
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

   What is still missing is the *associativity* coherence between the two
   `shiftedFunctorAdd` isomorphisms for a triple `n, m, k`, and any statement
   assembling the family into a `HasShift`-style structure.  Neither is needed
   by the triangles below, which is why this slice stopped here.
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
   and the unshifted cotwist cone autoequivalences of `H⁰`.  That is the first
   categorical invertibility statement about a twist here; everything earlier
   was numerical, on `K₀`, or a construction with no invertibility attached.
   Exactness is separate, and now supplied: `DGFunctor.PreservesShifts` and
   `PreservesChosenCones` are instantiated for a cone functor whenever its two
   ends carry them, so `twistH0IsTriangulated` makes `H⁰` of the twist a
   triangulated functor.  The shift half of that is free for every dg functor
   (`DGFunctor.preservesShifts`), so the `PreservesShifts` arguments the
   adjunction-side declarations still take can be filled in by any caller.  Together with the equivalence above that is an exact
   autoequivalence -- which is still not sphericality, since that needs all
   four Anno--Logvinenko conditions and the Morita framework the first
   paragraph rules out.
3. `CategoryTheory/Shift/FunctorCategory.lean` now supplies the pointwise
   shift on a functor category, which is what `Functor.ExactFamily` should be
   built on.  That rewiring is still open, and it is not an API-only change:
   `ExactBifunctor` records triangulatedness against the shift structure it
   chose, while the family needs it against that choice composed with the
   strict comparison for evaluation, so the transport needs a lemma comparing
   the two `mapTriangle`s.
4. `EvaluationData.functor` is the generic `RHom(E,-) ⊗ E` dg functor and
   `EvaluationData.evaluation` its degree-zero transformation to the identity,
   both in `Algebra/Homology/DGCategory/Copower.lean`.  They are built on
   `IsCopowerOf`, which states the tensoring the way `IsShiftBy` states the
   shift -- by its universal property, as data plus a bijectivity condition --
   because `HomologicalComplex.HasTensor` does not synthesize for the
   `ℤ`-indexed shape at the pin, so there is no tensor product of complexes to
   build the object with.

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

   What is open is *existence*.  Nothing constructs a copower, so nothing
   produces an `EvaluationData`; a dg category with enough copowers has to
   supply one, exactly as `IsPretriangulated` supplies cone and shift choices.
   And no theorem relates the object twist to a spherical object: that
   comparison needs `Perf(k)` as a dg category, which the repository does not
   have, so nothing here calls `E` spherical or claims `T_E` is invertible.
5. `CounitKernelConeData.arrow` is supplied.  Producing it geometrically needs
   convolution, the diagonal unit kernel, adjunction trace, and proof that the
   transformed arrow is the counit.  The enhancement of the kernel category,
   with `CommShift` and `IsTriangulated` for its comparison functor, is
   likewise supplied.
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
