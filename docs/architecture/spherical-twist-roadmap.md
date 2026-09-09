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
         └─ canonical inr/inl transformations and boundary equation

DGAdjunction
├─ closed unit and counit
├─ dg triangle identities
└─ CounitConeData
   └─ twist candidate Cone(LR ⟶ id)

EnhancedAdjunctionCones
├─ twist and dual-cotwist cones
├─ unshifted cones underlying dual twist and cotwist
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

1. There is no functorial shift of dg-category objects yet.  Objectwise
   `IsShiftBy` witnesses exist, but the shifted comparison maps needed for the
   full Anno--Logvinenko definition are not packaged as dg functors.
2. The repository has strict dg functors, not the Morita quasi-functor and
   bimodule framework used by the spherical-functor theorem.  Consequently it
   does not claim that the two recorded equivalence conditions imply full
   sphericality.
3. No generic `RHom(E,-) ⊗ E` dg functor or evaluation transformation has been
   constructed.  The current monoidal/exact-bifunctor roots are the intended
   lower dependency, but closed monoidal/Hom-complex representability is still
   missing.
4. `CounitKernelConeData.arrow` is supplied.  Producing it geometrically needs
   convolution, the diagonal unit kernel, adjunction trace, and proof that the
   transformed arrow is the counit.  The enhancement of the kernel category,
   with `CommShift` and `IsTriangulated` for its comparison functor, is
   likewise supplied.
5. No theorem currently identifies a categorical spherical object with a
   spherical functor from `Perf(k)`, or derives the Seidel--Thomas
   autoequivalence from `SerreFunctor.IsSphericalObject`.
6. The Enriques classification layer supplies categorical spherical objects
   and paper-level Fourier--Mukai conclusions through explicit seams.  It does
   not yet provide the dg evaluation functor, counit kernel arrow, or a
   concrete Enriques surface needed to instantiate this tree.

These seams should remain below any Enriques-specific adapter.  In particular,
an Enriques leaf must consume a generic evaluation/counit-kernel theorem; it
must not add a second paper-specific cone or spherical-twist structure.
