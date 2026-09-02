/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Effective
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperBlocks
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Transport

/-!
# Mutation, curve chains, Ext computations, and extension for the Enriques papers

This is the geometric adapter for the next layer of
arXiv:1912.04332v2 and arXiv:2104.13610v2.

* proposition-valued admissibility now produces an actual residual projection;
* the projection counit gives the paper's mutation triangle;
* an `A_n` chain of effective Cartier divisors records the `(-2)`-curve
  geometry of Paper II, Proposition 1.4;
* the line-bundle class formula and successive distinguished triangles are
  packaged together, and the generic projection-chain theorem proves that
  every member of a longer block has the same residual projection;
* self-Ext computations are separated from the Serre-shift and classification
  arguments, with constructors rebuilding the Paper I and Paper II theorem
  packages; and
* the closing aliases specialize the generic Fourier--Mukai extension result
  to the actual residual and ambient categories used here.

The remaining geometric gaps stay visible.  In particular, the current
Cartier-divisor API has no predicate saying that an effective divisor is an
irreducible curve, and the derived-category API does not yet turn the twisted
short exact divisor sequence into the required distinguished triangle
functorially.  Those facts are supplied in `PaperCurveChainData`; once
supplied, the same-projection result below is proved.  Likewise, constructing
the extended Fourier--Mukai kernel from a cone waits on #855, #853, and #854,
while its categorical consequences use the existing kernel/adjunction roots
immediately.
-/

universe u t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.ObjectProperty CategoryTheory.SerreFunctor
open CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry.DerivedCategory
open scoped BigOperators

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme Scheme.Modules IntersectionTheory.Number

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [SmoothProperVariety.IsEnriquesSurface k Y C]
variable {D : Cohomology.FiniteCohomology k Y} {S : D.LinearConnectingSystem}
variable (T : IsotropicCollection (Y := Y) (C := C) D S)

attribute [local instance] residualComponent_isTriangulated

/-! ## Projection existence and mutation triangles -/

/-- The geometric admissibility input for the residual component.

The papers obtain this from an admissible semiorthogonal decomposition.  It is
kept supplied here because the current Enriques construction proves only that
the residual right orthogonal is triangulated. -/
structure PaperResidualAdmissibilityData
    (exceptional : T.ExceptionalityData)
    (semiorthogonal : T.SemiorthogonalityData) : Prop where
  /-- The residual inclusion has a right adjoint. -/
  rightAdmissible :
    (T.residualComponent exceptional semiorthogonal).IsRightAdmissible

namespace PaperResidualAdmissibilityData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable (A : T.PaperResidualAdmissibilityData exceptional semiorthogonal)

/-- Choose the geometric residual projection from admissibility. -/
noncomputable def projectionData :
    T.PaperResidualProjectionData exceptional semiorthogonal :=
  RightProjectionData.ofIsRightAdmissible A.rightAdmissible

end PaperResidualAdmissibilityData

namespace PaperBlockData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {I : Type t} [Fintype I]
variable (B : T.PaperBlockData exceptional semiorthogonal I)

/-- The paper's objectwise mutation triangle

`S_i ⟶ L_{i1} ⟶ L_{\mathcal K}(L_{i1})`.

The first term is definitionally the residual projection object and the first
map is its adjunction counit. -/
noncomputable def mutationTriangle
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) (i : I) :
    Q.CounitTriangle (B.blocks.firstObject i) :=
  Q.counitTriangle
    (T.residualComponent_isTriangulated exceptional semiorthogonal)
    (B.blocks.firstObject i)

end PaperBlockData

/-! ## `(-2)`-curve chains -/

/-- A supplied `A_n` chain of effective Cartier divisors with the numerical
intersection matrix of `(-2)`-curves.

Effectivity and the intersection matrix are genuine repository notions.
Irreducibility/reducedness are not yet expressible, so the word "curve" in
the declaration name records the intended geometric realization rather than
an unavailable extra predicate. -/
structure MinusTwoCurveChain (n : ℕ) where
  /-- The effective Cartier divisors in the chain. -/
  curve : Fin n → EffectiveCartierDivisor (X := Y)
  /-- Every member has self-intersection `-2`. -/
  selfIntersection : ∀ i,
    T.intersection.picardIntersectionNumber
      ![CartierDivisor.toPic (curve i).divisor,
        CartierDivisor.toPic (curve i).divisor] = -2
  /-- Consecutive members intersect once. -/
  adjacentIntersection : ∀ (i : ℕ) (hi : i + 1 < n),
    T.intersection.picardIntersectionNumber
      ![CartierDivisor.toPic (curve ⟨i, by omega⟩).divisor,
        CartierDivisor.toPic (curve ⟨i + 1, hi⟩).divisor] = 1
  /-- Non-consecutive members are disjoint numerically. -/
  nonAdjacentIntersection : ∀ (i j : Fin n),
    (i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) →
      T.intersection.picardIntersectionNumber
        ![CartierDivisor.toPic (curve i).divisor,
          CartierDivisor.toPic (curve j).divisor] = 0

namespace MinusTwoCurveChain

variable {T} {n : ℕ} (A : T.MinusTwoCurveChain n)

/-- The sum of the first `j` divisors in the chain. -/
noncomputable def prefixDivisor (j : ℕ) (hj : j ≤ n) : CartierDivisor Y :=
  ∑ r : Fin j, (A.curve ⟨r.1, by omega⟩).divisor

@[simp]
theorem prefixDivisor_zero : A.prefixDivisor 0 (Nat.zero_le n) = 0 := by
  simp [prefixDivisor]

end MinusTwoCurveChain

/-- The geometric data behind a block decomposition in Paper II,
Proposition 1.4 and Lemma 1.9.

`memberClass` is the formula
`L_{ij} = L_{i1} ⊗ O(R_{i1}+⋯+R_{i,j-1})` in the Picard group.
`projectionTriangles` is the derived exact-sequence consequence needed below;
it is separate because the current derived embedding does not yet construct
that triangle from `EffectiveCartierDivisor.cohTwistSequence` automatically. -/
structure PaperCurveChainData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    {I : Type t} [Fintype I]
    (B : T.PaperBlockData exceptional semiorthogonal I) where
  /-- A chain of length one less than each exceptional block. -/
  chain : ∀ i, T.MinusTwoCurveChain (B.blocks.length i - 1)
  /-- The Picard-class formula for every member of every block. -/
  memberClass : ∀ (i : I) (j : Fin (B.blocks.length i)),
    (T.bundles (B.bundleIndex ⟨i, j⟩)).toPic =
      (T.bundles (B.firstBundleIndex i)).toPic *
        CartierDivisor.toPic
          ((chain i).prefixDivisor j.1 (by
            have := j.2
            omega))
  /-- Successive line bundles fit into distinguished triangles whose quotient
  terms are killed by the residual projection. -/
  projectionTriangles :
    OrthogonalExceptionalBlocks.ProjectionChainData B.blocks
      (T.residualComponent exceptional semiorthogonal)

namespace PaperCurveChainData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {I : Type t} [Fintype I]
variable {B : T.PaperBlockData exceptional semiorthogonal I}
variable (A : T.PaperCurveChainData B)

/-- **Paper II, Remark 2.3(ii): every member of a block has the same residual
projection as its first member.**

Unlike the earlier supplied statement seam, this is proved from the
successive divisor triangles and their residual-orthogonality. -/
noncomputable def projectionIso
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal)
    (i : I) (j : Fin (B.blocks.length i)) :
    B.projectedObject Q i ≅ Q.project ((B.blocks.collection i).obj j) :=
  OrthogonalExceptionalBlocks.ProjectionChainData.projectionIso
    B.blocks (T.residualComponent exceptional semiorthogonal) Q
      A.projectionTriangles
      (T.residualComponent_isTriangulated exceptional semiorthogonal) i j

end PaperCurveChainData

/-! ## Ext computations and classification constructors -/

/-- Paper I's Ext computations for the ten projected objects, separated from
their Serre-shift identifications and the completeness argument. -/
structure PaperIProjectionExtData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (B : T.PaperBlockData exceptional semiorthogonal (Fin 10))
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) : Prop where
  /-- Every projected object has the 3-spherical self-Ext profile. -/
  selfExt : ∀ i, SphericalExtProfile (k := k) 3 (B.projectedObject Q i)
  /-- Cross-Ext groups between distinct projections vanish in all degrees. -/
  pairwise : ∀ {i j}, i ≠ j →
    IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j)

namespace PaperIProjectionExtData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {P : T.PaperCategoryData exceptional semiorthogonal}
variable {B : T.PaperBlockData exceptional semiorthogonal (Fin 10)}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIProjectionExtData B Q)

include A

/-- Assemble Paper I's projection classification package from the Ext
calculation, the Serre action, and the remaining completeness theorem. -/
theorem toProjectionClassificationData
    (singleton : ∀ i, B.blocks.length i = 1)
    (serreShift : ∀ i, Nonempty
      (P.residualSerre.serre.S.obj (B.projectedObject Q i) ≅
        (B.projectedObject Q i)⟦(3 : ℤ)⟧))
    (complete : ∀ E : T.ResidualCategory exceptional semiorthogonal,
      IsSphericalObject P.residualSerre.serre 3 E ↔
        ∃ i, IsShiftOf E (B.projectedObject Q i)) :
    T.PaperIProjectionClassificationData P B Q where
  singleton := singleton
  spherical i := (A.selfExt i).toIsSphericalObject
    P.residualSerre.serre (serreShift i)
  pairwise_orthogonal := A.pairwise
  complete := complete

end PaperIProjectionExtData

/-- Paper II's block-sensitive self-Ext and cross-Ext computations. -/
structure PaperIIProjectionExtData
    {exceptional : T.ExceptionalityData}
    {semiorthogonal : T.SemiorthogonalityData}
    (P : T.PaperCategoryData exceptional semiorthogonal)
    {I : Type t} [Fintype I]
    (B : T.PaperBlockData exceptional semiorthogonal I)
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) : Prop where
  /-- Singleton blocks have the spherical Ext profile. -/
  sphericalExt : ∀ i, B.blocks.length i = 1 →
    SphericalExtProfile (k := k) 3 (B.projectedObject Q i)
  /-- Longer blocks have the pseudoprojective Ext profile. -/
  pseudoprojectiveExt : ∀ i, 2 ≤ B.blocks.length i →
    PseudoprojectiveExtProfile (k := k) 3 (B.projectedObject Q i)
  /-- The common Serre-shift computation. -/
  serreShift : ∀ i, Nonempty
    (P.residualSerre.serre.S.obj (B.projectedObject Q i) ≅
      (B.projectedObject Q i)⟦(3 : ℤ)⟧)
  /-- Cross-Ext groups between distinct blocks vanish in every degree. -/
  pairwise : ∀ {i j}, i ≠ j →
    IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j)

namespace PaperIIProjectionExtData

variable {T}
variable {exceptional : T.ExceptionalityData}
  {semiorthogonal : T.SemiorthogonalityData}
variable {P : T.PaperCategoryData exceptional semiorthogonal}
variable {I : Type t} [Fintype I]
variable {B : T.PaperBlockData exceptional semiorthogonal I}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIIProjectionExtData P B Q)

include A

/-- The Ext and Serre computations make a singleton projection spherical. -/
theorem spherical_of_singleton (i : I) (hi : B.blocks.length i = 1) :
    IsSphericalObject P.residualSerre.serre 3 (B.projectedObject Q i) :=
  (A.sphericalExt i hi).toIsSphericalObject
    P.residualSerre.serre (A.serreShift i)

/-- The Ext and Serre computations make a longer-block projection
pseudoprojective. -/
theorem pseudoprojective_of_longer (i : I) (hi : 2 ≤ B.blocks.length i) :
    IsPseudoprojectiveObject P.residualSerre.serre 3
      (B.projectedObject Q i) :=
  (A.pseudoprojectiveExt i hi).toIsPseudoprojectiveObject
    P.residualSerre.serre (A.serreShift i)

/-- Assemble Paper II's full classification package after supplying only the
two global completeness statements. -/
theorem toProjectionClassificationData
    (sphericalComplete :
      ∀ E : T.ResidualCategory exceptional semiorthogonal,
        IsSphericalObject P.residualSerre.serre 3 E ↔
          ∃ i, B.blocks.length i = 1 ∧
            IsShiftOf E (B.projectedObject Q i))
    (pseudoprojectiveComplete :
      ∀ E : T.ResidualCategory exceptional semiorthogonal,
        IsPseudoprojectiveObject P.residualSerre.serre 3 E ↔
          ∃ i, 2 ≤ B.blocks.length i ∧
            IsShiftOf E (B.projectedObject Q i)) :
    T.PaperIIProjectionClassificationData P B Q where
  spherical_of_singleton := A.spherical_of_singleton
  pseudoprojective_of_longer := A.pseudoprojective_of_longer
  pairwise_orthogonal := A.pairwise
  spherical_complete := sphericalComplete
  pseudoprojective_complete := pseudoprojectiveComplete

end PaperIIProjectionExtData

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection

/-! ## Fourier--Mukai extension between two Enriques surfaces -/

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme.Modules

variable {k : Type u} [Field k]
variable {Y₁ Y₂ : Scheme.{u}}
  [Y₁.Over (Spec (CommRingCat.of k))]
  [Y₂.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y₁] [IsSmoothProperVariety k Y₂]
variable {C₁ : SmoothProperVariety.CanonicalSheafData k Y₁ 2}
  {C₂ : SmoothProperVariety.CanonicalSheafData k Y₂ 2}
  [SmoothProperVariety.IsEnriquesSurface k Y₁ C₁]
  [SmoothProperVariety.IsEnriquesSurface k Y₂ C₂]
variable {D₁ : Cohomology.FiniteCohomology k Y₁}
  {D₂ : Cohomology.FiniteCohomology k Y₂}
  {S₁ : D₁.LinearConnectingSystem} {S₂ : D₂.LinearConnectingSystem}
variable (T₁ : IsotropicCollection (Y := Y₁) (C := C₁) D₁ S₁)
  (T₂ : IsotropicCollection (Y := Y₂) (C := C₂) D₂ S₂)
variable {exceptional₁ : T₁.ExceptionalityData}
  {exceptional₂ : T₂.ExceptionalityData}
  {semiorthogonal₁ : T₁.SemiorthogonalityData}
  {semiorthogonal₂ : T₂.SemiorthogonalityData}
variable {I : Type t} {J : Type t} [Fintype I] [Fintype J]
variable (B₁ : T₁.PaperBlockData exceptional₁ semiorthogonal₁ I)
  (B₂ : T₂.PaperBlockData exceptional₂ semiorthogonal₂ J)
variable {W W' : Type u} [Category W] [Category W']

/-- A Fourier--Mukai-type equivalence between the residual categories of two
Enriques block decompositions.  The block residuals are identified with the
previously constructed neutral residual components by `PaperBlockData.residual_eq`. -/
abbrev PaperResidualKernelEquivalence
    (corr : Correspondence (DerivedCat Y₁) (DerivedCat Y₂) W) :=
  ResidualKernelEquivalence B₁.blocks B₂.blocks corr

/-- The conclusion of the papers' finite extension argument, specialized to
the exceptional blocks of two Enriques surfaces.  Its
`ambientEquivalence` is the promoted equivalence of ambient derived
categories, and its `objectIso` uses one common shift on every member of a
block. -/
abbrev PaperExceptionalBlockExtensionData
    (corr : Correspondence (DerivedCat Y₁) (DerivedCat Y₂) W)
    (corr' : Correspondence (DerivedCat Y₂) (DerivedCat Y₁) W')
    (R : T₁.PaperResidualKernelEquivalence T₂ B₁ B₂ corr) :=
  ExceptionalBlockExtensionData B₁.blocks B₂.blocks corr corr' R

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
