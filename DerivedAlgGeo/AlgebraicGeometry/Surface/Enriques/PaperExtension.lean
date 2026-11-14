/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Effective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.DivisorSequence
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperBlocks
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Transport

/-!
# Mutation, curve chains, Ext computations, and extension for the Enriques papers

This is the geometric adapter for the mutation, curve-chain, Ext and extension
arguments of arXiv:1912.04332v2 (Paper I) and arXiv:2104.13610v2 (Paper II).

* proposition-valued admissibility produces an actual residual projection;
* the projection counit gives the paper's mutation triangle;
* an `A_n` chain of effective Cartier divisors records the `(-2)`-curve
  geometry of Paper II, Proposition 1.4;
* the line-bundle class formula supplies isomorphisms from the selected
  representatives to Cartier-prefix twists, whose exact sequences construct
  the successive distinguished triangles and block maps;
* self-Ext computations are separated from the Serre-shift and classification
  arguments, with constructors rebuilding the Paper I and Paper II theorem
  packages; and
* the closing aliases specialize the generic Fourier--Mukai extension result
  to the actual residual and ambient categories used here.

## Main definitions

* `PaperResidualAdmissibilityHypotheses` — supplied right admissibility of the residual
  component; `PaperResidualAdmissibilityHypotheses.projectionData` chooses the projection.
* `PaperBlockHypotheses.mutationTriangle` — the paper's objectwise mutation triangle, built
  from the projection counit.
* `MinusTwoCurveChain` — an `A_n` chain of effective Cartier divisors with the
  intersection matrix of `(-2)`-curves, and its step triangles
  `MinusTwoCurveChain.lineBundleStepTriangle`.
* `PaperCurveChainHypotheses` — the curve chains behind a block decomposition, with
  `PaperCurveChainHypotheses.projectionTriangles` the projection-chain triangle data they
  construct.
* `PaperIProjectionExtHypotheses`, `PaperIIProjectionExtHypotheses` — the Ext computations of
  Paper I and Paper II for the projected objects.
* `PaperResidualKernelEquivalence`, `PaperExceptionalBlockExtensionHypotheses` — the generic
  Fourier--Mukai extension notions specialized to two Enriques surfaces.

## Main results

* `MinusTwoCurveChain.lineBundleStepTriangle_distinguished` and
  `PaperCurveChainHypotheses.projectionTriangle_distinguished` — the divisor-chain step
  triangles, and their transports to the block representatives, are distinguished.
* `PaperCurveChainHypotheses.projectionIso` — Paper II, Remark 2.3(ii): every member of a
  block has the same residual projection as its first member.
* `PaperIIProjectionExtHypotheses.spherical_of_singleton` and
  `PaperIIProjectionExtHypotheses.pseudoprojective_of_longer` — the Ext and Serre
  computations make singleton projections spherical and longer-block projections
  pseudoprojective.
* `PaperIProjectionExtHypotheses.toProjectionClassificationData` and
  `PaperIIProjectionExtHypotheses.toProjectionClassificationData` — the classification
  packages of the two papers, assembled from the Ext computations.

## Implementation notes

The remaining geometric gaps stay visible. The current Cartier-divisor API
has no predicate saying that an effective divisor is an irreducible curve,
and `PaperCurveChainHypotheses` supplies residual orthogonality of each curve
quotient, while the triangles themselves are constructed rather than supplied.
The abstract dg cone and its pointwise transform triangle are functorial,
with `DGFunctor.HomogeneousNatTrans.ConeData` as the construction root and
`FourierMukai.CounitKernelConeData` as the adjunction-counit specialization.
Constructing the paper's extended Fourier--Mukai kernel requires the
geometric `H⁰` model, the paper's ordinary kernel morphism with its exact
counit-transform equation, an enhancement, and exactness of kernel
evaluation, none of which is constructed here; it is not silently identified
with the counit specialization. Its categorical consequences use the existing
kernel/adjunction roots directly.

## References

* arXiv:1912.04332v2 (Paper I).
* arXiv:2104.13610v2 (Paper II), Proposition 1.4, Lemma 1.9 and Remark 2.3(ii).

## Tags

Enriques surface, exceptional block, mutation, `(-2)`-curve, spherical object,
pseudoprojective object, Fourier--Mukai
-/

universe u t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
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
structure PaperResidualAdmissibilityHypotheses
    (exceptional : T.ExceptionalityHypotheses)
    (semiorthogonal : T.SemiorthogonalityHypotheses) : Prop where
  /-- The residual inclusion has a right adjoint. -/
  rightAdmissible :
    (T.residualComponent exceptional semiorthogonal).IsRightAdmissible

namespace PaperResidualAdmissibilityHypotheses

variable {T}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable (A : T.PaperResidualAdmissibilityHypotheses exceptional semiorthogonal)

/-- Choose the geometric residual projection from admissibility. -/
noncomputable def projectionData :
    T.PaperResidualProjectionData exceptional semiorthogonal :=
  RightProjectionData.ofIsRightAdmissible A.rightAdmissible

end PaperResidualAdmissibilityHypotheses

namespace PaperBlockHypotheses

variable {T}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable {I : Type t} [Fintype I]
variable (B : T.PaperBlockHypotheses exceptional semiorthogonal I)

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

end PaperBlockHypotheses

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

/-- Adding the next curve extends the prefix divisor by that curve. -/
theorem prefixDivisor_succ (j : ℕ) (hj : j < n) :
    A.prefixDivisor (j + 1) (by omega) =
      A.prefixDivisor j (by omega) + (A.curve ⟨j, hj⟩).divisor := by
  simp [prefixDivisor, Fin.sum_univ_castSucc]

/-- The source divisor in the normalized sequence for the next curve is the
preceding prefix. -/
theorem prefixDivisor_succ_sub (j : ℕ) (hj : j < n) :
    A.prefixDivisor (j + 1) (by omega) - (A.curve ⟨j, hj⟩).divisor =
      A.prefixDivisor j (by omega) := by
  rw [A.prefixDivisor_succ j hj]
  simp

/-- The canonical bounded-derived triangle for one step of the divisor
chain, after tensoring by an arbitrary base line bundle. Its first two
vertices are `L ⊗ O(prefix j)` and `L ⊗ O(prefix (j+1))`. -/
noncomputable def lineBundleStepTriangle (L : LineBundleData Y)
    (j : ℕ) (hj : j < n) : Triangle (DerivedCat Y) :=
  (A.curve ⟨j, hj⟩).cohLineBundleTwistBoundedTriangle L
    (A.prefixDivisor (j + 1) (by omega))

/-- A divisor-chain step triangle is distinguished. -/
theorem lineBundleStepTriangle_distinguished (L : LineBundleData Y)
    (j : ℕ) (hj : j < n) :
    A.lineBundleStepTriangle L j hj ∈ distTriang (DerivedCat Y) :=
  (A.curve ⟨j, hj⟩).cohLineBundleTwistBoundedTriangle_distinguished L
    (A.prefixDivisor (j + 1) (by omega))

/-- The first vertex of a divisor-chain step is the preceding prefix twist. -/
noncomputable def lineBundleStepTriangleObj₁Iso (L : LineBundleData Y)
    (j : ℕ) (hj : j < n) :
    (A.lineBundleStepTriangle L j hj).obj₁ ≅
      (L.tensor (CartierDivisor.lineBundleData
        (A.prefixDivisor j (by omega)))).boundedDerivedObject := by
  simpa only [lineBundleStepTriangle, A.prefixDivisor_succ_sub j hj] using
    (A.curve ⟨j, hj⟩).cohLineBundleTwistBoundedTriangleObj₁Iso L
      (A.prefixDivisor (j + 1) (by omega))

/-- The second vertex of a divisor-chain step is the extended prefix twist. -/
noncomputable def lineBundleStepTriangleObj₂Iso (L : LineBundleData Y)
    (j : ℕ) (hj : j < n) :
    (A.lineBundleStepTriangle L j hj).obj₂ ≅
      (L.tensor (CartierDivisor.lineBundleData
        (A.prefixDivisor (j + 1) (by omega)))).boundedDerivedObject :=
  (A.curve ⟨j, hj⟩).cohLineBundleTwistBoundedTriangleObj₂Iso L
    (A.prefixDivisor (j + 1) (by omega))

end MinusTwoCurveChain

/-- The geometric data behind a block decomposition in Paper II,
Proposition 1.4 and Lemma 1.9.

`memberClass` is the formula
`L_{ij} = L_{i1} ⊗ O(R_{i1}+⋯+R_{i,j-1})` in the Picard group.
The Picard formula proves that each supplied line-bundle representative is
isomorphic to the corresponding tensor product by `O(prefix j)`; the adapter
chooses such isomorphisms. The divisor-derived triangle is therefore
constructed below rather than stored. Only residual orthogonality of its
quotient remains supplied. -/
structure PaperCurveChainHypotheses
    {exceptional : T.ExceptionalityHypotheses}
    {semiorthogonal : T.SemiorthogonalityHypotheses}
    {I : Type t} [Fintype I]
    (B : T.PaperBlockHypotheses exceptional semiorthogonal I) where
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
  /-- The quotient in each canonical divisor-chain step is killed by the
  residual projection. This is the remaining geometric input after the
  distinguished triangle itself has been constructed from the Cartier
  sequence. -/
  quotientOrthogonal : ∀ (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i),
    (T.residualComponent exceptional semiorthogonal).rightOrthogonal
      (((chain i).lineBundleStepTriangle
        (T.bundles (B.firstBundleIndex i)) j (by omega)).obj₃)

namespace PaperCurveChainHypotheses

variable {T}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable {I : Type t} [Fintype I]
variable {B : T.PaperBlockHypotheses exceptional semiorthogonal I}
variable (A : T.PaperCurveChainHypotheses B)

/-- The Picard-class formula chooses an isomorphism from each selected bundle
to the first bundle tensored by the corresponding Cartier prefix. -/
noncomputable def memberLineIso (i : I) (j : Fin (B.blocks.length i)) :
    (T.bundles (B.bundleIndex ⟨i, j⟩)).line ≅
      ((T.bundles (B.firstBundleIndex i)).tensor
        (CartierDivisor.lineBundleData
          ((A.chain i).prefixDivisor j.1 (by omega)))).line :=
  Classical.choice
    ((LineBundleData.toPic_eq_iff _ _).1 (by
      simpa using A.memberClass i j))

/-- The member-line isomorphism lifted to bounded coherent derived objects. -/
noncomputable def memberBoundedDerivedIso
    (i : I) (j : Fin (B.blocks.length i)) :
    (T.bundles (B.bundleIndex ⟨i, j⟩)).boundedDerivedObject ≅
      ((T.bundles (B.firstBundleIndex i)).tensor
        (CartierDivisor.lineBundleData
          ((A.chain i).prefixDivisor j.1 (by omega)))).boundedDerivedObject :=
  ObjectProperty.isoMk
    (P := (DerivedCategory.TStructure.t (C := Coh Y)).bounded)
    (LineBundleData.derivedObjectIso (A.memberLineIso i j))

/-- Identify a block member with its canonical tensor-by-prefix derived
object, combining the block presentation and the Picard-class formula. -/
noncomputable def blockMemberTensorIso
    (i : I) (j : Fin (B.blocks.length i)) :
    (B.blocks.collection i).obj j ≅
      ((T.bundles (B.firstBundleIndex i)).tensor
        (CartierDivisor.lineBundleData
          ((A.chain i).prefixDivisor j.1 (by omega)))).boundedDerivedObject :=
  B.bundleIso ⟨i, j⟩ ≪≫ A.memberBoundedDerivedIso i j

/-- The canonical divisor-derived triangle underlying the `j`-th step of a
paper block. -/
noncomputable def stepTriangle (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) : Triangle (DerivedCat Y) :=
  (A.chain i).lineBundleStepTriangle
    (T.bundles (B.firstBundleIndex i)) j (by omega)

/-- Identify the source of the canonical step triangle with the `j`-th block
member. -/
noncomputable def stepTriangleObj₁Iso (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) :
    (A.stepTriangle i j hj).obj₁ ≅
      (B.blocks.collection i).obj ⟨j, by omega⟩ :=
  (A.chain i).lineBundleStepTriangleObj₁Iso
      (T.bundles (B.firstBundleIndex i)) j (by omega) ≪≫
    (A.blockMemberTensorIso i ⟨j, by omega⟩).symm

/-- Identify the target of the canonical step triangle with the next block
member. -/
noncomputable def stepTriangleObj₂Iso (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) :
    (A.stepTriangle i j hj).obj₂ ≅
      (B.blocks.collection i).obj ⟨j + 1, hj⟩ :=
  (A.chain i).lineBundleStepTriangleObj₂Iso
      (T.bundles (B.firstBundleIndex i)) j (by omega) ≪≫
    (A.blockMemberTensorIso i ⟨j + 1, hj⟩).symm

/-- The canonical divisor triangle transported to the paper's chosen block
representatives. Its first morphism is the required successive block map. -/
noncomputable def projectionTriangle (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) : Triangle (DerivedCat Y) where
  obj₁ := (B.blocks.collection i).obj ⟨j, by omega⟩
  obj₂ := (B.blocks.collection i).obj ⟨j + 1, hj⟩
  obj₃ := (A.stepTriangle i j hj).obj₃
  mor₁ := (A.stepTriangleObj₁Iso i j hj).inv ≫
    (A.stepTriangle i j hj).mor₁ ≫
      (A.stepTriangleObj₂Iso i j hj).hom
  mor₂ := (A.stepTriangleObj₂Iso i j hj).inv ≫
    (A.stepTriangle i j hj).mor₂
  mor₃ := (A.stepTriangle i j hj).mor₃ ≫
    (A.stepTriangleObj₁Iso i j hj).hom⟦(1 : ℤ)⟧'

/-- Canonical comparison from the divisor step triangle to its transport onto
the selected block representatives. -/
noncomputable def stepTriangleIso (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) :
    A.stepTriangle i j hj ≅ A.projectionTriangle i j hj := by
  dsimp only [projectionTriangle]
  refine Triangle.isoMk _ _
    (A.stepTriangleObj₁Iso i j hj)
    (A.stepTriangleObj₂Iso i j hj) (Iso.refl _) ?_ ?_ ?_
  · simp only [Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.id_comp]

/-- The transported paper-block step triangle is distinguished. -/
theorem projectionTriangle_distinguished (i : I) (j : ℕ)
    (hj : j + 1 < B.blocks.length i) :
    A.projectionTriangle i j hj ∈ distTriang (DerivedCat Y) :=
  isomorphic_distinguished _
    ((A.chain i).lineBundleStepTriangle_distinguished
      (T.bundles (B.firstBundleIndex i)) j (by omega)) _
    (A.stepTriangleIso i j hj).symm

/-- Construct the complete projection-chain triangle data from Cartier
sequences, Picard-class identifications, and the supplied quotient
orthogonality. -/
noncomputable def projectionTriangles :
    OrthogonalExceptionalBlocks.ProjectionChainData B.blocks
      (T.residualComponent exceptional semiorthogonal) where
  stepMap i j hj := (A.projectionTriangle i j hj).mor₁
  cone i j hj := (A.projectionTriangle i j hj).obj₃
  toCone i j hj := (A.projectionTriangle i j hj).mor₂
  connecting i j hj := (A.projectionTriangle i j hj).mor₃
  distinguished i j hj := A.projectionTriangle_distinguished i j hj
  cone_mem i j hj := A.quotientOrthogonal i j hj

/-- **Paper II, Remark 2.3(ii): every member of a block has the same residual
projection as its first member.**

This is proved, not supplied: it follows from the successive divisor
triangles and their residual-orthogonality. -/
noncomputable def projectionIso
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal)
    (i : I) (j : Fin (B.blocks.length i)) :
    B.projectedObject Q i ≅ Q.project ((B.blocks.collection i).obj j) :=
  OrthogonalExceptionalBlocks.ProjectionChainData.projectionIso
    B.blocks (T.residualComponent exceptional semiorthogonal) Q
      A.projectionTriangles
      (T.residualComponent_isTriangulated exceptional semiorthogonal) i j

end PaperCurveChainHypotheses

/-! ## Ext computations and classification constructors -/

/-- Paper I's Ext computations for the ten projected objects, separated from
their Serre-shift identifications and the completeness argument. -/
structure PaperIProjectionExtHypotheses
    {exceptional : T.ExceptionalityHypotheses}
    {semiorthogonal : T.SemiorthogonalityHypotheses}
    (B : T.PaperBlockHypotheses exceptional semiorthogonal (Fin 10))
    (Q : T.PaperResidualProjectionData exceptional semiorthogonal) : Prop where
  /-- Every projected object has the 3-spherical self-Ext profile. -/
  selfExt : ∀ i, SphericalExtProfile (k := k) 3 (B.projectedObject Q i)
  /-- Cross-Ext groups between distinct projections vanish in all degrees. -/
  pairwise : ∀ {i j}, i ≠ j →
    IsGradedOrthogonal (B.projectedObject Q i) (B.projectedObject Q j)

namespace PaperIProjectionExtHypotheses

variable {T}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable {P : T.PaperCategoryHypotheses exceptional semiorthogonal}
variable {B : T.PaperBlockHypotheses exceptional semiorthogonal (Fin 10)}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIProjectionExtHypotheses B Q)

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

end PaperIProjectionExtHypotheses

/-- Paper II's block-sensitive self-Ext and cross-Ext computations. -/
structure PaperIIProjectionExtHypotheses
    {exceptional : T.ExceptionalityHypotheses}
    {semiorthogonal : T.SemiorthogonalityHypotheses}
    (P : T.PaperCategoryHypotheses exceptional semiorthogonal)
    {I : Type t} [Fintype I]
    (B : T.PaperBlockHypotheses exceptional semiorthogonal I)
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

namespace PaperIIProjectionExtHypotheses

variable {T}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable {P : T.PaperCategoryHypotheses exceptional semiorthogonal}
variable {I : Type t} [Fintype I]
variable {B : T.PaperBlockHypotheses exceptional semiorthogonal I}
variable {Q : T.PaperResidualProjectionData exceptional semiorthogonal}
variable (A : T.PaperIIProjectionExtHypotheses P B Q)

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

end PaperIIProjectionExtHypotheses

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
variable {exceptional₁ : T₁.ExceptionalityHypotheses}
  {exceptional₂ : T₂.ExceptionalityHypotheses}
  {semiorthogonal₁ : T₁.SemiorthogonalityHypotheses}
  {semiorthogonal₂ : T₂.SemiorthogonalityHypotheses}
variable {I : Type t} {J : Type t} [Fintype I] [Fintype J]
variable (B₁ : T₁.PaperBlockHypotheses exceptional₁ semiorthogonal₁ I)
  (B₂ : T₂.PaperBlockHypotheses exceptional₂ semiorthogonal₂ J)
variable {W W' : Type u} [Category W] [Category W']

/-- A Fourier--Mukai-type equivalence between the residual categories of two
Enriques block decompositions.  The block residuals are identified with the
neutral residual components `residualComponent` by `PaperBlockHypotheses.residual_eq`. -/
abbrev PaperResidualKernelEquivalence
    (corr : Correspondence (DerivedCat Y₁) (DerivedCat Y₂) W) :=
  ResidualKernelEquivalence B₁.blocks B₂.blocks corr

/-- The conclusion of the papers' finite extension argument, specialized to
the exceptional blocks of two Enriques surfaces.  Its
`ambientEquivalence` is the promoted equivalence of ambient derived
categories, and its `objectIso` uses one common shift on every member of a
block. -/
abbrev PaperExceptionalBlockExtensionHypotheses
    (corr : Correspondence (DerivedCat Y₁) (DerivedCat Y₂) W)
    (corr' : Correspondence (DerivedCat Y₂) (DerivedCat Y₁) W')
    (R : T₁.PaperResidualKernelEquivalence T₂ B₁ B₂ corr) :=
  ExceptionalBlockExtensionHypotheses B₁.blocks B₂.blocks corr corr' R

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
