/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperExtension
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.PaperMatching
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalInduction
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.AdjacentExt

/-!
# Categorical assembly of the refined Enriques Torelli arguments

This file connects the paper-specific Enriques data to the three categorical
lanes used in the closing arguments of arXiv:1912.04332v2, Theorem 5.1, and
arXiv:2104.13610v2, Theorem 3.3.

1. Residual spherical/pseudoprojective classification determines a unique
   matching of exceptional blocks (`PaperMatching.lean`).
2. Extension in both directions proves equality of the matched block lengths,
   while the adjacent `k ⊕ k[-1]` Ext profile proves that every member of a
   block has one common shift.
3. Iterated one-object Fourier--Mukai extension, together with admissibility
   of the total exceptional parts, promotes the residual equivalence to an
   ambient kernel equivalence.

The functorial dg cone and its pointwise transform triangle now live below this
paper layer.  The remaining geometric seam in `OneStepExtensionCriterion` is
to realize the paper's kernel category as an `H⁰`, lift its actual kernel
morphism to that enhancement, and prove exactness of kernel evaluation.  No
ambient equivalence, length equality, or common-shift conclusion is accepted
as an extra axiom here: each is derived from its corresponding categorical
input.
-/

universe u t t'

open CategoryTheory CategoryTheory.Triangulated
open CategoryTheory.Triangulated.FourierMukai
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface.IsotropicCollection

open Scheme.Modules

attribute [local instance] residualComponent_isTriangulated

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [SmoothProperVariety.IsEnriquesSurface k Y C]
variable {D : Cohomology.FiniteCohomology k Y}
  {S : D.LinearConnectingSystem}
variable {T : IsotropicCollection (Y := Y) (C := C) D S}
variable {exceptional : T.ExceptionalityHypotheses}
  {semiorthogonal : T.SemiorthogonalityHypotheses}
variable {I : Type t} [Fintype I]

/-- The adjacent `k ⊕ k[-1]` Ext computations for the actual exceptional
blocks of an Enriques paper decomposition. -/
abbrev PaperAdjacentExtHypotheses
    (B : T.PaperBlockHypotheses exceptional semiorthogonal I) :=
  B.blocks.AdjacentExtHypotheses

section TwoSurfaces

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
variable {T₁ : IsotropicCollection (Y := Y₁) (C := C₁) D₁ S₁}
  {T₂ : IsotropicCollection (Y := Y₂) (C := C₂) D₂ S₂}
variable {exceptional₁ : T₁.ExceptionalityHypotheses}
  {exceptional₂ : T₂.ExceptionalityHypotheses}
  {semiorthogonal₁ : T₁.SemiorthogonalityHypotheses}
  {semiorthogonal₂ : T₂.SemiorthogonalityHypotheses}
variable {I : Type t} {J : Type t'} [Fintype I] [Fintype J]
variable {B₁ : T₁.PaperBlockHypotheses exceptional₁ semiorthogonal₁ I}
  {B₂ : T₂.PaperBlockHypotheses exceptional₂ semiorthogonal₂ J}

/-! ## Exact length and common-shift conclusions -/

/-- Prefix-by-prefix extension in both directions for two paper block
decompositions. -/
abbrev PaperBidirectionalPrefixHypotheses (e : I ≃ J) :=
  BidirectionalPrefixBlockEmbeddingHypotheses B₁.blocks B₂.blocks e

/-- Corresponding Enriques blocks have equal length, derived from the two
prefix extensions. -/
theorem PaperBidirectionalPrefixHypotheses.length_eq {e : I ≃ J}
    (A : PaperBidirectionalPrefixHypotheses (B₁ := B₁) (B₂ := B₂) e)
    (i : I) : B₁.blocks.length i = B₂.blocks.length (e i) :=
  BidirectionalPrefixBlockEmbeddingHypotheses.length_eq A i

namespace PaperIIProjectionClassificationData

variable {P₁ : T₁.PaperCategoryHypotheses exceptional₁ semiorthogonal₁}
  {P₂ : T₂.PaperCategoryHypotheses exceptional₂ semiorthogonal₂}
variable {Q₁ : T₁.PaperResidualProjectionData exceptional₁ semiorthogonal₁}
  {Q₂ : T₂.PaperResidualProjectionData exceptional₂ semiorthogonal₂}
variable (A₁ : T₁.PaperIIProjectionClassificationData P₁ B₁ Q₁)
  (A₂ : T₂.PaperIIProjectionClassificationData P₂ B₂ Q₂)
  (F : PaperResidualSerreEquivalence P₁ P₂)

/-- Bidirectional prefix extension indexed by the block matching forced by
the residual spherical/pseudoprojective classification. -/
abbrev MatchingPrefixHypotheses :=
  PaperBidirectionalPrefixHypotheses (B₁ := B₁) (B₂ := B₂)
    (A₁.matchingEquiv A₂ F)

/-- **Matched Paper II blocks have exactly equal length.**  Classification
determines the matching, and the two prefix extensions determine its exact
lengths. -/
theorem matchingEquiv_length_eq (L : A₁.MatchingPrefixHypotheses A₂ F)
    (i : I) :
    B₁.blocks.length i = B₂.blocks.length (A₁.matchingEquiv A₂ F i) :=
  PaperBidirectionalPrefixHypotheses.length_eq L i

end PaperIIProjectionClassificationData

/-- Memberwise images of two Enriques block decompositions, before adjacent
Ext rigidity identifies the shifts. -/
abbrev PaperMemberwiseBlockShiftHypotheses (e : I ≃ J)
    (length_eq : ∀ i, B₁.blocks.length i = B₂.blocks.length (e i))
    (G : DerivedCat Y₁ ⥤ DerivedCat Y₂) :=
  MemberwiseBlockShiftHypotheses B₁.blocks B₂.blocks e length_eq G

namespace PaperIIProjectionClassificationData

variable {P₁ : T₁.PaperCategoryHypotheses exceptional₁ semiorthogonal₁}
  {P₂ : T₂.PaperCategoryHypotheses exceptional₂ semiorthogonal₂}
variable {Q₁ : T₁.PaperResidualProjectionData exceptional₁ semiorthogonal₁}
  {Q₂ : T₂.PaperResidualProjectionData exceptional₂ semiorthogonal₂}
variable (A₁ : T₁.PaperIIProjectionClassificationData P₁ B₁ Q₁)
  (A₂ : T₂.PaperIIProjectionClassificationData P₂ B₂ Q₂)
  (F : PaperResidualSerreEquivalence P₁ P₂)
  (L : A₁.MatchingPrefixHypotheses A₂ F)

/-- Memberwise image data indexed by the classification-derived block
matching and its prefix-derived exact length equality. -/
abbrev MatchingMemberwiseShiftHypotheses (G : DerivedCat Y₁ ⥤ DerivedCat Y₂) :=
  PaperMemberwiseBlockShiftHypotheses (B₁ := B₁) (B₂ := B₂)
    (A₁.matchingEquiv A₂ F) (A₁.matchingEquiv_length_eq A₂ F L) G

end PaperIIProjectionClassificationData

namespace PaperMemberwiseBlockShiftHypotheses

variable {e : I ≃ J}
  {length_eq : ∀ i, B₁.blocks.length i = B₂.blocks.length (e i)}
  {G : DerivedCat Y₁ ⥤ DerivedCat Y₂}
variable [G.Additive] [G.Linear k] [G.CommShift ℤ]
variable [∀ n : ℤ, (shiftFunctor (DerivedCat Y₂) n).Linear k]
variable (M : PaperMemberwiseBlockShiftHypotheses
  (B₁ := B₁) (B₂ := B₂) e length_eq G)
  (A₁ : T₁.PaperAdjacentExtHypotheses B₁)
  (A₂ : T₂.PaperAdjacentExtHypotheses B₂)

/-- The common shift attached to a matched block. -/
noncomputable def commonShift (i : I) : ℤ :=
  M.shift i (B₁.blocks.firstIndex i)

include A₁ A₂

/-- Every member of a matched Enriques block carries its block's common
shift. -/
theorem shift_eq_common (hG : G.FullyFaithful) (i : I)
    (j : Fin (B₁.blocks.length i)) :
    M.shift i j = M.commonShift i :=
  M.shift_eq_first A₁ A₂ hG i j

/-- The memberwise image isomorphisms can therefore be expressed with one
shift per block, as required in Paper II, Theorem 3.3. -/
noncomputable def commonObjectIso (hG : G.FullyFaithful) (i : I)
    (j : Fin (B₁.blocks.length i)) :
    G.obj ((B₁.blocks.collection i).obj j) ≅
      ((B₂.blocks.collection (e i)).obj
        (Fin.cast (length_eq i) j))⟦M.commonShift i⟧ := by
  rw [← M.shift_eq_common A₁ A₂ hG i j]
  exact M.objectIso i j

end PaperMemberwiseBlockShiftHypotheses

/-! ## Finite Fourier--Mukai extension and ambient generation -/

variable {W : Type u} [Category W]
variable {corr : Correspondence (DerivedCat Y₁) (DerivedCat Y₂) W}
variable (R : ResidualKernelEquivalence B₁.blocks B₂.blocks corr)

/-- The finite extension sequence for the two actual Enriques exceptional
parts, including the admissibility data which certifies ambient generation. -/
abbrev PaperGeneratedExtensionSequenceHypotheses :=
  GeneratedBlockExtensionSequenceHypotheses B₁.blocks B₂.blocks corr R

namespace PaperGeneratedExtensionSequenceHypotheses

variable (A : PaperGeneratedExtensionSequenceHypotheses
  (B₁ := B₁) (B₂ := B₂) R)

/-- **Ambient extension conclusion of Paper I, Theorem 5.1, and Paper II,
Theorem 3.3.**

The final equivalence of the ambient derived categories is presented by the
last Fourier--Mukai kernel in the extension sequence. -/
noncomputable def toKernelEquivalence : KernelEquivalence corr :=
  GeneratedBlockExtensionSequenceHypotheses.toKernelEquivalence A

/-- The underlying promoted equivalence of ambient derived categories. -/
noncomputable def ambientEquivalence : DerivedCat Y₁ ≌ DerivedCat Y₂ :=
  A.toKernelEquivalence.equiv

/-- The final Fourier--Mukai transform is an equivalence of the ambient
derived categories. -/
theorem transform_isEquivalence :
    (corr.transform A.sequence.finalKernel).IsEquivalence :=
  A.sequence.finalTransform_isEquivalence
    A.toGeneratedExtensionSequenceData.sourceGenerates
    A.toGeneratedExtensionSequenceData.targetGenerates

end PaperGeneratedExtensionSequenceHypotheses

end TwoSurfaces

end AlgebraicGeometry.EnriquesSurface.IsotropicCollection
