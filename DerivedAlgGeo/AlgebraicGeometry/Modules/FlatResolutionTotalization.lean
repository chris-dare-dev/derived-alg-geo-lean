/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FlatGenerators
import DerivedAlgGeo.Algebra.Homology.HomologicalBicomplex
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.SingleZeroTotal
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Normalized free-Yoneda bicomplex augmentation and its total complex

For every scheme `X` and integer-indexed cochain complex of `X.Modules`, the
free-Yoneda left resolution gives a bicomplex whose natural augmentation
normalizes to a flipped single-zero bicomplex and is a quasi-isomorphism in
each resolution-direction row. Its integer-extended direct-sum total complex
has terms flat over the identity, and the signed total of the normalized
target is naturally the input complex.
The final augmentation is a constructed map, without an unbounded total
quasi-isomorphism or K-flatness claim.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.normalizedBicomplexAugmentation` is the
  natural map to the flipped single-zero bicomplex.
* `AlgebraicGeometry.Scheme.Modules.freeYonedaSheafCoproductTotalTargetIso`
  identifies the total of the original target with the input.
* `AlgebraicGeometry.Scheme.Modules.freeYonedaSheafCoproductTotalAugmentation`
  composes the normalized total map with the signed target comparison.

## Main results

* `AlgebraicGeometry.Scheme.Modules.normalizedBicomplexAugmentation_row_quasiIso`
  proves each resolution-direction row is a quasi-isomorphism.

## Implementation notes

The normalized map composes the existing row augmentation with
`HomologicalComplex₂.singleExtendMapFlipIso` at the image degree zero.
Its row maps stay quasi-isomorphisms because the second map is an isomorphism.
`HomologicalComplex₂.singleZeroFlipTotalNatIso` supplies the signed total
comparison. The original target type is retained for downstream consumers.

## References

The construction uses Mathlib's `ComplexShape.Embedding.extendFunctor`,
`HomologicalComplex₂.totalFunctor`, and the repository's natural
single-extension, mapped-single/flip, and signed single-zero comparisons.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Extend the resolution degree of the free-Yoneda bicomplex from nonnegative chain
degrees to nonpositive integer cochain degrees, then include the flat terms into all
module sheaves. -/
noncomputable def freeYonedaSheafCoproductResolutionBicomplexUpInt
    (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤
      HomologicalComplex₂ X.Modules (ComplexShape.up ℤ) (ComplexShape.up ℤ) := by
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  let E := ι.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor X.Modules
  letI : E.PreservesZeroMorphisms := by infer_instance
  exact freeYonedaSheafCoproductResolutionBicomplex X ⋙
    E.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The direct-sum total complex of the functorial free-Yoneda flat-resolution bicomplex.
The augmentation to the input is constructed below; its quasi-isomorphism
and K-flatness remain separate obligations. -/
noncomputable def freeYonedaSheafCoproductTotalComplexFunctor (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  freeYonedaSheafCoproductResolutionBicomplexUpInt X ⋙
    HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Apply the natural augmentation of each free-Yoneda left resolution in the
resolution direction. The target retains the input complex in resolution degree
zero after extending that direction to integer degrees. This is a bicomplex
map; its totalization is treated below, without a quasi-isomorphism claim. -/
noncomputable def freeYonedaSheafCoproductResolutionBicomplexAugmentation
    (X : Scheme.{u}) :
    freeYonedaSheafCoproductResolutionBicomplexUpInt X ⟶
      ((ChainComplex.single₀ X.Modules) ⋙
        ComplexShape.embeddingDownNat.extendFunctor X.Modules).mapHomologicalComplex
          (ComplexShape.up ℤ) := by
  let Λ := freeYonedaSheafCoproductReducedLeftResolution X
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  let E := ComplexShape.embeddingDownNat.extendFunctor X.Modules
  letI : Λ.chainComplexFunctor.PreservesZeroMorphisms :=
    ⟨fun M N => freeYonedaSheafCoproductReducedLeftResolution_chainComplexMap_zero X⟩
  letI : (ι.mapHomologicalComplex (ComplexShape.down ℕ)).PreservesZeroMorphisms :=
    by infer_instance
  letI : E.PreservesZeroMorphisms := by infer_instance
  letI : ((Λ.chainComplexFunctor ⋙
      ι.mapHomologicalComplex (ComplexShape.down ℕ)) ⋙ E).PreservesZeroMorphisms :=
    by infer_instance
  letI : ((ChainComplex.single₀ X.Modules) ⋙ E).PreservesZeroMorphisms :=
    by infer_instance
  exact NatTrans.mapHomologicalComplex
    (Functor.whiskerRight (Λ.chainComplexAugmentationNatTrans ι) E)
      (ComplexShape.up ℤ)

/-- In each input degree, the bicomplex augmentation is a quasi-isomorphism in
the resolution direction. Mathlib's embedding extension preserves the generic
left-resolution quasi-isomorphism; this does not imply that its unbounded
direct-sum totalization is a quasi-isomorphism. -/
theorem freeYonedaSheafCoproductResolutionBicomplexAugmentation_row_quasiIso
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (p : ℤ) :
    QuasiIso (((freeYonedaSheafCoproductResolutionBicomplexAugmentation X).app K).f p) := by
  let Λ := freeYonedaSheafCoproductReducedLeftResolution X
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  haveI : QuasiIso (Λ.chainComplexAugmentation ι (K.X p)) :=
    Λ.chainComplexAugmentation_quasiIso ι (K.X p)
  change QuasiIso (HomologicalComplex.extendMap
    (Λ.chainComplexAugmentation ι (K.X p)) ComplexShape.embeddingDownNat)
  infer_instance

/-- Normalize the free-Yoneda augmentation before totalization: the embedding
of the resolution degree sends source degree zero to integer degree zero, and
`HomologicalComplex₂.singleExtendMapFlipIso` identifies its target with the
flipped single-zero bicomplex. -/
noncomputable def normalizedBicomplexAugmentation (X : Scheme.{u}) :
    freeYonedaSheafCoproductResolutionBicomplexUpInt X ⟶
      HomologicalComplex.single (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0 ⋙
        HomologicalComplex₂.flipFunctor X.Modules (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) :=
  freeYonedaSheafCoproductResolutionBicomplexAugmentation X ≫
    (HomologicalComplex₂.singleExtendMapFlipIso
      (C := X.Modules) (ComplexShape.up ℤ) ComplexShape.embeddingDownNat 0 0 rfl).hom

/-- Each row of the normalized augmentation remains a quasi-isomorphism:
the original row theorem is followed by a component of a bicomplex
isomorphism. This rowwise fact does not assert anything about unbounded
direct-sum totalization. -/
theorem normalizedBicomplexAugmentation_row_quasiIso (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (p : ℤ) :
    QuasiIso (((normalizedBicomplexAugmentation X).app K).f p) := by
  haveI := freeYonedaSheafCoproductResolutionBicomplexAugmentation_row_quasiIso X K p
  dsimp [normalizedBicomplexAugmentation]
  infer_instance

/-- Totalize the natural bicomplex augmentation. The target is the total
complex of a bicomplex concentrated in resolution degree zero; a natural
identification with the input is constructed below, while quasi-isomorphism
of this unbounded total map remains open. -/
noncomputable def freeYonedaSheafCoproductTotalAugmentationToSingleZero
    (X : Scheme.{u}) :
    freeYonedaSheafCoproductTotalComplexFunctor X ⟶
      (((ChainComplex.single₀ X.Modules) ⋙
        ComplexShape.embeddingDownNat.extendFunctor X.Modules).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  Functor.whiskerRight (freeYonedaSheafCoproductResolutionBicomplexAugmentation X)
    (HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The original resolution-degree-zero total target is naturally the input.
First normalize the bicomplex target, then apply the signed flipped
single-zero total comparison. -/
noncomputable def freeYonedaSheafCoproductTotalTargetIso (X : Scheme.{u}) :
    (((ChainComplex.single₀ X.Modules) ⋙
        ComplexShape.embeddingDownNat.extendFunctor X.Modules).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex X.Modules ℤ) :=
  (CategoryTheory.Functor.isoWhiskerRight
    (HomologicalComplex₂.singleExtendMapFlipIso
      (C := X.Modules) (ComplexShape.up ℤ) ComplexShape.embeddingDownNat 0 0 rfl) _).trans
    (HomologicalComplex₂.singleZeroFlipTotalNatIso (C := X.Modules))

/-- The natural augmentation of the total free-Yoneda resolution into the
input complex. It totalizes the normalized bicomplex map and follows it by
the signed single-zero comparison. No total quasi-isomorphism is inferred
from the rowwise theorem. -/
noncomputable def freeYonedaSheafCoproductTotalAugmentation (X : Scheme.{u}) :
    freeYonedaSheafCoproductTotalComplexFunctor X ⟶
      𝟭 (CochainComplex X.Modules ℤ) :=
  Functor.whiskerRight (normalizedBicomplexAugmentation X)
      (HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ≫
    (HomologicalComplex₂.singleZeroFlipTotalNatIso (C := X.Modules)).hom

private theorem isFlatOverId_of_iso (X : Scheme.{u}) {M N : X.Modules}
    (e : M ≅ N) (hM : IsFlatOver (𝟙 X) M) : IsFlatOver (𝟙 X) N := by
  apply (isFlatOverId_iff_stalkwiseFlat X N).2
  intro x
  have h := ((isFlatOverId_iff_stalkwiseFlat X M).1 hM) x
  letI : Module.Flat (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj M) := h
  exact Module.Flat.of_linearEquiv ((moduleStalkFunctor X x).mapIso e).symm.toLinearEquiv

private theorem isFlatOverId_of_isZero (X : Scheme.{u}) {M : X.Modules}
    (hM : IsZero M) : IsFlatOver (𝟙 X) M := by
  apply (isFlatOverId_iff_stalkwiseFlat X M).2
  intro x
  let F := moduleStalkFunctor X x
  letI : PreservesFiniteLimits F := moduleStalkFunctor_preservesFiniteLimits X x
  have hZ : IsZero (F.obj M) := F.map_isZero hM
  letI : Subsingleton (F.obj M) := ModuleCat.subsingleton_of_isZero hZ
  exact Module.Flat.of_retract
    (0 : (F.obj M) →ₗ[X.presheaf.stalk x] (X.presheaf.stalk x))
    (0 : (X.presheaf.stalk x) →ₗ[X.presheaf.stalk x] (F.obj M))
    (by ext z; exact Subsingleton.elim _ _)

private theorem isFlatOverId_coprod_small (X : Scheme.{u}) {I : Type}
    (G : I → X.Modules) (hG : ∀ i, IsFlatOver (𝟙 X) (G i)) :
    IsFlatOver (𝟙 X) (∐ G) := by
  let G' : ULift.{u} I → X.Modules := fun i => G i.down
  have hG' : ∀ i, IsFlatOver (𝟙 X) (G' i) := fun i => hG i.down
  have h : IsFlatOver (𝟙 X) (∐ G') := isFlatOverId_coprod X G' hG'
  let e : ∐ G' ≅ ∐ G := Sigma.reindex (Equiv.ulift : ULift.{u} I ≃ I) G
  exact isFlatOverId_of_iso X e h

private theorem resolutionBicomplexUpInt_obj_X_isFlatOverId
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (p q : ℤ) :
    IsFlatOver (𝟙 X)
      ((((freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj K).X p).X q) := by
  let C := ((freeYonedaSheafCoproductResolutionBicomplex X).obj K).X p
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  let D : ChainComplex X.Modules ℕ :=
    (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj C
  change IsFlatOver (𝟙 X) ((D.extend ComplexShape.embeddingDownNat).X q)
  by_cases h : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = q
  · obtain ⟨n, hn⟩ := h
    have hD : IsFlatOver (𝟙 X) (D.X n) := by
      change IsFlatOver (𝟙 X) (ι.obj (C.X n))
      exact (C.X n).property
    exact isFlatOverId_of_iso X
      (D.extendXIso ComplexShape.embeddingDownNat hn).symm hD
  · have hZ : IsZero ((D.extend ComplexShape.embeddingDownNat).X q) :=
      D.isZero_extend_X ComplexShape.embeddingDownNat q (fun n hn => h ⟨n, hn⟩)
    exact isFlatOverId_of_isZero X hZ

/-- Every term of the direct-sum total complex of the free-Yoneda resolution is flat
over the identity of the scheme. This termwise statement supplies no K-flatness claim. -/
theorem freeYonedaSheafCoproductTotalComplexFunctor_obj_X_isFlatOverId
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    IsFlatOver (𝟙 X) (((freeYonedaSheafCoproductTotalComplexFunctor X).obj K).X n) := by
  let B := (freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj K
  change IsFlatOver (𝟙 X) ((B.total (ComplexShape.up ℤ)).X n)
  change IsFlatOver (𝟙 X)
    (∐ (B.toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n))
  apply isFlatOverId_coprod_small X _
  intro i
  exact resolutionBicomplexUpInt_obj_X_isFlatOverId X K i.1.1 i.1.2

end AlgebraicGeometry.Scheme.Modules
