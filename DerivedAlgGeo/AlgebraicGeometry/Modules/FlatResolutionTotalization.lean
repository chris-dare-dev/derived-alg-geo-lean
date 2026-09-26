/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.FlatGenerators
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Total complex of the free-Yoneda flat-resolution bicomplex

The objectwise left resolution gives a bicomplex of flat module sheaves. We include its
resolution direction into the integers and form Mathlib's direct-sum total complex in
`X.Modules`. Every term of this total complex is flat over the identity. Its comparison
with the input and K-flatness remain separate obligations.
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
Its comparison with the input and K-flatness remain separate obligations. -/
noncomputable def freeYonedaSheafCoproductTotalComplexFunctor (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  freeYonedaSheafCoproductResolutionBicomplexUpInt X ⋙
    HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

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
