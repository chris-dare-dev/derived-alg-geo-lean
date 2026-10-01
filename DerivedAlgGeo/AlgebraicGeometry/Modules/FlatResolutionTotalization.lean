/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.FlatGenerators
import DerivedAlgGeo.Algebra.Homology.Embedding.CochainComplex
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits
import DerivedAlgGeo.Algebra.Homology.TotalComplex
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
The final augmentation is a quasi-isomorphism for arbitrary inputs. K-flatness
remains a separate obligation.
For every strictly bounded-above input, termwise support and the nonpositive
resolution degree make its total augmentation a quasi-isomorphism. This
includes every canonical good truncation.

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
* `freeYonedaSheafCoproductTotalAugmentation_eq_toSingleZero_comp_targetIso`
  identifies the normalized total map with the earlier total-to-single-zero map
  followed by the target isomorphism.
* `quasiIso_freeYonedaSheafCoproductTotalAugmentation_of_isStrictlyLE` proves the
  augmentation is a quasi-isomorphism for strictly bounded-above inputs.
* `quasiIso_freeYonedaSheafCoproductTotalAugmentation_truncLE` specializes
  this result to each canonical good truncation.
* `AlgebraicGeometry.Scheme.Modules.quasiIso_freeYonedaSheafCoproductTotalAugmentation`
  passes the stagewise quasi-isomorphisms through the good-truncation colimit
  for arbitrary inputs.

## Implementation notes

The normalized map composes the existing row augmentation with
`HomologicalComplex₂.singleExtendMapFlipIso` at the image degree zero.
Its row maps stay quasi-isomorphisms because the second map is an isomorphism.
`HomologicalComplex₂.singleZeroFlipTotalNatIso` supplies the signed total
comparison. The original target type is retained for downstream consumers.
For an input strictly supported at `c`, both bicomplexes vanish in outer
degrees above `c` and inner degrees above zero. Reduced left resolution
preserves zero terms, so the four-bound total-map criterion applies on each
diagonal.
The source and target good-truncation cocones are colimiting. Exact filtered
colimits preserve stagewise quasi-isomorphisms, and naturality transports the
result from the chosen colimit to the original input.

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
The augmentation to the input and its quasi-isomorphism are proved below;
K-flatness remains a separate obligation. -/
noncomputable def freeYonedaSheafCoproductTotalComplexFunctor (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  freeYonedaSheafCoproductResolutionBicomplexUpInt X ⋙
    HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The literal total free-Yoneda resolution of the canonical good-truncation
tower has a colimiting cocone. The mapped bicomplex cocone is colimiting
degreewise, and direct-sum totalization preserves its colimit. This does not
assert that the total augmentation is a quasi-isomorphism. -/
noncomputable def isColimitFreeYonedaSheafCoproductTotalTruncLETowerCocone
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    IsColimit
      ((freeYonedaSheafCoproductTotalComplexFunctor X).mapCocone
        (CochainComplex.truncLETowerCocone K)) := by
  let Λ := freeYonedaSheafCoproductReducedLeftResolution X
  let ι := ObjectProperty.ι (fun M : X.Modules => IsFlatOver (𝟙 X) M)
  let E := ι.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor X.Modules
  haveI : Λ.chainComplexFunctor.PreservesZeroMorphisms :=
    ⟨fun M N => freeYonedaSheafCoproductReducedLeftResolution_chainComplexMap_zero X⟩
  haveI : E.PreservesZeroMorphisms := by infer_instance
  haveI : (Λ.chainComplexFunctor ⋙ E).PreservesZeroMorphisms := by infer_instance
  have hB := CochainComplex.isColimitMapTruncLETowerCocone
    (Λ.chainComplexFunctor ⋙ E) K
  change IsColimit
    ((freeYonedaSheafCoproductResolutionBicomplexUpInt X).mapCocone
      (CochainComplex.truncLETowerCocone K)) at hB
  have hT := isColimitOfPreserves
    (HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) hB
  change IsColimit
    ((freeYonedaSheafCoproductTotalComplexFunctor X).mapCocone
      (CochainComplex.truncLETowerCocone K)) at hT
  exact hT

/-- Apply the natural augmentation of each free-Yoneda left resolution in the
resolution direction. The target retains the input complex in resolution degree
zero after extending that direction to integer degrees. Its totalization and
comparison with the input are constructed below. -/
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
complex of a bicomplex concentrated in resolution degree zero. A natural
identification with the input is constructed below and compared with this map. -/
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

/-- The original resolution-degree-zero total target is naturally the input,
by specializing the generic extended-single total isomorphism at the
resolution-degree embedding and degree zero. -/
noncomputable def freeYonedaSheafCoproductTotalTargetIso (X : Scheme.{u}) :
    (((ChainComplex.single₀ X.Modules) ⋙
        ComplexShape.embeddingDownNat.extendFunctor X.Modules).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        HomologicalComplex₂.totalFunctor X.Modules (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex X.Modules ℤ) :=
  HomologicalComplex₂.singleExtendMapTotalIso
    (C := X.Modules) ComplexShape.embeddingDownNat 0 rfl

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

/-- The earlier and normalized augmentations identify the single-zero target
at different stages. After unfolding the generic comparison and distributing
right whiskering over composition, the two maps are definitionally equal;
downstream proofs can switch presentations by rewriting. -/
theorem freeYonedaSheafCoproductTotalAugmentation_eq_toSingleZero_comp_targetIso (X : Scheme.{u}) :
    freeYonedaSheafCoproductTotalAugmentation X =
      freeYonedaSheafCoproductTotalAugmentationToSingleZero X ≫
        (freeYonedaSheafCoproductTotalTargetIso X).hom := by
  simp only [freeYonedaSheafCoproductTotalAugmentation,
    normalizedBicomplexAugmentation,
    freeYonedaSheafCoproductTotalAugmentationToSingleZero,
    freeYonedaSheafCoproductTotalTargetIso,
    HomologicalComplex₂.singleExtendMapTotalIso,
    Functor.isoWhiskerRight_hom, Iso.trans_hom, Functor.whiskerRight_comp]
  rfl

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

section BoundedAugmentation

variable (X : Scheme.{u}) (M : CochainComplex X.Modules ℤ) (c : ℤ)

private theorem isZero_resolutionBicomplexUpInt_X_of_isStrictlyLE_of_lt [M.IsStrictlyLE c]
    (p : ℤ) (hp : c < p) :
    IsZero (((freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj M).X p) := by
  let Λ := freeYonedaSheafCoproductReducedLeftResolution X
  letI : Λ.chainComplexFunctor.PreservesZeroMorphisms := ⟨fun A B =>
    freeYonedaSheafCoproductReducedLeftResolution_chainComplexMap_zero X⟩
  let ι := ObjectProperty.ι (fun N : X.Modules => IsFlatOver (𝟙 X) N)
  let E := ι.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor X.Modules
  letI : E.PreservesZeroMorphisms := by infer_instance
  have hM : IsZero (M.X p) :=
    CochainComplex.isZero_of_isStrictlyLE M c p hp
  have hΛ : IsZero (Λ.chainComplexFunctor.obj (M.X p)) :=
    Λ.chainComplexFunctor.map_isZero hM
  have hE : IsZero (E.obj (Λ.chainComplexFunctor.obj (M.X p))) :=
    E.map_isZero hΛ
  exact hE


private theorem isZero_resolutionBicomplexUpInt_inner_of_pos (p q : ℤ) (hq : 0 < q) :
    IsZero (((((freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj
      M).X p).X q)) := by
  let Λ := freeYonedaSheafCoproductReducedLeftResolution X
  let ι := ObjectProperty.ι (fun N : X.Modules => IsFlatOver (𝟙 X) N)
  let D := (ι.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Λ.chainComplexFunctor.obj (M.X p))
  change IsZero ((D.extend ComplexShape.embeddingDownNat).X q)
  exact CochainComplex.isZero_of_isStrictlyLE
    (D.extend ComplexShape.embeddingDownNat) 0 q (by omega)

private theorem isZero_singleZeroFlip_inner_of_ne (p q : ℤ) (hq : q ≠ 0) :
    IsZero ((((((HomologicalComplex.single
      (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0) ⋙
      HomologicalComplex₂.flipFunctor X.Modules (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj M).X p).X q)) := by
  change IsZero ((((HomologicalComplex.single
    (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0).obj M).X q).X p)
  exact (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) p).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M q hq)

private theorem isZero_singleZeroFlip_X_of_isStrictlyLE_of_lt [M.IsStrictlyLE c]
    (p q : ℤ) (hp : c < p) :
    IsZero ((((((HomologicalComplex.single
      (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0) ⋙
      HomologicalComplex₂.flipFunctor X.Modules (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj M).X p).X q)) := by
  have hM : IsZero (M.X p) :=
    CochainComplex.isZero_of_isStrictlyLE M c p hp
  change IsZero ((((HomologicalComplex.single
    (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0).obj M).X q).X p)
  by_cases hq : q = 0
  · subst q
    simpa only [HomologicalComplex.single_obj_X_self] using hM
  · exact (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) p).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M q hq)


private theorem isZero_resolutionBicomplexUpInt_diagonal_of_add_eq_of_lt
    (n p q : ℤ) (hn : p + q = n) (hp : p < n) :
    IsZero (((((freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj
      M).X p).X q)) := by
  exact isZero_resolutionBicomplexUpInt_inner_of_pos X M p q (by omega)

private theorem isZero_singleZeroFlip_diagonal_of_add_eq_of_lt
    (n p q : ℤ) (hn : p + q = n) (hp : p < n) :
    IsZero ((((((HomologicalComplex.single
      (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0) ⋙
      HomologicalComplex₂.flipFunctor X.Modules (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj M).X p).X q)) := by
  exact isZero_singleZeroFlip_inner_of_ne X M p q (by omega)

private theorem quasiIso_normalizedBicomplexAugmentation_totalMap_of_isStrictlyLE
    [M.IsStrictlyLE c] :
    QuasiIso (HomologicalComplex₂.total.map
      ((normalizedBicomplexAugmentation X).app M)
      (ComplexShape.up ℤ)) := by
  let K := (freeYonedaSheafCoproductResolutionBicomplexUpInt X).obj M
  let L := ((HomologicalComplex.single
      (CochainComplex X.Modules ℤ) (ComplexShape.up ℤ) 0) ⋙
      HomologicalComplex₂.flipFunctor X.Modules (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj M
  let f : K ⟶ L := (normalizedBicomplexAugmentation X).app M
  have hKLower : ∀ n p q : ℤ, p + q = n → p < n → IsZero ((K.X p).X q) := by
    intro n p q hpq hp
    exact isZero_resolutionBicomplexUpInt_diagonal_of_add_eq_of_lt X M n p q hpq hp
  have hKUpper : ∀ n p q : ℤ, p + q = n → c < p → IsZero ((K.X p).X q) := by
    intro n p q _ hp
    exact (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) q).map_isZero
      (isZero_resolutionBicomplexUpInt_X_of_isStrictlyLE_of_lt X M c p hp)
  have hLLower : ∀ n p q : ℤ, p + q = n → p < n → IsZero ((L.X p).X q) := by
    intro n p q hpq hp
    exact isZero_singleZeroFlip_diagonal_of_add_eq_of_lt X M n p q hpq hp
  have hLUpper : ∀ n p q : ℤ, p + q = n → c < p → IsZero ((L.X p).X q) := by
    intro n p q _ hp
    exact isZero_singleZeroFlip_X_of_isStrictlyLE_of_lt X M c p q hp
  exact HomologicalComplex₂.quasiIso_totalMap_of_four_diagonal_bounds_of_column_quasiIso
    f (fun n => n) (fun _ => c) (fun n => n) (fun _ => c)
    hKLower hKUpper hLLower hLUpper
    (normalizedBicomplexAugmentation_row_quasiIso X M)

/-- The free-Yoneda total augmentation is a quasi-isomorphism for inputs
whose terms vanish strictly above `c`. The cutoff and nonpositive resolution
degree give finite support on each total diagonal. -/
theorem quasiIso_freeYonedaSheafCoproductTotalAugmentation_of_isStrictlyLE
    [M.IsStrictlyLE c] :
    QuasiIso ((freeYonedaSheafCoproductTotalAugmentation X).app M) := by
  haveI : QuasiIso (HomologicalComplex₂.total.map
      ((normalizedBicomplexAugmentation X).app M)
      (ComplexShape.up ℤ)) :=
    quasiIso_normalizedBicomplexAugmentation_totalMap_of_isStrictlyLE X M c
  let f := HomologicalComplex₂.total.map
      ((normalizedBicomplexAugmentation X).app M) (ComplexShape.up ℤ)
  let g := (HomologicalComplex₂.singleZeroFlipTotalNatIso
      (C := X.Modules)).hom.app M
  change QuasiIso (f ≫ g)
  haveI hIso : IsIso g := by infer_instance
  haveI hQI : QuasiIso g := by exact quasiIso_of_isIso g
  exact quasiIso_comp
    (hφ := quasiIso_normalizedBicomplexAugmentation_totalMap_of_isStrictlyLE X M c)
    (hφ' := hQI) f g

/-- Good truncations are strictly bounded above, so the bounded augmentation
theorem applies at each stage of the tower used for the unbounded result below. -/
theorem quasiIso_freeYonedaSheafCoproductTotalAugmentation_truncLE :
    QuasiIso ((freeYonedaSheafCoproductTotalAugmentation X).app (M.truncLE c)) :=
  quasiIso_freeYonedaSheafCoproductTotalAugmentation_of_isStrictlyLE X (M.truncLE c) c

end BoundedAugmentation

/-- The free-Yoneda total augmentation is a quasi-isomorphism for every input
complex. Both good-truncation cocones are colimiting, so exact filtered colimits
preserve the stagewise quasi-isomorphisms and naturality identifies the
resulting map with the original augmentation. -/
theorem quasiIso_freeYonedaSheafCoproductTotalAugmentation
    (X : Scheme.{u}) (M : CochainComplex X.Modules ℤ) :
    QuasiIso ((freeYonedaSheafCoproductTotalAugmentation X).app M) := by
  letI : AB5OfSize.{0,0} X.Modules := AB5OfSize_of_univLE X.Modules
  let H := freeYonedaSheafCoproductTotalComplexFunctor X
  let α := freeYonedaSheafCoproductTotalAugmentation X
  let T := CochainComplex.truncLETower M
  let hT := CochainComplex.isColimitTruncLETowerCocone M
  letI : PreservesColimit T H := preservesColimit_of_preserves_colimit_cocone hT
    (isColimitFreeYonedaSheafCoproductTotalTruncLETowerCocone X M)
  have hcolim : QuasiIso (α.app (colimit T)) :=
    HomologicalComplex.quasiIso_app_colimit_of_preserves T α
      (fun n => quasiIso_freeYonedaSheafCoproductTotalAugmentation_truncLE X M (n : ℤ))
  let e : M ≅ colimit T := IsColimit.coconePointUniqueUpToIso hT (colimit.isColimit T)
  have hn := α.naturality e.hom
  haveI : QuasiIso (α.app (colimit T)) := hcolim
  haveI : QuasiIso (H.map e.hom) := inferInstance
  haveI : QuasiIso (H.map e.hom ≫ α.app (colimit T)) :=
    quasiIso_comp (H.map e.hom) (α.app (colimit T))
  have hcomp : α.app M ≫ e.hom = H.map e.hom ≫ α.app (colimit T) := by
    simpa using hn.symm
  haveI : QuasiIso (α.app M ≫ e.hom) := by
    rw [hcomp]
    exact ‹QuasiIso (H.map e.hom ≫ α.app (colimit T))›
  exact quasiIso_of_comp_right (α.app M) e.hom

end AlgebraicGeometry.Scheme.Modules
