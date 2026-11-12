/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Morphisms essentially of finite type

A morphism of schemes `f : Z ⟶ Y` is *essentially of finite type* if it is of finite type, or if
`Z` is the spectrum of a localization `R[M⁻¹]` and `f` factors as
`Z ≅ Spec R[M⁻¹] ⟶ Spec R ⟶ Y` with `Spec R ⟶ Y` of finite type. Replacing "of finite type" by
"locally of finite type" gives *essentially locally of finite type*. This is Definition 11.16 of
[arXiv:1902.08184v4](https://arxiv.org/abs/1902.08184v4), §11.4.

BLMNPS allow `Y` to be an algebraic space; here `Y` is a scheme. Mathlib has no scheme-level
`FiniteType` class; a morphism is of finite type when it is `LocallyOfFiniteType` and
`QuasiCompact`.

## Main definitions

* `AlgebraicGeometry.EssentiallyLocallyOfFiniteType`: Definition 11.16, local form.
* `AlgebraicGeometry.EssentiallyOfFiniteType`: Definition 11.16.

## Main results

* `AlgebraicGeometry.essentiallyOfFiniteType_iff_essentiallyLocallyOfFiniteType`: over a locally
  Noetherian base the two notions agree for an affine source (Remark 11.17).
* `AlgebraicGeometry.essentiallyOfFiniteType_spec_map_comp`: `Spec B ⟶ Spec A ⟶ Y` is essentially
  of finite type when `A ⟶ B` is essentially of finite type and `Spec A ⟶ Y` is of finite type.
* `AlgebraicGeometry.essentiallyOfFiniteType_spec_map_iff`: on affine schemes the notion agrees
  with Mathlib's `RingHom.EssFiniteType`.

## Implementation notes

Definition 11.16 is kept as the definition, not replaced by an affine-local condition built from
`RingHom.EssFiniteType`: its second clause asks that `Spec R ⟶ Y` be (locally) of finite type over
a possibly non-affine `Y`, which an affine-local essentially-of-finite-type condition does not
give.

## References

* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in families*,
  arXiv:1902.08184v4, §11.4, Definition 11.16 and Remark 11.17

## Tags

essentially of finite type, morphism of schemes, localization
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {Z Y : Scheme.{u}}

/-- A morphism `f : Z ⟶ Y` is *essentially locally of finite type* if it is locally of finite
type, or if it factors as `Z ≅ Spec R[M⁻¹] ⟶ Spec R ⟶ Y` with `Spec R ⟶ Y` locally of finite type.
This is the locally-of-finite-type form of Definition 11.16 of arXiv:1902.08184v4. -/
def EssentiallyLocallyOfFiniteType (f : Z ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∨ ∃ (R : CommRingCat.{u}) (M : Submonoid R) (g : Spec R ⟶ Y)
    (e : Z ≅ Spec (.of (Localization M))), LocallyOfFiniteType g ∧
      f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) ≫ g

/-- A morphism `f : Z ⟶ Y` is *essentially of finite type* if it is of finite type, or if it
factors as `Z ≅ Spec R[M⁻¹] ⟶ Spec R ⟶ Y` with `Spec R ⟶ Y` of finite type. Here "of finite type"
is `LocallyOfFiniteType` together with `QuasiCompact`. This is Definition 11.16 of
arXiv:1902.08184v4. -/
def EssentiallyOfFiniteType (f : Z ⟶ Y) : Prop :=
  (LocallyOfFiniteType f ∧ QuasiCompact f) ∨ ∃ (R : CommRingCat.{u}) (M : Submonoid R)
    (g : Spec R ⟶ Y) (e : Z ≅ Spec (.of (Localization M))), LocallyOfFiniteType g ∧
      QuasiCompact g ∧
        f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) ≫ g

/-- Each clause of Definition 11.16 implies its locally-of-finite-type counterpart by forgetting
quasi-compactness. -/
theorem EssentiallyOfFiniteType.essentiallyLocallyOfFiniteType {f : Z ⟶ Y}
    (hf : EssentiallyOfFiniteType f) : EssentiallyLocallyOfFiniteType f := by
  obtain ⟨hf, -⟩ | ⟨R, M, g, e, hg, -, rfl⟩ := hf
  · exact .inl hf
  · exact .inr ⟨R, M, g, e, hg, rfl⟩

/-- A morphism locally of finite type from an affine scheme to a locally Noetherian scheme is
quasi-compact: its source is a Noetherian scheme. -/
private lemma quasiCompact_of_isAffine_of_locallyOfFiniteType [IsLocallyNoetherian Y] [IsAffine Z]
    (f : Z ⟶ Y) [LocallyOfFiniteType f] : QuasiCompact f := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian Z := ⟨⟩
  infer_instance

/-- Over a locally Noetherian base, a morphism from an affine scheme is essentially of finite type
if and only if it is essentially locally of finite type. This is Remark 11.17 of
arXiv:1902.08184v4. -/
theorem essentiallyOfFiniteType_iff_essentiallyLocallyOfFiniteType [IsLocallyNoetherian Y]
    [IsAffine Z] (f : Z ⟶ Y) : EssentiallyOfFiniteType f ↔ EssentiallyLocallyOfFiniteType f := by
  refine ⟨EssentiallyOfFiniteType.essentiallyLocallyOfFiniteType, ?_⟩
  rintro (hf | ⟨R, M, g, e, hg, rfl⟩)
  · exact .inl ⟨hf, quasiCompact_of_isAffine_of_locallyOfFiniteType f⟩
  · exact .inr ⟨R, M, g, e, hg, quasiCompact_of_isAffine_of_locallyOfFiniteType g, rfl⟩

/-- If `φ : A ⟶ B` is essentially of finite type and `g : Spec A ⟶ Y` is of finite type, then
`Spec B ⟶ Spec A ⟶ Y` is essentially of finite type. -/
theorem essentiallyOfFiniteType_spec_map_comp {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.EssFiniteType) (g : Spec A ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g] :
    EssentiallyOfFiniteType (Spec.map φ ≫ g) := by
  algebraize [φ.hom]
  let C := Algebra.EssFiniteType.subalgebra A B
  let M : Submonoid (CommRingCat.of C) := Algebra.EssFiniteType.submonoid A B
  let ψ : A ⟶ .of C := CommRingCat.ofHom (algebraMap A C)
  have hψ : ψ.hom.FiniteType := by
    change (algebraMap A C).FiniteType
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  have : LocallyOfFiniteType (Spec.map ψ) := HasRingHomProperty.Spec_iff.mpr hψ
  let ι : CommRingCat.of (Localization M) ≅ B :=
    (IsLocalization.algEquiv M (Localization M) B).toRingEquiv.toCommRingCatIso
  refine .inr ⟨.of C, M, Spec.map ψ ≫ g, Scheme.Spec.mapIso ι.op, inferInstance, inferInstance, ?_⟩
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  change algebraMap A B a = (IsLocalization.algEquiv M (Localization M) B)
    (algebraMap C (Localization M) (algebraMap A C a))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

/-- A morphism `Spec B ⟶ Spec A` is essentially of finite type if and only if the ring map
`A ⟶ B` is essentially of finite type. -/
theorem essentiallyOfFiniteType_spec_map_iff {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    EssentiallyOfFiniteType (Spec.map φ) ↔ φ.hom.EssFiniteType := by
  refine ⟨?_, fun hφ ↦ by simpa using essentiallyOfFiniteType_spec_map_comp φ hφ (𝟙 _)⟩
  rintro (⟨hf, -⟩ | ⟨R, M, g, e, hg, -, hf⟩)
  · exact (HasRingHomProperty.Spec_iff.mp hf).essFiniteType
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hψ : ψ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp hg
  let χ : CommRingCat.of (Localization M) ⟶ B := Spec.preimage e.hom
  have : IsIso χ := by
    have : IsIso (Scheme.Spec.map χ.op) := by
      rw [show Scheme.Spec.map χ.op = e.hom from Spec.map_preimage e.hom]
      infer_instance
    have := Spec.fullyFaithful.isIso_of_isIso_map χ.op
    exact isIso_of_op χ
  have hφ : φ = ψ ≫ CommRingCat.ofHom (algebraMap R (Localization M)) ≫ χ := by
    apply Spec.map_injective
    simp only [Spec.map_comp, χ, Spec.map_preimage, hf, Category.assoc]
  rw [hφ]
  refine (RingHom.EssFiniteType.comp hψ.essFiniteType ?_)
  refine RingHom.EssFiniteType.comp ?_ ?_
  · change (algebraMap R (Localization M)).EssFiniteType
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ M
  · exact (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso χ).2).essFiniteType

end AlgebraicGeometry
