/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# Finite-support bifunctor maps of cochain complexes

Mathlib's `HomologicalComplex.mapBifunctorMap` is a map between direct-sum totals.
When the fixed input complex has finitely supported terms, a columnwise
quasi-isomorphism criterion for literal bicomplex totals applies to this map.

## Main results

* `HomologicalComplex.quasiIso_mapBifunctorMap_id_of_finite_support` passes
  quasi-isomorphic mapped columns in the second input to a quasi-isomorphism
  of literal totals under finite term support in the first.
* `HomologicalComplex.quasiIso_mapBifunctorMap_id_right_of_finite_support`
  fixes finite support in the second input and maps the first by signed flip.

## References

These results extend Mathlib's `HomologicalComplex.mapBifunctorMap` and use
`HomologicalComplex₂.quasiIso_totalMap_of_four_diagonal_bounds_of_column_quasiIso`.

## Tags

bifunctor, cochain complex, quasi-isomorphism, finite support
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HomologicalComplex

open ComplexShape

set_option backward.isDefEq.respectTransparency false

private theorem isZero_mapped_complex_of_isZero
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (X : C₁) (hX : IsZero X) (L : CochainComplex C₂ ℤ) :
    IsZero (((F.obj X).mapHomologicalComplex (up ℤ)).obj L) := by
  rw [IsZero.iff_id_eq_zero]
  ext q
  have hq : IsZero ((F.obj X).obj (L.X q)) :=
    (F.flip.obj (L.X q)).map_isZero hX
  rw [IsZero.iff_id_eq_zero] at hq
  change (𝟙 ((F.obj X).obj (L.X q))) = 0
  exact hq

private theorem quasiIso_mapBifunctorMap_id_of_finite_support_all_columns
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ) {L M : CochainComplex C₂ ℤ} (f : L ⟶ M)
    [HasMapBifunctor K L F (up ℤ)] [HasMapBifunctor K M F (up ℤ)]
    (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hcol : ∀ p, QuasiIso (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f)) :
    QuasiIso (mapBifunctorMap (𝟙 K) f F (up ℤ)) := by
  let B := F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)
  have hcol' (p : ℤ) : QuasiIso (((B.obj K).map f).f p) := by
    exact hcol p
  have ht := HomologicalComplex₂.quasiIso_totalMap_of_four_diagonal_bounds_of_column_quasiIso
    ((B.obj K).map f) (fun _ => a) (fun _ => b) (fun _ => a) (fun _ => b)
    (fun _ p q _ hp => (F.flip.obj (L.X q)).map_isZero (hLower p hp))
    (fun _ p q _ hp => (F.flip.obj (L.X q)).map_isZero (hUpper p hp))
    (fun _ p q _ hp => (F.flip.obj (M.X q)).map_isZero (hLower p hp))
    (fun _ p q _ hp => (F.flip.obj (M.X q)).map_isZero (hUpper p hp)) hcol'
  change QuasiIso (HomologicalComplex₂.total.map
    ((B.map (𝟙 K)).app L ≫ (B.obj K).map f) (up ℤ))
  rw [B.map_id, NatTrans.id_app, Category.id_comp]
  exact ht

/-- Finite term support in the first complex lets columnwise quasi-isomorphisms
pass through Mathlib's literal bifunctor total map. Only columns within the
support interval need quasi-isomorphism evidence. The second map is unrestricted;
the bounds concern terms, not cohomology. -/
theorem quasiIso_mapBifunctorMap_id_of_finite_support
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ) {L M : CochainComplex C₂ ℤ} (f : L ⟶ M)
    [HasMapBifunctor K L F (up ℤ)] [HasMapBifunctor K M F (up ℤ)]
    (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f)) :
    QuasiIso (mapBifunctorMap (𝟙 K) f F (up ℤ)) := by
  apply quasiIso_mapBifunctorMap_id_of_finite_support_all_columns
    F K f a b hLower hUpper
  intro p
  by_cases hp : a ≤ p ∧ p ≤ b
  · exact hcol p hp.1 hp.2
  have hK : IsZero (K.X p) := by
    rcases not_and_or.mp hp with hpa | hpb
    · exact hLower p (lt_of_not_ge hpa)
    · exact hUpper p (lt_of_not_ge hpb)
  have hL : IsZero (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).obj L) :=
    isZero_mapped_complex_of_isZero F (K.X p) hK L
  have hM : IsZero (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).obj M) :=
    isZero_mapped_complex_of_isZero F (K.X p) hK M
  have : IsIso (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f) :=
    isIso_of_source_target_iso_zero _ hL.isoZero hM.isoZero
  infer_instance

/-- Signed flipping turns finite term support in the second complex into the
left-slot criterion, without a symmetric monoidal structure. Only supported
columns need quasi-isomorphism evidence. -/
theorem quasiIso_mapBifunctorMap_id_right_of_finite_support
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₂ ℤ) {L M : CochainComplex C₁ ℤ} (f : L ⟶ M)
    [HasMapBifunctor L K F (up ℤ)] [HasMapBifunctor M K F (up ℤ)]
    (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((F.flip.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f)) :
    QuasiIso (mapBifunctorMap f (𝟙 K) F (up ℤ)) := by
  haveI := quasiIso_mapBifunctorMap_id_of_finite_support F.flip K f a b hLower hUpper hcol
  have hnat := mapBifunctorFlipIso_hom_naturality f (𝟙 K) F (up ℤ)
  apply (quasiIso_iff_comp_left (mapBifunctorFlipIso L K F (up ℤ)).hom _).mp
  rw [← hnat]
  infer_instance

end HomologicalComplex
