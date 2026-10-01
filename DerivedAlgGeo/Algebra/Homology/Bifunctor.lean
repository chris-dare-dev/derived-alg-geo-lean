/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FiniteStripTotal
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# Finite-support bifunctor maps of cochain complexes

Mathlib's `HomologicalComplex.mapBifunctorMap` is a map between direct-sum totals.
When the fixed input complex has finitely supported terms, a columnwise
quasi-isomorphism criterion for literal bicomplex totals applies to this map.

## Main definitions

This module introduces no new definitions; it studies Mathlib's existing
`HomologicalComplex.mapBifunctorMap`.

## Main results

* `HomologicalComplex.quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso` passes
  quasi-isomorphic mapped columns in the second input to a quasi-isomorphism
  of literal totals under finite term support in the first.
* `HomologicalComplex.quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso`
  fixes finite support in the second input and maps the first by signed flip.

## Implementation notes

The fixed complex supplies the finite horizontal support strip for both
bicomplexes. The finite-strip total-map criterion needs columnwise evidence
only inside it; the right-slot result uses naturality of Mathlib's signed flip.

## References

These results extend Mathlib's `HomologicalComplex.mapBifunctorMap` and use
`HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip`.

## Tags

bifunctor, cochain complex, quasi-isomorphism, finite support
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HomologicalComplex

open ComplexShape

set_option backward.isDefEq.respectTransparency false

/-- Finite term support in the first complex lets columnwise quasi-isomorphisms
pass through Mathlib's literal bifunctor total map. Only columns within the
support interval need quasi-isomorphism evidence. The second map is unrestricted;
the bounds concern terms, not cohomology. -/
theorem quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso
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
  let B := F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)
  have ht := HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip
    ((B.obj K).map f) a b
    (fun p q hp => by
      rcases hp with hpa | hpb
      · exact (F.flip.obj (L.X q)).map_isZero (hLower p hpa)
      · exact (F.flip.obj (L.X q)).map_isZero (hUpper p hpb))
    (fun p q hp => by
      rcases hp with hpa | hpb
      · exact (F.flip.obj (M.X q)).map_isZero (hLower p hpa)
      · exact (F.flip.obj (M.X q)).map_isZero (hUpper p hpb))
    (fun p hpa hpb => hcol p hpa hpb)
  change QuasiIso (HomologicalComplex₂.total.map
    ((B.map (𝟙 K)).app L ≫ (B.obj K).map f) (up ℤ))
  rw [B.map_id, NatTrans.id_app, Category.id_comp]
  exact ht

/-- Signed flipping turns finite term support in the second complex into the
left-slot criterion, without a symmetric monoidal structure. Only supported
columns need quasi-isomorphism evidence. -/
theorem quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso
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
  haveI := quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso
    F.flip K f a b hLower hUpper hcol
  have hnat := mapBifunctorFlipIso_hom_naturality f (𝟙 K) F (up ℤ)
  apply (quasiIso_iff_comp_left (mapBifunctorFlipIso L K F (up ℤ)).hom _).mp
  rw [← hnat]
  infer_instance

end HomologicalComplex
