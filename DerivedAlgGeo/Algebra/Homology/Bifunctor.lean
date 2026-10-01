/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FiniteStripTotal
import DerivedAlgGeo.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Finite-support bifunctor maps and colimits of complex totals

Mathlib's `HomologicalComplex.mapBifunctorMap` is a map between direct-sum totals.
When the fixed input complex has finitely supported terms, a columnwise
quasi-isomorphism criterion for literal bicomplex totals applies to this map.
For arbitrary compatible complex shapes, the literal total preserves a
diagram-shape colimit in either varying slot when the corresponding partial
bifunctor preserves it at the fixed complex's terms.

## Main definitions

This module introduces no new public definitions; it studies Mathlib's existing
`HomologicalComplex.mapBifunctorMap`, `CategoryTheory.Functor.map₂HomologicalComplex`,
and its cochain specialization `CategoryTheory.Functor.map₂CochainComplex`.

## Main results

* `HomologicalComplex.quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso` passes
  quasi-isomorphic mapped columns in the second input to a quasi-isomorphism
  of literal totals under finite term support in the first.
* `HomologicalComplex.quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso`
  fixes finite support in the second input and maps the first by signed flip.
* `CategoryTheory.Functor.preservesColimitsOfShape_map₂HomologicalComplex_obj` and
  `CategoryTheory.Functor.preservesColimitsOfShape_map₂HomologicalComplex_flip_obj`
  preserve a colimit in either varying slot for arbitrary compatible shapes.
* `CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj` and
  `CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_flip_obj`
  specialize these results to integer cochain totals.

## Implementation notes

The fixed complex supplies the finite horizontal support strip for both
bicomplexes. The finite-strip total-map criterion needs columnwise evidence
only inside it; the right-slot result uses naturality of Mathlib's signed flip.
For colimits, two evaluations reduce the mapped bicomplex to the partial
base functor at each bidegree. The existing total-functor colimit theorem
then applies under coproducts over each total-degree fiber; private natural
isomorphisms identify its composite with Mathlib's literal map₂ functor in
each slot. Countable coproducts suffice for the integer cochain case.

## References

These results extend Mathlib's `HomologicalComplex.mapBifunctorMap` and use
`HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip`. The colimit results use
`HomologicalComplex₂.totalFunctor_preservesColimitsOfShape`.

## Tags

bifunctor, homological complex, cochain complex, quasi-isomorphism, finite support, colimit
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

namespace CategoryTheory.Functor

open ComplexShape

universe u₁ u₂ u₃ v₁ v₂ v₃ w z a b d

set_option backward.isDefEq.respectTransparency false in
private theorem bicomplex_left
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [HasZeroMorphisms D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₂]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    (K : HomologicalComplex C₁ c₁)
    [∀ p, PreservesColimitsOfShape J (F.obj (K.X p))] :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex c₁ c₂).obj K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro p
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  change PreservesColimitsOfShape J
    (HomologicalComplex.eval C₂ c₂ q ⋙ F.obj (K.X p))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem bicomplex_right
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [HasZeroMorphisms D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₁]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    (K : HomologicalComplex C₂ c₂)
    [∀ q, PreservesColimitsOfShape J (F.flip.obj (K.X q))] :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex c₁ c₂).flip.obj K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro p
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  change PreservesColimitsOfShape J
    (HomologicalComplex.eval C₁ c₁ p ⋙ F.flip.obj (K.X q))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def totalIso_left
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b} {I₁₂ : Type d}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) D]
    (K : HomologicalComplex C₁ c₁) :
    (F.mapBifunctorHomologicalComplex c₁ c₂).obj K ⋙
      HomologicalComplex₂.totalFunctor D c₁ c₂ c₁₂ ≅
    (F.map₂HomologicalComplex c₁ c₂ c₁₂).obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp [HomologicalComplex.mapBifunctorMap])

set_option backward.isDefEq.respectTransparency false in
private def totalIso_right
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b} {I₁₂ : Type d}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) D]
    (K : HomologicalComplex C₂ c₂) :
    (F.mapBifunctorHomologicalComplex c₁ c₂).flip.obj K ⋙
      HomologicalComplex₂.totalFunctor D c₁ c₂ c₁₂ ≅
    (F.map₂HomologicalComplex c₁ c₂ c₁₂).flip.obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp [HomologicalComplex.mapBifunctorMap])

/-- For any compatible complex shapes, fixing the first complex preserves
`J`-colimits of the literal bifunctor total when the partial functor at each
term of that complex does. The total functor uses the stated coproducts over
its degree fibers; no homology exactness is required. -/
theorem preservesColimitsOfShape_map₂HomologicalComplex_obj
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₂] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b} {I₁₂ : Type d}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) D]
    (K : HomologicalComplex C₁ c₁)
    [∀ p, PreservesColimitsOfShape J (F.obj (K.X p))] :
    PreservesColimitsOfShape J ((F.map₂HomologicalComplex c₁ c₂ c₁₂).obj K) := by
  letI := bicomplex_left (J := J) F c₁ c₂ K
  exact preservesColimitsOfShape_of_natIso (totalIso_left F c₁ c₂ c₁₂ K)

/-- Fixing the second complex preserves `J`-colimits of the literal total
when each partial functor at its terms does. The proof keeps the original
bidegree order, evaluates twice, and transports through direct-sum totalization. -/
theorem preservesColimitsOfShape_map₂HomologicalComplex_flip_obj
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₁] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    {I₁ : Type a} {I₂ : Type b} {I₁₂ : Type d}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) D]
    (K : HomologicalComplex C₂ c₂)
    [∀ q, PreservesColimitsOfShape J (F.flip.obj (K.X q))] :
    PreservesColimitsOfShape J ((F.map₂HomologicalComplex c₁ c₂ c₁₂).flip.obj K) := by
  letI := bicomplex_right (J := J) F c₁ c₂ K
  exact preservesColimitsOfShape_of_natIso (totalIso_right F c₁ c₂ c₁₂ K)

/-- The cochain specialization of
`CategoryTheory.Functor.preservesColimitsOfShape_map₂HomologicalComplex_obj`. Countable coproducts
supply every integer-diagonal total. -/
theorem preservesColimitsOfShape_map₂CochainComplex_obj
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₂] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ)
    [∀ p, PreservesColimitsOfShape J (F.obj (K.X p))] :
    PreservesColimitsOfShape J (F.map₂CochainComplex.obj K) := by
  exact preservesColimitsOfShape_map₂HomologicalComplex_obj F (up ℤ) (up ℤ) (up ℤ) K

/-- The fixed-second cochain specialization retains the original bicomplex
degree order and uses countable coproducts for each total diagonal. -/
theorem preservesColimitsOfShape_map₂CochainComplex_flip_obj
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₁] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₂ ℤ)
    [∀ q, PreservesColimitsOfShape J (F.flip.obj (K.X q))] :
    PreservesColimitsOfShape J (F.map₂CochainComplex.flip.obj K) := by
  exact preservesColimitsOfShape_map₂HomologicalComplex_flip_obj F (up ℤ) (up ℤ) (up ℤ) K

end CategoryTheory.Functor
