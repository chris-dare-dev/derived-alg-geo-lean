/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexShift
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Data.Int.Interval
import DerivedAlgGeo.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Colimits and diagonal coordinates of direct-sum total complexes

Mathlib's direct-sum total functor preserves colimits of any diagram shape when
the component category has those colimits and each total-degree fiber admits
coproducts. For a particular cocone, colimits of its bidegree diagrams suffice.
No exactness or homology argument is involved.

For integer-indexed totals, a projection to one summand exposes the horizontal
and signed vertical parts of the incoming differential. Exactness in one column
then clears one coordinate of a generalized cycle after an epi refinement.
Finite iteration and a finite-support coproduct identity turn this into
degree-local exactness and acyclicity when each total diagonal has finite
nonzero support and the supported column entries are exact. The results
assume the literal total already exists.

## Main definitions

* `HomologicalComplex₂.isColimitTotalFunctorMapCocone` constructs the
  universal property for the literal mapped cocone.
* `HomologicalComplex₂.totalProjection` specializes the canonical coproduct
  projection to one total-degree summand.

## Main results

* `HomologicalComplex₂.totalFunctor_preservesColimitsOfShape` exposes
  colimit preservation to typeclass search.
* `HomologicalComplex₂.total_d_comp_totalProjection` computes the incoming
  differential at one direct-sum coordinate.
* `HomologicalComplex₂.exists_totalCycleRefinement_zero_le` clears one
  coordinate of a generalized total cycle by an epi refinement.
* `HomologicalComplex₂.exactAt_total_of_diagonal_bounds_of_column_exactAt`
  proves exactness from finite support and exactness on one total-degree diagonal.
* `HomologicalComplex₂.acyclic_total_of_diagonal_bounds_of_column_exactAt`
  allows a separate finite support interval in every degree;
  `HomologicalComplex₂.acyclic_total_of_upper_bounds_of_column_exactAt`
  derives the uniform-rectangle case.
* `HomologicalComplex₂.columnCone` is the vertical pointwise cone of a
  bicomplex map; `HomologicalComplex₂.hasTotal_columnCone` constructs its
  literal total from source/target totals and the required biproducts.
* `HomologicalComplex₂.totalColumnConeIso` compares that literal total with
  the mapping cone of the literal total map, using a horizontal-degree sign
  on the source branch.

## Implementation notes

Evaluate in each total degree, view its diagonal coproduct as a colimit over
a discrete category, and commute the two colimits. Degreewise evaluation
then reflects the resulting universal property.

For the integer-indexed coordinate result, compose each summand inclusion
with the total differential and the canonical coproduct projection. The
horizontal term reaches the next column, while the signed vertical term stays
in the current column. Epi refinement supplies a preimage of the vertical
cycle, and its boundary leaves all earlier columns zero. Finite iteration
composes the epi refinements; the generic finite-support zero-map criterion
`CategoryTheory.Limits.Sigma.hom_eq_zero_of_finite_support` makes the
zero-coordinate residual a zero map.

## References

The construction extends Mathlib's `HomologicalComplex₂.totalFunctor` and
uses `HomologicalComplex.isColimitOfEval` and
`CategoryTheory.Limits.evaluationJointlyReflectsColimits`. The coordinate
results use `CategoryTheory.Limits.Sigma.π` and
`CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`.

## Tags

bicomplex, total complex, coproduct, colimit, exactness, epi refinement
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {J : Type w} [Category J]
  {I₁ I₂ I₁₂ : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  [∀ n : I₁₂, HasCoproductsOfShape ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C]

private def totalDegreeFiberFunctor
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I₁ I₂ I₁₂ : Type*}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] (n : I₁₂) :
    HomologicalComplex₂ C c₁ c₂ ⥤
      GradedObject ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C where
  obj K i := (K.X i.1.1).X i.1.2
  map f i := (f.f i.1.1).f i.1.2

private noncomputable def totalDegreeIsColimit
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂) (s : Cocone F) (n : I₁₂)
    (hs : ∀ i : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}, IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s))) :
    IsColimit ((HomologicalComplex.eval C c₁₂ n).mapCocone
      ((totalFunctor C c₁ c₂ c₁₂).mapCocone s)) := by
  change IsColimit (colim.mapCocone
    ((piEquivalenceFunctorDiscrete ((ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}) C).functor.mapCocone
      ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s)))
  apply isColimitOfPreserves
  exact evaluationJointlyReflectsColimits _ (fun i => hs i.as)

private noncomputable def totalIsColimit
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂) (s : Cocone F)
    (hs : ∀ (n : I₁₂) (i : (ComplexShape.π c₁ c₂ c₁₂) ⁻¹' {n}), IsColimit
      ((GradedObject.eval (C := C) i).mapCocone
        ((totalDegreeFiberFunctor c₁ c₂ c₁₂ n).mapCocone s))) :
    IsColimit ((totalFunctor C c₁ c₂ c₁₂).mapCocone s) :=
  HomologicalComplex.isColimitOfEval _ _
    (fun n => totalDegreeIsColimit c₁ c₂ c₁₂ F s n (hs n))

/-- Evaluate the cocone in each bidegree, commute its diagram colimit with
the coproduct over each total-degree fiber, and reflect colimits through
degreewise evaluation. Only the bidegree diagrams occurring in `F` need
colimits; ambient colimits of shape `J` are unnecessary. -/
noncomputable def isColimitTotalFunctorMapCocone
    (F : J ⥤ HomologicalComplex₂ C c₁ c₂)
    [∀ (p : I₁) (q : I₂), HasColimit
      ((F ⋙ HomologicalComplex.eval (HomologicalComplex C c₂) c₁ p) ⋙
        HomologicalComplex.eval C c₂ q)]
    (s : Cocone F) (h : IsColimit s) :
    IsColimit ((totalFunctor C c₁ c₂ c₁₂).mapCocone s) := by
  apply totalIsColimit c₁ c₂ c₁₂ F s
  intro n i
  let p : I₁ := i.1.1
  let q : I₂ := i.1.2
  change IsColimit
    ((HomologicalComplex.eval (HomologicalComplex C c₂) c₁ p ⋙
      HomologicalComplex.eval C c₂ q).mapCocone s)
  exact isColimitOfPreserves _ h

/-- Register `HomologicalComplex₂.isColimitTotalFunctorMapCocone` for
 typeclass search, so downstream consumers can transport their cocones with
 `CategoryTheory.Limits.isColimitOfPreserves`. -/
noncomputable instance totalFunctor_preservesColimitsOfShape
    [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (totalFunctor C c₁ c₂ c₁₂) :=
  ⟨fun {F} => ⟨fun h => ⟨isColimitTotalFunctorMapCocone c₁ c₂ c₁₂ F _ h⟩⟩⟩

end HomologicalComplex₂


open Category HomologicalComplex

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C]

section Components
variable [Preadditive C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

/-- The canonical projection from the literal direct-sum total complex to its
`(p,q)` summand in total degree `n`. -/
noncomputable abbrev totalProjection (p q n : ℤ) (h : p + q = n) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X p).X q :=
  Sigma.π (K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
    ⟨(p, q), h⟩

private lemma inclusion_projection (p q n : ℤ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p q n h ≫ totalProjection K p q n h = 𝟙 _ := by
  exact Sigma.ι_π_eq_id _ _

private lemma inclusion_projection_ne (p q p' q' n : ℤ)
    (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p') :
    K.ιTotal (ComplexShape.up ℤ) p q n h ≫ totalProjection K p' q' n h' = 0 := by
  apply Sigma.ι_π_of_ne
  intro hEq
  exact hp (congrArg (fun x => x.1.1) hEq)

set_option backward.isDefEq.respectTransparency false in
private lemma boundary_projection (p q n : ℤ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p (q - 1) (n - 1) (by change p + (q-1) = n-1; omega) ≫
      (K.total (ComplexShape.up ℤ)).d (n - 1) n ≫ totalProjection K p q n h =
    (ComplexShape.up ℤ).ε p • (K.X p).d (q - 1) q := by
  change _ ≫ (K.D₁ (ComplexShape.up ℤ) (n-1) n +
    K.D₂ (ComplexShape.up ℤ) (n-1) n) ≫ _ = _
  rw [Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [HomologicalComplex₂.d₁_eq K (ComplexShape.up ℤ)
    (i₁' := p+1) (by simp) (q-1) n (by change (p+1)+(q-1)=n; omega)]
  rw [HomologicalComplex₂.d₂_eq K (ComplexShape.up ℤ)
    p (i₂' := q) (by simp) n h]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [inclusion_projection_ne K (p+1) (q-1) p q n _ h (by omega),
    inclusion_projection K p q n h]
  simp
end Components

section Correction
variable [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
private theorem literal_total_cycle_correction
    (p q n : ℤ) (h : p + q = n)
    (hE : (ShortComplex.mk ((K.X p).d (q-1) q) ((K.X p).d q (q+1))
      ((K.X p).d_comp_d _ _ _)).Exact)
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (hx : x ≫ (K.total (ComplexShape.up ℤ)).d n (n+1) = 0)
    (hv : (x ≫ totalProjection K p q n h) ≫ (K.X p).d q (q+1) = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ (K.X p).X (q-1)),
      let z := ((ComplexShape.up ℤ).ε p • y) ≫
        K.ιTotal (ComplexShape.up ℤ) p (q-1) (n-1) (by change p+(q-1)=n-1; omega)
      ((π ≫ x - z ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
        (K.total (ComplexShape.up ℤ)).d n (n+1) = 0) ∧
      ((π ≫ x - z ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
        totalProjection K p q n h = 0) := by
  obtain ⟨A', π, hπ, y, hy⟩ := hE.exact_up_to_refinements
    (x ≫ totalProjection K p q n h) hv
  refine ⟨A', π, hπ, y, ?_, ?_⟩
  · simp only [Preadditive.sub_comp, Category.assoc, hx,
      HomologicalComplex.d_comp_d, comp_zero, sub_self]
  · rw [Preadditive.sub_comp, Category.assoc, Category.assoc,
      Category.assoc, boundary_projection]
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul]
    exact sub_eq_zero.mpr hy
end Correction

section Strengthening
variable [Preadditive C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
private lemma boundary_projection_off (p q r s n : ℤ)
    (h : p + q = n) (hr : r + s = n)
    (hp : p ≠ r) (hp' : p + 1 ≠ r) :
    K.ιTotal (ComplexShape.up ℤ) p (q - 1) (n - 1) (by change p+(q-1)=n-1; omega) ≫
      (K.total (ComplexShape.up ℤ)).d (n - 1) n ≫ totalProjection K r s n hr = 0 := by
  change _ ≫ (K.D₁ (ComplexShape.up ℤ) (n-1) n +
    K.D₂ (ComplexShape.up ℤ) (n-1) n) ≫ _ = _
  rw [Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [HomologicalComplex₂.d₁_eq K (ComplexShape.up ℤ)
    (i₁' := p+1) (by simp) (q-1) n (by change (p+1)+(q-1)=n; omega)]
  rw [HomologicalComplex₂.d₂_eq K (ComplexShape.up ℤ)
    p (i₂' := q) (by simp) n h]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂, Linear.units_smul_comp, Category.assoc]
  rw [inclusion_projection_ne K (p+1) (q-1) r s n _ hr hp',
    inclusion_projection_ne K p q r s n h hr hp]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma correction_preserves_lower
    (p q n : ℤ) (h : p + q = n)
    {A A' : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (π : A' ⟶ A) (y : A' ⟶ (K.X p).X (q-1))
    (r s : ℤ) (hr : r + s = n) (hl : r < p)
    (hx : x ≫ totalProjection K r s n hr = 0) :
    (π ≫ x - (((ComplexShape.up ℤ).ε p • y) ≫
      K.ιTotal (ComplexShape.up ℤ) p (q-1) (n-1) (by change p+(q-1)=n-1; omega)) ≫
      (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫ totalProjection K r s n hr = 0 := by
  rw [Preadditive.sub_comp, Category.assoc, hx, comp_zero]
  simp only [Category.assoc]
  rw [boundary_projection_off K p q r s n h hr (by omega) (by omega)]
  simp

end Strengthening

section Incoming
variable [Preadditive C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
set_option backward.isDefEq.respectTransparency false in
/-- Compute an incoming coordinate by checking each coproduct inclusion against
Mathlib's outgoing differential formulas. This uses the coproduct universal
property and requires no finite diagonal support. -/
lemma total_d_comp_totalProjection (p q n : ℤ) (h : p + q = n) :
    (K.total (ComplexShape.up ℤ)).d n (n+1) ≫
      totalProjection K p (q+1) (n+1) (by omega) =
    totalProjection K (p-1) (q+1) n (by omega) ≫ (K.d (p-1) p).f (q+1) +
      (ComplexShape.up ℤ).ε p •
        (totalProjection K p q n h ≫ (K.X p).d q (q+1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  change K.ιTotal (ComplexShape.up ℤ) a b n hab ≫
    (K.D₁ (ComplexShape.up ℤ) n (n+1) + K.D₂ (ComplexShape.up ℤ) n (n+1)) ≫ _ = _
  rw [Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  by_cases ha : a = p
  · subst a
    have hb : b = q := by omega
    subst b
    rw [HomologicalComplex₂.d₁_eq K (ComplexShape.up ℤ)
      (i₁' := p+1) (by simp) q (n+1) (by change (p+1)+q=n+1; omega)]
    rw [HomologicalComplex₂.d₂_eq K (ComplexShape.up ℤ)
      p (i₂' := q+1) (by simp) (n+1) (by change p+(q+1)=n+1; omega)]
    simp only [ComplexShape.ε₁, ComplexShape.ε₂, Linear.units_smul_comp,
      Category.assoc, Preadditive.comp_add, Linear.comp_units_smul]
    rw [inclusion_projection_ne K (p+1) q p (q+1) (n+1) _ _ (by omega),
      inclusion_projection K p (q+1) (n+1)]
    rw [← Category.assoc, inclusion_projection_ne K p q (p-1) (q+1) n _ _ (by omega)]
    rw [← Category.assoc, inclusion_projection K p q n]
    simp
  · by_cases ha' : a + 1 = p
    · have he : a = p-1 := by omega
      have hb : b = q+1 := by omega
      subst a b
      rw [HomologicalComplex₂.d₁_eq K (ComplexShape.up ℤ)
        (i₁' := p) (by simp) (q+1) (n+1) (by change p+(q+1)=n+1; omega)]
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.up ℤ)
        (p-1) (i₂' := q+1+1) (by simp) (n+1) (by change (p-1)+(q+1+1)=n+1; omega)]
      simp only [ComplexShape.ε₁, ComplexShape.ε₂, Linear.units_smul_comp,
        Category.assoc, Preadditive.comp_add, Linear.comp_units_smul]
      rw [inclusion_projection K p (q+1) (n+1),
        inclusion_projection_ne K (p-1) (q+1+1) p (q+1) (n+1) _ _ (by omega)]
      rw [← Category.assoc, inclusion_projection K (p-1) (q+1) n]
      rw [← Category.assoc, inclusion_projection_ne K (p-1) (q+1) p q n _ _ (by omega)]
      simp
    · rw [HomologicalComplex₂.d₁_eq K (ComplexShape.up ℤ)
        (i₁' := a+1) (by simp) b (n+1) (by change (a+1)+b=n+1; omega)]
      rw [HomologicalComplex₂.d₂_eq K (ComplexShape.up ℤ)
        a (i₂' := b+1) (by simp) (n+1) (by change a+(b+1)=n+1; omega)]
      simp only [ComplexShape.ε₁, ComplexShape.ε₂, Linear.units_smul_comp,
        Category.assoc, Preadditive.comp_add, Linear.comp_units_smul]
      rw [inclusion_projection_ne K (a+1) b p (q+1) (n+1) _ _ ha',
        inclusion_projection_ne K a (b+1) p (q+1) (n+1) _ _ ha]
      rw [← Category.assoc, inclusion_projection_ne K a b (p-1) (q+1) n _ _ (by omega)]
      rw [← Category.assoc, inclusion_projection_ne K a b p q n _ _ ha]
      simp
end Incoming

section VerticalClosure
variable [Preadditive C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
/-- The incoming-coordinate formula isolates the vertical differential after
the horizontal contribution vanishes; applying its sign again removes the
sign. Only the selected total-differential coordinate must vanish, so callers
need not supply a full total cycle. -/
lemma comp_totalProjection_comp_d_eq_zero_of_total_component_eq_zero_of_horizontal_eq_zero
    (p q n : ℤ) (h : p+q=n)
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (hx : (x ≫ (K.total (ComplexShape.up ℤ)).d n (n+1)) ≫
      totalProjection K p (q+1) (n+1) (by omega) = 0)
    (hl : (x ≫ totalProjection K (p-1) (q+1) n (by omega)) ≫
      (K.d (p-1) p).f (q+1) = 0) :
    (x ≫ totalProjection K p q n h) ≫ (K.X p).d q (q+1) = 0 := by
  rw [Category.assoc, total_d_comp_totalProjection K p q n h,
    Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, hl,
    zero_add] at hx
  have hh' := congrArg (fun f => (ComplexShape.up ℤ).ε p • f) hx
  simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero,
    Category.assoc] using hh'

private lemma totalProjection_isCycle_of_cycle_and_previous_zero (p q n : ℤ) (h : p+q=n)
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (hx : x ≫ (K.total (ComplexShape.up ℤ)).d n (n+1) = 0)
    (hl : x ≫ totalProjection K (p-1) (q+1) n (by omega) = 0) :
    (x ≫ totalProjection K p q n h) ≫ (K.X p).d q (q+1) = 0 := by
  apply comp_totalProjection_comp_d_eq_zero_of_total_component_eq_zero_of_horizontal_eq_zero
    K p q n h x
  · rw [hx, zero_comp]
  · rw [hl, zero_comp]

end VerticalClosure

section Elimination
variable [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
set_option backward.isDefEq.respectTransparency false in
/-- Apply exactness up to epi refinement to the selected vertical cycle, then
subtract the boundary of its signed preimage. That boundary reaches only
columns `p` and `p + 1`, preserving the cleared lower coordinates. Refinement
avoids assuming that the generalized cycle lifts on its original source. -/
theorem exists_totalCycleRefinement_zero_le
    (p q n : ℤ) (h : p + q = n)
    (hE : (ShortComplex.mk ((K.X p).d (q-1) q) ((K.X p).d q (q+1))
      ((K.X p).d_comp_d _ _ _)).Exact)
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (hx : x ≫ (K.total (ComplexShape.up ℤ)).d n (n+1) = 0)
    (hlow : ∀ r s : ℤ, ∀ (hr : r+s=n), r < p → x ≫ totalProjection K r s n hr = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (y : A' ⟶ (K.X p).X (q-1)),
      let z := ((ComplexShape.up ℤ).ε p • y) ≫
        K.ιTotal (ComplexShape.up ℤ) p (q-1) (n-1) (by change p+(q-1)=n-1; omega)
      ((π ≫ x - z ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
        (K.total (ComplexShape.up ℤ)).d n (n+1) = 0) ∧
      (∀ r s : ℤ, ∀ (hr : r+s=n), r ≤ p →
        (π ≫ x - z ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
          totalProjection K r s n hr = 0) := by
  have hv := totalProjection_isCycle_of_cycle_and_previous_zero K p q n h x hx
    (hlow (p-1) (q+1) (by omega) (by omega))
  obtain ⟨A', π, hπ, y, hcycle, hselected⟩ :=
    literal_total_cycle_correction K p q n h hE x hx hv
  refine ⟨A', π, hπ, y, hcycle, ?_⟩
  intro r s hr hle
  by_cases he : r = p
  · subst r
    have hs : s = q := by omega
    subst s
    exact hselected
  · exact correction_preserves_lower K p q n h x π y r s hr (by omega)
      (hlow r s hr (by omega))
end Elimination

end HomologicalComplex₂

namespace HomologicalComplex₂

universe u' v'

section FiniteSupport
variable {C : Type u'} [Category.{v'} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

private def diagonalEmbedding (n : ℤ) :
    ℤ ↪ ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) ⁻¹' {n}) where
  toFun p := ⟨(p, n-p), by change p + (n-p) = n; omega⟩
  inj' _ _ h := congrArg (fun i => i.1.1) h

/-- The finite-support coproduct identity detects a zero incoming map on a
literal total-degree diagonal. This helper is confined to the exactness proof. -/
private lemma total_hom_eq_zero_of_finite_support (n : ℤ) (s : Finset ℤ)
    (hz : ∀ p q, p+q=n → p ∉ s → IsZero ((K.X p).X q))
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (h : ∀ p ∈ s, x ≫ K.totalProjection p (n-p) n (by omega) = 0) : x = 0 := by
  classical
  let f := K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) n
  apply Sigma.hom_eq_zero_of_finite_support f (s.map (diagonalEmbedding n)) ?_ x ?_
  · intro i hi
    apply hz i.1.1 i.1.2 i.2
    intro hp
    apply hi
    apply Finset.mem_map.mpr
    refine ⟨i.1.1, hp, ?_⟩
    apply Subtype.ext
    change (i.1.1, n-i.1.1) = (i.1.1, i.1.2)
    congr 1
    have hsum := i.2
    change i.1.1 + i.1.2 = n at hsum
    omega
  · intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hi
    convert h p hp using 1 <;> rfl

end FiniteSupport

section FiniteRefinement
open CategoryTheory.Preadditive
variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]

set_option backward.isDefEq.respectTransparency false in
/-- Iterate the one-coordinate correction through a finite interval. The
composite epi changes the source, while the accumulated boundary and residual
keep the cycle equation and cleared lower coordinates. -/
private theorem exists_finite_total_cycle_refinement (n a : ℤ) (m : ℕ)
    (hE : ∀ p : ℤ, a ≤ p → p < a + m →
      (ShortComplex.mk ((K.X p).d (n-p-1) (n-p))
        ((K.X p).d (n-p) (n-p+1)) ((K.X p).d_comp_d _ _ _)).Exact)
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (hx : x ≫ (K.total (ComplexShape.up ℤ)).d n (n+1) = 0)
    (hlow : ∀ r s : ℤ, ∀ (hr : r+s=n), r < a →
      x ≫ K.totalProjection r s n hr = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π)
        (t : A' ⟶ (K.total (ComplexShape.up ℤ)).X (n-1)),
      ((π ≫ x - t ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
        (K.total (ComplexShape.up ℤ)).d n (n+1) = 0) ∧
      (∀ r s : ℤ, ∀ (hr : r+s=n), r < a + m →
        (π ≫ x - t ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) ≫
          K.totalProjection r s n hr = 0) := by
  induction m with
  | zero =>
      refine ⟨A, 𝟙 A, inferInstance, 0, ?_, ?_⟩
      · simpa using hx
      · simpa using hlow
  | succ m ih =>
      obtain ⟨B, π, hπ, t, htcycle, htlow⟩ :=
        ih (fun p hp hpm => hE p hp (by omega))
      letI : Epi π := hπ
      obtain ⟨D, ρ, hρ, y, hcycle, hzero⟩ :=
        K.exists_totalCycleRefinement_zero_le (a+m) (n-(a+m)) n (by omega)
          (hE (a+m) (by omega) (by omega))
          (π ≫ x - t ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n)
          htcycle htlow
      letI : Epi ρ := hρ
      let z := ((ComplexShape.up ℤ).ε (a+m) • y) ≫
        K.ιTotal (ComplexShape.up ℤ) (a+m) (n-(a+m)-1) (n-1) (by
          change a+(m:ℤ)+(n-(a+m)-1)=n-1
          omega)
      have hres : (ρ ≫ π) ≫ x - (ρ ≫ t + z) ≫
          (K.total (ComplexShape.up ℤ)).d (n-1) n =
          ρ ≫ (π ≫ x - t ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n) -
            z ≫ (K.total (ComplexShape.up ℤ)).d (n-1) n := by
        simp only [Category.assoc, comp_sub, add_comp]
        abel
      refine ⟨D, ρ ≫ π, inferInstance, ρ ≫ t + z, ?_, ?_⟩
      · rw [hres]
        exact hcycle
      · intro r s hr hrs
        rw [hres]
        exact hzero r s hr (by omega)

set_option backward.isDefEq.respectTransparency false in
omit [K.HasTotal (ComplexShape.up ℤ)] in
private theorem diagonal_exactAt_to_short (n p : ℤ)
    (hE : (K.X p).ExactAt (n-p)) :
    (ShortComplex.mk ((K.X p).d (n-p-1) (n-p))
      ((K.X p).d (n-p) (n-p+1)) ((K.X p).d_comp_d _ _ _)).Exact := by
  exact ((K.X p).exactAt_iff' (n-p-1) (n-p) (n-p+1)
    (by simp) (by simp)).1 hE

set_option backward.isDefEq.respectTransparency false in
/-- Refine a total cycle through the finitely supported diagonal, then use
the finite projection identity to make its residual zero. The abelian
exactness criterion then makes the literal total exact at `n`. -/
theorem exactAt_total_of_diagonal_bounds_of_column_exactAt (n a b : ℤ)
    (hLower : ∀ p q : ℤ, p + q = n → p < a → IsZero ((K.X p).X q))
    (hUpper : ∀ p q : ℤ, p + q = n → b < p → IsZero ((K.X p).X q))
    (hExact : ∀ p : ℤ, a ≤ p → p ≤ b → (K.X p).ExactAt (n-p)) :
    (K.total (ComplexShape.up ℤ)).ExactAt n := by
  apply ((K.total (ComplexShape.up ℤ)).exactAt_iff_exact_up_to_refinements
    (n-1) n (n+1) (by simp) (by simp)).2
  intro A x hx
  by_cases hab : a ≤ b
  · have hcount : ((b+1-a).toNat : ℤ) = b+1-a :=
      Int.toNat_of_nonneg (by omega)
    obtain ⟨B, π, hπ, t, hcycle, hzero⟩ :=
      exists_finite_total_cycle_refinement K n a (b+1-a).toNat
        (fun p hp hpb => diagonal_exactAt_to_short K n p
          (hExact p hp (by omega))) x hx
        (fun p q hpq hp => (hLower p q hpq hp).eq_of_tgt _ _)
    refine ⟨B, π, hπ, t, ?_⟩
    apply sub_eq_zero.mp
    apply total_hom_eq_zero_of_finite_support K n (Finset.Icc a b)
    · intro p q hpq hp
      rw [Finset.mem_Icc] at hp
      by_cases hpa : p < a
      · exact hLower p q hpq hpa
      · exact hUpper p q hpq (by omega)
    · intro p hp
      exact hzero p (n-p) (by omega) (by
        have := (Finset.mem_Icc.mp hp).2
        omega)
  · refine ⟨A, 𝟙 A, inferInstance, 0, ?_⟩
    simp only [Category.id_comp, zero_comp]
    apply total_hom_eq_zero_of_finite_support K n ∅
    · intro p q hpq _
      by_cases hpa : p < a
      · exact hLower p q hpq hpa
      · exact hUpper p q hpq (by omega)
    · simp

/-- Apply degree-local exactness to each diagonal, allowing the support
interval and required column exactness to vary with total degree. -/
theorem acyclic_total_of_diagonal_bounds_of_column_exactAt
    (hData : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ p q : ℤ, p + q = n → p < a → IsZero ((K.X p).X q)) ∧
      (∀ p q : ℤ, p + q = n → b < p → IsZero ((K.X p).X q)) ∧
      (∀ p : ℤ, a ≤ p → p ≤ b → (K.X p).ExactAt (n-p))) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  intro n
  obtain ⟨a, b, hLower, hUpper, hExact⟩ := hData n
  exact exactAt_total_of_diagonal_bounds_of_column_exactAt K n a b hLower hUpper hExact

/-- A uniform upper rectangle gives finite support on every diagonal. Only
columns and degrees inside that rectangle need the exactness premise. -/
theorem acyclic_total_of_upper_bounds_of_column_exactAt (b c : ℤ)
    (hp : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hq : ∀ p q : ℤ, c < q → IsZero ((K.X p).X q))
    (hExact : ∀ p q : ℤ, p ≤ b → q ≤ c → (K.X p).ExactAt q) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  intro n
  apply exactAt_total_of_diagonal_bounds_of_column_exactAt K n (n-c) b
  · intro p q hpq hpl
    exact hq p q (by omega)
  · intro p q hpq hpu
    exact hp p q hpu
  · intro p hpl hpu
    exact hExact p (n-p) hpu (by omega)

end FiniteRefinement
end HomologicalComplex₂
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {I : Type w}
  (A B : I → C) [HasCoproduct A] [HasCoproduct B]
  [HasBinaryBiproduct (∐ A) (∐ B)]
  [∀ i, HasBinaryBiproduct (A i) (B i)]

set_option backward.isDefEq.respectTransparency false in
private theorem hasCoproduct_pointwise_biprod :
    HasCoproduct (fun i => A i ⊞ B i) where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk ((∐ A) ⊞ (∐ B))
        (fun i => biprod.desc (Sigma.ι A i ≫ biprod.inl) (Sigma.ι B i ≫ biprod.inr))
      isColimit := by
        refine Cofan.IsColimit.mk _ (fun t => biprod.desc
          (Sigma.desc (fun i => biprod.inl ≫ t.inj i))
          (Sigma.desc (fun i => biprod.inr ≫ t.inj i))) ?_ ?_
        · intro t i
          apply biprod.hom_ext'
          · simp only [cofan_mk_inj]
            rw [← Category.assoc, biprod.inl_desc, Category.assoc, biprod.inl_desc, Sigma.ι_desc]
          · simp only [cofan_mk_inj]
            rw [← Category.assoc, biprod.inr_desc, Category.assoc, biprod.inr_desc, Sigma.ι_desc]
        · intro t m hm
          apply biprod.hom_ext'
          · apply Sigma.hom_ext
            intro i
            have hi := hm i
            have h := congrArg (fun k => biprod.inl ≫ k) hi
            simpa [cofan_mk_inj, ← Category.assoc] using h
          · apply Sigma.hom_ext
            intro i
            have hi := hm i
            have h := congrArg (fun k => biprod.inr ≫ k) hi
            simpa [cofan_mk_inj, ← Category.assoc] using h
    }

open ComplexShape
namespace HomologicalComplex₂
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]

private theorem hasHomotopyCofiber_flip_map : HomologicalComplex.HasHomotopyCofiber
    ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f) := by
  letI : ∀ q : ℤ, HasBinaryBiproduct
      (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj K).X (q + 1))
      (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj L).X q) := by
    intro q
    letI : ∀ p : ℤ, HasBinaryBiproduct
      ((((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj K).X (q + 1)).X p)
      ((((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj L).X q).X p) := by
      intro p
      change HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)
      infer_instance
    exact HomologicalComplex.instHasBinaryBiproduct _ _
  infer_instance

/-- Take the pointwise cone vertically, leaving the horizontal bicomplex
direction in place. -/
noncomputable def columnCone : HomologicalComplex₂ C (up ℤ) (up ℤ) := by
  letI := hasHomotopyCofiber_flip_map f
  exact HomologicalComplex₂.flip (CochainComplex.mappingCone
    ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f))

private def diagEquiv (n : ℤ) :
    ((π (up ℤ) (up ℤ) (up ℤ)) ⁻¹' {n}) ≃ ℤ where
  toFun i := i.1.1
  invFun p := ⟨(p, n-p), by change p + (n-p) = n; omega⟩
  left_inv := by
    rintro ⟨⟨p,q⟩,h⟩
    have hq : q = n - p := by
      change p + q = n at h
      omega
    subst q
    rfl
  right_inv := by intro p; rfl

private noncomputable def componentIso (p q : ℤ) :
    ((columnCone f).X p).X q ≅ ((K.X p).X (q + 1)) ⊞ ((L.X p).X q) := by
  letI := hasHomotopyCofiber_flip_map f
  letI : HasBinaryBiproduct
      (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj K).X (q + 1))
      (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj L).X q) :=
    HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f) q (q+1) (by simp)
  letI : ∀ i : ℤ, HasBinaryBiproduct
      ((((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj K).X (q + 1)).X i)
      ((((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).obj L).X q).X i) := by
    intro i
    change HasBinaryBiproduct ((K.X i).X (q+1)) ((L.X i).X q)
    infer_instance
  dsimp [columnCone]
  exact (HomologicalComplex.eval C (up ℤ) p).mapIso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f) q (q + 1) (by simp)) ≪≫
    HomologicalComplex.biprodXIso _ _ p

variable [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

/-- Construct a literal total of the vertical column cone from the two given
totals. Only the pointwise and total-degree biproducts are needed. -/
theorem hasTotal_columnCone : (columnCone f).HasTotal (up ℤ) := by
  intro n
  let A : ℤ → C := fun p => (K.X p).X (n + 1 - p)
  let B : ℤ → C := fun p => (L.X p).X (n - p)
  haveI hA : HasCoproduct A := by
    apply hasCoproduct_of_equiv_of_iso
      (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n + 1)) A
      (diagEquiv (n + 1)).symm
    intro p
    exact Iso.refl _
  haveI hB : HasCoproduct B := by
    apply hasCoproduct_of_equiv_of_iso
      (L.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n) B
      (diagEquiv n).symm
    intro p
    exact Iso.refl _
  have eA : ∐ A ≅ (K.total (up ℤ)).X (n+1) := by
    change ∐ A ≅ ∐ (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n+1))
    letI : HasCoproduct (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n+1) ∘
      (diagEquiv (n+1)).symm) := hA
    change ∐ (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n+1) ∘
      (diagEquiv (n+1)).symm) ≅ ∐ (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n+1))
    exact Sigma.reindex (diagEquiv (n+1)).symm _
  have eB : ∐ B ≅ (L.total (up ℤ)).X n := by
    change ∐ B ≅ ∐ (L.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n)
    letI : HasCoproduct (L.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n ∘
      (diagEquiv n).symm) := hB
    change ∐ (L.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n ∘
      (diagEquiv n).symm) ≅ ∐ (L.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n)
    exact Sigma.reindex (diagEquiv n).symm _
  letI : HasBinaryBiproduct (∐ A) (∐ B) :=
    hasBinaryBiproduct_of_iso eA.symm eB.symm
  letI : ∀ p : ℤ, HasBinaryBiproduct (A p) (B p) := by
    intro p
    change HasBinaryBiproduct ((K.X p).X (n+1-p)) ((L.X p).X (n-p))
    have hdeg : n-p+1 = n+1-p := by omega
    simpa only [hdeg] using
      (inferInstance : HasBinaryBiproduct ((K.X p).X ((n-p)+1)) ((L.X p).X (n-p)))
  haveI hAB : HasCoproduct (fun p => A p ⊞ B p) :=
    hasCoproduct_pointwise_biprod A B
  apply hasCoproduct_of_equiv_of_iso (fun p => A p ⊞ B p)
    ((columnCone f).toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n)
    (diagEquiv n)
  rintro ⟨⟨p,q⟩,h⟩
  have hq : q = n - p := by
    change p + q = n at h
    omega
  subst q
  change ((columnCone f).X p).X (n-p) ≅
    ((K.X p).X (n+1-p)) ⊞ ((L.X p).X (n-p))
  have hdeg : n-p+1 = n+1-p := by omega
  simpa only [hdeg] using componentIso f p (n-p)
omit [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)] in
private theorem hasHomotopyCofiber_total_map : HomologicalComplex.HasHomotopyCofiber
    (HomologicalComplex₂.total.map f (up ℤ)) := by
  letI : ∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n) :=
    fun n => inferInstance
  infer_instance

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

private noncomputable def componentMap (p q n : ℤ) (h : p + q = n) :
    ((columnCone f).X p).X q ⟶
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).X n := by
  letI := hasHomotopyCofiber_total_map f
  letI := hasHomotopyCofiber_flip_map f
  letI : HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q) := inferInstance
  let e := componentIso f p q
  let s : ((K.X p).X (q + 1)) ⟶
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).X n :=
    (p.negOnePow • K.ιTotal (up ℤ) p (q + 1) (n + 1)
      (by change p + (q + 1) = n + 1; omega)) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex₂.total.map f (up ℤ))).v (n + 1) n (by omega)
  let t : ((L.X p).X q) ⟶
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).X n :=
    L.ιTotal (up ℤ) p q n (by change p + q = n; exact h) ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex₂.total.map f (up ℤ))).f n
  exact e.hom ≫ biprod.desc s t

private noncomputable def comparisonMap [(columnCone f).HasTotal (up ℤ)] (n : ℤ) :
    ((columnCone f).total (up ℤ)).X n ⟶
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).X n := by
  letI := hasHomotopyCofiber_total_map f
  exact (columnCone f).totalDesc (fun p q h =>
    componentMap f p q n (by change p + q = n at h; exact h))

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

omit [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)] in
private theorem target_branch_d (p q n : ℤ) (h : p + q = n) :
    (L.ιTotal (up ℤ) p q n (by change p + q = n; exact h)) ≫
      (CochainComplex.mappingCone.inr (HomologicalComplex₂.total.map f (up ℤ))).f n ≫
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).d n (n+1) =
    (L.ιTotal (up ℤ) p q n (by change p + q = n; exact h)) ≫
      (L.total (up ℤ)).d n (n+1) ≫
      (CochainComplex.mappingCone.inr (HomologicalComplex₂.total.map f (up ℤ))).f (n+1) := by
  letI := hasHomotopyCofiber_total_map f
  simp only [CochainComplex.mappingCone.inr_f_d]

omit [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)] in
private theorem source_branch_d (p q n : ℤ) (h : p + q = n) :
    (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
      (by change p + (q+1) = n+1; omega)) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex₂.total.map f (up ℤ))).v (n+1) n (by omega) ≫
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).d n (n+1) =
    ((p.negOnePow • (f.f p).f (q+1)) ≫
      L.ιTotal (up ℤ) p (q+1) (n+1)
        (by change p + (q+1) = n+1; omega)) ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex₂.total.map f (up ℤ))).f (n+1) -
    (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
      (by change p + (q+1) = n+1; omega)) ≫
      (K.total (up ℤ)).d (n+1) (n+1+1) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex₂.total.map f (up ℤ))).v (n+1+1) (n+1) (by omega) := by
  letI := hasHomotopyCofiber_total_map f
  rw [CochainComplex.mappingCone.inl_v_d
    (HomologicalComplex₂.total.map f (up ℤ)) (n+1) n (n+1+1) (by omega) (by omega)]
  simp only [Preadditive.comp_sub, Category.assoc]
  congr 1
  rw [← Category.assoc, Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map]
  simp only [Linear.units_smul_comp, Category.assoc]

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

private theorem componentMap_source (p q n : ℤ) (h : p + q = n) :
    biprod.inl ≫ (componentIso f p q).inv ≫ componentMap f p q n h =
      (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
        (by change p + (q+1) = n+1; omega)) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex₂.total.map f (up ℤ))).v (n+1) n (by omega) := by
  letI := hasHomotopyCofiber_total_map f
  letI := hasHomotopyCofiber_flip_map f
  dsimp [componentMap]
  simp

private theorem componentMap_target (p q n : ℤ) (h : p + q = n) :
    biprod.inr ≫ (componentIso f p q).inv ≫ componentMap f p q n h =
      L.ιTotal (up ℤ) p q n (by change p + q = n; exact h) ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex₂.total.map f (up ℤ))).f n := by
  letI := hasHomotopyCofiber_total_map f
  letI := hasHomotopyCofiber_flip_map f
  dsimp [componentMap]
  simp

end HomologicalComplex₂


namespace HomologicalComplex₂
set_option backward.isDefEq.respectTransparency false
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

private noncomputable def colInl (p q : ℤ) :
    ((K.X p).X (q+1)) ⟶ ((columnCone f).X p).X q := by
  letI := hasHomotopyCofiber_flip_map f
  exact biprod.inl ≫ (componentIso f p q).inv

private noncomputable def colInr (p q : ℤ) :
    ((L.X p).X q) ⟶ ((columnCone f).X p).X q := by
  letI := hasHomotopyCofiber_flip_map f
  exact biprod.inr ≫ (componentIso f p q).inv

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInl_eq (p q : ℤ)
    [HomologicalComplex.HasHomotopyCofiber
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)] :
    colInl f p q =
      ((CochainComplex.mappingCone.inl
        ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).v
          (q+1) q (by omega)).f p := by
  letI := hasHomotopyCofiber_flip_map f
  dsimp only [colInl, componentIso]
  simp only [id_eq, Iso.trans_inv, HomologicalComplex.biprodXIso, Functor.mapBiprod_inv]
  rw [← Category.assoc, biprod.inl_desc]
  simp only [Functor.mapIso_inv, ← Functor.map_comp,
    HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]
  rfl

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInr_eq (p q : ℤ)
    [HomologicalComplex.HasHomotopyCofiber
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)] :
    colInr f p q =
      ((CochainComplex.mappingCone.inr
        ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).f q).f p := by
  letI := hasHomotopyCofiber_flip_map f
  dsimp only [colInr, componentIso]
  simp only [id_eq, Iso.trans_inv, HomologicalComplex.biprodXIso, Functor.mapBiprod_inv]
  rw [← Category.assoc, biprod.inr_desc]
  simp only [Functor.mapIso_inv, ← Functor.map_comp,
    HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv]
  rfl

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInl_vertical (p q : ℤ) :
    colInl f p q ≫ ((columnCone f).X p).d q (q+1) =
      (f.f p).f (q+1) ≫ colInr f p (q+1) -
      (K.X p).d (q+1) (q+1+1) ≫ colInl f p (q+1) := by
  letI := hasHomotopyCofiber_flip_map f
  rw [colInl_eq f p q, colInl_eq f p (q+1), colInr_eq f p (q+1)]
  have hc := congrArg (fun g => g.f p)
    (CochainComplex.mappingCone.inl_v_d
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)
      (q+1) q (q+1+1) (by omega) (by omega))
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply] at hc
  convert hc using 1 <;> rfl

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInr_vertical (p q : ℤ) :
    colInr f p q ≫ ((columnCone f).X p).d q (q+1) =
      (L.X p).d q (q+1) ≫ colInr f p (q+1) := by
  letI := hasHomotopyCofiber_flip_map f
  rw [colInr_eq f p q, colInr_eq f p (q+1)]
  have hc := congrArg (fun g => g.f p)
    (CochainComplex.mappingCone.inr_f_d
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f) q (q+1))
  simp only [HomologicalComplex.comp_f] at hc
  convert hc using 1 <;> rfl

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInl_horizontal (p q : ℤ) :
    colInl f p q ≫ ((columnCone f).d p (p+1)).f q =
      (K.d p (p+1)).f (q+1) ≫ colInl f (p+1) q := by
  letI := hasHomotopyCofiber_flip_map f
  rw [colInl_eq f p q, colInl_eq f (p+1) q]
  have hc := (CochainComplex.mappingCone.inl
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).v
        (q+1) q (by omega) |>.comm p (p+1)
  convert hc using 1 <;> rfl

omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ (n : ℤ), HasBinaryBiproduct ((K.total (up ℤ)).X (n + 1)) ((L.total (up ℤ)).X n)] in
private theorem colInr_horizontal (p q : ℤ) :
    colInr f p q ≫ ((columnCone f).d p (p+1)).f q =
      (L.d p (p+1)).f q ≫ colInr f (p+1) q := by
  letI := hasHomotopyCofiber_flip_map f
  rw [colInr_eq f p q, colInr_eq f (p+1) q]
  have hc := ((CochainComplex.mappingCone.inr
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).f q).comm p (p+1)
  convert hc using 1 <;> rfl

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
set_option backward.isDefEq.respectTransparency false
variable {C : Type*} [Category* C] [Preadditive C]

private theorem ι_total_d (T : HomologicalComplex₂ C (up ℤ) (up ℤ))
    [T.HasTotal (up ℤ)] (p q n : ℤ) (h : p+q=n) :
    T.ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
      (T.total (up ℤ)).d n (n+1) =
    (T.d p (p+1)).f q ≫ T.ιTotal (up ℤ) (p+1) q (n+1)
      (by change p+1+q=n+1; omega) +
    p.negOnePow • ((T.X p).d q (q+1) ≫
      T.ιTotal (up ℤ) p (q+1) (n+1)
        (by change p+(q+1)=n+1; omega)) := by
  have hhor : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p+1,q) = n+1 := by
    change p+1+q=n+1; omega
  have hver : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p,q+1) = n+1 := by
    change p+(q+1)=n+1; omega
  change T.ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
    (T.D₁ (up ℤ) n (n+1) + T.D₂ (up ℤ) n (n+1)) = _
  rw [Preadditive.comp_add, T.ι_D₁, T.ι_D₂]
  rw [T.d₁_eq (up ℤ) (by simp : (up ℤ).Rel p (p+1)) q (n+1) hhor]
  rw [T.d₂_eq (up ℤ) p (by simp : (up ℤ).Rel q (q+1)) (n+1) hver]
  simp only [show ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p,q) = 1 from rfl,
    show ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) (p,q) = p.negOnePow from rfl,
    one_smul]

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
set_option backward.isDefEq.respectTransparency false
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]
  [(columnCone f).HasTotal (up ℤ)]

omit [(columnCone f).HasTotal (up ℤ)] in
private theorem colInr_componentMap (p q n : ℤ) (h : p+q=n) :
    colInr f p q ≫ componentMap f p q n h =
      L.ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex₂.total.map f (up ℤ))).f n := by
  letI := hasHomotopyCofiber_total_map f
  letI := hasHomotopyCofiber_flip_map f
  simpa only [colInr, Category.assoc] using componentMap_target f p q n h

omit [(columnCone f).HasTotal (up ℤ)] in
private theorem colInl_componentMap (p q n : ℤ) (h : p+q=n) :
    colInl f p q ≫ componentMap f p q n h =
      (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
        (by change p+(q+1)=n+1; omega)) ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex₂.total.map f (up ℤ))).v (n+1) n (by omega) := by
  letI := hasHomotopyCofiber_total_map f
  letI := hasHomotopyCofiber_flip_map f
  simpa only [colInl, Category.assoc] using componentMap_source f p q n h

private theorem comparison_d (n : ℤ) :
    comparisonMap f n ≫
      (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).d n (n+1) =
    ((columnCone f).total (up ℤ)).d n (n+1) ≫ comparisonMap f (n+1) := by
  letI := hasHomotopyCofiber_total_map f
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  dsimp only [comparisonMap]
  rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
  rw [show ((columnCone f).total (up ℤ)).d n (n+1) =
      (columnCone f).D₁ (up ℤ) n (n+1) +
        (columnCone f).D₂ (up ℤ) n (n+1) from rfl]
  simp only [Preadditive.comp_add, Preadditive.add_comp]
  rw [← Category.assoc, HomologicalComplex₂.ι_D₁]
  rw [← Category.assoc, HomologicalComplex₂.ι_D₂]
  have hpq : p + q = n := by change p + q = n at h; exact h
  have hhor : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p+1,q) = n+1 := by
    change p+1+q=n+1; omega
  have hver : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p,q+1) = n+1 := by
    change p+(q+1)=n+1; omega
  rw [(columnCone f).d₁_eq (up ℤ) (by simp : (up ℤ).Rel p (p+1)) q (n+1) hhor]
  rw [(columnCone f).d₂_eq (up ℤ) p (by simp : (up ℤ).Rel q (q+1)) (n+1) hver]
  rw [show ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p,q) = 1 from rfl, one_smul]
  rw [show ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) (p,q) = p.negOnePow from rfl]
  simp only [Category.assoc, HomologicalComplex₂.ι_totalDesc,
    Linear.units_smul_comp]
  letI := hasHomotopyCofiber_flip_map f
  rw [← cancel_epi (componentIso f p q).inv]
  apply biprod.hom_ext'
  · simp only [Preadditive.comp_add, ← Category.assoc]
    rw [show (biprod.inl ≫ (componentIso f p q).inv) ≫ componentMap f p q n hpq =
      (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
        (by change p+(q+1)=n+1; omega)) ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex₂.total.map f (up ℤ))).v (n+1) n (by omega) from
      colInl_componentMap f p q n hpq]
    rw [Category.assoc, source_branch_d f p q n hpq]
    have hh := colInl_horizontal f p q
    have hv := colInl_vertical f p q
    simp only [colInl, colInr] at hh hv
    rw [hh]
    simp only [Linear.comp_units_smul, ← Category.assoc]
    rw [hv]
    simp only [Preadditive.sub_comp, smul_sub, Linear.units_smul_comp, Category.assoc]
    rw [componentMap_source f (p+1) q (n+1) (by omega),
      componentMap_target f p (q+1) (n+1) (by omega),
      componentMap_source f p (q+1) (n+1) (by omega)]
    have hk : p+(q+1)=n+1 := by omega
    have hK := ι_total_d K p (q+1) (n+1) hk
    simp only [Linear.units_smul_comp, ← Category.assoc]
    rw [hK]
    simp only [Int.negOnePow_succ, smul_add, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
      Units.neg_smul, Preadditive.add_comp, Category.assoc]
    simp only [Preadditive.comp_neg, Linear.comp_units_smul]
    abel
  · simp only [Preadditive.comp_add, ← Category.assoc]
    rw [show (biprod.inr ≫ (componentIso f p q).inv) ≫ componentMap f p q n hpq =
      L.ιTotal (up ℤ) p q n (by change p+q=n; exact hpq) ≫
        (CochainComplex.mappingCone.inr (HomologicalComplex₂.total.map f (up ℤ))).f n from
      colInr_componentMap f p q n hpq]
    rw [Category.assoc, target_branch_d f p q n hpq]
    have hh := colInr_horizontal f p q
    have hv := colInr_vertical f p q
    simp only [colInr] at hh hv
    rw [hh]
    simp only [Linear.comp_units_smul, ← Category.assoc]
    rw [hv]
    simp only [Category.assoc]
    rw [componentMap_target f (p+1) q (n+1) (by omega),
      componentMap_target f p (q+1) (n+1) (by omega)]
    rw [← Category.assoc, ι_total_d L p q n hpq]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]
  [(columnCone f).HasTotal (up ℤ)]

private noncomputable def sourceToColumnTotal (n : ℤ) :
    (K.total (up ℤ)).X (n+1) ⟶ ((columnCone f).total (up ℤ)).X n := by
  letI := hasTotal_columnCone f
  exact K.totalDesc (fun p r h => by
    let q : ℤ := r-1
    have hq : q+1 = r := by dsimp [q]; omega
    have hn : p+q = n := by
      change p+r=n+1 at h
      dsimp [q]
      omega
    let j : ((K.X p).X (q+1)) ⟶ ((columnCone f).total (up ℤ)).X n :=
      (p.negOnePow • biprod.inl) ≫ (componentIso f p q).inv ≫
        (columnCone f).ιTotal (up ℤ) p q n
          (by change p+q=n; exact hn)
    exact hq ▸ j)

private noncomputable def targetToColumnTotal (n : ℤ) :
    (L.total (up ℤ)).X n ⟶ ((columnCone f).total (up ℤ)).X n := by
  letI := hasTotal_columnCone f
  exact L.totalDesc (fun p q h =>
    biprod.inr ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n at h; exact h))

private noncomputable def inverseMap (n : ℤ) :
    (CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ))).X n ⟶
      ((columnCone f).total (up ℤ)).X n := by
  letI := hasTotal_columnCone f
  letI := hasHomotopyCofiber_total_map f
  exact (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (HomologicalComplex₂.total.map f (up ℤ)) n (n+1) (by simp)).hom ≫
    biprod.desc (sourceToColumnTotal f n) (targetToColumnTotal f n)

private theorem inverseMap_source (n : ℤ) :
    (CochainComplex.mappingCone.inl (HomologicalComplex₂.total.map f (up ℤ))).v
      (n+1) n (by omega) ≫ inverseMap f n = sourceToColumnTotal f n := by
  letI := hasHomotopyCofiber_total_map f
  dsimp [inverseMap]
  change HomologicalComplex.homotopyCofiber.inlX
      (HomologicalComplex₂.total.map f (up ℤ)) (n+1) n (by simp) ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (HomologicalComplex₂.total.map f (up ℤ)) n (n+1) (by simp)).hom ≫
      biprod.desc (sourceToColumnTotal f n) (targetToColumnTotal f n) = _
  rw [← Category.assoc,
    HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom]
  simp

private theorem inverseMap_target (n : ℤ) :
    (CochainComplex.mappingCone.inr (HomologicalComplex₂.total.map f (up ℤ))).f n ≫
      inverseMap f n = targetToColumnTotal f n := by
  letI := hasHomotopyCofiber_total_map f
  dsimp [inverseMap]
  change HomologicalComplex.homotopyCofiber.inrX
      (HomologicalComplex₂.total.map f (up ℤ)) n ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (HomologicalComplex₂.total.map f (up ℤ)) n (n+1) (by simp)).hom ≫
      biprod.desc (sourceToColumnTotal f n) (targetToColumnTotal f n) = _
  rw [← Category.assoc,
    HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)] in
private theorem source_transport (p q₀ q n : ℤ) (e : q₀=q)
    (he : q₀+1=q+1) (h₀ : p+q₀=n) (h : p+q=n) :
    he ▸ ((p.negOnePow • biprod.inl) ≫ (componentIso f p q₀).inv ≫
      (columnCone f).ιTotal (up ℤ) p q₀ n
        (by change p+q₀=n; exact h₀)) =
    p.negOnePow • (biprod.inl ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h)) := by
  subst q₀
  simp only [Linear.units_smul_comp]

private theorem ι_sourceToColumnTotal (p q n : ℤ) (h : p+q=n) :
    K.ιTotal (up ℤ) p (q+1) (n+1)
      (by change p+(q+1)=n+1; omega) ≫ sourceToColumnTotal f n =
    p.negOnePow • (biprod.inl ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h)) := by
  dsimp [sourceToColumnTotal]
  rw [K.ι_totalDesc]
  exact source_transport f p (q+1-1) q n (by omega) (by omega) (by omega) h

private theorem ι_targetToColumnTotal (p q n : ℤ) (h : p+q=n) :
    L.ιTotal (up ℤ) p q n
      (by change p+q=n; exact h) ≫ targetToColumnTotal f n =
    biprod.inr ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) := by
  dsimp [targetToColumnTotal]
  rw [L.ι_totalDesc]

private theorem componentMap_inverse_source (p q n : ℤ) (h : p+q=n) :
    biprod.inl ≫ (componentIso f p q).inv ≫ componentMap f p q n h ≫
      inverseMap f n =
    biprod.inl ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) := by
  calc
    _ = (biprod.inl ≫ (componentIso f p q).inv ≫ componentMap f p q n h) ≫
        inverseMap f n := by simp only [Category.assoc]
    _ = _ := by
      rw [componentMap_source]
      rw [Category.assoc, inverseMap_source]
      rw [Linear.units_smul_comp]
      rw [← Category.assoc, ι_sourceToColumnTotal f p q n h]
      simp [smul_smul]

private theorem componentMap_inverse_target (p q n : ℤ) (h : p+q=n) :
    biprod.inr ≫ (componentIso f p q).inv ≫ componentMap f p q n h ≫
      inverseMap f n =
    biprod.inr ≫ (componentIso f p q).inv ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) := by
  calc
    _ = (biprod.inr ≫ (componentIso f p q).inv ≫ componentMap f p q n h) ≫
        inverseMap f n := by simp only [Category.assoc]
    _ = _ := by
      rw [componentMap_target]
      rw [Category.assoc, inverseMap_target]
      exact ι_targetToColumnTotal f p q n h

private theorem componentMap_inverse (p q n : ℤ) (h : p+q=n) :
    componentMap f p q n h ≫ inverseMap f n =
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) := by
  rw [← cancel_epi (componentIso f p q).inv]
  apply biprod.hom_ext'
  · simpa only [Category.assoc] using componentMap_inverse_source f p q n h
  · simpa only [Category.assoc] using componentMap_inverse_target f p q n h

private theorem comparisonMap_inverse (n : ℤ) :
    comparisonMap f n ≫ inverseMap f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  rw [← Category.assoc]
  dsimp [comparisonMap]
  rw [HomologicalComplex₂.ι_totalDesc]
  change p+q=n at h
  rw [componentMap_inverse f p q n h]
  simp

private theorem targetToColumnTotal_comparisonMap (n : ℤ) :
    targetToColumnTotal f n ≫ comparisonMap f n =
      (CochainComplex.mappingCone.inr (HomologicalComplex₂.total.map f (up ℤ))).f n := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  rw [← Category.assoc]
  dsimp [targetToColumnTotal]
  rw [L.ι_totalDesc]
  dsimp [comparisonMap]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ι_totalDesc]
  change p+q=n at h
  exact componentMap_target f p q n h

private theorem sourceToColumnTotal_comparisonMap (n : ℤ) :
    sourceToColumnTotal f n ≫ comparisonMap f n =
      (CochainComplex.mappingCone.inl (HomologicalComplex₂.total.map f (up ℤ))).v
        (n+1) n (by omega) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p r h
  generalize hq : r-1=q
  have hr : r=q+1 := by omega
  subst r
  have hn : p+q=n := by
    change p+(q+1)=n+1 at h
    omega
  rw [← Category.assoc, ι_sourceToColumnTotal f p q n hn]
  rw [Linear.units_smul_comp]
  dsimp [comparisonMap]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ι_totalDesc]
  rw [componentMap_source]
  simp [smul_smul]

private theorem inverseMap_comparisonMap (n : ℤ) :
    inverseMap f n ≫ comparisonMap f n = 𝟙 _ := by
  letI := hasHomotopyCofiber_total_map f
  apply CochainComplex.mappingCone.ext_from
    (HomologicalComplex₂.total.map f (up ℤ)) (n+1) n (by omega)
  · rw [← Category.assoc, inverseMap_source]
    rw [sourceToColumnTotal_comparisonMap]
    simp
  · rw [← Category.assoc, inverseMap_target]
    rw [targetToColumnTotal_comparisonMap]
    simp

end HomologicalComplex₂


namespace HomologicalComplex₂
open ComplexShape
attribute [local instance] hasTotal_columnCone hasHomotopyCofiber_total_map
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

/-- The literal total of the vertical column cone is the mapping cone of the
literal total map. The source branch at horizontal degree `p` acquires the
sign `(-1)^p`; the target branch is unchanged. -/
noncomputable def totalColumnConeIso :
    (columnCone f).total (up ℤ) ≅
      CochainComplex.mappingCone (HomologicalComplex₂.total.map f (up ℤ)) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    { hom := comparisonMap f n
      inv := inverseMap f n
      hom_inv_id := comparisonMap_inverse f n
      inv_hom_id := inverseMap_comparisonMap f n }) ?_
  intro n n' h
  have hn : n+1=n' := by change n+1=n' at h; exact h
  subst n'
  exact comparison_d f n

end HomologicalComplex₂

namespace HomologicalComplex₂
open ComplexShape
attribute [local instance] hasHomotopyCofiber_flip_map hasTotal_columnCone
  hasHomotopyCofiber_total_map
variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L)
  [∀ p q : ℤ, HasBinaryBiproduct ((K.X p).X (q + 1)) ((L.X p).X q)]
  [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]
  [∀ n : ℤ, HasBinaryBiproduct ((K.total (up ℤ)).X (n+1)) ((L.total (up ℤ)).X n)]

/-- This source-branch rewrite rule exposes the sign needed to reconcile
totalization with the negated differential on the shifted cone source. -/
theorem ι_totalColumnConeIso_hom_source (p q n : ℤ) (h : p+q=n) :
    ((CochainComplex.mappingCone.inl
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).v
        (q+1) q (by omega)).f p ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) ≫
      (totalColumnConeIso f).hom.f n =
    (p.negOnePow • K.ιTotal (up ℤ) p (q+1) (n+1)
      (by change p+(q+1)=n+1; omega)) ≫
      (CochainComplex.mappingCone.inl
        (HomologicalComplex₂.total.map f (up ℤ))).v (n+1) n (by omega) := by
  rw [← colInl_eq f p q]
  change colInl f p q ≫
    (columnCone f).ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
    comparisonMap f n = _
  dsimp [comparisonMap]
  rw [HomologicalComplex₂.ι_totalDesc]
  exact colInl_componentMap f p q n h

/-- Use this rule to transport the target-cone inclusion through the
comparison without unfolding the coproduct descent maps. -/
theorem ι_totalColumnConeIso_hom_target (p q n : ℤ) (h : p+q=n) :
    ((CochainComplex.mappingCone.inr
      ((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f)).f q).f p ≫
      (columnCone f).ιTotal (up ℤ) p q n
        (by change p+q=n; exact h) ≫
      (totalColumnConeIso f).hom.f n =
    L.ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex₂.total.map f (up ℤ))).f n := by
  rw [← colInr_eq f p q]
  change colInr f p q ≫
    (columnCone f).ιTotal (up ℤ) p q n (by change p+q=n; exact h) ≫
    comparisonMap f n = _
  dsimp [comparisonMap]
  rw [HomologicalComplex₂.ι_totalDesc]
  exact colInr_componentMap f p q n h

end HomologicalComplex₂
