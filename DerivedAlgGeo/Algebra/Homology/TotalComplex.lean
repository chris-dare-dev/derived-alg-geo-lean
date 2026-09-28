/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.TotalComplex
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
nonzero support. The results assume the literal total already exists.

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
* `HomologicalComplex₂.total_exactAt_of_diagonal_bounds` proves exactness
  from finite support and exactness on one total-degree diagonal.
* `HomologicalComplex₂.total_acyclic_of_diagonal_bounds` allows a separate
  finite support interval in every degree; `total_acyclic_of_upper_bounds`
  derives the uniform-rectangle case.

## Implementation notes

Evaluate in each total degree, view its diagonal coproduct as a colimit over
a discrete category, and commute the two colimits. Degreewise evaluation
then reflects the resulting universal property.

For the integer-indexed coordinate result, compose each summand inclusion
with the total differential and the canonical coproduct projection. The
horizontal term reaches the next column, while the signed vertical term stays
in the current column. Epi refinement supplies a preimage of the vertical
cycle, and its boundary leaves all earlier columns zero. Finite iteration
composes the epi refinements; the generic finite-support identity from
`CategoryTheory.Limits.Sigma` makes the zero-coordinate residual a zero map.

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
private lemma total_eq_zero_of_finiteSupport (n : ℤ) (s : Finset ℤ)
    (hz : ∀ p q, p+q=n → p ∉ s → IsZero ((K.X p).X q))
    {A : C} (x : A ⟶ (K.total (ComplexShape.up ℤ)).X n)
    (h : ∀ p ∈ s, x ≫ K.totalProjection p (n-p) n (by omega) = 0) : x = 0 := by
  classical
  let f := K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) n
  apply Sigma.hom_eq_zero_of_finiteSupport f (s.map (diagonalEmbedding n)) ?_ x ?_
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
private theorem exists_finite_totalCycleRefinement (n a : ℤ) (m : ℕ)
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
exactness criterion turns that epi-refined boundary into `ExactAt`. -/
theorem total_exactAt_of_diagonal_bounds (n a b : ℤ)
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
      exists_finite_totalCycleRefinement K n a (b+1-a).toNat
        (fun p hp hpb => diagonal_exactAt_to_short K n p
          (hExact p hp (by omega))) x hx
        (fun p q hpq hp => (hLower p q hpq hp).eq_of_tgt _ _)
    refine ⟨B, π, hπ, t, ?_⟩
    apply sub_eq_zero.mp
    apply total_eq_zero_of_finiteSupport K n (Finset.Icc a b)
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
    apply total_eq_zero_of_finiteSupport K n ∅
    · intro p q hpq _
      by_cases hpa : p < a
      · exact hLower p q hpq hpa
      · exact hUpper p q hpq (by omega)
    · simp

/-- Apply degree-local exactness to each diagonal, allowing the support
interval and required column exactness to vary with total degree. -/
theorem total_acyclic_of_diagonal_bounds
    (hData : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ p q : ℤ, p + q = n → p < a → IsZero ((K.X p).X q)) ∧
      (∀ p q : ℤ, p + q = n → b < p → IsZero ((K.X p).X q)) ∧
      (∀ p : ℤ, a ≤ p → p ≤ b → (K.X p).ExactAt (n-p))) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  intro n
  obtain ⟨a, b, hLower, hUpper, hExact⟩ := hData n
  exact total_exactAt_of_diagonal_bounds K n a b hLower hUpper hExact

/-- A uniform upper rectangle gives finite support on every diagonal. Only
columns and degrees inside that rectangle need the exactness premise. -/
theorem total_acyclic_of_upper_bounds (b c : ℤ)
    (hp : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hq : ∀ p q : ℤ, c < q → IsZero ((K.X p).X q))
    (hExact : ∀ p q : ℤ, p ≤ b → q ≤ c → (K.X p).ExactAt q) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  intro n
  apply total_exactAt_of_diagonal_bounds K n (n-c) b
  · intro p q hpq hpl
    exact hq p q (by omega)
  · intro p q hpq hpu
    exact hp p q hpu
  · intro p hpl hpu
    exact hExact p (n-p) hpu (by omega)

end FiniteRefinement
end HomologicalComplex₂
