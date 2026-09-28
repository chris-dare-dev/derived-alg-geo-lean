/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.TotalComplex
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

## Implementation notes

Evaluate in each total degree, view its diagonal coproduct as a colimit over
a discrete category, and commute the two colimits. Degreewise evaluation
then reflects the resulting universal property.

For the integer-indexed coordinate result, compose each summand inclusion
with the total differential and the canonical coproduct projection. The
horizontal term reaches the next column, while the signed vertical term stays
in the current column. Epi refinement supplies a preimage of the vertical
cycle, and its boundary leaves all earlier columns zero.

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
/-- The incoming differential at `(p,q+1)` is the horizontal contribution
from `(p-1,q+1)` plus the signed vertical contribution from `(p,q)`. -/
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
/-- A selected total coordinate is vertically closed when the selected
projection of the total differential and the preceding horizontal
contribution vanish. -/
lemma totalProjection_isCycle_of_horizontal_zero (p q n : ℤ) (h : p+q=n)
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
  apply totalProjection_isCycle_of_horizontal_zero K p q n h x
  · rw [hx, zero_comp]
  · rw [hl, zero_comp]

end VerticalClosure

section Elimination
variable [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
set_option backward.isDefEq.respectTransparency false in
/-- If all columns below `p` already vanish and column `p` is exact at `q`,
an epi refinement and one signed boundary correction clear every column at
most `p`, while preserving the total-cycle equation. -/
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
