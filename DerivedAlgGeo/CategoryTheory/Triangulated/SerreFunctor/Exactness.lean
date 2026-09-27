/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.CategoryTheory.Triangulated.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Shift
import DerivedAlgGeo.CategoryTheory.Triangulated.ShiftFunctor
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Exactness of the Serre functor

The signed shift comparison gives the rotation boundary for the image of a
distinguished triangle. Complete that boundary to a distinguished triangle,
then use Serre duality and the exact Hom sequences to identify its middle
object with the Serre image. The resulting `SerreFunctorData.isTriangulated`
requires no equivalence or Hom-finiteness hypothesis.

This file uses an arbitrary distinguished completion. It does not postulate
the image triangle as distinguished.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.SerreFunctor.SerreFunctorData

universe w v u
variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C]

open CategoryTheory.Limits CategoryTheory.Preadditive

variable [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [HasZeroObject C] [Pretriangulated C]

-- The target triangle is an arbitrary distinguished completion with the
-- prescribed boundary; its middle object is compared to the Serre image.

private def prescribedFunctional (D : SerreFunctorData k C)
    (T : Pretriangulated.Triangle C) (E : C) (p : E ⟶ D.S.obj T.obj₃) :
    ((T.obj₂ ⟶ D.S.obj T.obj₁) × (T.obj₃ ⟶ E)) →ₗ[k] k :=
  ((D.eta T.obj₂ (D.S.obj T.obj₁)).symm (D.S.map T.mor₁)).coprod
    ((D.eta T.obj₃ E).symm p)

omit [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [HasShift C ℤ] [HasZeroObject C] [Pretriangulated C] in
private theorem eta_symm_apply_eq_trace (D : SerreFunctorData k C)
    {A B : C} (f : A ⟶ B) (g : B ⟶ D.S.obj A) :
    (D.eta A B).symm g f = D.trace A (f ≫ g) := by
  have hn := D.naturality_right f ((D.eta A B).symm g)
  simp only [LinearEquiv.apply_symm_apply] at hn
  change (D.eta A B).symm g f = (D.eta A A).symm (f ≫ g) (𝟙 A)
  rw [← hn]
  simp [Linear.rightComp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem signed_kernel_residual (D : SerreFunctorData k C)
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (c : D.S.obj T.obj₃ ⟶ (D.S.obj T.obj₁)⟦(1 : ℤ)⟧)
    (hE : Pretriangulated.Triangle.mk i p c ∈ distTriang C)
    (u : T.obj₂ ⟶ D.S.obj T.obj₁) (v : T.obj₃ ⟶ E)
    (hw : u ≫ i + T.mor₂ ≫ v = 0) :
    ∃ b : T.obj₁⟦(1 : ℤ)⟧ ⟶ D.S.obj T.obj₃,
      (prescribedFunctional D T E p) (u, v) =
        D.trace (T.obj₁⟦(1 : ℤ)⟧)
          ((b ≫ c) ≫
            (letI : D.S.CommShift ℤ := D.signedCommShift
             (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁)) -
        D.trace (T.obj₁⟦(1 : ℤ)⟧) (b ≫ D.S.map T.mor₃) := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  have huv : u ≫ i = -(T.mor₂ ≫ v) := by
    exact (add_eq_zero_iff_eq_neg).mp hw
  have hcomm : T.mor₂ ≫ (-v) = u ≫ i := by
    rw [comp_neg, huv]
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism
    T.rotate (Pretriangulated.Triangle.mk i p c)
    (rot_of_distTriang T hT) hE u (-v) hcomm
  dsimp [Pretriangulated.Triangle.rotate, Pretriangulated.Triangle.mk] at ha₁ ha₂
  let b : T.obj₁⟦(1 : ℤ)⟧ ⟶ D.S.obj T.obj₃ := a
  have hb₁ : T.mor₃ ≫ b = (-v) ≫ p := ha₁
  have hb₂ : (-(shiftFunctor C (1 : ℤ)).map T.mor₁) ≫
      (shiftFunctor C (1 : ℤ)).map u = b ≫ c := ha₂
  refine ⟨b, ?_⟩
  have htrace₁ :
      (D.eta T.obj₂ (D.S.obj T.obj₁)).symm (D.S.map T.mor₁) u =
        D.trace T.obj₁ (T.mor₁ ≫ u) := by
    rw [eta_symm_apply_eq_trace D u (D.S.map T.mor₁)]
    exact D.trace_comp T.mor₁ u
  have htrace₂ :
      (D.eta T.obj₃ E).symm p v = D.trace T.obj₃ (v ≫ p) :=
    eta_symm_apply_eq_trace D v p
  have hcomp : v ≫ p = -(T.mor₃ ≫ b) := by
    calc
      v ≫ p = -((-v) ≫ p) := by simp
      _ = -(T.mor₃ ≫ b) := congrArg Neg.neg hb₁.symm
  have hlast :
      -((shiftFunctor C (1 : ℤ)).map (T.mor₁ ≫ u) ≫
          (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) =
        (b ≫ c) ≫ (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁ := by
    calc
      -((shiftFunctor C (1 : ℤ)).map (T.mor₁ ≫ u) ≫
          (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) =
          ((-(shiftFunctor C (1 : ℤ)).map T.mor₁) ≫
            (shiftFunctor C (1 : ℤ)).map u) ≫
            (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁ := by
          simp [Functor.map_comp, neg_comp]
      _ = (b ≫ c) ≫ (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁ :=
        congrArg (fun m => m ≫ (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) hb₂
  have htrace₃ :
      D.trace (T.obj₁⟦(1 : ℤ)⟧)
        ((b ≫ c) ≫ (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) =
      D.trace T.obj₁ (T.mor₁ ≫ u) := by
    rw [← hlast]
    simp only [map_neg, D.trace_shift_one_signed T.obj₁ (T.mor₁ ≫ u), neg_neg]
  have htrace₂' : D.trace T.obj₃ (v ≫ p) =
      -D.trace T.obj₃ (T.mor₃ ≫ b) := by
    rw [hcomp]
    simp only [map_neg]
  calc
    (prescribedFunctional D T E p) (u, v) =
        D.trace T.obj₁ (T.mor₁ ≫ u) + D.trace T.obj₃ (v ≫ p) := by
          simp only [prescribedFunctional, LinearMap.coprod_apply,
            htrace₁, htrace₂]
    _ = D.trace (T.obj₁⟦(1 : ℤ)⟧)
          ((b ≫ c) ≫ (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) -
        D.trace (T.obj₁⟦(1 : ℤ)⟧) (b ≫ D.S.map T.mor₃) := by
          rw [htrace₂', D.trace_comp T.mor₃ b, ← htrace₃]
          simp only [sub_eq_add_neg]

private def overlapMap (D : SerreFunctorData k C)
    (T : Pretriangulated.Triangle C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) :
    ((T.obj₂ ⟶ D.S.obj T.obj₁) × (T.obj₃ ⟶ E)) →ₗ[k] (T.obj₂ ⟶ E) :=
  (Linear.rightComp k T.obj₂ i).coprod (Linear.leftComp k E T.mor₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem signed_kernel_inclusion (D : SerreFunctorData k C)
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (hE : (letI : D.S.CommShift ℤ := D.signedCommShift
      Pretriangulated.Triangle.mk i p
        (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ∈
      distTriang C) :
    LinearMap.ker (overlapMap D T E i) ≤
      LinearMap.ker (prescribedFunctional D T E p) := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  intro w hw
  rcases w with ⟨u, v⟩
  have hzero : u ≫ i + T.mor₂ ≫ v = 0 := by
    simpa [overlapMap, LinearMap.coprod_apply] using
      (LinearMap.mem_ker).mp hw
  obtain ⟨b, hb⟩ := signed_kernel_residual D T hT E i p
    (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)
    hE u v hzero
  have hcancel :
      ((b ≫ (D.S.map T.mor₃ ≫
        (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ≫
          (D.S.commShiftIso (1 : ℤ)).inv.app T.obj₁) =
        b ≫ D.S.map T.mor₃ := by
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
  rw [hcancel, sub_self] at hb
  exact (LinearMap.mem_ker).mpr hb


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem signed_completion_kernel_exists
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ distTriang C) :
    ∃ (E : C) (i : D.S.obj T.obj₁ ⟶ E)
      (p : E ⟶ D.S.obj T.obj₃),
      (letI : D.S.CommShift ℤ := D.signedCommShift
       Pretriangulated.Triangle.mk i p
         (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ∈
        distTriang C ∧
      LinearMap.ker (overlapMap D T E i) ≤
        LinearMap.ker (prescribedFunctional D T E p) := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  obtain ⟨E, i, p, hE⟩ := distinguished_cocone_triangle₂
    (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)
  exact ⟨E, i, p, hE, signed_kernel_inclusion D T hT E i p hE⟩


universe u₁ u₂
variable {U : Type u₁} {V : Type u₂}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
private theorem exists_dual_factor (F : U →ₗ[k] V) (μ : U →ₗ[k] k)
    (hker : LinearMap.ker F ≤ LinearMap.ker μ) :
    ∃ psi : V →ₗ[k] k, psi.comp F = μ := by
  let μrange : LinearMap.range F →ₗ[k] k :=
    ((LinearMap.ker F).liftQ μ hker).comp F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨psi, hpsi⟩ := LinearMap.exists_extend μrange
  refine ⟨psi, ?_⟩
  ext u
  have h := LinearMap.congr_fun hpsi ⟨F u, ⟨u, rfl⟩⟩
  simpa [μrange, LinearMap.comp_apply] using h

omit [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]
  [HasZeroObject C] [Pretriangulated C] in
private theorem serre_comparison_of_kernel (D : SerreFunctorData k C)
    (T : Pretriangulated.Triangle C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (hker : LinearMap.ker (overlapMap D T E i) ≤
      LinearMap.ker (prescribedFunctional D T E p)) :
    ∃ phi : E ⟶ D.S.obj T.obj₂,
      i ≫ phi = D.S.map T.mor₁ ∧ phi ≫ D.S.map T.mor₂ = p := by
  obtain ⟨psi, hpsi⟩ := exists_dual_factor (overlapMap D T E i)
    (prescribedFunctional D T E p) hker
  refine ⟨D.eta T.obj₂ E psi, ?_, ?_⟩
  · have hpsi₁ : psi.comp (Linear.rightComp k T.obj₂ i) =
        (D.eta T.obj₂ (D.S.obj T.obj₁)).symm (D.S.map T.mor₁) := by
      ext f
      have h := LinearMap.congr_fun hpsi (f, 0)
      simpa [overlapMap, prescribedFunctional, LinearMap.comp_apply,
        LinearMap.coprod_apply] using h
    rw [← D.naturality_right i psi, hpsi₁]
    exact LinearEquiv.apply_symm_apply _ _
  · have hpsi₂ : psi.comp (Linear.leftComp k E T.mor₂) =
        (D.eta T.obj₃ E).symm p := by
      ext f
      have h := LinearMap.congr_fun hpsi (0, f)
      simpa [overlapMap, prescribedFunctional, LinearMap.comp_apply,
        LinearMap.coprod_apply] using h
    rw [← D.naturality_left T.mor₂ psi, hpsi₂]
    exact LinearEquiv.apply_symm_apply _ _
omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem serre_image_coyoneda_exact₂
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ distTriang C) (X : C)
    (u : X ⟶ D.S.obj T.obj₂)
    (hu : u ≫ D.S.map T.mor₂ = 0) :
    ∃ t : X ⟶ D.S.obj T.obj₁,
      u = t ≫ D.S.map T.mor₁ := by
  let μ : Module.Dual k (T.obj₂ ⟶ X) := (D.eta T.obj₂ X).symm u
  let F : (T.obj₂ ⟶ X) →ₗ[k] (T.obj₁ ⟶ X) :=
    Linear.leftComp k X T.mor₁
  have hker : LinearMap.ker F ≤ LinearMap.ker μ := by
    intro m hm
    have hmzero : T.mor₁ ≫ m = 0 := by
      exact (LinearMap.mem_ker).mp hm
    obtain ⟨n, hn⟩ := T.yoneda_exact₂ hT m hmzero
    have hnat := D.naturality_left T.mor₂ μ
    have hμg : μ.comp (Linear.leftComp k X T.mor₂) = 0 := by
      apply (D.eta T.obj₃ X).injective
      rw [hnat]
      simp [μ, hu]
    apply (LinearMap.mem_ker).mpr
    have h := LinearMap.congr_fun hμg n
    simpa [μ, LinearMap.comp_apply, Linear.leftComp, ← hn] using h
  obtain ⟨ν, hν⟩ := exists_dual_factor F μ hker
  refine ⟨D.eta T.obj₁ X ν, ?_⟩
  have hnat := D.naturality_left T.mor₁ ν
  rw [hν] at hnat
  simpa only [μ, LinearEquiv.apply_symm_apply] using hnat


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem serre_comparison_isIso_of_kernel
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ distTriang C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (c : D.S.obj T.obj₃ ⟶ (D.S.obj T.obj₁)⟦(1 : ℤ)⟧)
    (hE : Pretriangulated.Triangle.mk i p c ∈ distTriang C)
    (hc : D.S.map T.mor₂ ≫ c = 0)
    (φ : E ⟶ D.S.obj T.obj₂)
    (hi : i ≫ φ = D.S.map T.mor₁)
    (hp : φ ≫ D.S.map T.mor₂ = p)
    (hker : ∀ (X : C) (t : X ⟶ D.S.obj T.obj₁),
      t ≫ D.S.map T.mor₁ = 0 → t ≫ i = 0) : IsIso φ := by
  apply isIso_of_yoneda_map_bijective φ
  intro X
  constructor
  · intro x₁ x₂ h
    have hd : (x₁ - x₂) ≫ φ = 0 := by
      rw [sub_comp, sub_eq_zero.mpr h]
    have hdp : (x₁ - x₂) ≫ p = 0 := by
      rw [← hp, ← Category.assoc, hd, zero_comp]
    obtain ⟨t, ht⟩ :=
      (Pretriangulated.Triangle.mk i p c).coyoneda_exact₂ hE
        (x₁ - x₂) hdp
    change x₁ - x₂ = t ≫ i at ht
    have hta : t ≫ D.S.map T.mor₁ = 0 := by
      rw [← hi, ← Category.assoc, ← ht, hd]
    have hti := hker X t hta
    have hdzero : x₁ - x₂ = 0 := by rw [ht, hti]
    exact sub_eq_zero.mp hdzero
  · intro y
    have hyc : (y ≫ D.S.map T.mor₂) ≫ c = 0 := by
      rw [Category.assoc, hc, comp_zero]
    obtain ⟨x, hx⟩ :=
      (Pretriangulated.Triangle.mk i p c).coyoneda_exact₃ hE
        (y ≫ D.S.map T.mor₂) hyc
    let x' : X ⟶ E := x
    have hx' : y ≫ D.S.map T.mor₂ = x' ≫ p := hx
    have hdb : (y - x' ≫ φ) ≫ D.S.map T.mor₂ = 0 := by
      rw [sub_comp, Category.assoc, hp, ← hx', sub_self]
    obtain ⟨t, ht⟩ :=
      serre_image_coyoneda_exact₂ D T hT X
        (y - x' ≫ φ) hdb
    refine ⟨x' + t ≫ i, ?_⟩
    change (x' + t ≫ i) ≫ φ = y
    rw [add_comp, Category.assoc, hi, ← ht]
    abel


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem serre_first_kernel_of_invrot_boundary
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ distTriang C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E)
    (hboundary : D.S.map T.invRotate.mor₁ ≫ i = 0) :
    ∀ (X : C) (t : X ⟶ D.S.obj T.obj₁),
      t ≫ D.S.map T.mor₁ = 0 → t ≫ i = 0 := by
  intro X t ht
  have ht' : t ≫ D.S.map T.invRotate.mor₂ = 0 := ht
  obtain ⟨q, hq⟩ :=
    serre_image_coyoneda_exact₂ D T.invRotate
      (inv_rot_of_distTriang T hT) X t ht'
  rw [hq, Category.assoc, hboundary, comp_zero]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem serre_invrot_boundary_of_shift_compat
    (D : SerreFunctorData k C) [D.S.CommShift ℤ]
    (T : Pretriangulated.Triangle C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (c : D.S.obj T.obj₃ ⟶ (D.S.obj T.obj₁)⟦(1 : ℤ)⟧)
    (hE : Pretriangulated.Triangle.mk i p c ∈ distTriang C)
    (hcompat :
      (D.S.commShiftIso (-1 : ℤ)).inv.app T.obj₃ ≫
        D.S.map T.invRotate.mor₁ =
          (Pretriangulated.Triangle.mk i p c).invRotate.mor₁) :
    D.S.map T.invRotate.mor₁ ≫ i = 0 := by
  let ψ := (D.S.commShiftIso (-1 : ℤ)).app T.obj₃
  have hzero := comp_distTriang_mor_zero₁₂
    (Pretriangulated.Triangle.mk i p c).invRotate
    (inv_rot_of_distTriang _ hE)
  have hpre : ψ.inv ≫ (D.S.map T.invRotate.mor₁ ≫ i) = 0 := by
    rw [← Category.assoc]
    change ((D.S.commShiftIso (-1 : ℤ)).inv.app T.obj₃ ≫
      D.S.map T.invRotate.mor₁) ≫ i = 0
    rw [hcompat]
    exact hzero
  have h := congrArg (fun q => ψ.hom ≫ q) hpre
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp,
    comp_zero] using h


omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem serre_comparison_isIso_of_shift_compat
    (D : SerreFunctorData k C) [D.S.CommShift ℤ]
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (E : C)
    (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃)
    (c : D.S.obj T.obj₃ ⟶ (D.S.obj T.obj₁)⟦(1 : ℤ)⟧)
    (hE : Pretriangulated.Triangle.mk i p c ∈ distTriang C)
    (hc : D.S.map T.mor₂ ≫ c = 0)
    (φ : E ⟶ D.S.obj T.obj₂)
    (hi : i ≫ φ = D.S.map T.mor₁)
    (hp : φ ≫ D.S.map T.mor₂ = p)
    (hcompat :
      (D.S.commShiftIso (-1 : ℤ)).inv.app T.obj₃ ≫
        D.S.map T.invRotate.mor₁ =
          (Pretriangulated.Triangle.mk i p c).invRotate.mor₁) :
    IsIso φ :=
  serre_comparison_isIso_of_kernel D T hT E i p c hE hc φ hi hp
    (serre_first_kernel_of_invrot_boundary D T hT E i
      (serre_invrot_boundary_of_shift_compat D T E i p c hE hcompat))


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasZeroObject C] [Pretriangulated C] in
private theorem signed_invrot_compat
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (E : C) (i : D.S.obj T.obj₁ ⟶ E) (p : E ⟶ D.S.obj T.obj₃) :
    (letI : D.S.CommShift ℤ := D.signedCommShift
     (D.S.commShiftIso (-1 : ℤ)).inv.app T.obj₃) ≫
      D.S.map T.invRotate.mor₁ =
    (letI : D.S.CommShift ℤ := D.signedCommShift
     (Pretriangulated.Triangle.mk i p
       (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)).invRotate.mor₁) := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  have h := ((D.S.mapTriangleInvRotateIso).hom.app T).comm₁
  change (D.S.mapTriangle.obj T).invRotate.mor₁ ≫
      (D.S.mapTriangleInvRotateIso.hom.app T).hom₂ =
    (D.S.mapTriangleInvRotateIso.hom.app T).hom₁ ≫
      D.S.map T.invRotate.mor₁ at h
  rw [Functor.mapTriangleInvRotateIso_hom_app_hom₁,
    Functor.mapTriangleInvRotateIso_hom_app_hom₂] at h
  erw [Category.comp_id] at h
  exact h.symm


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem signed_completion_middle_isIso
    (D : SerreFunctorData k C) (T : Pretriangulated.Triangle C)
    (hT : T ∈ distTriang C) :
    ∃ (E : C) (i : D.S.obj T.obj₁ ⟶ E)
      (p : E ⟶ D.S.obj T.obj₃) (φ : E ⟶ D.S.obj T.obj₂),
      (letI : D.S.CommShift ℤ := D.signedCommShift
       Pretriangulated.Triangle.mk i p
         (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ∈
        distTriang C ∧
      i ≫ φ = D.S.map T.mor₁ ∧
      φ ≫ D.S.map T.mor₂ = p ∧ IsIso φ := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  obtain ⟨E, i, p, hE, hker⟩ := signed_completion_kernel_exists D T hT
  obtain ⟨φ, hi, hp⟩ := serre_comparison_of_kernel D T E i p hker
  have hc : D.S.map T.mor₂ ≫
      (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁) = 0 := by
    rw [← Category.assoc, ← D.S.map_comp, comp_distTriang_mor_zero₂₃ T hT]
    simp
  have hcompat := signed_invrot_compat D T E i p
  have hIso : IsIso φ :=
    serre_comparison_isIso_of_shift_compat D T hT E i p
      (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁)
      hE hc φ hi hp hcompat
  exact ⟨E, i, p, φ, hE, hi, hp, hIso⟩


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Serre functor preserves distinguished triangles with the signed
shift comparison. This does not require it to be an equivalence. -/
theorem isTriangulated
    (D : SerreFunctorData k C) :
    (letI : D.S.CommShift ℤ := D.signedCommShift
     D.S.IsTriangulated) := by
  letI : D.S.Additive := D.additive
  letI : D.S.CommShift ℤ := D.signedCommShift
  refine ⟨?_⟩
  intro T hT
  obtain ⟨E, i, p, φ, hE, hi, hp, hφ⟩ :=
    signed_completion_middle_isIso D T hT
  let e : Triangle.mk i p
      (D.S.map T.mor₃ ≫ (D.S.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≅
      D.S.mapTriangle.obj T :=
    Triangle.isoMk _ _ (Iso.refl _) (asIso φ) (Iso.refl _)
      (by simpa using hi)
      (by simpa using hp.symm)
      (by simp)
  exact isomorphic_distinguished _ hE _ e.symm


end CategoryTheory.SerreFunctor.SerreFunctorData
