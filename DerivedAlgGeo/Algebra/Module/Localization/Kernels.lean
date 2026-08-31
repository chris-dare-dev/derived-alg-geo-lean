/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels and localization of modules

This file contains the algebraic kernel maps used to express that localization
of modules is left exact. The statements are independent of sites and schemes:
the geometric coherent-sheaf argument is a consumer of this root.

## Main results

* `LinearMap.kerMap` is the map on kernels induced by a commutative square;
* `IsLocalizedModule.kerMap` proves that the induced linear map is a
  localization map;
* `IsLocalizedModule.kernelMap` is the corresponding statement for categorical
  kernels in `ModuleCat`;
* `IsLocalizedModule.kernelNatTrans` applies the result to a natural
  transformation between finite-limit-preserving functors.
-/

open CategoryTheory Limits

namespace LinearMap

universe w

variable {A M M' N N' : Type w} [CommSemiring A]
variable [AddCommMonoid M] [Module A M] [AddCommMonoid M'] [Module A M']
variable [AddCommMonoid N] [Module A N] [AddCommMonoid N'] [Module A N']

/-- The map on kernels induced by a commutative square of linear maps. -/
def kerMap (a : M →ₗ[A] M') (b : N →ₗ[A] N')
    (g : M →ₗ[A] N) (g' : M' →ₗ[A] N') (h : g'.comp a = b.comp g) :
    g.ker →ₗ[A] g'.ker where
  toFun x := ⟨a x.1, by
    change g' (a x.1) = 0
    have hh := LinearMap.congr_fun h x.1
    dsimp at hh
    rw [hh]
    simp⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end LinearMap

namespace IsLocalizedModule

universe w

variable {A M M' N N' : Type w} [CommSemiring A]
variable [AddCommMonoid M] [Module A M] [AddCommMonoid M'] [Module A M']
variable [AddCommMonoid N] [Module A N] [AddCommMonoid N'] [Module A N']
variable (S : Submonoid A)

/-- Localization commutes with kernels, for arbitrary choices of localized targets. -/
theorem kerMap (a : M →ₗ[A] M') [ha : IsLocalizedModule S a]
    (b : N →ₗ[A] N') [hb : IsLocalizedModule S b]
    (g : M →ₗ[A] N) (g' : M' →ₗ[A] N') (h : g'.comp a = b.comp g) :
    IsLocalizedModule S (LinearMap.kerMap a b g g' h) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact ((Module.End.isUnit_iff _).mp (ha.map_units s)).1
        (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp (ha.map_units s)).2 y.1
      have hz' : g' z = 0 := by
        apply ((Module.End.isUnit_iff _).mp (hb.map_units s)).1
        have hz'' := congrArg g' hz
        have hy : g' y.1 = 0 := y.2
        simpa only [Module.algebraMap_end_apply, map_smul, hy, smul_zero] using hz''
      exact ⟨⟨z, hz'⟩, Subtype.ext hz⟩
  surj y := by
    obtain ⟨⟨x, s⟩, hs⟩ := ha.surj y.1
    have hh := LinearMap.congr_fun h x
    dsimp at hh
    have heq : b (g x) = b 0 := by
      rw [map_zero]
      calc
        b (g x) = g' (a x) := hh.symm
        _ = g' (s.1 • y.1) := congrArg g' hs.symm
        _ = 0 := by simp
    obtain ⟨t, ht⟩ := hb.exists_of_eq heq
    have htx : g (t.1 • x) = 0 := by
      rw [map_smul]
      change t.1 • g x = t.1 • 0 at ht
      simpa only [smul_zero] using ht
    refine ⟨⟨⟨t.1 • x, htx⟩, t * s⟩, ?_⟩
    apply Subtype.ext
    change (t * s).1 • y.1 = a (t.1 • x)
    rw [Submonoid.coe_mul, mul_smul, map_smul]
    exact congrArg (fun z => t.1 • z) hs
  exists_of_eq {x y} hxy := by
    obtain ⟨s, hs⟩ := ha.exists_of_eq (congrArg Subtype.val hxy)
    exact ⟨s, Subtype.ext hs⟩

variable {A : Type w} [CommRing A] (S : Submonoid A)

/-- Localization commutes with the map on categorical kernels in `ModuleCat`. -/
theorem kernelMap {M M' N N' : ModuleCat.{w} A}
    (a : M ⟶ M') [IsLocalizedModule S a.hom]
    (b : N ⟶ N') [IsLocalizedModule S b.hom]
    (g : M ⟶ N) (g' : M' ⟶ N') (h : g ≫ b = a ≫ g') :
    IsLocalizedModule S (kernel.map g g' a b h).hom := by
  let hlin : g'.hom.comp a.hom = b.hom.comp g.hom :=
    ModuleCat.hom_ext_iff.mp h.symm
  let L := LinearMap.kerMap a.hom b.hom g.hom g'.hom hlin
  letI : IsLocalizedModule S L :=
    IsLocalizedModule.kerMap S a.hom b.hom g.hom g'.hom hlin
  let e := ModuleCat.kernelIsoKer g
  let e' := ModuleCat.kernelIsoKer g'
  letI : IsLocalizedModule S (e'.symm.toLinearEquiv.toLinearMap ∘ₗ L) := inferInstance
  letI : IsLocalizedModule S
      ((e'.symm.toLinearEquiv.toLinearMap ∘ₗ L) ∘ₗ
        e.toLinearEquiv.toLinearMap) := inferInstance
  have hL : ModuleCat.ofHom L ≫
        ModuleCat.ofHom (LinearMap.ker g'.hom).subtype =
      ModuleCat.ofHom (LinearMap.ker g.hom).subtype ≫ a := by
    ext x
    rfl
  have heq : e.hom ≫ ModuleCat.ofHom L ≫ e'.inv = kernel.map g g' a b h := by
    apply (cancel_mono (kernel.ι g')).1
    dsimp only [e, e']
    rw [Category.assoc, Category.assoc, ModuleCat.kernelIsoKer_inv_kernel_ι]
    rw [hL, ← Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype]
    simp
  rw [← heq]
  change IsLocalizedModule S
    ((e'.symm.toLinearEquiv.toLinearMap ∘ₗ L) ∘ₗ e.toLinearEquiv.toLinearMap)
  infer_instance

variable {C : Type (w + 1)} [Category.{w} C] [HasZeroMorphisms C]

/-- A natural transformation whose endpoint components are localization maps remains a
localization map on kernels, provided both functors preserve finite limits. -/
theorem kernelNatTrans (F G : C ⥤ ModuleCat.{w} A)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] (α : F ⟶ G)
    {X Y : C} (g : X ⟶ Y) [HasKernel g]
    [IsLocalizedModule S (α.app X).hom]
    [IsLocalizedModule S (α.app Y).hom] :
    IsLocalizedModule S (α.app (kernel g)).hom := by
  let h := α.naturality g
  let k := kernel.map (F.map g) (G.map g) (α.app X) (α.app Y) h
  letI : IsLocalizedModule S k.hom :=
    IsLocalizedModule.kernelMap S (α.app X) (α.app Y) (F.map g) (G.map g) h
  let eF := PreservesKernel.iso F g
  let eG := PreservesKernel.iso G g
  letI : IsLocalizedModule S (eG.symm.toLinearEquiv.toLinearMap ∘ₗ k.hom) := inferInstance
  letI : IsLocalizedModule S
      ((eG.symm.toLinearEquiv.toLinearMap ∘ₗ k.hom) ∘ₗ
        eF.toLinearEquiv.toLinearMap) := inferInstance
  have heq : eF.hom ≫ k ≫ eG.inv = α.app (kernel g) := by
    apply (cancel_mono (G.map (kernel.ι g))).1
    simp [k, eF, eG]
  rw [← heq]
  change IsLocalizedModule S
    ((eG.symm.toLinearEquiv.toLinearMap ∘ₗ k.hom) ∘ₗ eF.toLinearEquiv.toLinearMap)
  infer_instance

end IsLocalizedModule
