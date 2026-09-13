/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearH0

/-!
# Degree-zero Hom cohomology in a scalar-linear dg category

The degree-zero cohomology of a scalar-linear dg Hom-complex is the quotient of
closed degree-zero morphisms by boundaries.  This file identifies that quotient
with the existing Hom-module in `H⁰`.

This comparison is intrinsic to a scalar-linear dg category: it does not use a
pretriangulated structure or a selected shift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace H0

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

private def cyclesLinearEquiv (X Y : C) :
    LinearMap.ker
        (((DGLinear.homComplex k X Y).sc' (-1) 0 1).g).hom ≃ₗ[k]
      cocycles X Y where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma boundaries_map_cyclesLinearEquiv (X Y : C) :
    (LinearMap.range
        ((DGLinear.homComplex k X Y).sc' (-1) 0 1).moduleCatToCycles).map
        (cyclesLinearEquiv (k := k) X Y : _ →ₗ[k] _) =
      coboundariesSubmodule (k := k) X Y := by
  ext f
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    refine ⟨⟨((DGLinear.homComplex k X Y).d (-1) 0).hom g, ?_⟩, ?_, ?_⟩
    · exact ConcreteCategory.congr_hom
        ((DGLinear.homComplex k X Y).d_comp_d (-1) 0 1) g
    · exact ⟨g, rfl⟩
    · exact Subtype.ext hg

private noncomputable def scHomologyLinearEquiv (X Y : C) :
    ((((DGLinear.homComplex k X Y).sc' (-1) 0 1).homology : ModuleCat.{v} k) : Type v) ≃ₗ[k]
      (cocycles X Y ⧸ coboundariesSubmodule (k := k) X Y) :=
  ((DGLinear.homComplex k X Y).sc' (-1) 0 1).moduleCatHomologyIso.toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (cyclesLinearEquiv (k := k) X Y)
      (boundaries_map_cyclesLinearEquiv (k := k) X Y))

private def homMkLinear (X Y : C) :
    cocycles X Y →ₗ[k] ((show H0 C from X) ⟶ (show H0 C from Y)) where
  toFun := H0.homMk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def quotientToH0LinearMap (X Y : C) :
    (cocycles X Y ⧸ coboundariesSubmodule (k := k) X Y) →ₗ[k]
      ((show H0 C from X) ⟶ (show H0 C from Y)) :=
  (coboundariesSubmodule (k := k) X Y).liftQ (homMkLinear (k := k) X Y) (by
    intro f hf
    rw [LinearMap.mem_ker]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hf)

private lemma bijective_quotientToH0LinearMap (X Y : C) :
    Function.Bijective (quotientToH0LinearMap (k := k) X Y) := by
  constructor
  · intro a b hab
    induction a using Submodule.Quotient.induction_on with
    | _ a =>
      induction b using Submodule.Quotient.induction_on with
      | _ b =>
        apply (Submodule.Quotient.eq _).2
        exact QuotientAddGroup.eq_iff_sub_mem.mp hab
  · intro z
    induction z using Quotient.ind with
    | _ z => exact ⟨Submodule.Quotient.mk z, rfl⟩

private noncomputable def quotientToH0LinearEquiv (X Y : C) :
    (cocycles X Y ⧸ coboundariesSubmodule (k := k) X Y) ≃ₗ[k]
      ((show H0 C from X) ⟶ (show H0 C from Y)) :=
  LinearEquiv.ofBijective (quotientToH0LinearMap (k := k) X Y)
    (bijective_quotientToH0LinearMap (k := k) X Y)

/-- Degree-zero cohomology of the scalar-linear dg Hom-complex is the Hom-module
of `H⁰`. -/
noncomputable def homologyZeroLinearEquiv (X Y : C) :
    ((DGLinear.homComplex k X Y).homology 0 : Type v) ≃ₗ[k]
      ((show H0 C from X) ⟶ (show H0 C from Y)) :=
  ((DGLinear.homComplex k X Y).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).toLinearEquiv.trans
    ((scHomologyLinearEquiv (k := k) X Y).trans
      (quotientToH0LinearEquiv (k := k) X Y))

/-- The degree-zero comparison sends the homology class represented by a
closed dg morphism to its class in `H⁰`. -/
lemma homologyZeroLinearEquiv_homologyπ_cyclesMk (X Y : C)
    (f : (dgHom X Y).X 0)
    (hf : ((dgHom X Y).d 0 1).hom f = 0) :
    homologyZeroLinearEquiv (k := k) X Y
        (((DGLinear.homComplex k X Y).homologyπ 0).hom
          ((DGLinear.homComplex k X Y).cyclesMk f 1 (by simp) hf)) =
      H0.homMk ⟨f, hf⟩ := by
  let K := DGLinear.homComplex k X Y
  let S := K.sc' (-1) 0 1
  let z := K.cyclesMk f 1 (by simp) hf
  have hhomology :
      ((K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom).hom
          ((K.homologyπ 0).hom z) =
        (S.homologyπ).hom
          (((K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom).hom z) := by
    exact ConcreteCategory.congr_hom
      (K.π_homologyIsoSc'_hom (-1) 0 1 (by simp) (by simp)) z
  have hmodule (z' : S.cycles) :
      S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z') =
        S.moduleCatLeftHomologyData.π.hom
          (S.moduleCatCyclesIso.hom.hom z') := by
    exact ConcreteCategory.congr_hom S.π_moduleCatCyclesIso_hom z'
  have hcycles :
      S.moduleCatCyclesIso.hom.hom
          ((K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom.hom z) =
        ⟨f, hf⟩ := by
    apply Subtype.ext
    change S.moduleCatLeftHomologyData.i.hom
        (S.moduleCatCyclesIso.hom.hom
          ((K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom.hom z)) = f
    rw [← ConcreteCategory.comp_apply, S.moduleCatCyclesIso_hom_i,
      ← ConcreteCategory.comp_apply,
      K.cyclesIsoSc'_hom_iCycles (-1) 0 1 (by simp) (by simp)]
    exact K.i_cyclesMk f 1 (by simp) hf
  simp only [homologyZeroLinearEquiv, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply]
  rw [hhomology]
  simp only [scHomologyLinearEquiv, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply]
  rw [hmodule, hcycles]
  rfl

end H0

end CategoryTheory
