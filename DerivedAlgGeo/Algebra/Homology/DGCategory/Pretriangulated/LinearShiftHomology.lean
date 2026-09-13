/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearH0Homology
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearShiftIso

/-!
# Hom cohomology and explicit dg shifts

For a scalar-linear dg category, an explicit witness `s : IsShiftBy Y n Yn`
identifies degree-`n` cohomology of `dgHom X Y` with morphisms `X ⟶ Yn` in
`H⁰`.  The comparison uses the scalar-linear Hom-complex isomorphism induced
by `s`, followed by Mathlib's homology comparison for shifted complexes.

This statement depends only on the supplied shift witness.  Selecting shift
objects functorially is a separate, pretriangulated enhancement layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace IsShiftBy

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- Cohomology of a scalar-linear dg Hom-complex as morphisms into an explicitly
supplied target shift.  The target is shifted by `n`, while the comparison of
Hom-complexes is shifted by `-n`, so degree `n` becomes degree zero. -/
noncomputable def homologyLinearEquiv {Y Yn : C} {n : ℤ}
    (s : IsShiftBy Y n Yn) (X : C) :
    ((DGLinear.homComplex k X Y).homology n : Type v) ≃ₗ[k]
      ((show H0 C from X) ⟶ (show H0 C from Yn)) :=
  (HomologicalComplex.homologyMapIso (s.linearHomIso (k := k) X) n).toLinearEquiv |>.trans
    (((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{v} k) (-n) n 0 (by omega)).app
      (DGLinear.homComplex k X Yn)).toLinearEquiv.trans
        (H0.homologyZeroLinearEquiv (k := k) X Yn))

/-- On a represented cohomology class, the explicit-shift comparison is right
composition by the distinguished shift element. -/
lemma homologyLinearEquiv_homologyπ_cyclesMk {Y Yn : C} {n : ℤ}
    (s : IsShiftBy Y n Yn) (X : C) (f : (dgHom X Y).X n)
    (hf : ((dgHom X Y).d n (n + 1)).hom f = 0) :
    s.homologyLinearEquiv (k := k) X
        (((DGLinear.homComplex k X Y).homologyπ n).hom
          ((DGLinear.homComplex k X Y).cyclesMk f (n + 1) (by simp) hf)) =
      H0.homMk
        ⟨dgComp n (-n) 0 (by omega) f s.hom,
          dgComp_closed (by omega) (by omega) hf s.hom_closed⟩ := by
  let K := DGLinear.homComplex k X Y
  let L := DGLinear.homComplex k X Yn
  let φ := s.linearHomMap (k := k) X
  let Q := L⟦-n⟧
  let z := K.cyclesMk f (n + 1) (by simp) hf
  let g : L.X 0 := dgComp n (-n) 0 (by omega) f s.hom
  let gQ : Q.X n := (φ.f n).hom f
  have hg : (L.d 0 1).hom g = 0 :=
    dgComp_closed (by omega) (by omega) hf s.hom_closed
  have hgQ : (Q.d n (n + 1)).hom gQ = 0 := by
    rw [← ConcreteCategory.comp_apply, φ.comm n (n + 1),
      ConcreteCategory.comp_apply]
    change (φ.f (n + 1)).hom (((dgHom X Y).d n (n + 1)).hom f) = 0
    rw [hf, map_zero]
  let zQ := Q.cyclesMk gQ (n + 1) (by simp) hgQ
  let zL := L.cyclesMk g 1 (by simp) hg
  have hzi : (K.iCycles n).hom z = f := by
    dsimp only [z]
    exact K.i_cyclesMk f (n + 1) (by simp) hf
  have hzQi : (Q.iCycles n).hom zQ = gQ := by
    dsimp only [zQ]
    exact Q.i_cyclesMk gQ (n + 1) (by simp) hgQ
  have hzLi : (L.iCycles 0).hom zL = g := by
    dsimp only [zL]
    exact L.i_cyclesMk g 1 (by simp) hg
  have hcyclesMap :
      (HomologicalComplex.cyclesMap φ n).hom z = zQ := by
    apply (ModuleCat.mono_iff_injective (Q.iCycles n)).1 inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
    rw [hzi, hzQi]
  have hhomologyMap :
      (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom z) =
        (Q.homologyπ n).hom zQ := by
    calc
      _ = (Q.homologyπ n).hom
          ((HomologicalComplex.cyclesMap φ n).hom z) :=
        ConcreteCategory.congr_hom
          (HomologicalComplex.homologyπ_naturality φ n) z
      _ = _ := congrArg (Q.homologyπ n).hom hcyclesMap
  let ψ : Q.sc n ⟶ L.sc 0 := (CochainComplex.shiftShortComplexFunctorIso
    (ModuleCat.{v} k) (-n) n 0 (by omega)).hom.app L
  have htransport (r : ℤ) (hr : n + -n = r) :
      (show ((DGLinear.homComplex k X Yn).sc r).X₂ from
        ((DGLinear.homComplex k X Yn).XIsoOfEq hr).hom.hom
          (dgComp n (-n) (n + -n) rfl f s.hom)) =
        (show ((DGLinear.homComplex k X Yn).sc r).X₂ from
          dgComp n (-n) r hr f s.hom) := by
    subst r
    rfl
  have hshiftCycles :
      (ShortComplex.cyclesMap ψ).hom zQ = zL := by
    apply (ModuleCat.mono_iff_injective (L.sc 0).iCycles).1 inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
    change ψ.τ₂.hom ((Q.iCycles n).hom zQ) = (L.iCycles 0).hom zL
    rw [hzQi, hzLi]
    dsimp only [ψ, gQ, g, φ, Q, L]
    rw [CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂]
    change
      (show ((DGLinear.homComplex k X Yn).sc 0).X₂ from
        ((DGLinear.homComplex k X Yn).XIsoOfEq (by omega)).hom.hom
          (dgComp n (-n) (n + -n) rfl f s.hom)) =
        (show ((DGLinear.homComplex k X Yn).sc 0).X₂ from
          dgComp n (-n) 0 (by omega) f s.hom)
    exact htransport 0 (by omega)
  have hshift :
      ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{v} k)
        (-n) n 0 (by omega)).hom.app L).hom ((Q.homologyπ n).hom zQ) =
        (L.homologyπ 0).hom zL := by
    rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
    change (ShortComplex.homologyMap ψ).hom ((Q.homologyπ n).hom zQ) = _
    calc
      _ = (L.homologyπ 0).hom ((ShortComplex.cyclesMap ψ).hom zQ) :=
        ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality ψ) zQ
      _ = _ := congrArg (L.homologyπ 0).hom hshiftCycles
  change H0.homologyZeroLinearEquiv (k := k) X Yn
      (((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{v} k)
        (-n) n 0 (by omega)).hom.app L).hom
        ((HomologicalComplex.homologyMapIso
          (s.linearHomIso (k := k) X) n).hom.hom ((K.homologyπ n).hom z))) = _
  rw [show
      (HomologicalComplex.homologyMapIso (s.linearHomIso (k := k) X) n).hom.hom
          ((K.homologyπ n).hom z) = (Q.homologyπ n).hom zQ by
        exact hhomologyMap,
    hshift]
  exact H0.homologyZeroLinearEquiv_homologyπ_cyclesMk X Yn g hg

end IsShiftBy

end CategoryTheory
