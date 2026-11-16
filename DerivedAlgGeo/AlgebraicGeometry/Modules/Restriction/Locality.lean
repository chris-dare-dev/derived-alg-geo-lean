/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Abelian

/-!
# Vanishing of a module sheaf is local on open covers

A sheaf of modules on a scheme is zero once its restriction to every member of a family of opens
covering the scheme is zero.

## Main definitions

This file introduces no new definitions.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_restrict` — a module sheaf whose
  restrictions to a covering family of opens are zero is zero.

## Implementation notes

The proof goes through stalks. Mathlib's `Scheme.Modules.restrictStalkNatIso` identifies the
stalk of a restriction with the stalk of the original sheaf, and
`TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` detects a zero sheaf of abelian groups on
stalks. The faithful forgetful functor `SheafOfModules.toSheaf` then reflects the zero object.

## References

Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` and
`TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`.

## Tags

sheaf of modules, restriction, open cover, zero object
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A sheaf of modules on `X` is zero if its restriction to each member of a family of opens
covering `X` is zero. -/
theorem isZero_of_isZero_restrict {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (h : ∀ i, IsZero (M.restrict (U i).ι)) : IsZero M := by
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hSheaf : IsZero M' := by
    refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero M').2 fun x ↦ ?_
    obtain ⟨i, hi⟩ := hU x
    let y : (U i).toScheme := ⟨x, hi⟩
    exact ((toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ y).map_isZero (h i)).of_iso
      ((restrictStalkNatIso (U i).ι y).app M).symm
  have hSheaf' : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := hSheaf
  rw [IsZero.iff_id_eq_zero]
  exact (SheafOfModules.toSheaf X.ringCatSheaf).map_injective (hSheaf'.eq_of_src _ _)

end AlgebraicGeometry.Scheme.Modules
