/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HomComparison
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineHomVanishing
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Extensions

/-!
# Bounded-below affine Hom comparison

For a bounded-below object with quasi-coherent cohomology on an affine scheme,
maps from the structure sheaf are determined by the degree-zero truncation.
This is a step toward an affine hypercohomology comparison.

## Main definitions

This file introduces no carrier, class, or instance.

## Main results

* `AlgebraicGeometry.Cohomology.affineHomToDegreeZeroTruncAddEquiv` gives the
  additive Hom comparison under an explicit lower cohomological bound.

## Implementation notes

The generic t-structure comparison requires two negative Hom groups to vanish.
Both vanish by the existing bounded affine theorem, applied to the negative
truncation and its shift. The Dqc property is preserved by truncation and shift.

## References

`AlgebraicGeometry.Cohomology.hom_unit_eq_zero_of_isGE_of_isLE_neg` is the
bounded affine vanishing input; Mathlib's t-structure truncation and shift laws
supply the remaining bounds.

## Tags

affine scheme, quasi-coherent cohomology, derived category, hypercohomology
-/

universe u

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open AlgebraicGeometry.DerivedCategory

namespace AlgebraicGeometry.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}}

/-- On an affine scheme, bounded-below quasi-coherent cohomology makes the
structure-sheaf Hom group insensitive to the negative part of the upper
truncation. The target is the degree-zero heart object, without asserting a
comparison to global sections or ambient derived global sections. -/
noncomputable def affineHomToDegreeZeroTruncAddEquiv
    {M : SchemeDerivedCategory (Spec R)}
    (hM : Dqc.schemeQuasicoherentCohomology (Spec R) M)
    (a : ℤ) [DerivedCategory.TStructure.t.IsGE M a] :
    ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj (Scheme.Modules.unit (Spec R)) ⟶ M) ≃+
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj (Scheme.Modules.unit (Spec R)) ⟶
        (DerivedCategory.TStructure.t.truncGE 0).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj M)) := by
  let t := DerivedCategory.TStructure.t (C := (Spec R).Modules)
  let U := (DerivedCategory.singleFunctor (Spec R).Modules 0).obj (Scheme.Modules.unit (Spec R))
  let L := (t.truncLT 1).obj M
  let N := (t.truncLT 0).obj L
  let P : ObjectProperty (Spec R).Modules :=
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  haveI : P.IsClosedUnderIsomorphisms :=
    Dqc.SchemeQuasicoherentDerivedCategory.quasicoherent_isClosedUnderIsomorphisms (Spec R)
  haveI : P.ContainsZero := AlgebraicGeometry.quasicoherent_containsZero (Spec R)
  have hL : Dqc.schemeQuasicoherentCohomology (Spec R) L := by
    change DerivedCategory.cohomologyIn P L
    exact DerivedCategory.cohomologyIn_truncLT P (E := M) hM 1
  have hN : Dqc.schemeQuasicoherentCohomology (Spec R) N := by
    change DerivedCategory.cohomologyIn P N
    exact DerivedCategory.cohomologyIn_truncLT P (E := L) hL 0
  haveI : t.IsGE L a := inferInstance
  haveI : t.IsGE N a := inferInstance
  haveI : t.IsLE N (-1) := t.isLE_truncLT_obj L 0 (-1) (by omega)
  have h₁ : ∀ f : U ⟶ N, f = 0 := by
    intro f
    exact hom_unit_eq_zero_of_isGE_of_isLE_neg hN a f
  have hNs : Dqc.schemeQuasicoherentCohomology (Spec R) (N⟦(1 : ℤ)⟧) :=
    ((Dqc.schemeQuasicoherentCohomology (Spec R)).prop_shift_iff_of_isStableUnderShift N 1).2 hN
  haveI : t.IsGE (N⟦(1 : ℤ)⟧) (a - 1) :=
    t.isGE_shift N a 1 (a - 1) (by omega)
  haveI : t.IsLE (N⟦(1 : ℤ)⟧) (-2) :=
    t.isLE_shift N (-1) 1 (-2) (by omega)
  haveI : t.IsLE (N⟦(1 : ℤ)⟧) (-1) :=
    t.isLE_of_le _ (-2) (-1) (by omega)
  have h₄ : ∀ f : U ⟶ N⟦(1 : ℤ)⟧, f = 0 := by
    intro f
    exact hom_unit_eq_zero_of_isGE_of_isLE_neg hNs (a - 1) f
  exact t.homToDegreeZeroTruncAddEquiv h₁ h₄

end AlgebraicGeometry.Cohomology
