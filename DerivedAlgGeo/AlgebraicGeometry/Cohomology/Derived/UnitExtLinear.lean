/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The linear unit-Ext/cohomology comparison

On a variety over a field, the additive comparison

`Extⁿ_{X.Modules}(𝒪_X, F) ≃+ Hⁿ(X, F)`

is compatible with the canonical base-field actions on both sides.  The proof identifies both
actions with postcomposition by multiplication by the scalar on `F`: on Ext this is
`Abelian.Ext.smul_eq_comp_mk₀`, while on cohomology it is the action used to construct
`linearCoherentH`.

This file remains on the all-module-sheaf side.  It does not compare Ext in `Coh X` with Ext in
`X.Modules`; that is the separate `CoherentExtComparison` boundary.

## Main result

* `Scheme.Modules.extUnitLinearEquivCoherentH` identifies Ext from the structure sheaf with the
  canonical linear coherent cohomology module.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Abelian
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.hasExt_of_hasDerivedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

/-- The unit-Ext/cohomology comparison respects the canonical base-field action. -/
theorem extUnitAddEquivDerivedH_smul (F : Coh X) (n : ℕ) (r : k)
    (e : Ext.{u + 1} (unit X) ((Coh.ι X).obj F) n) :
    extUnitAddEquivDerivedH ((Coh.ι X).obj F) n (r • e) =
      Cohomology.coherentHScalarAction k X n F r
        (extUnitAddEquivDerivedH ((Coh.ι X).obj F) n e) := by
  rw [Abelian.Ext.smul_eq_comp_mk₀]
  rw [Variety.smul_eq_action_comp, Category.comp_id]
  change extComparisonMap (unitFromConstant X)
      (e.comp (Ext.mk₀ (Cohomology.varietyScalarAction X ((Coh.ι X).obj F) r))
        (add_zero n)) = _
  rw [extComparisonMap_comp_mk₀]
  rfl

/-- **Ext from the structure sheaf is linearly equivalent to coherent cohomology.**

The target is the canonical `linearCoherentH` realization, not an independently chosen vector
space structure on the underlying cohomology group. -/
noncomputable def extUnitLinearEquivCoherentH (F : Coh X) (n : ℕ) :
    Ext.{u + 1} (unit X) ((Coh.ι X).obj F) n ≃ₗ[k]
      (Cohomology.linearCoherentH k X n).obj F where
  __ := extUnitAddEquivDerivedH ((Coh.ι X).obj F) n
  map_smul' r e := by
    change extUnitAddEquivDerivedH ((Coh.ι X).obj F) n (r • e) =
      Cohomology.coherentHScalarAction k X n F r
        (extUnitAddEquivDerivedH ((Coh.ι X).obj F) n e)
    exact extUnitAddEquivDerivedH_smul (k := k) F n r e

@[simp]
theorem extUnitLinearEquivCoherentH_apply (F : Coh X) (n : ℕ)
    (e : Ext.{u + 1} (unit X) ((Coh.ι X).obj F) n) :
    extUnitLinearEquivCoherentH (k := k) F n e =
      extUnitAddEquivDerivedH ((Coh.ι X).obj F) n e :=
  rfl

end AlgebraicGeometry.Scheme.Modules
