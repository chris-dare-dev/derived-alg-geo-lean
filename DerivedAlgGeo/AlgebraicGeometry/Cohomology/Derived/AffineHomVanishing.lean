/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.HomVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc

/-!
# No maps from `𝒪_X` into bounded quasi-coherent complexes in negative degrees, affine case

On `Spec R`, a bounded object `M` of `D(X.Modules)` with quasi-coherent cohomology and
`M ∈ D^{≤ -1}` receives no nonzero map from `𝒪_X[0]`: the hypercohomology of `M` in degree
zero vanishes. This is `DerivedCategory.hom_eq_zero_of_isGE_of_isLE_neg_of_cohomologyIn` with
the affine vanishing `Ext^k(𝒪_X, F) ≃ H^k(F) = 0` for quasi-coherent `F` and `k ≥ 1`.

Together with `Ext^0(𝒪_X, F) = Γ(F)` this is the bounded half of the compactness of `𝒪_X` in
`Dqc(Spec R)` (#723, slice 723b). The unbounded half, that `Hom(𝒪_X, M) = 0` for every
`M ∈ D_qc^{≤ -1}` and not only the bounded ones, needs `M ≅ holim τ≥-n M` in `D(X.Modules)`
and a Milnor sequence; neither is available at this Mathlib pin, and this file does not
claim it.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Abelian
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

namespace AlgebraicGeometry.Cohomology

variable {R : CommRingCat.{u}}

/-- `Ext^(k+1)(𝒪_X, F) = 0` for quasi-coherent `F` on `Spec R`, as the hypothesis of the
generic dévissage. -/
theorem subsingleton_ext_unit_of_isQuasicoherent (F : (Spec R).Modules)
    (hF : SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf F) (k : ℕ) :
    Subsingleton (Ext.{u + 1} (Scheme.Modules.unit (Spec R)) F (k + 1)) := by
  haveI : F.IsQuasicoherent := hF
  haveI := modules_H_subsingleton_of_isQuasicoherent F (k + 1) (Nat.succ_pos k)
  exact (Scheme.Modules.extUnitAddEquivDerivedH F (k + 1)).toEquiv.subsingleton

/-- **Affine vanishing for bounded quasi-coherent complexes.** No nonzero map from `𝒪_X[0]`
into a bounded object of `D^{≤ -1}(X.Modules)` with quasi-coherent cohomology, `X = Spec R`. -/
theorem hom_unit_eq_zero_of_isGE_of_isLE_neg {M : SchemeDerivedCategory (Spec R)}
    (hM : Dqc.schemeQuasicoherentCohomology (Spec R) M) (a : ℤ)
    [hGE : DerivedCategory.TStructure.t.IsGE M a] [hLE : DerivedCategory.TStructure.t.IsLE M (-1)]
    (f : (DerivedCategory.singleFunctor (Spec R).Modules 0).obj (Scheme.Modules.unit (Spec R)) ⟶ M) :
    f = 0 :=
  @DerivedCategory.hom_eq_zero_of_isGE_of_isLE_neg_of_cohomologyIn.{u + 1, u, u + 1}
    (SheafOfModules.{u} (Spec R).ringCatSheaf) _ _ (HasDerivedCategory.standard _)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) _ _ (Scheme.Modules.unit (Spec R))
    (fun F hF k ↦ subsingleton_ext_unit_of_isQuasicoherent F hF k) M hM a hGE hLE f

end AlgebraicGeometry.Cohomology
