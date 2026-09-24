/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.LocalizedModule.Submodule

/-! # Localized submodule finite-generation audit and direct client -/

#print axioms Submodule.exists_fg_localized_submodule

-- Import only the owner leaf and use it with the ordinary `Module.Finite`
-- packaging of a submodule, not just its explicit `Submodule.FG` premise.
universe u v w x

example {R : Type u} [CommSemiring R] {R' : Type v} [CommSemiring R']
    [Algebra R R'] {M : Type w} [AddCommMonoid M] [Module R M]
    {M' : Type x} [AddCommMonoid M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (S : Submonoid R) [IsLocalization S R']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (P : Submodule R' M') [Module.Finite R' P] :
    ∃ N : Submodule R M, Module.Finite R N ∧ N.localized' R' S f = P := by
  obtain ⟨N, hN, hNP⟩ :=
    Submodule.exists_fg_localized_submodule S f P (Module.Finite.iff_fg.mp inferInstance)
  exact ⟨N, Module.Finite.iff_fg.mpr hN, hNP⟩
