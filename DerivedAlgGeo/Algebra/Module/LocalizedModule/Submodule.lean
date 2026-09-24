/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite generation before localizing a submodule

Every finitely generated submodule of a localized module is the localization of
some finitely generated submodule of the original module. The original module
need not be finite, and no Noetherian hypothesis is used.

This is an algebraic statement for any multiplicative set. It does not assert
that the associated morphism of spectra is an open immersion, or extend a
finite-type quasi-coherent subsheaf across a quasi-compact open.
-/

namespace Submodule

universe u v w x

/-- A finitely generated submodule of a localized module has a finitely
generated submodule upstairs whose localization is exactly the given one. -/
theorem exists_fg_localized_submodule
    {R : Type u} [CommSemiring R] {R' : Type v} [CommSemiring R']
    [Algebra R R'] {M : Type w} [AddCommMonoid M] [Module R M]
    {M' : Type x} [AddCommMonoid M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (S : Submonoid R) [IsLocalization S R']
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (P : Submodule R' M') (hP : P.FG) :
    ∃ N : Submodule R M, N.FG ∧ N.localized' R' S f = P := by
  classical
  obtain ⟨t, ht, htspan⟩ := Submodule.fg_def.mp hP
  let n : M' → M := fun y => ((IsLocalizedModule.surj S f y).choose).1
  let d : M' → S := fun y => ((IsLocalizedModule.surj S f y).choose).2
  have hn (y : M') : d y • y = f (n y) :=
    (IsLocalizedModule.surj S f y).choose_spec
  let N : Submodule R M := Submodule.span R (n '' t)
  refine ⟨N, Submodule.fg_def.mpr ⟨n '' t, ht.image _, rfl⟩, ?_⟩
  apply le_antisymm
  · apply ((Submodule.localized'gi R' S f).gc N P).2
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyP : y ∈ P := by
      rw [← htspan]
      exact Submodule.subset_span hy
    change f (n y) ∈ P
    rw [← hn y]
    exact P.smul_of_tower_mem (d y : R) hyP
  · rw [← htspan]
    apply Submodule.span_le.mpr
    intro y hy
    change ∃ m ∈ N, ∃ s : S, IsLocalizedModule.mk' f m s = y
    refine ⟨n y, Submodule.subset_span ⟨y, hy, rfl⟩, d y, ?_⟩
    exact IsLocalizedModule.mk'_eq_iff.mpr (hn y).symm

end Submodule
