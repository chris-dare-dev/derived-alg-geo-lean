/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Cohomology of a localized three-term complex

Three degreewise module localizations that commute with consecutive differentials
induce a localization of the kernel modulo the preceding image. This is a
module-level cohomology statement; it does not identify a particular derived
category Hom or assert geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)

private theorem quotientMap_isLocalized
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    [Module (Localization S) N] [IsScalarTower R (Localization S) N]
    (P : Submodule R M) (Q : Submodule R N)
    (h : (P.localized' (Localization S) S f).restrictScalars R = Q)
    (hmap : P ≤ Q.comap f) :
    IsLocalizedModule S (Submodule.mapQ P Q f hmap) := by
  let e : (N ⧸ P.localized' (Localization S) S f) ≃ₗ[R] N ⧸ Q :=
    (Submodule.Quotient.restrictScalarsEquiv R
      (P.localized' (Localization S) S f)).symm.trans
        (Submodule.quotEquivOfEq _ _ h)
  haveI : IsLocalizedModule S
      (e.toLinearMap ∘ₗ P.toLocalizedQuotient' (Localization S) S f) :=
    IsLocalizedModule.of_linearEquiv S
      (P.toLocalizedQuotient' (Localization S) S f) e
  convert this using 1
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp [e, Submodule.mapQ_apply]

variable {M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
  [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
  [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
  [Module R M₀] [Module R M₁] [Module R M₂]
  [Module R N₀] [Module R N₁] [Module R N₂]
  (f₀ : M₀ →ₗ[R] N₀) (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂)
  [IsLocalizedModule S f₀] [IsLocalizedModule S f₁] [IsLocalizedModule S f₂]
  (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) (hd : d₁.comp d₀ = 0)

/-- The first differential, with codomain restricted to cycles of the second. -/
def boundaryToCycles : M₀ →ₗ[R] d₁.ker :=
  d₀.codRestrict d₁.ker (fun x => by
    have h := LinearMap.congr_fun hd x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.mem_ker] using h)

/-- The localized second differential. -/
def localizedDifferential : N₁ →ₗ[R] N₂ :=
  (IsLocalizedModule.map S f₁ f₂) d₁

/-- The canonical localization map on cycles. -/
def localizedCyclesMap :
    d₁.ker →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  LinearMap.toKerIsLocalized S f₁ f₂ d₁

private def localizedBoundaryToCyclesViaMap :
    N₀ →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  letI : Module (Localization S) N₁ := IsLocalizedModule.module S f₁
  letI : IsScalarTower R (Localization S) N₁ :=
    IsLocalizedModule.isScalarTower_module S f₁
  letI : Module (Localization S) N₂ := IsLocalizedModule.module S f₂
  letI : IsScalarTower R (Localization S) N₂ :=
    IsLocalizedModule.isScalarTower_module S f₂
  letI : IsLocalizedModule S (localizedCyclesMap S f₁ f₂ d₁) :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S f₁ f₂ d₁
  (IsLocalizedModule.map S f₀ (localizedCyclesMap S f₁ f₂ d₁))
    (boundaryToCycles d₀ d₁ hd)

include hd in
private theorem localized_comp_zero :
    ((IsLocalizedModule.map S f₁ f₂) d₁).comp
      ((IsLocalizedModule.map S f₀ f₁) d₀) = 0 := by
  rw [← IsLocalizedModule.map_comp' S f₀ f₁ f₂ d₀ d₁, hd]
  simp

/-- The localized first differential, with codomain restricted to cycles of
the localized second differential. -/
def localizedBoundaryToCycles :
    N₀ →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  ((IsLocalizedModule.map S f₀ f₁) d₀).codRestrict
    (localizedDifferential S f₁ f₂ d₁).ker (fun x => by
      have h := LinearMap.congr_fun (localized_comp_zero S f₀ f₁ f₂ d₀ d₁ hd) x
      simpa only [localizedDifferential, LinearMap.comp_apply, LinearMap.zero_apply,
        LinearMap.mem_ker] using h)

private theorem localizedBoundaryToCyclesViaMap_eq :
    localizedBoundaryToCyclesViaMap S f₀ f₁ f₂ d₀ d₁ hd =
      localizedBoundaryToCycles S f₀ f₁ f₂ d₀ d₁ hd := by
  letI : Module (Localization S) N₁ := IsLocalizedModule.module S f₁
  letI : IsScalarTower R (Localization S) N₁ :=
    IsLocalizedModule.isScalarTower_module S f₁
  letI : Module (Localization S) N₂ := IsLocalizedModule.module S f₂
  letI : IsScalarTower R (Localization S) N₂ :=
    IsLocalizedModule.isScalarTower_module S f₂
  letI : IsLocalizedModule S (localizedCyclesMap S f₁ f₂ d₁) :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S f₁ f₂ d₁
  apply IsLocalizedModule.linearMap_ext S f₀ (localizedCyclesMap S f₁ f₂ d₁)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [localizedBoundaryToCyclesViaMap, localizedBoundaryToCycles,
    IsLocalizedModule.map_apply, localizedCyclesMap, boundaryToCycles]
  change f₁ (d₀ x) = f₁ (d₀ x)
  rfl

/-- The map on kernel modulo image induced by three degreewise localizations. -/
def cohomologyMap :
    (d₁.ker ⧸ (boundaryToCycles d₀ d₁ hd).range) →ₗ[R]
      ((localizedDifferential S f₁ f₂ d₁).ker ⧸
        (localizedBoundaryToCycles (S := S) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
          d₀ d₁ hd).range) :=
  Submodule.mapQ _ _ (localizedCyclesMap S f₁ f₂ d₁) (by
    rintro x ⟨y, rfl⟩
    rw [← localizedBoundaryToCyclesViaMap_eq S f₀ f₁ f₂ d₀ d₁ hd]
    exact ⟨f₀ y, by
      simp [localizedBoundaryToCyclesViaMap, IsLocalizedModule.map_apply]⟩)

/-- Localization is exact on the cohomology quotient of a three-term complex. -/
theorem cohomologyMap_isLocalized :
    IsLocalizedModule S
      (cohomologyMap (S := S) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
        d₀ d₁ hd) := by
  letI : Module (Localization S) N₁ := IsLocalizedModule.module S f₁
  letI : IsScalarTower R (Localization S) N₁ :=
    IsLocalizedModule.isScalarTower_module S f₁
  letI : Module (Localization S) N₂ := IsLocalizedModule.module S f₂
  letI : IsScalarTower R (Localization S) N₂ :=
    IsLocalizedModule.isScalarTower_module S f₂
  letI : IsLocalizedModule S (localizedCyclesMap S f₁ f₂ d₁) :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S f₁ f₂ d₁
  letI : Module (Localization S) (localizedDifferential S f₁ f₂ d₁).ker :=
    IsLocalizedModule.module S (localizedCyclesMap S f₁ f₂ d₁)
  letI : IsScalarTower R (Localization S)
      (localizedDifferential S f₁ f₂ d₁).ker :=
    IsLocalizedModule.isScalarTower_module S (localizedCyclesMap S f₁ f₂ d₁)
  apply quotientMap_isLocalized S (localizedCyclesMap S f₁ f₂ d₁)
    (boundaryToCycles d₀ d₁ hd).range
    (localizedBoundaryToCycles (S := S) (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
      d₀ d₁ hd).range
  · rw [← localizedBoundaryToCyclesViaMap_eq S f₀ f₁ f₂ d₀ d₁ hd]
    rw [Submodule.restrictScalars_localized']
    exact (LinearMap.range_localizedMap_eq_localized₀_range S f₀
      (localizedCyclesMap S f₁ f₂ d₁) (boundaryToCycles d₀ d₁ hd)).symm

end IsLocalizedModule
