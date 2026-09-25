/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.FixedTargetArrow

/-!
# Three-term descent with a fixed terminal module

Let `A` be a localization of a Noetherian ring `R`. A zero-composite diagram
`M₀ → M₁ → A ⊗[R] T`, with the first two `A`-modules finite and `T` an
arbitrary `R`-module, descends to `L₀ → L₁ → T`. Both `Lᵢ` are finitely
presented over `R`; the original arrows agree with their scalar extensions
through specified equivalences.

The zero composite cannot be inferred just because its scalar extension is
zero: `T` may have `S`-torsion. Finite presentation supplies one denominator
annihilating the descended composite. Scaling the first arrow and its source
equivalence by inverse localization units then makes the composite exactly
zero without changing either comparison equation.

This is a module-level diagram witness. It does not package a `ShortComplex`
or prove a derived, geometric, or heart-level extension theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

noncomputable section

private theorem Module.fixedTerminal_mapExtendScalars_mk
    {R A L T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup L] [Module R L] [AddCommGroup T] [Module R T]
    (f : L →ₗ[R] T) (x : L) :
    (IsLocalizedModule.mapExtendScalars S
      (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f)
        ((TensorProduct.mk R A L 1) x) =
      (TensorProduct.mk R A T 1) (f x) := by
  letI : IsLocalizedModule S (TensorProduct.mk R A L 1) := inferInstance
  letI : IsLocalizedModule S (TensorProduct.mk R A T 1) := inferInstance
  simp only [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]

private theorem Module.fixedTerminal_uniformDenominator
    {R A M₀ M₁ L₀ L₁ T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup M₀] [Module R M₀] [Module A M₀] [IsScalarTower R A M₀]
    [AddCommGroup M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]
    [AddCommGroup L₀] [Module R L₀] [Module.FinitePresentation R L₀]
    [AddCommGroup L₁] [Module R L₁]
    [AddCommGroup T] [Module R T]
    (d : M₀ →ₗ[A] M₁) (β : M₁ →ₗ[A] A ⊗[R] T)
    (d₀ : L₀ →ₗ[R] L₁) (f : L₁ →ₗ[R] T)
    (e₀ : M₀ ≃ₗ[A] A ⊗[R] L₀) (e₁ : M₁ ≃ₗ[A] A ⊗[R] L₁)
    (hd : e₁.toLinearMap.comp d =
      (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L₀ 1) (TensorProduct.mk R A L₁ 1) A d₀).comp
          e₀.toLinearMap)
    (hβ : β = (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L₁ 1) (TensorProduct.mk R A T 1) A f).comp
          e₁.toLinearMap)
    (hz : β.comp d = 0) :
    ∃ s : S, s • (f.comp d₀) = 0 := by
  let l₀ := TensorProduct.mk R A L₀ 1
  let l₁ := TensorProduct.mk R A L₁ 1
  let lT := TensorProduct.mk R A T 1
  let D := IsLocalizedModule.mapExtendScalars S l₀ l₁ A d₀
  let F := IsLocalizedModule.mapExtendScalars S l₁ lT A f
  let H := IsLocalizedModule.mapExtendScalars S l₀ lT A
  letI : IsLocalizedModule S l₀ := inferInstance
  letI : IsLocalizedModule S lT := inferInstance
  letI : IsLocalizedModule S H := inferInstance
  have hH : H (f.comp d₀) = H 0 := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S l₀ lT
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    let m : M₀ := e₀.symm (l₀ x)
    have he₀ : e₀ m = l₀ x := e₀.apply_symm_apply _
    have hdm : e₁ (d m) = D (e₀ m) := LinearMap.congr_fun hd m
    have hβm : β (d m) = F (e₁ (d m)) := LinearMap.congr_fun hβ (d m)
    have hzm : β (d m) = 0 := by
      have h := LinearMap.congr_fun hz m
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
    have hcomp : H (f.comp d₀) (l₀ x) = lT (f (d₀ x)) :=
      Module.fixedTerminal_mapExtendScalars_mk S (f.comp d₀) x
    have hD : D (l₀ x) = l₁ (d₀ x) :=
      Module.fixedTerminal_mapExtendScalars_mk S d₀ x
    have hF : F (l₁ (d₀ x)) = lT (f (d₀ x)) :=
      Module.fixedTerminal_mapExtendScalars_mk S f (d₀ x)
    calc
      H (f.comp d₀) (l₀ x) = lT (f (d₀ x)) := hcomp
      _ = F (l₁ (d₀ x)) := hF.symm
      _ = F (D (l₀ x)) := by rw [hD]
      _ = F (D (e₀ m)) := by rw [he₀]
      _ = F (e₁ (d m)) := by rw [hdm]
      _ = β (d m) := hβm.symm
      _ = 0 := hzm
      _ = H 0 (l₀ x) := by simp
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := H) hH
  exact ⟨s, by simpa using hs⟩

private theorem Module.fixedTerminal_rescaleMap
    {R A M L T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup L] [Module R L]
    [AddCommGroup T] [Module R T]
    (β : M →ₗ[A] A ⊗[R] T)
    (f : L →ₗ[R] T) (e : M ≃ₗ[A] A ⊗[R] L)
    (h : β = (IsLocalizedModule.mapExtendScalars S
      (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f).comp e.toLinearMap)
    (s : S) :
    β = (IsLocalizedModule.mapExtendScalars S
      (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A (s • f)).comp
        (e.trans
          (LinearEquiv.smulOfUnit (IsLocalization.map_units A s).unit).symm).toLinearMap := by
  let u : Aˣ := (IsLocalization.map_units A s).unit
  let H := IsLocalizedModule.mapExtendScalars S
    (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A
  apply LinearMap.ext
  intro m
  have hm := LinearMap.congr_fun h m
  change β m = H f (e m) at hm
  change β m = H (s • f) ((u⁻¹ : Aˣ) • e m)
  rw [hm]
  have hs : H (s • f) = s • H f := by
    simpa only [Submonoid.smul_def] using (map_smul H (s : R) f)
  rw [hs]
  simp only [LinearMap.smul_apply, Submonoid.smul_def]
  rw [← IsScalarTower.algebraMap_smul A (s : R)]
  change H f (e m) = (u : A) • H f ((u⁻¹ : Aˣ) • e m)
  simp only [Units.smul_def]
  rw [map_smul]
  simp [smul_smul, u]

/-- Descend a zero-composite three-term module diagram with fixed terminal
`R`-module `T`. Only `M₀` and `M₁` must be finite over the localization; `T`
may be arbitrary. The equivalences need not be induced by the submodule
inclusions, since clearing the composite rescales the first equivalence. -/
theorem Module.exists_finitely_presented_fixedTerminalThreeTerm_of_isLocalization
    {R A M₀ M₁ T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] [IsNoetherianRing R]
    [AddCommGroup M₀] [Module R M₀] [Module A M₀] [IsScalarTower R A M₀]
    [AddCommGroup M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]
    [Module.Finite A M₀] [Module.Finite A M₁]
    [AddCommGroup T] [Module R T]
    (d : M₀ →ₗ[A] M₁) (β : M₁ →ₗ[A] A ⊗[R] T)
    (hz : β.comp d = 0) :
    ∃ (L₀ : Submodule R M₀) (L₁ : Submodule R M₁),
      Module.FinitePresentation R L₀ ∧ Module.FinitePresentation R L₁ ∧
      ∃ (d₀ : L₀ →ₗ[R] L₁) (f : L₁ →ₗ[R] T)
        (e₀ : M₀ ≃ₗ[A] A ⊗[R] L₀)
        (e₁ : M₁ ≃ₗ[A] A ⊗[R] L₁),
        f.comp d₀ = 0 ∧
        e₁.toLinearMap.comp d =
            (IsLocalizedModule.mapExtendScalars S
              (TensorProduct.mk R A L₀ 1) (TensorProduct.mk R A L₁ 1) A d₀).comp
                e₀.toLinearMap ∧
        β = (IsLocalizedModule.mapExtendScalars S
              (TensorProduct.mk R A L₁ 1) (TensorProduct.mk R A T 1) A f).comp
                e₁.toLinearMap := by
  obtain ⟨L₁, hfp₁, f, e₁, hβ⟩ :=
    Module.exists_finitely_presented_fixedTargetArrow_of_isLocalization S β
  obtain ⟨L₀, hfp₀, d₀, e₀, hd⟩ :=
    Module.exists_finitely_presented_fixedTargetArrow_of_isLocalization S
      (e₁.toLinearMap.comp d)
  letI : Module.FinitePresentation R L₀ := hfp₀
  obtain ⟨s, hs⟩ := Module.fixedTerminal_uniformDenominator S d β d₀ f e₀ e₁ hd hβ hz
  let d₀' : L₀ →ₗ[R] L₁ := s • d₀
  let e₀' : M₀ ≃ₗ[A] A ⊗[R] L₀ :=
    e₀.trans (LinearEquiv.smulOfUnit (IsLocalization.map_units A s).unit).symm
  have hz' : f.comp d₀' = 0 := by
    calc
      f.comp d₀' = s • (f.comp d₀) := by
        simpa only [d₀', Submonoid.smul_def] using
          (LinearMap.comp_smul f (s : R) d₀)
      _ = 0 := hs
  have hd' : e₁.toLinearMap.comp d =
      (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L₀ 1) (TensorProduct.mk R A L₁ 1) A d₀').comp
          e₀'.toLinearMap :=
    Module.fixedTerminal_rescaleMap S (e₁.toLinearMap.comp d) d₀ e₀ hd s
  exact ⟨L₀, L₁, hfp₀, hfp₁, d₀', f, e₀', e₁, hz', hd', hβ⟩

end
