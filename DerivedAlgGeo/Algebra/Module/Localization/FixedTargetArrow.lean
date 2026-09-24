/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.FiniteDescent

/-!
# Fixed-target arrows over a localized ring

Let `A` be a localization of a Noetherian ring `R`. An arrow from a finite
`A`-module `N` into the base change of an arbitrary `R`-module `T` comes from
an arrow into that same target `T`, after replacing the domain by a finitely
presented `R`-module whose base change is isomorphic to `N`.

The domain is obtained by finite module descent. Finite presentation then
localizes its Hom module, and a denominator is absorbed into the domain
isomorphism. This is a module-level statement: it does not descend complexes
or establish fixed-target extension in a derived category or a t-heart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

noncomputable section

private theorem Module.exists_finitely_presented_fixedTargetArrow_denominator
    {R A N T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] [AddCommGroup T] [Module R T]
    (β : N →ₗ[A] A ⊗[R] T) :
    ∃ L : Submodule R N, Module.FinitePresentation R L ∧
      ∃ (e : A ⊗[R] L ≃ₗ[A] N) (f : L →ₗ[R] T) (s : S),
        s • (β.comp e.toLinearMap) =
          IsLocalizedModule.mapExtendScalars S
            (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f := by
  obtain ⟨L, hfp, _, ⟨e⟩⟩ :=
    Module.exists_finitely_presented_submodule_of_isLocalization
      (R := R) (A := A) (N := N) S
  letI : Module.FinitePresentation R L := hfp
  let lL : L →ₗ[R] A ⊗[R] L := TensorProduct.mk R A L 1
  let lT : T →ₗ[R] A ⊗[R] T := TensorProduct.mk R A T 1
  letI : IsLocalizedModule S lL := by
    dsimp [lL]
    infer_instance
  letI : IsLocalizedModule S lT := by
    dsimp [lT]
    infer_instance
  let h : (L →ₗ[R] T) →ₗ[R] (A ⊗[R] L →ₗ[A] A ⊗[R] T) :=
    IsLocalizedModule.mapExtendScalars S lL lT A
  letI : IsLocalizedModule S h := inferInstance
  obtain ⟨⟨f, s⟩, hs⟩ := IsLocalizedModule.surj S h (β.comp e.toLinearMap)
  exact ⟨L, hfp, e, f, s, hs⟩

/-- Over a localization of a Noetherian ring, every arrow from a finite
localized module into the base change of a fixed `R`-module descends after
changing its domain by an isomorphism. The target `T` need not be finite. -/
theorem Module.exists_finitely_presented_fixedTargetArrow_of_isLocalization
    {R A N T : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] [AddCommGroup T] [Module R T]
    (β : N →ₗ[A] A ⊗[R] T) :
    ∃ L : Submodule R N, Module.FinitePresentation R L ∧
      ∃ (f : L →ₗ[R] T) (e : N ≃ₗ[A] A ⊗[R] L),
        β = (IsLocalizedModule.mapExtendScalars S
          (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f).comp
            e.toLinearMap := by
  obtain ⟨L, hfp, e₀, f, s, hs⟩ :=
    Module.exists_finitely_presented_fixedTargetArrow_denominator S β
  let u : Aˣ := (IsLocalization.map_units A s).unit
  let e : N ≃ₗ[A] A ⊗[R] L :=
    e₀.symm.trans (LinearEquiv.smulOfUnit u).symm
  refine ⟨L, hfp, f, e, ?_⟩
  apply LinearMap.ext
  intro n
  have hs' := LinearMap.congr_fun hs (e₀.symm n)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply] at hs'
  change s • β (e₀ (e₀.symm n)) = _ at hs'
  rw [e₀.apply_symm_apply] at hs'
  have hsA : (u : A) • β n =
      (IsLocalizedModule.mapExtendScalars S
        (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f) (e₀.symm n) := by
    simpa only [u, IsUnit.unit_spec, Submonoid.smul_def,
      IsScalarTower.algebraMap_smul A s.1] using hs'
  change β n =
    (IsLocalizedModule.mapExtendScalars S
      (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f) (e n)
  calc
    β n = (u⁻¹ : Aˣ) • ((u : Aˣ) • β n) := (inv_smul_smul u (β n)).symm
    _ = (u⁻¹ : Aˣ) •
        (IsLocalizedModule.mapExtendScalars S
          (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f) (e₀.symm n) := by
            simpa only [Units.smul_def] using
              congrArg (fun x => (u⁻¹ : Aˣ) • x) hsA
    _ = (IsLocalizedModule.mapExtendScalars S
          (TensorProduct.mk R A L 1) (TensorProduct.mk R A T 1) A f)
        ((u⁻¹ : Aˣ) • e₀.symm n) := by
          simp only [Units.smul_def, map_smul]
    _ = _ := rfl

end
