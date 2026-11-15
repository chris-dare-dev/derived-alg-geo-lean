/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing

/-!
# Sections of a quasi-coherent module sheaf over a basic open

For a quasi-coherent module sheaf `M` on a scheme `X`, an affine open `U` and `f : Γ(X, U)`,
restriction `Γ(M, U) → Γ(M, D(f))` is the localization of `Γ(M, U)` away from `f`
(Stacks 01IA, 01HV). This is the module form of
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`: restriction to `D(f)` is
  `IsLocalizedModule (Submonoid.powers f)`, for any `Γ(X, U)`-module structure on `Γ(M, D(f))`
  that factors through `Γ(X, D(f))`.

## Implementation notes

The module structure of `Γ(M, D(f))` over `Γ(X, U)` is not an instance in this repository, so
the statement takes one as an argument together with the scalar tower through `Γ(X, D(f))`; the
restriction map is any linear map with the restriction as its underlying function. The proof
restricts `M` along `IsAffineOpen.fromSpec` and uses the affine case
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent`.

## References

* [Stacks, Lemma 26.7.4 (Tag 01IA)](https://stacks.math.columbia.edu/tag/01IA): a quasi-coherent
  module on an affine scheme is the sheaf associated to its global sections.
* [Stacks, Lemma 26.5.4 (Tag 01HV)](https://stacks.math.columbia.edu/tag/01HV): the sections of
  `M~` over `D(f)` are `M_f`, and restriction is the localization map.

## Tags

quasi-coherent, module sheaf, basic open, localization
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On `Spec Γ(X, U)`, the scalar action of `Γ(X, U)` on sections restricted along
`IsAffineOpen.fromSpec` is the action of the restricted sections over `X`. -/
private theorem fromSpec_appIso_inv_ΓSpecIso {U : X.Opens} (hU : IsAffineOpen U)
    (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE
        ((hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le)).op r := by
  have e : W ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]; exact le_top
  have h1 : hU.fromSpec.appLE U W e r = (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, IsAffineOpen.fromSpec_app_self,
      CommRingCat.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← h1, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_appIso_inv]

/-- Sections of a quasi-coherent module sheaf over a basic open `D(f)` of an affine open `U`
are, up to a power of `f`, restrictions of sections over `U`. -/
private theorem exists_res_eq_pow_smul (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (t : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (s : Γ(M, U)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op s =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • t := by
  let ι := hU.fromSpec
  let N := M.restrict ι
  have hloc := N.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  have himg : ι ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have htop : U ≤ ι ''ᵁ ⊤ :=
    ((Scheme.Hom.image_top_eq_opensRange ι).trans hU.opensRange_fromSpec).ge
  let t' : Γ(M, ι ''ᵁ PrimeSpectrum.basicOpen f) := M.presheaf.map (eqToHom himg).op t
  obtain ⟨⟨s₀, ⟨_, n, rfl⟩⟩, hs'⟩ := hloc.surj (show Γ(N, PrimeSpectrum.basicOpen f) from t')
  let s' : Γ(M, ι ''ᵁ ⊤) := s₀
  refine ⟨n, M.presheaf.map (homOfLE htop).op s', ?_⟩
  have hle : ι ''ᵁ PrimeSpectrum.basicOpen f ≤ U :=
    (ι.image_le_opensRange _).trans hU.opensRange_fromSpec.le
  have key : M.presheaf.map (homOfLE (ι.image_mono le_top)).op s' =
      X.presheaf.map (homOfLE hle).op (f ^ n) • t' := by
    refine hs'.symm.trans ?_
    change (hU.fromSpec.appIso (PrimeSpectrum.basicOpen f : (Spec Γ(X, U)).Opens)).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv (f ^ n))) •
        t' = _
    exact congrArg (· • t') (fromSpec_appIso_inv_ΓSpecIso hU _ (f ^ n))
  have hDX : X.basicOpen f ≤ ι ''ᵁ PrimeSpectrum.basicOpen f := himg.ge
  calc M.presheaf.map (homOfLE (X.basicOpen_le f)).op (M.presheaf.map (homOfLE htop).op s')
      = M.presheaf.map (homOfLE hDX).op
          (M.presheaf.map (homOfLE (ι.image_mono le_top)).op s') := by
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl
    _ = M.presheaf.map (homOfLE hDX).op (X.presheaf.map (homOfLE hle).op (f ^ n) • t') := by
        rw [key]
    _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • t := by
        rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 1
        change M.presheaf.map (homOfLE hDX).op (M.presheaf.map (eqToHom himg).op t) = t
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg (fun φ ↦ (M.presheaf.map φ).hom t) (Subsingleton.elim _ (𝟙 _)) |>.trans
          (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- A section of a quasi-coherent module sheaf over an affine open `U` that vanishes on a basic
open `D(f)` is killed by a power of `f`. -/
private theorem exists_pow_smul_eq_zero (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (s : Γ(M, U))
    (hs : M.presheaf.map (homOfLE (X.basicOpen_le f)).op s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  let ι := hU.fromSpec
  let N := M.restrict ι
  have hloc := N.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  have himg : ι ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  have htop' : ι ''ᵁ ⊤ ≤ U := (ι.image_le_opensRange _).trans hU.opensRange_fromSpec.le
  have htop : U ≤ ι ''ᵁ ⊤ :=
    ((Scheme.Hom.image_top_eq_opensRange ι).trans hU.opensRange_fromSpec).ge
  let s' : Γ(M, ι ''ᵁ ⊤) := M.presheaf.map (homOfLE htop').op s
  have h0 : (N.basicOpenRestriction f).hom
      (show (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤) from s') =
        (N.basicOpenRestriction f).hom 0 := by
    rw [map_zero]
    change M.presheaf.map (homOfLE (ι.image_mono le_top)).op s' = 0
    calc M.presheaf.map (homOfLE (ι.image_mono le_top)).op s'
        = M.presheaf.map (eqToHom himg).op
            (M.presheaf.map (homOfLE (X.basicOpen_le f)).op s) := by
          rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
            ← Functor.map_comp]
          rfl
      _ = 0 := by rw [hs, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := hloc.exists_of_eq h0
  refine ⟨n, ?_⟩
  rw [smul_zero] at hc
  have hc' : X.presheaf.map (homOfLE htop').op (f ^ n) • s' = 0 := by
    refine Eq.trans ?_ hc
    change _ = (hU.fromSpec.appIso ⊤).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv (f ^ n))) •
        s'
    exact congrArg (· • s') (fromSpec_appIso_inv_ΓSpecIso hU ⊤ (f ^ n)).symm
  rw [← Scheme.Modules.map_smul] at hc'
  calc f ^ n • s = M.presheaf.map (homOfLE htop).op
        (M.presheaf.map (homOfLE htop').op (f ^ n • s)) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact (congrArg (fun φ ↦ (M.presheaf.map φ).hom (f ^ n • s))
          (Subsingleton.elim _ (𝟙 _)) |>.trans (by rw [CategoryTheory.Functor.map_id]; rfl)).symm
    _ = 0 := by rw [hc', map_zero]

/-- **Sections of a quasi-coherent module over a basic open** (Stacks 01IA, 01HV). For a
quasi-coherent `M`, an affine open `U` and `f : Γ(X, U)`, restriction `Γ(M, U) → Γ(M, D(f))` is
the localization away from `f`. The `Γ(X, U)`-module structure on `Γ(M, D(f))` is any one
factoring through `Γ(X, D(f))`, and `g` is any linear map whose underlying function is the
restriction. -/
theorem isLocalizedModule_basicOpen (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)]
    (g : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f))
    (hg : ∀ s, g s = M.presheaf.map (homOfLE (X.basicOpen_le f)).op s) :
    IsLocalizedModule (Submonoid.powers f) g where
  map_units s := by
    obtain ⟨_, n, rfl⟩ := s
    have := hU.isLocalization_basicOpen f
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have h (x : Γ(M, X.basicOpen f)) :
        algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) (f ^ n) x =
          algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n) • x := by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨(↑hu.unit⁻¹ : Γ(X, X.basicOpen f)) • b, ?_⟩⟩
    · rw [h, h] at hab
      exact hu.smul_left_cancel.mp hab
    · rw [h, smul_smul, IsUnit.mul_val_inv, one_smul]
  surj t := by
    obtain ⟨n, s, hs⟩ := exists_res_eq_pow_smul M hU f t
    refine ⟨⟨s, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    change f ^ n • t = g s
    rw [hg, hs, ← algebraMap_smul Γ(X, X.basicOpen f) (f ^ n) t]
    rfl
  exists_of_eq {s₁ s₂} h := by
    rw [hg, hg] at h
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M hU f (s₁ - s₂) (by rw [map_sub, h, sub_self])
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

end AlgebraicGeometry.Scheme.Modules
