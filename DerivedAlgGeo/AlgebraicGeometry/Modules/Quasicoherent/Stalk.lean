/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing
import DerivedAlgGeo.AlgebraicGeometry.Modules.Ample

/-!
# Germs of a quasi-coherent module sheaf over an affine open

For a quasi-coherent module sheaf `M` on a scheme `X` and an affine open `U`, the germ map
`Γ(U, M) → M_x` at a point `x ∈ U` is the localization of the `Γ(X, U)`-module `Γ(U, M)` at the
prime of `x`: on `U`, `M` is the sheaf associated to `Γ(U, M)` (Stacks 01IA), whose stalk at a
prime `𝔭` is the localization at `𝔭` (Stacks 01HV). The stalk is a `Γ(X, U)`-module through the
germ of functions.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.germLinearMap`: the germ map at `x ∈ U` as a `Γ(X, U)`-linear
  map into the stalk.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germLinearMap`: for quasi-coherent `M` and
  affine `U`, the germ map at the point `hU.fromSpec y` is the localization at `y`.

## Implementation notes

The proof reads the localization off the basic opens of `U`. A section over `D(f) ⊆ U` is a
restriction from `U` up to a power of `f`, and a section over `U` vanishing on `D(f)` is killed by
a power of `f`. Both are transported from `Spec Γ(X, U)` along `IsAffineOpen.fromSpec`, where
`isLocalizedModule_basicOpenRestriction_of_isQuasicoherent` supplies them.

## References

* [Stacks, Lemma 26.7.4 (Tag 01IA)](https://stacks.math.columbia.edu/tag/01IA)
* [Stacks, Lemma 26.5.4 (Tag 01HV)](https://stacks.math.columbia.edu/tag/01HV), item 7

## Tags

quasi-coherent sheaf, stalk, localization, affine open
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}}

/-- On `Spec Γ(X, U)`, the scalar action of `Γ(X, U)` on sections restricted along
`IsAffineOpen.fromSpec` is the action of the restricted sections over `X`. -/
theorem fromSpec_appIso_inv_ΓSpecIso {U : X.Opens} (hU : IsAffineOpen U)
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

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The germ map at `x ∈ U` as a `Γ(X, U)`-linear map. The stalk is a `Γ(X, U)`-module by
restriction of scalars along the germ of functions. -/
noncomputable def germLinearMap (M : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) :
    Γ(M, U) →ₗ[Γ(X, U)] (ModuleCat.restrictScalars (X.presheaf.germ U x hx).hom).obj
      ((moduleStalkFunctor X x).obj M) where
  toFun := germ M x hx
  map_add' := germ_add M x hx
  map_smul' := germ_smul M x hx

@[simp]
theorem germLinearMap_apply (M : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(M, U)) :
    germLinearMap M U x hx s = germ M x hx s :=
  rfl

/-- Restricting along `V ≤ W ≤ U` in two steps is restricting in one. -/
private theorem res_res (M : X.Modules) {U V W : X.Opens} (hVW : V ≤ W) (hWU : W ≤ U)
    (s : Γ(M, U)) :
    M.presheaf.map (homOfLE hVW).op (M.presheaf.map (homOfLE hWU).op s) =
      M.presheaf.map (homOfLE (hVW.trans hWU)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting along an equality of opens and back is the identity. -/
private theorem res_self (M : X.Modules) {U : X.Opens} (h : U ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op s = s := by
  change M.presheaf.map (𝟙 (op U)) s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **Sections of a quasi-coherent module sheaf over a basic open `D(f)` of an affine open `U`
are, up to a power of `f`, restrictions of sections over `U`.** -/
theorem exists_res_eq_pow_smul (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
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
    exact congrArg (· • t') (hU.fromSpec_appIso_inv_ΓSpecIso _ (f ^ n))
  have hDX : X.basicOpen f ≤ ι ''ᵁ PrimeSpectrum.basicOpen f := himg.ge
  calc M.presheaf.map (homOfLE (X.basicOpen_le f)).op (M.presheaf.map (homOfLE htop).op s')
      = M.presheaf.map (homOfLE hDX).op
          (M.presheaf.map (homOfLE (ι.image_mono le_top)).op s') := by
        rw [res_res, res_res]
    _ = M.presheaf.map (homOfLE hDX).op (X.presheaf.map (homOfLE hle).op (f ^ n) • t') := by
        rw [key]
    _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • t := by
        rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 1
        change M.presheaf.map (homOfLE hDX).op (M.presheaf.map (eqToHom himg).op t) = t
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg (fun φ ↦ (M.presheaf.map φ).hom t) (Subsingleton.elim _ (𝟙 _)) |>.trans
          (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- **A section of a quasi-coherent module sheaf over an affine open `U` that vanishes on a basic
open `D(f)` is killed by a power of `f`.** -/
theorem exists_pow_smul_eq_zero (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
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
    exact congrArg (· • s') (hU.fromSpec_appIso_inv_ΓSpecIso ⊤ (f ^ n)).symm
  rw [← Scheme.Modules.map_smul] at hc'
  calc f ^ n • s = M.presheaf.map (homOfLE htop).op
        (M.presheaf.map (homOfLE htop').op (f ^ n • s)) := by
        rw [res_res, res_self]
    _ = 0 := by rw [hc', map_zero]

private theorem mem_basicOpen_fromSpec_iff {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (g : Γ(X, U)) :
    hU.fromSpec y ∈ X.basicOpen g ↔ g ∉ y.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  rfl

private theorem mem_basicOpen_pow {U : X.Opens} {x : X} (hx : x ∈ U) (f : Γ(X, U)) (n : ℕ)
    (hxf : x ∈ X.basicOpen f) : x ∈ X.basicOpen (f ^ n) := by
  rw [X.mem_basicOpen _ _ hx, map_pow]
  exact ((X.mem_basicOpen _ _ hx).mp hxf).pow n

/-- **For a quasi-coherent module sheaf and an affine open `U`, the germ map
`Γ(U, M) → M_x` is the localization at the prime of `x`.** -/
theorem isLocalizedModule_germLinearMap (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec y ∈ U) :
    IsLocalizedModule y.asIdeal.primeCompl (germLinearMap M U (hU.fromSpec y) hy) where
  map_units g := by
    obtain ⟨u, hu⟩ := (X.mem_basicOpen (g : Γ(X, U)) _ hy).mp
      ((mem_basicOpen_fromSpec_iff hU y g).mpr g.2)
    rw [Module.End.isUnit_iff]
    refine ⟨fun m m' h ↦ ?_, fun m ↦ ⟨(↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • m, ?_⟩⟩
    · change X.presheaf.germ U _ hy g • m = X.presheaf.germ U _ hy g • m' at h
      rw [← hu] at h
      have := congrArg (fun z ↦ (↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • z) h
      simpa only [smul_smul, Units.inv_mul, one_smul] using this
    · change X.presheaf.germ U _ hy g • (↑u⁻¹ : X.presheaf.stalk (hU.fromSpec y)) • m = m
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  surj m := by
    obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq M _ m
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨_, hxW⟩ hy
    obtain ⟨n, s, hs⟩ := exists_res_eq_pow_smul M hU f (M.presheaf.map (homOfLE hfW).op t)
    have hn : f ^ n ∈ y.asIdeal.primeCompl :=
      (mem_basicOpen_fromSpec_iff hU y _).mp (mem_basicOpen_pow hy f n hxf)
    refine ⟨⟨s, ⟨f ^ n, hn⟩⟩, ?_⟩
    change X.presheaf.germ U _ hy (f ^ n) • germ M _ hxW t = germ M _ hy s
    rw [← germ_res M (X.basicOpen_le f) _ hxf s, hs, germ_smul, germ_res,
      TopCat.Presheaf.germ_res_apply]
  exists_of_eq {s₁ s₂} h := by
    have h' : germ M _ hy (s₁ - s₂) = germ M _ hy 0 := by
      rw [germ_zero]
      exact ((germLinearMap M U _ hy).map_sub s₁ s₂).trans (sub_eq_zero.mpr h)
    obtain ⟨W, hxW, hWU, hWU', hW⟩ := exists_res_eq_of_germ_eq M _ hy hy _ _ h'
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨_, hxW⟩ hy
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M hU f (s₁ - s₂) (by
      rw [← res_res M hfW hWU, hW, map_zero, map_zero])
    refine ⟨⟨f ^ n, (mem_basicOpen_fromSpec_iff hU y _).mp (mem_basicOpen_pow hy f n hxf)⟩, ?_⟩
    change f ^ n • s₁ = f ^ n • s₂
    rwa [smul_sub, sub_eq_zero] at hn

end AlgebraicGeometry.Scheme.Modules
