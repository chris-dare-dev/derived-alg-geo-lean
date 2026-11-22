/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Finiteness
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Transport
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finitely presented sections over affine opens

A finitely presented module sheaf `F` on a scheme `X` has, around every point, an affine open `U`
on which `Γ(U, F)` is a finitely presented `Γ(X, U)`-module. The module `Γ(U, F)` is the cokernel
of a map between finite free modules, read off a finite presentation of `F` on `U ≅ Spec Γ(X, U)`.

`Modules/Affine/Finiteness.lean` has the finite-type form, `Module.Finite` of the sections of a
finitely presented sheaf on `Spec R`; this file adds the relations.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finitePresentation_globalSections_of_presentation`: a module
  sheaf on `Spec R` with a finite global presentation has finitely presented global sections.
* `AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_presentation`: the same over
  an affine open `U` of any scheme, for a finite presentation of the restriction to
  `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Modules.exists_isAffineOpen_presentation`: a finitely presented module
  sheaf has finite presentations on the spectra of arbitrarily small affine opens around each
  point.
* `AlgebraicGeometry.Scheme.Modules.exists_isAffineOpen_finitePresentation_sections`: hence it has
  finitely presented sections on arbitrarily small affine opens around each point.

## Implementation notes

The affine opens are taken inside the opens of a finite `QuasicoherentData`, where a finite
presentation is given. This avoids gluing finite presentation over a cover of `U` by basic opens,
which `Module.FinitePresentation.of_localizationSpan` would also allow; whether every affine open
has finitely presented sections is not needed here and not proved.

## References

The presentation of a sheaf on `Spec R` as the tilde of a cokernel is Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_of_presentation`, and the transport to an affine chart is that
of `AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_presentation`.

## Tags

finitely presented module, quasi-coherent sheaf, affine open, presentation
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **A finite global presentation gives finitely presented global sections.** If a module sheaf
`M` on `Spec R` is the cokernel of a map of free sheaves of finite rank, then `Γ(M)` is a finitely
presented `R`-module.

`tilde` is fully faithful on free modules and preserves cokernels, so `M` is the tilde of the
cokernel of a map `R^J → R^I`, as in Mathlib's `isIso_fromTildeΓ_of_presentation`, and
`Γ(tilde N) ≅ N`. -/
theorem finitePresentation_globalSections_of_presentation (M : (Spec R).Modules)
    (P : M.Presentation) [P.IsFinite] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  let g := (tilde.functor R).preimage <| (tildeFinsupp _).hom ≫ P.relations.π ≫ kernel.ι _ ≫
    (tildeFinsupp _).inv
  let iso : cokernel ((tilde.functor R).map g) ≅ cokernel (P.relations.π ≫ kernel.ι _) := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    simp only [g, (tilde.functor R).map_preimage]
    simp
  let e : (tilde.functor R).obj (cokernel g) ≅ M :=
    PreservesCokernel.iso (tilde.functor R) g ≪≫ iso ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit
  let e' : cokernel g ≅ moduleSpecΓFunctor.obj M :=
    tilde.isoTop _ ≪≫ moduleSpecΓFunctor.mapIso e
  let q := ModuleCat.cokernelIsoRangeQuotient g
  have : Module.FinitePresentation R (cokernel g : ModuleCat.{u} R) := by
    have h : Module.FinitePresentation R
        ((P.generators.I →₀ R) ⧸ LinearMap.range g.hom) :=
      Module.finitePresentation_of_surjective (LinearMap.range g.hom).mkQ
        (Submodule.mkQ_surjective _) (by
          rw [Submodule.ker_mkQ]
          rw [← Submodule.map_top]
          exact (Module.Finite.fg_top (R := R) (M := P.relations.I →₀ R)).map g.hom)
    exact Module.FinitePresentation.of_equiv q.toLinearEquiv.symm
  exact Module.FinitePresentation.of_equiv e'.toLinearEquiv


/-- If `algebraMap R S` is bijective, a module that is finitely presented over `R` is finitely
presented over `S`: the identity is a base change along the localization of `R` at `⊥`. -/
private theorem finitePresentation_of_bijective_algebraMap {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (h : Function.Bijective (algebraMap R S)) [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module.FinitePresentation R M] :
    Module.FinitePresentation S M := by
  have : IsLocalization (⊥ : Submonoid R) S :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_bot]; exact bot_le) h
  exact FinitePresentation.of_isBaseChange LinearMap.id
    ((isLocalizedModule_iff_isBaseChange (⊥ : Submonoid R) S _).mp (isLocalizedModule_id _ M S))

variable {X : Scheme.{u}}

/-- **Finitely presented sections over an affine open.** If the restriction of `F` to the
spectrum of an affine open `U` has a finite presentation, then `Γ(U, F)` is a finitely presented
`Γ(X, U)`-module.

The sections are transported from `Spec Γ(X, U)` along `IsAffineOpen.fromSpec`, through the
ring isomorphisms `Γ(X, U) ≅ Γ(Spec Γ(X, U), ⊤) ≅ Γ(X, U)`, as for finiteness in
`Modules/GenericFlatness.lean`. -/
theorem finitePresentation_sections_of_presentation (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (P : (F.restrict hU.fromSpec).Presentation) [P.IsFinite] :
    Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  let A₀ := Γ(Spec Γ(X, U), ⊤)
  have h₁ : Module.FinitePresentation A₀ Γ(F.restrict hU.fromSpec, ⊤) := by
    let : Algebra Γ(X, U) A₀ := (Scheme.ΓSpecIso Γ(X, U)).inv.hom.toAlgebra
    let : Module Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso Γ(X, U)).inv.hom
    have : Module.FinitePresentation Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      finitePresentation_globalSections_of_presentation _ P
    have : IsScalarTower Γ(X, U) A₀ Γ(F.restrict hU.fromSpec, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact finitePresentation_of_bijective_algebraMap
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, U)).inv)
  let ρ := (hU.fromSpec.appIso ⊤).inv.hom
  let : Algebra A₀ Γ(X, hU.fromSpec ''ᵁ ⊤) := ρ.toAlgebra
  let : Module A₀ Γ(F, hU.fromSpec ''ᵁ ⊤) := Module.compHom _ ρ
  have : IsScalarTower A₀ Γ(X, hU.fromSpec ''ᵁ ⊤) Γ(F, hU.fromSpec ''ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : Γ(F.restrict hU.fromSpec, ⊤) ≃ₗ[A₀] Γ(F, hU.fromSpec ''ᵁ ⊤) :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec F ⊤ r m }
  have : Module.FinitePresentation A₀ Γ(F, hU.fromSpec ''ᵁ ⊤) :=
    Module.FinitePresentation.of_equiv e
  have h := finitePresentation_of_bijective_algebraMap (R := A₀)
    (S := Γ(X, hU.fromSpec ''ᵁ ⊤)) (M := Γ(F, hU.fromSpec ''ᵁ ⊤))
    (ConcreteCategory.bijective_of_isIso (hU.fromSpec.appIso ⊤).inv)
  rwa [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec] at h

set_option backward.isDefEq.respectTransparency false in
/-- **Local finite presentations on affine charts.** Around every point, a finitely presented
module sheaf has a finite presentation on the spectrum of an affine open inside any given
neighbourhood.

The affine open is chosen inside an open of the chosen finite `QuasicoherentData`, and its
presentation is transported along `IsAffineOpen.fromSpec` as in Mathlib's
`Scheme.Modules.exists_isOpenCover_presentation`. -/
theorem exists_isAffineOpen_presentation (F : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u, u, u} F] (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (P : (F.restrict hU.fromSpec).Presentation),
      P.IsFinite ∧ x ∈ U ∧ U ≤ W := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨V, f, hf, hxV⟩ := q.coversTop ⊤ x (by simp)
  obtain ⟨i, ⟨k⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
  have hxi : x ∈ q.X i := k.le hxV
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ q.X i ⊓ W from ⟨hxi, hx⟩)
  replace hU : IsAffineOpen U := hU
  let Wi : X.Opens := q.X i
  have hUi : U ≤ Wi := hUle.trans inf_le_left
  let u : Spec Γ(X, U) ⟶ Wi.toScheme := IsOpenImmersion.lift Wi.ι hU.fromSpec (by
    rw [hU.range_fromSpec, Scheme.Opens.range_ι]; exact hUi)
  have hu : u ≫ Wi.ι = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion u := by
    have : IsOpenImmersion (u ≫ Wi.ι) := by rw [hu]; infer_instance
    exact IsOpenImmersion.of_comp u Wi.ι
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
  let G := (overEquiv Wi).functor ⋙ restrictFunctor u
  have : PreservesColimitsOfSize.{u, u} G := inferInstance
  let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ G ≅ restrictFunctor hU.fromSpec :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
      (restrictFunctorComp _ _).symm ≪≫ (restrictFunctorCongr hu)
  have : ((q.presentation i).map G (Scheme.Modules.restrictUnitIso _).symm).IsFinite :=
    SheafOfModules.Presentation.isFinite_map _ G _
  exact ⟨U, hU, SheafOfModules.Presentation.ofIsIso (iso.app F).hom
    ((q.presentation i).map G (Scheme.Modules.restrictUnitIso _).symm), inferInstance,
    hxU, hUle.trans inf_le_right⟩

/-- **Finitely presented sections on a basis of affine opens.** Around every point and inside any
neighbourhood of it, a finitely presented module sheaf has an affine open on which its sections
are a finitely presented module over the ring of functions. -/
theorem exists_isAffineOpen_finitePresentation_sections (F : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u, u, u} F] (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
      Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  obtain ⟨U, hU, P, hP, hxU, hUW⟩ := exists_isAffineOpen_presentation F x W hx
  exact ⟨U, hU, hxU, hUW, finitePresentation_sections_of_presentation F hU P⟩

end AlgebraicGeometry.Scheme.Modules
