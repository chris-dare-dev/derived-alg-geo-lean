/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Epi
import DerivedAlgGeo.AlgebraicGeometry.Modules.LocallySurjective
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Pushforward along an affine morphism preserves epimorphisms of quasi-coherent sheaves

Pushforward of module sheaves is a right adjoint, so it is left exact on every sheaf; along an
affine morphism it is also right exact on quasi-coherent sheaves.  This file proves the
epimorphism half of that statement, which is what makes the pushforward of coherent sheaves
along a finite morphism exact (`Modules/Coherent/Pushforward/Finite.lean`).

## Main results

* `Scheme.Modules.isQuasicoherent_pushforward_SpecMap`: pushforward along a morphism of affine
  spectra preserves quasi-coherent module sheaves.
* `gammaPushforwardNatIso`: global sections identify affine pushforward with restriction of
  scalars, naturally in the module sheaf.
* `Scheme.Modules.pushforward_map_epi_of_isAffineHom`: for an affine morphism `f` and an
  epimorphism `u` of quasi-coherent sheaves, `f_* u` is an epimorphism.

## Implementation notes

The statement is about one morphism, not `(pushforward f).PreservesEpimorphisms`: pushforward
along an affine morphism does not preserve epimorphisms of arbitrary module sheaves, so the
class would be false; the closed-embedding case where it does hold on every sheaf is
`pushforward_preservesFiniteColimits_of_isClosedImmersion`.

The proof is the pointwise-preimage criterion `epi_of_pointwise_preimages`: a section of
`f_* N` near a point of `Y` lives on an affine open `W`, the preimage `f ⁻¹ᵁ W` is affine
because `f` is, and `surjective_app_of_epi_of_isAffineOpen` lifts the section there.  The
sections of `f_* N` over `W` are the sections of `N` over `f ⁻¹ᵁ W` by definition, so no
comparison isomorphism appears.

## References

* Hartshorne, *Algebraic Geometry*, Exercise II.5.17(b) and (e): an affine morphism identifies
  quasi-coherent sheaves on the source with quasi-coherent modules over `f_* 𝒪_X`, of which
  this is the right-exactness half; the affine-sections input is referenced in
  `Modules/Affine/Epi.lean`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The global sections of a pushforward along `Spec.map f`, as an `R`-module, are the global
sections of the original with `R` acting through `f`. -/
noncomputable def gammaPushforwardIso (M : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj M) ≅
      (ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj M) :=
  (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : (Spec R).Opens))).mapIso
    ((pushforwardCompModulesSpecToSheafIso f).app M)

/-- Global sections identify affine pushforward with restriction of scalars,
naturally in the module sheaf. -/
noncomputable def gammaPushforwardNatIso :
    Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars f.hom :=
  NatIso.ofComponents (gammaPushforwardIso f) (fun {M N} g ↦ by
    let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : (Spec R).Opens))
    change H.map ((Scheme.Modules.pushforward (Spec.map f) ⋙
        modulesSpecToSheaf).map g) ≫
        H.map ((pushforwardCompModulesSpecToSheafIso f).hom.app N) =
      H.map ((pushforwardCompModulesSpecToSheafIso f).hom.app M) ≫
        H.map ((modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map f).base ⋙
          sheafCompose _ (ModuleCat.restrictScalars f.hom)).map g)
    rw [← H.map_comp, (pushforwardCompModulesSpecToSheafIso f).hom.naturality,
      H.map_comp]
    rfl)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward along a morphism of affine spectra preserves quasi-coherence.  The affine
counit remains invertible after pushforward, and on an affine spectrum invertibility of that
counit characterizes quasi-coherent module sheaves. -/
theorem isQuasicoherent_pushforward_SpecMap
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((pushforward (Spec.map f)).obj M).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  letI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  exact isIso_fromTildeΓ_pushforward f M

/-- Pushforward along an affine morphism sends an epimorphism of quasi-coherent module
sheaves to an epimorphism.  Locally on the target, a section over an affine open `W` is a
section of `N` over the affine open `f ⁻¹ᵁ W`, where `surjective_app_of_epi_of_isAffineOpen`
lifts it. -/
theorem pushforward_map_epi_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {M N : X.Modules} (u : M ⟶ N) [Epi u] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Epi ((pushforward f).map u) := by
  refine epi_of_pointwise_preimages _ ?_
  intro U t y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hy
  exact ⟨W, hWU, hyW, surjective_app_of_epi_of_isAffineOpen u (f ⁻¹ᵁ W)
    (IsAffineHom.isAffine_preimage W hW) _⟩

end AlgebraicGeometry.Scheme.Modules
