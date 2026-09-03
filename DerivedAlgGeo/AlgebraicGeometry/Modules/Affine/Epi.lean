/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Iso
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Epimorphisms of quasi-coherent sheaves are surjective on affine sections

An epimorphism of sheaves is only locally surjective on sections.  For quasi-coherent
sheaves the defect disappears over affine opens: an epimorphism `u : M ⟶ N` of
quasi-coherent module sheaves is surjective on sections over every affine open.  This is the
degree-one consequence of the vanishing of higher cohomology of quasi-coherent sheaves on
affine schemes, and it is the form in which that vanishing enters the exactness of pushforward
along an affine morphism (`Modules/Pushforward/Affine.lean`).

## Main results

* `Scheme.Modules.surjective_app_top_of_epi_spec`: on `Spec R`, global sections of an
  epimorphism of quasi-coherent sheaves are surjective.
* `Scheme.Modules.surjective_app_top_of_epi_of_isAffine`: the same on any affine scheme.
* `Scheme.Modules.surjective_app_of_epi_of_isAffineOpen`: sections over an affine open of any
  scheme.

## Implementation notes

No cohomology is computed.  On `Spec R` the global-sections functor restricted to
quasi-coherent sheaves is the inverse half of Mathlib's `tildeEquiv`, an equivalence preserves
epimorphisms, and an epimorphism in `ModuleCat R` is a surjection.  The affine-scheme and
affine-open cases transport this along `X.isoSpec` and along the restriction to the open:
pushforward along an isomorphism is restriction along its inverse (`pushforwardIsoRestrict`),
restriction along an open immersion is a left adjoint and so preserves epimorphisms, and
quasi-coherence restricts (`Scheme.Hom.isQuasicoherent_restrict`).

The morphism `u` has to cross the `Scheme.Modules` wrapper to be seen as a morphism of the
full subcategory `tildeEquiv` lands in; `Scheme.Modules.epi_sheafOfModules` is that transfer,
and `Modules/Affine/Equivalence.lean` explains why it is needed.

## References

* Hartshorne, *Algebraic Geometry*, Corollary II.5.5: the equivalence `M ↦ M~` with inverse
  `Γ`, which is Mathlib's `tildeEquiv` and is all the proof uses.  The cohomological reading
  is Theorem III.3.5 for Noetherian `A` or, without the chain condition, the Stacks Project
  lemma on vanishing of quasi-coherent cohomology on affine schemes.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R`, an epimorphism of quasi-coherent module sheaves is surjective on global
sections.  Global sections restricted to quasi-coherent sheaves are the inverse half of
`tildeEquiv`, so they preserve epimorphisms, and an epimorphism of `R`-modules is a
surjection.  The `Scheme.Modules` wrapper is crossed once, through `epi_sheafOfModules`. -/
theorem surjective_app_top_of_epi_spec {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (u : M ⟶ N) [Epi u] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective (u.app ⊤) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, ‹M.IsQuasicoherent›⟩
  let N' : P.FullSubcategory := ⟨N, ‹N.IsQuasicoherent›⟩
  let u' : M' ⟶ N' := P.fullyFaithfulι.preimage (X := M') (Y := N') u
  have hu' : P.ι.map u' = u := P.fullyFaithfulι.map_preimage (X := M') (Y := N') u
  haveI : Epi u' := P.ι.epi_of_epi_map (by rw [hu']; exact epi_sheafOfModules u)
  haveI : (tildeEquiv (R := R)).inverse.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (tildeEquiv (R := R)).symm.toAdjunction
  have h : Epi ((tildeEquiv (R := R)).inverse.map u') := inferInstance
  have h2 : Epi (moduleSpecΓFunctor.map u) := by
    have e : (tildeEquiv (R := R)).inverse.map u' = moduleSpecΓFunctor.map u := by
      change moduleSpecΓFunctor.map (P.ι.map u') = _
      rw [hu']
      rfl
    rw [e] at h
    exact h
  exact (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map u)).1 h2

/-- On an affine scheme, an epimorphism of quasi-coherent module sheaves is surjective on
global sections.  Transported to `Spec Γ(X, ⊤)` along `X.isoSpec`: pushforward along an
isomorphism is restriction along its inverse, which is a left adjoint and preserves both
epimorphisms and quasi-coherence, and the global sections of the pushforward are the global
sections of `M` by definition. -/
theorem surjective_app_top_of_epi_of_isAffine {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    (u : M ⟶ N) [Epi u] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective (u.app ⊤) := by
  let e := X.isoSpec
  haveI : (pushforward e.hom).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms.of_iso (pushforwardIsoRestrict e).symm
  haveI hM : ((pushforward e.hom).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      ((pushforwardIsoRestrict e).app M).symm
      (e.inv.isQuasicoherent_restrict M (SheafOfModules.isQuasicoherent_over M _))
  haveI hN : ((pushforward e.hom).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      ((pushforwardIsoRestrict e).app N).symm
      (e.inv.isQuasicoherent_restrict N (SheafOfModules.isQuasicoherent_over N _))
  exact surjective_app_top_of_epi_spec ((pushforward e.hom).map u)

/-- Over an affine open `V` of any scheme, an epimorphism of quasi-coherent module sheaves is
surjective on sections.  Restriction to `V` is a left adjoint and quasi-coherence restricts,
so `surjective_app_top_of_epi_of_isAffine` applies on the affine scheme `V.toScheme`, whose
global sections are the sections over `V` because `V.ι ''ᵁ ⊤ = V`. -/
theorem surjective_app_of_epi_of_isAffineOpen {X : Scheme.{u}} {M N : X.Modules}
    (u : M ⟶ N) [Epi u] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (V : X.Opens) (hV : IsAffineOpen V) :
    Function.Surjective (u.app V) := by
  haveI : IsAffine V.toScheme := hV
  haveI : (M.restrict V.ι).IsQuasicoherent :=
    V.ι.isQuasicoherent_restrict M (SheafOfModules.isQuasicoherent_over M _)
  haveI : (N.restrict V.ι).IsQuasicoherent :=
    V.ι.isQuasicoherent_restrict N (SheafOfModules.isQuasicoherent_over N _)
  have h := surjective_app_top_of_epi_of_isAffine ((restrictFunctor V.ι).map u)
  change Function.Surjective (u.app (V.ι ''ᵁ ⊤)) at h
  rwa [Scheme.Opens.ι_image_top] at h

end AlgebraicGeometry.Scheme.Modules
