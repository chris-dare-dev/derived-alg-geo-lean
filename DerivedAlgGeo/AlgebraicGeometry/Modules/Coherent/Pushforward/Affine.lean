/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Basic.Isomorphism

/-!
# Pushforward of a coherent sheaf along an affine closed immersion

Step 2 of #572 asks for coherence of `ι_* F` along a closed immersion. This file proves the
affine case, which is where the mathematical content is: everything else is the descent already
in `CoherentSheaf/Descent/Locality.lean`.

## The route

Three facts do the work, and all three are at the pin:

* a coherent sheaf on an affine scheme is the tilde of its global sections
  (`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`);
* being a tilde is preserved by pushforward along `Spec.map`
  (`AlgebraicGeometry.isIso_fromTildeΓ_pushforward`);
* the global sections of the pushforward are the global sections of the original, with the base
  ring acting through `φ` (`AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso`, evaluated at
  `⊤`) — this is `gammaPushforwardIso` below.

So the pushforward is the tilde of an `R`-module, and coherence reduces to that module being
finitely generated over `R`. That is the only place the hypothesis on `φ` is used, and it is
used through `Module.Finite R S`: surjectivity is sufficient, not necessary. The statement is
phrased with surjectivity because that is what a closed immersion supplies
(`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:361`).

## Noetherian hypotheses

`R` must be noetherian: finite generation of the pushed-forward module gives finite
*presentation* only there, and coherence in this repository is finite presentation. `S` needs no
hypothesis — `moduleFinite_globalSections` reads finiteness straight off the presentation.
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The global sections of a pushforward along `Spec.map φ`, as an `R`-module, are the global
sections of the original with `R` acting through `φ`.

This is `pushforwardCompModulesSpecToSheafIso` evaluated at the top open. Mathlib states that
compatibility at the level of sheaves of modules; what is needed downstream is its value on
global sections, and taking it here keeps the evaluation out of the finiteness argument. -/
noncomputable def gammaPushforwardIso (M : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M) :=
  (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (CategoryTheory.evaluation _ _).obj (op (⊤ : (Spec R).Opens))).mapIso
    ((AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ).app M)

/-- Global sections of a coherent sheaf stay finitely generated after restriction of scalars
along a surjection. The surjection makes `S` a finite `R`-module, and finiteness composes down
the tower. -/
theorem moduleFinite_gammaPushforward (hφ : Function.Surjective φ.hom)
    (M : (Spec S).Modules) (hM : Scheme.Modules.IsCoherent (Spec S) M) :
    Module.Finite R
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) := by
  have hM' : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  haveI : Module.Finite S (moduleSpecΓFunctor.obj M) :=
    Scheme.Modules.moduleFinite_globalSections M hM'
  algebraize [φ.hom]
  haveI : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hφ
  -- The tower is not an instance: `ModuleCat.restrictScalars` leaves the carrier alone, so
  -- Mathlib's `RestrictScalars.isScalarTower` does not match. It is `mul_smul` all the same.
  letI : IsScalarTower R S
      ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) :=
    ⟨fun r s x ↦ by
      show (r • s) • (show moduleSpecΓFunctor.obj M from x) = _
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  haveI : Module.Finite S
      ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) :=
    inferInstanceAs (Module.Finite S (moduleSpecΓFunctor.obj M))
  haveI : Module.Finite R ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) :=
    Module.Finite.trans (R := R) S _
  exact Module.Finite.equiv (gammaPushforwardIso φ M).symm.toLinearEquiv

/-- **Coherence is preserved by pushforward along an affine closed immersion.**

The tilde identification is what makes this true rather than merely plausible: the pushforward
is not coherent because coherence is somehow local along `φ`, it is coherent because it *is* the
tilde of a finitely generated module over a noetherian ring. -/
theorem isCoherent_pushforward_of_surjective [IsNoetherianRing R]
    (hφ : Function.Surjective φ.hom) (M : (Spec S).Modules)
    (hM : Scheme.Modules.IsCoherent (Spec S) M) :
    Scheme.Modules.IsCoherent (Spec R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M) := by
  have hM' : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  haveI : M.IsQuasicoherent := inferInstance
  haveI : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  haveI : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ M
  haveI : Module.Finite R
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)) :=
    moduleFinite_gammaPushforward φ hφ M hM
  exact (Scheme.coherent (Spec R)).prop_of_iso
    (asIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ)
    (isCoherent_tilde_of_finite
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M)))

end AlgebraicGeometry
