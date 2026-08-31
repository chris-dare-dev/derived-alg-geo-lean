/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Basic.Definitions
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Finiteness
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Finite
import DerivedAlgGeo.Topology.Opens.Limits
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Coherent sheaves on an affine scheme

**Layer B, stage 1.** The affine comparison between coherent sheaves on `Spec R` and
finitely presented `R`-modules.

## Main results

* `AlgebraicGeometry.isFinitePresentation_tilde` — `M^~` is of finite presentation whenever
  `M` is a finitely presented `R`-module;
* `AlgebraicGeometry.isCoherent_tilde` — the same statement phrased with
  `Scheme.Modules.IsCoherent`, which is what `Coh (Spec R)` is carved out of;
* `AlgebraicGeometry.isCoherent_tilde_of_finite` — over a noetherian ring the hypothesis
  weakens to finite generation;
* `AlgebraicGeometry.moduleFinite_globalSections_of_isFiniteType` — finite-type
  quasi-coherent sheaves have finite global sections on an affine noetherian scheme;
* `AlgebraicGeometry.moduleFinitePresentation_globalSections_of_isCoherent` — coherent
  sheaves have finitely presented global sections.
* `AlgebraicGeometry.Coh.affineEquivalence` — coherent sheaves on `Spec R` are equivalent
  to finitely generated `R`-modules when `R` is noetherian.

## Proof strategy

Mathlib already does the mathematics. `AlgebraicGeometry.presentationTilde` turns a
generating set `s` for `M` together with a generating set `t` for the kernel of `R^s → M`
into a global `SheafOfModules.Presentation (tilde M)`, and that is exactly the data recorded
by `Module.FinitePresentation`. So the content here is only that the presentation is
*finite* — `Presentation.IsFinite` is finiteness of the two index types, and
`presentationTilde` builds them out of `s` and `t` themselves — after which
`SheafOfModules.IsFinitePresentation.of_presentation` applies.

## Two elaboration hazards

Both cost more time than the mathematics, and both are recorded here so the next caller does
not rediscover them.

1. **Universes do not propagate from the goal.** `Presentation.IsFinite` and
   `of_presentation` carry universe parameters that bind *before* their explicit arguments,
   so a goal phrased as `Scheme.Modules.IsCoherent …` does not pin them; Lean defaults them
   to `0` and reports a type mismatch at `Type 1` rather than an ambiguity. Annotating
   `.{u, u, u}` at the use site is what fixes it — `(M := …)` does not, because the
   universes bind first. This is the gotcha already recorded in
   `CategoryTheory/Sites/Sheaves/Modules/Presentation.lean`.
2. **Anonymous constructors do not see the expected type here.** `refine ⟨⟨?_⟩, ?_⟩` against
   a ground `Presentation.IsFinite …` goal still elaborates at universe `0`, and
   `refine Presentation.IsFinite.mk ?_ ?_` gets stuck synthesising
   `WEqualsLocallyBijective ?J AddCommGrpCat` because the head is elaborated before the goal
   is unified. `constructor` unifies with the goal first and goes through.

The `Finset`/`Set` mismatch that an earlier investigation predicted — `FinitePresentation`
gives `s : Finset M` while `presentationTilde` wants `s : Set M` and `t : Set (↥s →₀ R)` —
does not in fact bite: the coercion is accepted as written.

The converse finiteness results use the affine comparison and localisation patching developed
in `AlgebraicGeometry.Modules.Affine.Finiteness`.

## Affine equivalence

The object-level finiteness results restrict Mathlib's `tilde ⊣ Γ` adjunction to
`FGModuleCat R` and `Coh (Spec R)`. The restricted unit is inherited from Mathlib's tilde
comparison, while the restricted counit is an isomorphism by the affine comparison theorem
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`. Thus the restricted adjunction is an
equivalence.

The global-sections functor `Coh.affineGlobalSections` itself does not need noetherianity:
finite presentation already implies finite global sections on an affine scheme. The
noetherian hypothesis first appears on `FGModuleCat.affineTilde`, where it upgrades a finite
module to a finitely presented module, and consequently on the adjunction and equivalence.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA) — quasi-coherent modules on
  an affine scheme
-/

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- **`M^~` is of finite presentation when `M` is.**

The presentation is Mathlib's `presentationTilde`, whose generator and relation index types
are the two generating sets supplied by `Module.FinitePresentation`; finiteness of the
presentation is therefore finiteness of those sets. -/
theorem isFinitePresentation_tilde (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation.{u, u, u} (tilde M) := by
  obtain ⟨s, hs, hker⟩ := (‹Module.FinitePresentation R M›).out
  rw [Submodule.fg_def] at hker
  obtain ⟨t, htfin, ht⟩ := hker
  haveI : Finite ((s : Set M) : Type u) := s.finite_toSet.to_subtype
  haveI : Finite t := htfin.to_subtype
  -- The explicit universes are load-bearing; see the module docstring.
  haveI : Presentation.IsFinite.{u, u, u} (presentationTilde M (s : Set M) hs t ht) := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_⟩
      exact inferInstanceAs (Finite ((s : Set M) : Type u))
    · refine ⟨?_⟩
      exact inferInstanceAs (Finite t)
  exact IsFinitePresentation.of_presentation.{u, u, u} (presentationTilde M (s : Set M) hs t ht)

/-- **`M^~` is coherent when `M` is finitely presented.**

This is `isFinitePresentation_tilde` phrased through `Scheme.Modules.IsCoherent`, which is
the predicate `Coh (Spec R)` is carved out of. -/
theorem isCoherent_tilde (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Scheme.Modules.IsCoherent (Spec R) (tilde M) :=
  isFinitePresentation_tilde M

/-- Over a noetherian ring, `M^~` is coherent as soon as `M` is finitely generated.

`Module.finitePresentation_of_finite` is where `IsNoetherianRing` earns its place: finite
generation alone is not enough in general, because the relations need not be finitely
generated. -/
theorem isCoherent_tilde_of_finite [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : Scheme.Modules.IsCoherent (Spec R) (tilde M) :=
  haveI := Module.finitePresentation_of_finite (R := R) (M := M)
  isCoherent_tilde M

/-- A quasi-coherent finite-type module sheaf on an affine noetherian scheme has finitely
generated global sections. The underlying finite-generation theorem does not need the
noetherian hypothesis; it is retained here because this is the public corollary consumed by the
noetherian affine equivalence. -/
theorem moduleFinite_globalSections_of_isFiniteType [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : SheafOfModules.IsFiniteType.{u, u, u} M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) :=
  Scheme.Modules.moduleFinite_globalSections_of_isFiniteType M hM

/-- A coherent module sheaf on an affine noetherian scheme has finitely presented global
sections. -/
theorem moduleFinitePresentation_globalSections_of_isCoherent [IsNoetherianRing R]
    (M : (Spec R).Modules) (hM : Scheme.Modules.IsCoherent (Spec R) M) :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  have hM' : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    Scheme.Modules.moduleFinite_globalSections M hM'
  exact Module.finitePresentation_of_finite R (moduleSpecΓFunctor.obj M)

/-- Global sections restrict from coherent sheaves on `Spec R` to finitely generated
`R`-modules. No noetherian hypothesis is needed in this direction. -/
noncomputable def Coh.affineGlobalSections (R : CommRingCat.{u}) :
    Coh (Spec R) ⥤ FGModuleCat.{u} R :=
  (ModuleCat.isFG R).lift
    (Coh.ι (Spec R) ⋙ moduleSpecΓFunctor)
    fun M => by
      have hM : SheafOfModules.IsFinitePresentation.{u, u, u} M.obj := M.property
      exact Scheme.Modules.moduleFinite_globalSections M.obj hM

/-- Over a noetherian ring, tilde restricts from finitely generated modules to coherent
sheaves on the affine spectrum. -/
noncomputable def FGModuleCat.affineTilde [IsNoetherianRing R] :
    FGModuleCat.{u} R ⥤ Coh (Spec R) :=
  (Scheme.coherent (Spec R)).lift
    ((ModuleCat.isFG R).ι ⋙ tilde.functor R)
    fun M => by
      letI : Module.Finite R M.obj := M.property
      exact isCoherent_tilde_of_finite M.obj

private noncomputable def affineTildeCompιIso [IsNoetherianRing R] :
    (ModuleCat.isFG R).ι ⋙ tilde.functor R ≅
      FGModuleCat.affineTilde (R := R) ⋙ (Scheme.coherent (Spec R)).ι :=
  .refl _

private noncomputable def affineGlobalSectionsCompιIso :
    (Scheme.coherent (Spec R)).ι ⋙ moduleSpecΓFunctor ≅
      Coh.affineGlobalSections R ⋙ (ModuleCat.isFG R).ι :=
  .refl _

/-- Mathlib's tilde-global-sections adjunction restricted to finitely generated modules and
coherent sheaves on an affine noetherian scheme. -/
noncomputable def Coh.affineAdjunction [IsNoetherianRing R] :
    FGModuleCat.affineTilde (R := R) ⊣ Coh.affineGlobalSections R :=
  (tilde.adjunction (R := R)).restrictFullyFaithful
    (ModuleCat.isFG R).fullyFaithfulι
    (Scheme.coherent (Spec R)).fullyFaithfulι
    affineTildeCompιIso affineGlobalSectionsCompιIso

private theorem affineAdjunction_unit_isIso [IsNoetherianRing R]
    (M : FGModuleCat.{u} R) :
    IsIso ((Coh.affineAdjunction (R := R)).unit.app M) := by
  let hUnit : IsIso ((tilde.adjunction (R := R)).unit.app
      ((ModuleCat.isFG R).ι.obj M)) := by
    dsimp [tilde.adjunction]
    exact NatIso.hom_app_isIso (tilde.toTildeΓNatIso (R := R)) M.obj
  let hMap : IsIso (moduleSpecΓFunctor.map (affineTildeCompιIso.hom.app M)) :=
    Functor.map_isIso moduleSpecΓFunctor (affineTildeCompιIso.hom.app M)
  let hComm₂ : IsIso (affineGlobalSectionsCompιIso.hom.app
      (FGModuleCat.affineTilde (R := R).obj M)) :=
    NatIso.hom_app_isIso affineGlobalSectionsCompιIso _
  haveI : IsIso ((ModuleCat.isFG R).ι.map
      ((Coh.affineAdjunction (R := R)).unit.app M)) := by
    have h :=
      (tilde.adjunction (R := R)).map_restrictFullyFaithful_unit_app
        (ModuleCat.isFG R).fullyFaithfulι
        (Scheme.coherent (Spec R)).fullyFaithfulι
        affineTildeCompιIso affineGlobalSectionsCompιIso M
    exact h.symm ▸ IsIso.comp_isIso' hUnit (IsIso.comp_isIso' hMap hComm₂)
  exact (ModuleCat.isFG R).fullyFaithfulι.isIso_of_isIso_map _

private theorem affineAdjunction_counit_isIso [IsNoetherianRing R]
    (M : Coh (Spec R)) :
    IsIso ((Coh.affineAdjunction (R := R)).counit.app M) := by
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} M.obj := M.property
  let hCounit : IsIso ((tilde.adjunction (R := R)).counit.app
      ((Scheme.coherent (Spec R)).ι.obj M)) := by
    dsimp [tilde.adjunction, Scheme.Modules.fromTildeΓNatTrans]
    exact Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M.obj
  let hComm₁ : IsIso (affineTildeCompιIso.inv.app
      ((Coh.affineGlobalSections R).obj M)) :=
    NatIso.inv_app_isIso affineTildeCompιIso _
  let hMap : IsIso ((tilde.functor R).map
      (affineGlobalSectionsCompιIso.inv.app M)) :=
    Functor.map_isIso (tilde.functor R) (affineGlobalSectionsCompιIso.inv.app M)
  haveI : IsIso ((Scheme.coherent (Spec R)).ι.map
      ((Coh.affineAdjunction (R := R)).counit.app M)) := by
    have h :=
      (tilde.adjunction (R := R)).map_restrictFullyFaithful_counit_app
        (ModuleCat.isFG R).fullyFaithfulι
        (Scheme.coherent (Spec R)).fullyFaithfulι
        affineTildeCompιIso affineGlobalSectionsCompιIso M
    exact h.symm ▸ IsIso.comp_isIso' hComm₁ (IsIso.comp_isIso' hMap hCounit)
  exact (Scheme.coherent (Spec R)).fullyFaithfulι.isIso_of_isIso_map _

/-- For a noetherian ring `R`, coherent sheaves on `Spec R` are equivalent to finitely
generated `R`-modules. The forward functor is global sections and the inverse is tilde. -/
noncomputable def Coh.affineEquivalence [IsNoetherianRing R] :
    Coh (Spec R) ≌ FGModuleCat.{u} R := by
  letI (M : FGModuleCat.{u} R) := affineAdjunction_unit_isIso M
  letI (M : Coh (Spec R)) := affineAdjunction_counit_isIso M
  exact (Coh.affineAdjunction (R := R)).toEquivalence.symm

@[simp]
theorem Coh.affineEquivalence_functor [IsNoetherianRing R] :
    (Coh.affineEquivalence (R := R)).functor = Coh.affineGlobalSections R :=
  rfl

@[simp]
theorem Coh.affineEquivalence_inverse [IsNoetherianRing R] :
    (Coh.affineEquivalence (R := R)).inverse = FGModuleCat.affineTilde (R := R) :=
  rfl

end AlgebraicGeometry
