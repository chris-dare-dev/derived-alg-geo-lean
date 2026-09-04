/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.Affine
import DerivedAlgGeo.Topology.Sheaves.Cech.BasisComparison
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.ModuleForget

/-!
# Affine Čech-to-derived comparison on the distinguished-open basis

This file combines the relative distinguished-open calculation with the
generic compact-basis comparison theorem.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Cohomology

/-- The compact, finite-intersection-stable basis of distinguished opens of an affine
spectrum. -/
noncomputable def affineBasicOpenBasis (R : CommRingCat.{u}) :
    CategoryTheory.Sheaf.CompactOpenBasis (Spec R) :=
  CategoryTheory.Sheaf.CompactOpenBasis.ofIsBasis
    (Set.range (@_root_.PrimeSpectrum.basicOpen R _))
    _root_.PrimeSpectrum.isBasis_basic_opens (by
    rintro U ⟨f, rfl⟩
    exact _root_.PrimeSpectrum.isCompact_basicOpen f) (by
    rintro U V ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, _root_.PrimeSpectrum.basicOpen_mul f g⟩)

/-- The whole affine spectrum is the distinguished open `D(1)`. -/
lemma top_mem_affineBasicOpenBasis (R : CommRingCat.{u}) :
    (⊤ : Opens (Spec R)) ∈ (affineBasicOpenBasis R).carrier :=
  ⟨1, _root_.PrimeSpectrum.basicOpen_one⟩

set_option maxHeartbeats 1000000 in
/-- The underlying abelian sheaf of `M̃` is Čech-acyclic on the distinguished-open basis. -/
theorem underlyingTilde_isCechAcyclicOnCompactBasis
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis (affineBasicOpenBasis R)
      ((Scheme.Modules.toSheaf (Spec R)).obj (tilde M)) := by
  intro I _ V hV U hUB hcover n hn
  obtain ⟨d, rfl⟩ := hV
  choose f hf using hUB
  have hU : U = fun i ↦ _root_.PrimeSpectrum.basicOpen (f i) :=
    funext fun i ↦ (hf i).symm
  subst U
  have hcover' : _root_.PrimeSpectrum.basicOpen d =
      ⨆ i, _root_.PrimeSpectrum.basicOpen (f i) := hcover
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  have hmod := tilde_cechComplex_exactAt_succ_of_eq_iSup f d hcover' M k
  change ((cechComplexFunctor (fun i ↦
      (_root_.PrimeSpectrum.basicOpen (f i) : Opens (_root_.PrimeSpectrum R)))).obj
    ((modulesSpecToSheaf.obj (tilde M)).presheaf ⋙
      forget₂ (ModuleCat R) AddCommGrpCat.{u})).ExactAt (k + 1)
  let hlim : HasFiniteLimits (Opens (_root_.PrimeSpectrum R)) :=
    TopologicalSpace.Opens.hasFiniteLimits (_root_.PrimeSpectrum R)
  let hprod : HasFiniteProducts (Opens (_root_.PrimeSpectrum R)) :=
    @hasFiniteProducts_of_hasFiniteLimits
      (Opens (_root_.PrimeSpectrum R)) _ hlim
  exact @cechComplex_exactAt_forget₂AddCommGrp_of_exactAt
    (Opens (_root_.PrimeSpectrum R)) _ hprod R I
    (fun i ↦ (_root_.PrimeSpectrum.basicOpen (f i) :
      Opens (_root_.PrimeSpectrum R)))
    (modulesSpecToSheaf.obj (tilde M)).presheaf (k + 1) hmod

end AlgebraicGeometry.Cohomology
