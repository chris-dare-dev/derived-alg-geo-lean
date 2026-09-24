/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.CochainComplexFiniteProjectiveResolution
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
Audit and downstream clients for finite-term, bounded-above projective
replacements. These are complex-level quasi-isomorphisms, not derived-arrow
localization or bounded-below replacements.
-/

#print axioms FGModuleCat.exists_boundedAbove_projective_replacement
#print axioms ModuleCat.exists_finite_projective_replacement

noncomputable section FiniteComplexProjectiveResolutionClient

open CategoryTheory

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

example (K : CochainComplex (FGModuleCat.{u} R) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex (FGModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p :=
  FGModuleCat.exists_boundedAbove_projective_replacement K b

example (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      P.IsKProjective ∧ QuasiIso p := by
  obtain ⟨P, p, hBound, hFinite, hProj, hp⟩ :=
    ModuleCat.exists_finite_projective_replacement K b hfinite
  letI : P.IsStrictlyLE b := hBound
  letI : ∀ i : ℤ, Projective (P.X i) := hProj
  exact ⟨P, p, hBound, hFinite,
    CochainComplex.isKProjective_of_projective P b, hp⟩

end FiniteComplexProjectiveResolutionClient
