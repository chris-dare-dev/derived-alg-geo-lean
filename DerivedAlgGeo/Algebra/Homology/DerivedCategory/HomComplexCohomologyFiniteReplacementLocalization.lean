/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.CochainComplexFiniteProjectiveResolution
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization

/-!
# Derived-category Hom localization from a finite-projective replacement

Over a noetherian commutative ring, a strictly bounded-above complex of finite
modules has a strictly bounded-above replacement with finite projective terms.
For a bounded-below target, the derived-category Hom map out of that chosen
replacement is a module localization. The quasi-isomorphism to the original
complex is retained as part of the witness, but this theorem does not assert
localization for the Hom map out of the original complex.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (K Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

attribute [local instance] sourceDerivedCategory targetDerivedCategory

/-- A bounded-above complex of finite modules has a finite-projective,
K-projective replacement whose derived-category Hom map into a bounded-below
complex localizes. The replacement may have an infinite negative-degree tail;
no localization assertion is made for the Hom map out of `K` itself. -/
theorem exists_finite_projective_replacement_derivedHomLocalized
    (b c : ℤ) [K.IsStrictlyLE b] [Q.IsStrictlyGE c]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      (∀ i : ℤ, Projective (P.X i)) ∧ P.IsKProjective ∧
      QuasiIso p ∧ IsLocalizedModule S (derivedHomLocalizedMap S P Q) := by
  obtain ⟨P, p, hBound, hFinite, hProjective, hQuasiIso⟩ :=
    ModuleCat.exists_finite_projective_replacement K b hfinite
  letI : P.IsStrictlyLE b := hBound
  letI (i : ℤ) : Module.Finite R (P.X i) := hFinite i
  letI (i : ℤ) : Projective (P.X i) := hProjective i
  letI (i : {p : ℤ // p ∈ Finset.Icc (c - 1) b}) :
      Module.FinitePresentation R (P.X i.1) :=
    Module.finitePresentation_of_finite R _
  refine ⟨P, p, hBound, hFinite, hProjective,
    CochainComplex.isKProjective_of_projective P b, hQuasiIso, ?_⟩
  exact derivedHomLocalizedMap_isLocalized_of_bounded_projective S P Q c b

end

end CochainComplex.HomComplex
