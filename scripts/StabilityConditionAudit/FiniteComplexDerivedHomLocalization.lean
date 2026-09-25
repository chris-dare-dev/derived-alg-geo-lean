/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteReplacementLocalization

/-!
Audit and direct-import client for bounded-complex finite-projective replacement
and the localization of derived-category Hom out of that replacement.
-/

#print axioms CochainComplex.HomComplex.exists_finite_projective_replacement_derivedHomLocalized

noncomputable section FiniteComplexDerivedHomLocalizationClient

open CategoryTheory
open scoped ModuleCat.Algebra CochainComplex.HomComplex

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (K Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

local instance : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

example (b c : ℤ) [K.IsStrictlyLE b] [Q.IsStrictlyGE c]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      (∀ i : ℤ, Projective (P.X i)) ∧ P.IsKProjective ∧
      QuasiIso p ∧
      IsLocalizedModule S (CochainComplex.HomComplex.derivedHomLocalizedMap S P Q) :=
  CochainComplex.HomComplex.exists_finite_projective_replacement_derivedHomLocalized
    K Q S b c hfinite

end FiniteComplexDerivedHomLocalizationClient
