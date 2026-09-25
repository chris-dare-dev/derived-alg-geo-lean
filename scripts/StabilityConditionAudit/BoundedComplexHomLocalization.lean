/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyBoundedComplexLocalization

/-! Axiom audit and direct-import client for bounded-complex Hom localization. -/

#print axioms CochainComplex.HomComplex.derivedHomLocalizedMap_precomp
#print axioms CochainComplex.HomComplex.derivedHomLocalizedMap_isLocalized_of_bounded_finite

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (S : Submonoid R) (K Q : CochainComplex (ModuleCat.{u} R) ℤ)

local instance : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

example (b c : ℤ) [K.IsStrictlyLE b] [Q.IsStrictlyGE c]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    IsLocalizedModule S (CochainComplex.HomComplex.derivedHomLocalizedMap S K Q) :=
  CochainComplex.HomComplex.derivedHomLocalizedMap_isLocalized_of_bounded_finite
    S K Q b c hfinite

end
