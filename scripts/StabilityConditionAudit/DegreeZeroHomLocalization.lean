/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyDegreeZeroLocalization

/-! Axiom audit and direct-import client for the degree-zero module theorem. -/

#print axioms CochainComplex.HomComplex.degreeZero_derivedHomLocalizedMap_isLocalized

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M]
  (S : Submonoid R) (Q : CochainComplex (ModuleCat.{u} R) ℤ)

local instance : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

example (c : ℤ) [Q.IsStrictlyGE c] :
    IsLocalizedModule S
      (CochainComplex.HomComplex.derivedHomLocalizedMap S
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) Q) :=
  CochainComplex.HomComplex.degreeZero_derivedHomLocalizedMap_isLocalized S M Q c

end
