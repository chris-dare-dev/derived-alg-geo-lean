/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteResolutionLocalization

/-! Axiom audit and direct-import client for finite-resolution Hom localization. -/

#print axioms CochainComplex.HomComplex.exists_finite_projectiveResolution_derivedHomLocalized

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
    ∃ P : ProjectiveResolution M,
      (∀ i : ℤ, Module.Finite R (P.cochainComplex.X i)) ∧
      P.cochainComplex.IsStrictlyLE 0 ∧
      (∀ i : ℤ, Projective (P.cochainComplex.X i)) ∧
      QuasiIso P.π' ∧
      IsLocalizedModule S
        (CochainComplex.HomComplex.derivedHomLocalizedMap S P.cochainComplex Q) :=
  CochainComplex.HomComplex.exists_finite_projectiveResolution_derivedHomLocalized
    M S Q c

end
