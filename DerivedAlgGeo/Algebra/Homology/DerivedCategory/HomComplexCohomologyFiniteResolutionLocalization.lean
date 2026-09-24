/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.ProjectiveResolution
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization

/-!
# Degree-zero Hom localization from a finite-term resolution

For a finite module over a noetherian commutative ring, choose the finite-term
projective resolution supplied by `ModuleCat.exists_finite_projectiveResolution`.
Against a bounded-below module complex, the degree-zero derived-category Hom
map of this *chosen cochain resolution* is a module localization. The source
resolution is strictly bounded above by zero and may have an infinite negative
tail. This does not identify the map with localization of derived Homs from the
degree-zero complex of the original module; that requires a separate
quasi-isomorphism comparison.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M]
  (S : Submonoid R) (Q : CochainComplex (ModuleCat.{u} R) ℤ)

private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

attribute [local instance] sourceDerivedCategory targetDerivedCategory

/-- A finite module admits a finite-term projective cochain resolution whose
degree-zero derived-category Hom map into a bounded-below target localizes.
The `ProjectiveResolution` witness also carries the augmentation to `M`;
no finite length or derived-Hom comparison for `M[0]` is asserted. -/
theorem exists_finite_projectiveResolution_derivedHomLocalized (c : ℤ)
    [Q.IsStrictlyGE c] :
    ∃ P : ProjectiveResolution M,
      (∀ i : ℤ, Module.Finite R (P.cochainComplex.X i)) ∧
      P.cochainComplex.IsStrictlyLE 0 ∧
      (∀ i : ℤ, Projective (P.cochainComplex.X i)) ∧
      QuasiIso P.π' ∧
      IsLocalizedModule S (derivedHomLocalizedMap S P.cochainComplex Q) := by
  obtain ⟨P, -, hfinite⟩ := ModuleCat.exists_finite_projectiveResolution M
  letI (i : ℤ) : Module.Finite R (P.cochainComplex.X i) := hfinite i
  letI (i : {p : ℤ // p ∈ Finset.Icc (c - 1) 0}) :
      Module.FinitePresentation R (P.cochainComplex.X i.1) :=
    Module.finitePresentation_of_finite R _
  refine ⟨P, hfinite, inferInstance, (fun _ => inferInstance), inferInstance, ?_⟩
  exact derivedHomLocalizedMap_isLocalized_of_bounded_projective
    S P.cochainComplex Q c 0

end

end CochainComplex.HomComplex
