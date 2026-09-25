/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyClassLocalization

/-!
# Canonical integer localization of degree-zero Hom-complex cohomology classes

The generic class-localization map carries a scoped, transported `R`-module
structure. At `R = ℤ`, the same underlying additive map is relinearized with
the ordinary integer action, and remains a module localization. This is a
statement about Hom-complex cohomology, not derived-category Homs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u v

noncomputable section

private theorem isLocalizedModule_toIntLinearMap
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [mM : Module ℤ M] [mN : Module ℤ N]
    (S : Submonoid ℤ) (f : M →ₗ[ℤ] N)
    (hf : IsLocalizedModule S f) :
    @IsLocalizedModule ℤ inferInstance M N inferInstance inferInstance
      (AddCommGroup.toIntModule M) (AddCommGroup.toIntModule N)
      S f.toAddMonoidHom.toIntLinearMap := by
  have hM : mM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  have hN : mN = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  cases hM
  cases hN
  have heq : f.toAddMonoidHom.toIntLinearMap = f := by
    ext x
    rfl
  rw [heq]
  exact hf

private abbrev localized (S : Submonoid ℤ)
    (E : CochainComplex (ModuleCat ℤ) ℤ) :=
  ((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj E

/-- Under half-boundedness and finite presentation on `Icc (c - 1) b`, the
ordinary integer-linear class map is a module localization. -/
theorem cohomologyClassLocalizedIntMap_isLocalized
    (P Q : CochainComplex (ModuleCat ℤ) ℤ) (S : Submonoid ℤ)
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation ℤ (P.X i.1)] :
    IsLocalizedModule S
      ((cohomologyClassLocalizedMap P Q S).toAddMonoidHom.toIntLinearMap) := by
  letI : Linear ℤ (ModuleCat ℤ) := ModuleCat.Algebra.instLinear
  letI : Linear ℤ (ModuleCat (Localization S)) := ModuleCat.Algebra.instLinear
  exact @isLocalizedModule_toIntLinearMap
    (CohomologyClass P Q 0)
    (CohomologyClass (localized S P) (localized S Q) 0)
    inferInstance inferInstance
    (cohomologyClassModule P Q 0)
    (cohomologyClassModule (localized S P) (localized S Q) 0)
    S (cohomologyClassLocalizedMap P Q S)
    (cohomologyClassLocalizedMap_isLocalized_of_bounded_above_below P Q S c b)

end

end CochainComplex.HomComplex
