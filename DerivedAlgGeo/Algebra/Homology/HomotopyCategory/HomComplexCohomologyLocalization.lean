/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexLocalization
import DerivedAlgGeo.Algebra.Module.Localization.Cohomology

/-!
# Degree-zero cohomology of a localized Hom complex

The map on the concrete kernel/range quotient of the degree-zero Hom-complex
cohomology is a module localization when its three contributing cochain maps
are localizations. A bounded-above source, bounded-below target, and finite
presentation in the contributing source degrees supply those hypotheses.

This is not a derived-Hom or geometric base-change theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localized (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private theorem delta_comp_delta
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    (E F : CochainComplex C ℤ) :
    (δ_hom R E F 0 1).comp (δ_hom R E F (-1) 0) = 0 := by
  apply LinearMap.ext
  intro γ
  change δ 0 1 (δ (-1) 0 γ) = 0
  exact δ_δ (-1) 0 1 γ

private theorem localized_delta_eq_map (i j : ℤ)
    [IsLocalizedModule S (cochainLocalizedMap P Q i S)]
    [IsLocalizedModule S (cochainLocalizedMap P Q j S)] :
    (IsLocalizedModule.map S (cochainLocalizedMap P Q i S)
      (cochainLocalizedMap P Q j S)) (δ_hom R P Q i j) =
      δ_hom R (localized S P) (localized S Q) i j := by
  apply IsLocalizedModule.linearMap_ext S (cochainLocalizedMap P Q i S)
    (cochainLocalizedMap P Q j S)
  apply LinearMap.ext
  intro γ
  simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  change (cochainLocalizedMap P Q j S) (δ i j γ) =
    δ i j ((cochainLocalizedMap P Q i S) γ)
  exact cochainLocalizedMap_delta P Q i S j γ

/-- Degree-zero cohomology of the Hom complex as cycles modulo boundaries. -/
abbrev concreteCohomology
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    (E F : CochainComplex C ℤ) : Type w :=
  (δ_hom R E F 0 1).ker ⧸
    (IsLocalizedModule.boundaryToCycles
      (δ_hom R E F (-1) 0) (δ_hom R E F 0 1)
      (delta_comp_delta E F)).range

private def cohomologyEquivOfEq
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (d₀ d₀' : M₀ →ₗ[R] M₁) (d₁ d₁' : M₁ →ₗ[R] M₂)
    (hd : d₁.comp d₀ = 0) (hd' : d₁'.comp d₀' = 0)
    (h₀ : d₀ = d₀') (h₁ : d₁ = d₁') :
    (d₁.ker ⧸ (IsLocalizedModule.boundaryToCycles d₀ d₁ hd).range) ≃ₗ[R]
      (d₁'.ker ⧸ (IsLocalizedModule.boundaryToCycles d₀' d₁' hd').range) := by
  subst d₀'
  subst d₁'
  exact LinearEquiv.refl R _

private def localizedCohomologyEquiv
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    ((IsLocalizedModule.localizedDifferential S
        (cochainLocalizedMap P Q 0 S) (cochainLocalizedMap P Q 1 S)
        (δ_hom R P Q 0 1)).ker ⧸
      (IsLocalizedModule.localizedBoundaryToCycles S
        (cochainLocalizedMap P Q (-1) S)
        (cochainLocalizedMap P Q 0 S)
        (cochainLocalizedMap P Q 1 S)
        (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
        (delta_comp_delta P Q)).range) ≃ₗ[R]
      concreteCohomology (R := R) (localized S P) (localized S Q) := by
  letI := hprev
  letI := hcur
  letI := hnext
  have h₀ := localized_delta_eq_map P Q S (-1) 0
  have h₁ := localized_delta_eq_map P Q S 0 1
  have hd : ((IsLocalizedModule.map S (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)) (δ_hom R P Q 0 1)).comp
      ((IsLocalizedModule.map S (cochainLocalizedMap P Q (-1) S)
        (cochainLocalizedMap P Q 0 S)) (δ_hom R P Q (-1) 0)) = 0 := by
    rw [h₀, h₁]
    exact delta_comp_delta (localized S P) (localized S Q)
  exact cohomologyEquivOfEq
    ((IsLocalizedModule.map S (cochainLocalizedMap P Q (-1) S)
      (cochainLocalizedMap P Q 0 S)) (δ_hom R P Q (-1) 0))
    (δ_hom R (localized S P) (localized S Q) (-1) 0)
    ((IsLocalizedModule.map S (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)) (δ_hom R P Q 0 1))
    (δ_hom R (localized S P) (localized S Q) 0 1)
    hd (delta_comp_delta (localized S P) (localized S Q)) h₀ h₁

/-- The canonical map on concrete degree-zero Hom-complex cohomology induced
by termwise module localization. Its codomain uses the actual differentials
of the localized Hom complex. -/
def concreteCohomologyLocalizedMap
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    concreteCohomology (R := R) P Q →ₗ[R]
      concreteCohomology (R := R) (localized S P) (localized S Q) := by
  letI := hprev
  letI := hcur
  letI := hnext
  exact (localizedCohomologyEquiv P Q S hprev hcur hnext).toLinearMap ∘ₗ
    IsLocalizedModule.cohomologyMap S
      (cochainLocalizedMap P Q (-1) S)
      (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)
      (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
      (delta_comp_delta P Q)

/-- Three localized cochain degrees give localization on their degree-zero
kernel/range quotient. -/
theorem concreteCohomologyLocalizedMap_isLocalized
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    IsLocalizedModule S
      (concreteCohomologyLocalizedMap P Q S hprev hcur hnext) := by
  letI := hprev
  letI := hcur
  letI := hnext
  letI : IsLocalizedModule S
      (IsLocalizedModule.cohomologyMap S
        (cochainLocalizedMap P Q (-1) S)
        (cochainLocalizedMap P Q 0 S)
        (cochainLocalizedMap P Q 1 S)
        (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
        (delta_comp_delta P Q)) :=
    IsLocalizedModule.cohomologyMap_isLocalized S
      (cochainLocalizedMap P Q (-1) S)
      (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)
      (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
      (delta_comp_delta P Q)
  exact IsLocalizedModule.of_linearEquiv S
    (IsLocalizedModule.cohomologyMap S
      (cochainLocalizedMap P Q (-1) S)
      (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)
      (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
      (delta_comp_delta P Q))
    (localizedCohomologyEquiv P Q S hprev hcur hnext)

/-- The concrete degree-zero map under half-boundedness and finite presentation
in its three contributing degrees. -/
def concreteCohomologyLocalizedMapOfBoundedAboveBelow
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation R (P.X i.1)] :
    concreteCohomology (R := R) P Q →ₗ[R]
      concreteCohomology (R := R) (localized S P) (localized S Q) := by
  letI (i : {p : ℤ // p ∈ Finset.Icc (c - (-1)) b}) :
      Module.FinitePresentation R (P.X i.1) := by
    have hi : i.1 ∈ Finset.Icc (c - 1) b := by
      have hii := Finset.mem_Icc.mp i.2
      apply Finset.mem_Icc.mpr
      omega
    exact inferInstanceAs (Module.FinitePresentation R
      (P.X (⟨i.1, hi⟩ : {p : ℤ // p ∈ Finset.Icc (c - 1) b}).1))
  letI (i : {p : ℤ // p ∈ Finset.Icc (c - 0) b}) :
      Module.FinitePresentation R (P.X i.1) := by
    have hi : i.1 ∈ Finset.Icc (c - 1) b := by
      have hii := Finset.mem_Icc.mp i.2
      apply Finset.mem_Icc.mpr
      omega
    exact inferInstanceAs (Module.FinitePresentation R
      (P.X (⟨i.1, hi⟩ : {p : ℤ // p ∈ Finset.Icc (c - 1) b}).1))
  letI : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S) :=
    cochainLocalizedMap_isLocalized_of_bounded_above_below P Q (-1) S c b
  letI : IsLocalizedModule S (cochainLocalizedMap P Q 0 S) :=
    cochainLocalizedMap_isLocalized_of_bounded_above_below P Q 0 S c b
  letI : IsLocalizedModule S (cochainLocalizedMap P Q 1 S) :=
    cochainLocalizedMap_isLocalized_of_bounded_above_below P Q 1 S c b
  exact concreteCohomologyLocalizedMap P Q S
    (inferInstance : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (inferInstance : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (inferInstance : IsLocalizedModule S (cochainLocalizedMap P Q 1 S))

/-- A strictly bounded-above source and strictly bounded-below target need
finite presentation only on `Icc (c - 1) b` for degree-zero cohomology. -/
theorem concreteCohomologyLocalizedMapOfBoundedAboveBelow_isLocalized
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S
      (concreteCohomologyLocalizedMapOfBoundedAboveBelow P Q S c b) := by
  unfold concreteCohomologyLocalizedMapOfBoundedAboveBelow
  exact concreteCohomologyLocalizedMap_isLocalized P Q S _ _ _

end

end CochainComplex.HomComplex
