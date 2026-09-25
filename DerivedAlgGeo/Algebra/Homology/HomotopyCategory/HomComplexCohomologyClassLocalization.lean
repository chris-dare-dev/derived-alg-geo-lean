/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyNaturality
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyLocalization

/-!
# Degree-zero Hom-complex cohomology classes under localization

The class map induced by degreewise localization agrees, through the linear
class/quotient equivalences, with the localized map on the concrete degree-zero
kernel/range quotient. Exactness of module localization then makes this class
map a localization map. A half-bounded specialization needs finite presentation
only for source terms in `Finset.Icc (c - 1) b`.

This does not identify derived-category Homs or establish geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localized (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private theorem cochainLocalizedMap_square (i j : ℤ) :
    (δ_hom R (localized S P) (localized S Q) i j).comp
      (cochainLocalizedMap P Q i S) =
    (cochainLocalizedMap P Q j S).comp (δ_hom R P Q i j) := by
  apply LinearMap.ext
  intro γ
  change δ i j ((cochainLocalizedMap P Q i S) γ) =
    (cochainLocalizedMap P Q j S) (δ i j γ)
  exact (cochainLocalizedMap_delta P Q i S j γ).symm

/-- The degree-zero map on Hom-complex cohomology classes induced by
degreewise localization of both complexes. -/
def cohomologyClassLocalizedMap :
    CohomologyClass P Q 0 →ₗ[R]
      CohomologyClass (localized S P) (localized S Q) 0 :=
  cohomologyClassMapLinear P Q 0 (localized S P) (localized S Q)
    (cochainLocalizedMap P Q (0 - 1) S)
    (cochainLocalizedMap P Q 0 S)
    (cochainLocalizedMap P Q (0 + 1) S)
    (cochainLocalizedMap_square P Q S (0 - 1) 0)
    (cochainLocalizedMap_square P Q S 0 (0 + 1))

/-- The generic concrete quotient map is the degree-zero map constructed
using exact localization. Both maps send a cycle class to its localized cycle. -/
theorem concreteCohomologyMap_eq_localized
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    concreteCohomologyMap (R := R) P Q 0 (localized S P) (localized S Q)
      (cochainLocalizedMap P Q (0 - 1) S)
      (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q (0 + 1) S)
      (cochainLocalizedMap_square P Q S (0 - 1) 0)
      (cochainLocalizedMap_square P Q S 0 (0 + 1)) =
    concreteCohomologyLocalizedMap P Q S hprev hcur hnext := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    rw [concreteCohomologyMap_mk]
    have heq : (0 : ℤ) + 1 = 1 := by omega
    let z' : (δ_hom R P Q 0 1).ker := heq ▸ z
    have h := concreteCohomologyLocalizedMap_mk P Q S hprev hcur hnext z'
    convert h.symm using 1 <;> cases heq <;> rfl

/-- The degree-zero class map commutes with the concrete localization map
through the source and target linear class/quotient equivalences. -/
theorem cohomologyClassLocalizedMap_naturality
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    (cohomologyClassLocalizedMap P Q S).comp
      (cohomologyClassLinearEquiv (R := R) P Q 0).toLinearMap =
    (cohomologyClassLinearEquiv (R := R)
      (localized S P) (localized S Q) 0).toLinearMap.comp
      (concreteCohomologyLocalizedMap P Q S hprev hcur hnext) := by
  calc
    (cohomologyClassLocalizedMap P Q S).comp
        (cohomologyClassLinearEquiv (R := R) P Q 0).toLinearMap =
      (cohomologyClassLinearEquiv (R := R)
        (localized S P) (localized S Q) 0).toLinearMap.comp
        (concreteCohomologyMap (R := R) P Q 0
          (localized S P) (localized S Q)
          (cochainLocalizedMap P Q (0 - 1) S)
          (cochainLocalizedMap P Q 0 S)
          (cochainLocalizedMap P Q (0 + 1) S)
          (cochainLocalizedMap_square P Q S (0 - 1) 0)
          (cochainLocalizedMap_square P Q S 0 (0 + 1))) :=
      cohomologyClassLinearEquiv_naturality P Q 0
        (localized S P) (localized S Q)
        (cochainLocalizedMap P Q (0 - 1) S)
        (cochainLocalizedMap P Q 0 S)
        (cochainLocalizedMap P Q (0 + 1) S)
        (cochainLocalizedMap_square P Q S (0 - 1) 0)
        (cochainLocalizedMap_square P Q S 0 (0 + 1))
    _ = _ := by
      rw [concreteCohomologyMap_eq_localized P Q S hprev hcur hnext]
      rfl

/-- Localization of the three contributing cochain degrees makes the induced
degree-zero map on `CohomologyClass` a module localization. -/
theorem cohomologyClassLocalizedMap_isLocalized
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    IsLocalizedModule S (cohomologyClassLocalizedMap P Q S) := by
  let e₀ := cohomologyClassLinearEquiv (R := R) P Q 0
  let e₁ := cohomologyClassLinearEquiv (R := R)
    (localized S P) (localized S Q) 0
  let f := concreteCohomologyLocalizedMap P Q S hprev hcur hnext
  letI : IsLocalizedModule S f :=
    concreteCohomologyLocalizedMap_isLocalized P Q S hprev hcur hnext
  haveI : IsLocalizedModule S (e₁.toLinearMap.comp f) :=
    IsLocalizedModule.of_linearEquiv S f e₁
  haveI : IsLocalizedModule S
      ((cohomologyClassLocalizedMap P Q S).comp e₀.toLinearMap) := by
    rw [cohomologyClassLocalizedMap_naturality P Q S hprev hcur hnext]
    change IsLocalizedModule S (e₁.toLinearMap.comp f)
    infer_instance
  haveI : IsLocalizedModule S
      (((cohomologyClassLocalizedMap P Q S).comp e₀.toLinearMap).comp
        e₀.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S _ e₀.symm
  convert this using 1
  apply LinearMap.ext
  intro z
  change (cohomologyClassLocalizedMap P Q S) z =
    (cohomologyClassLocalizedMap P Q S) (e₀ (e₀.symm z))
  rw [e₀.apply_symm_apply]

/-- If the source is strictly bounded above by `b`, the target is strictly
bounded below by `c`, and the source terms in `Icc (c - 1) b` are finitely
presented, the degree-zero class map is a localization. -/
theorem cohomologyClassLocalizedMap_isLocalized_of_bounded_above_below
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S (cohomologyClassLocalizedMap P Q S) := by
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
  exact cohomologyClassLocalizedMap_isLocalized P Q S
    (cochainLocalizedMap_isLocalized_of_bounded_above_below P Q (-1) S c b)
    (cochainLocalizedMap_isLocalized_of_bounded_above_below P Q 0 S c b)
    (cochainLocalizedMap_isLocalized_of_bounded_above_below P Q 1 S c b)

end

end CochainComplex.HomComplex
