/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteReplacementLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalizationNaturality

/-!
# Derived-category Hom localization from bounded-above finite complexes

For a strictly bounded-above complex of finite modules over a noetherian
commutative ring, the finite-projective replacement of 4aq has a
quasi-isomorphism to the original complex. Its image under degreewise
localization is also a quasi-isomorphism. The two induced source isomorphisms
transport localization of derived-category Hom-sets from the replacement to
the original complex, against a strictly bounded-below target.

The replacement may have an infinite negative-degree tail. This theorem is
about Hom-sets in the derived category; it does not construct an internal
derived-Hom complex, a geometric pullback or projector comparison, a heart
statement, or Theorem 5.7(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (S : Submonoid R) (K Q : CochainComplex (ModuleCat.{u} R) ℤ)

private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

attribute [local instance] sourceDerivedCategory targetDerivedCategory

/-- A strictly bounded-above complex of finite `R`-modules has a localized
derived-category Hom-set map into every strictly bounded-below complex.
There is no finiteness assumption on the target. The codomain of the map is
the Hom-set between the degreewise localized displayed complexes. -/
theorem derivedHomLocalizedMap_isLocalized_of_bounded_finite
    (b c : ℤ) [K.IsStrictlyLE b] [Q.IsStrictlyGE c]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    IsLocalizedModule S (derivedHomLocalizedMap S K Q) := by
  obtain ⟨P, p, -, -, -, -, hπ, hP⟩ :=
    exists_finite_projective_replacement_derivedHomLocalized K Q S b c hfinite
  let F := ModuleCat.localizedModuleFunctor.{u} S
  let f : P ⟶ K := p
  letI : QuasiIso f := hπ
  haveI hIso : IsIso
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f)) := by
    rw [DerivedCategory.isIso_Qh_map_iff,
      HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e := asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f))
  haveI hLocalizedQuasiIso : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    inferInstance
  haveI hLocalizedIso : IsIso
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f))) := by
    rw [DerivedCategory.isIso_Qh_map_iff,
      HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let eLocalized := asIso
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map f)))
  let eSource := Linear.homCongr R e.symm
    (Iso.refl (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
  let eTarget := Linear.homCongr R eLocalized.symm
    (Iso.refl (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q))))
  let mapP := derivedHomLocalizedMap S P Q
  let mapK := derivedHomLocalizedMap S K Q
  have hcomm (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) :
      mapP (eSource g) = eTarget (mapK g) := by
    simp only [eSource, eTarget, Linear.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Iso.symm_inv]
    change derivedHomLocalizedMap S P Q
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) ≫ g) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((F.mapHomologicalComplex (.up ℤ)).map f)) ≫
        derivedHomLocalizedMap S K Q g
    exact derivedHomLocalizedMap_precomp S P K Q f g
  letI : IsLocalizedModule S mapP := hP
  letI : IsLocalizedModule S (mapP.comp eSource.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S mapP eSource
  haveI : IsLocalizedModule S
      (eTarget.symm.toLinearMap.comp (mapP.comp eSource.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv S _ eTarget.symm
  change IsLocalizedModule S mapK
  convert this using 1
  apply LinearMap.ext
  intro g
  change mapK g = eTarget.symm (mapP (eSource g))
  rw [hcomm]
  exact (eTarget.symm_apply_apply _).symm

end

end CochainComplex.HomComplex
