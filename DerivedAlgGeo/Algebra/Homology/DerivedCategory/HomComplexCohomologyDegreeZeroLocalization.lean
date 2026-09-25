/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteResolutionLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalizationNaturality

/-!
# Degree-zero derived-category Hom localization for a finite module

The finite-term projective resolution of a finite module over a noetherian
commutative ring gives localization of derived-category Hom-sets from that
resolution. Its quasi-isomorphism to the degree-zero complex of the module,
and the corresponding localized quasi-isomorphism, transport this statement
to the degree-zero complex itself. The target is still the degreewise
localization of that complex; no comparison with a single complex of the
localized module is asserted here.

This concerns Hom-sets in the derived category, not an internal derived-Hom
complex. The target complex is bounded below; the chosen resolution may have
an infinite negative tail. No assertion about arbitrary bounded complexes,
geometric pullback, hearts, or Theorem 5.7(2) follows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] (S : Submonoid R)

private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

attribute [local instance] sourceDerivedCategory targetDerivedCategory

variable [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M]
  (Q : CochainComplex (ModuleCat.{u} R) ℤ)

/-- For a finite module over a noetherian ring, localization of the degree-zero
derived-category Hom-set from its degree-zero complex into any bounded-below
module complex is a localization of `R`-modules. The codomain uses degreewise
localization of the displayed complexes; no single-complex identification or
internal derived-Hom base change is part of this statement. -/
theorem degreeZero_derivedHomLocalizedMap_isLocalized (c : ℤ) [Q.IsStrictlyGE c] :
    IsLocalizedModule S
      (derivedHomLocalizedMap S ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
        Q) := by
  obtain ⟨P, -, -, -, hπ, hP⟩ :=
    exists_finite_projectiveResolution_derivedHomLocalized M S Q c
  let X := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  let F := ModuleCat.localizedModuleFunctor.{u} S
  let f : P.cochainComplex ⟶ X := P.π'
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
  let mapP := derivedHomLocalizedMap S P.cochainComplex Q
  let mapM := derivedHomLocalizedMap S X Q
  have hcomm (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) :
      mapP (eSource g) = eTarget (mapM g) := by
    simp only [eSource, eTarget, Linear.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Iso.symm_inv]
    change derivedHomLocalizedMap S P.cochainComplex Q
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) ≫ g) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((F.mapHomologicalComplex (.up ℤ)).map f)) ≫
        derivedHomLocalizedMap S X Q g
    exact derivedHomLocalizedMap_precomp S P.cochainComplex X Q f g
  letI : IsLocalizedModule S mapP := hP
  letI : IsLocalizedModule S (mapP.comp eSource.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S mapP eSource
  haveI : IsLocalizedModule S
      (eTarget.symm.toLinearMap.comp (mapP.comp eSource.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv S _ eTarget.symm
  change IsLocalizedModule S mapM
  convert this using 1
  apply LinearMap.ext
  intro g
  change mapM g = eTarget.symm (mapP (eSource g))
  rw [hcomm]
  exact (eTarget.symm_apply_apply _).symm

end

end CochainComplex.HomComplex
