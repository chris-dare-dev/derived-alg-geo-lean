/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Projective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.FullSubcategory

/-!
# Finite-term bounded-above projective replacements

`CochainComplex.exists_boundedAbove_projective_replacement` gives strictly bounded-above
projective replacements in any abelian category with enough projectives. In
`FGModuleCat R` over a noetherian ring, finite-free epimorphisms supply enough projectives.
The `ModuleCat` version below transfers the resulting complex and quasi-isomorphism
through the finite-module inclusion. No finite lower bound or derived-arrow comparison
is asserted.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace FGModuleCat

/-- A strictly bounded-above complex of finite modules over a noetherian
commutative ring has a strictly bounded-above quasi-isomorphic complex of
projective finite modules. Its negative-degree tail may be infinite. -/
theorem exists_boundedAbove_projective_replacement {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : CochainComplex (FGModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex (FGModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p := by
  letI : EnoughProjectives (FGModuleCat.{u} R) := by
    constructor
    intro X
    obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi X
    exact ⟨{ p := FGModuleCat.of R (Fin k → R)
             projective := FGModuleCat.projective_of_finFree k
             f := q
             epi := hq }⟩
  exact CochainComplex.exists_boundedAbove_projective_replacement K b

end FGModuleCat

namespace ModuleCat

/-- A strictly bounded-above complex of finite modules over a noetherian
commutative ring has a strictly bounded-above, termwise finite-projective
replacement in `ModuleCat`. The quasi-isomorphism is an actual complex map to
the supplied complex. No strict lower bound is claimed for the replacement. -/
theorem exists_finite_projective_replacement {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p := by
  classical
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  let Kfg : CochainComplex (FGModuleCat.{u} R) ℤ :=
    HomologicalComplex.liftObjectProperty (ModuleCat.isFG R) K
      (by intro i; change Module.Finite R (K.X i); exact hfinite i)
  have hKfg : Kfg.IsStrictlyLE b := by
    apply (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff Kfg F b).mp
    change K.IsStrictlyLE b
    infer_instance
  letI : Kfg.IsStrictlyLE b := hKfg
  obtain ⟨Pfg, pfg, hPbound, hPproj, hpfg⟩ :=
    FGModuleCat.exists_boundedAbove_projective_replacement Kfg b
  have hProjective (X : FGModuleCat.{u} R) (hX : Projective X) :
      Projective (F.obj X) := by
    letI : Projective X := hX
    obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi X
    letI : Epi q := hq
    let s := Projective.factorThru (𝟙 X) q
    have hs : s ≫ q = 𝟙 X := Projective.factorThru_comp (𝟙 X) q
    have hFree : Projective (F.obj (FGModuleCat.of R (Fin k → R))) := by
      change Projective (ModuleCat.of R (Fin k → R))
      exact ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    letI : Projective (F.obj (FGModuleCat.of R (Fin k → R))) := hFree
    exact ((Retract.mk s q hs).map F).projective
  letI : F.Additive := by infer_instance
  letI : F.PreservesHomology := by infer_instance
  let P : CochainComplex (ModuleCat.{u} R) ℤ := (F.mapHomologicalComplex (.up ℤ)).obj Pfg
  let p : P ⟶ K := (F.mapHomologicalComplex (.up ℤ)).map pfg
  have hBound : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff Pfg F b).mpr hPbound
  have hFinite (i : ℤ) : Module.Finite R (P.X i) := by
    change Module.Finite R (Pfg.X i).obj
    exact (Pfg.X i).property
  have hProj (i : ℤ) : Projective (P.X i) := by
    change Projective (F.obj (Pfg.X i))
    exact hProjective (Pfg.X i) (hPproj i)
  have hQuasi : QuasiIso p := by
    letI : QuasiIso pfg := hpfg
    exact HomologicalComplex.quasiIso_map_of_preservesHomology pfg F
  exact ⟨P, p, hBound, hFinite, hProj, hQuasi⟩

end ModuleCat

end
