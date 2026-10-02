/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Degree-zero homology and left-exact functors

For an `ℕ`-indexed cochain complex, degree-zero homology is its degree-zero
cycle object: there is no incoming differential. A functor preserving finite
limits preserves these cycles, so its degreewise extension commutes with
degree-zero homology. The comparison is natural in the complex.

This is a statement about ordinary complexes. It does not identify degree-zero
homology of a right-derived functor with its underived functor; that requires
an injective-resolution comparison.

## Main definitions

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso`: the canonical
  degree-zero homology comparison for a finite-limit-preserving functor.

## Main results

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso_naturality`: the
  comparison commutes with every cochain map.

## Implementation notes

The incoming differential at zero vanishes. Mathlib's canonical isomorphism
from cycles to homology and its preserved-cycles isomorphism give the result.

## References

* Mathlib `Algebra/Homology/ShortComplex/{HomologicalComplex,PreservesHomology}.lean`
  at repository pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

homological algebra, left exact functor, degree-zero homology
-/

namespace CategoryTheory.Functor

open Limits

universe u v

/-- A functor preserving finite limits commutes with degree-zero homology of
an `ℕ`-indexed cochain complex. The preservation hypothesis is sufficient:
the zero-morphism preservation needed to map complexes is inferred. -/
noncomputable def mapCochainComplexHomologyZeroIso
    {C : Type u} {D : Type v} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D)
    [PreservesFiniteLimits F] (K : CochainComplex C ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 ≅
      F.obj (K.homology 0) := by
  have hzero : (K.sc 0).f = 0 := by
    change K.d (ComplexShape.up ℕ |>.prev 0) 0 = 0
    simp
  haveI : F.PreservesLeftHomologyOf (K.sc 0) :=
    F.preservesLeftHomology_of_zero_f (K.sc 0) hzero
  exact (CochainComplex.isoHomologyπ₀ _).symm ≪≫
    (K.sc 0).mapCyclesIso F ≪≫ F.mapIso (CochainComplex.isoHomologyπ₀ K)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `Functor.mapCochainComplexHomologyZeroIso` in a cochain map. -/
@[reassoc]
theorem mapCochainComplexHomologyZeroIso_naturality
    {C : Type u} {D : Type v} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D)
    [PreservesFiniteLimits F]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0 ≫
      (mapCochainComplexHomologyZeroIso F L).hom =
      (mapCochainComplexHomologyZeroIso F K).hom ≫
        F.map (HomologicalComplex.homologyMap φ 0) := by
  simp only [mapCochainComplexHomologyZeroIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc]
  have hzeroK : (K.sc 0).f = 0 := by
    change K.d (ComplexShape.up ℕ |>.prev 0) 0 = 0
    simp
  have hzeroL : (L.sc 0).f = 0 := by
    change L.d (ComplexShape.up ℕ |>.prev 0) 0 = 0
    simp
  haveI : F.PreservesLeftHomologyOf (K.sc 0) :=
    F.preservesLeftHomology_of_zero_f (K.sc 0) hzeroK
  haveI : F.PreservesLeftHomologyOf (L.sc 0) :=
    F.preservesLeftHomology_of_zero_f (L.sc 0) hzeroL
  have hcycles :
      HomologicalComplex.cyclesMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0 ≫
        ((L.sc 0).mapCyclesIso F).hom =
      ((K.sc 0).mapCyclesIso F).hom ≫
        F.map (HomologicalComplex.cyclesMap φ 0) := by
    exact ShortComplex.mapCyclesIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) 0).map φ) F
  calc
    _ = (CochainComplex.isoHomologyπ₀
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
          (HomologicalComplex.cyclesMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 0 ≫
            ((L.sc 0).mapCyclesIso F).hom) ≫ F.map L.isoHomologyπ₀.hom := by
          simp only [Category.assoc]
    _ = (CochainComplex.isoHomologyπ₀
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
          (((K.sc 0).mapCyclesIso F).hom ≫
            F.map (HomologicalComplex.cyclesMap φ 0)) ≫
          F.map L.isoHomologyπ₀.hom := by
          exact congrArg (fun t =>
            (CochainComplex.isoHomologyπ₀
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫ t ≫
                F.map L.isoHomologyπ₀.hom) hcycles
    _ = _ := by
      simp only [Category.assoc, ← F.map_comp, HomologicalComplex.isoHomologyπ_hom]
      rw [HomologicalComplex.homologyπ_naturality]

end CategoryTheory.Functor
