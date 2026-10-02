/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Degree-zero homology under preserved kernels

For an `ℕ`-indexed cochain complex, degree-zero homology is its degree-zero
cycle object: there is no incoming differential. A functor preserving the
outgoing kernel of this complex preserves these cycles, so its degreewise
extension commutes with degree-zero homology. The comparison is natural in the
complex when the corresponding kernel is preserved at each endpoint.

This is a statement about ordinary complexes. It does not identify degree-zero
homology of a right-derived functor with its underived functor; that requires
an injective-resolution comparison.

## Main definitions

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso`: the canonical
  degree-zero homology comparison under preservation of one outgoing kernel.

## Main results

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso_naturality`: the
  comparison commutes with every cochain map.

## Implementation notes

The incoming differential at zero vanishes. Mathlib's canonical isomorphism
from cycles to homology and its preserved-cycles isomorphism give the result.
An additive left-exact functor between abelian categories supplies the local
homology and preservation instances in this statement.

## References

* Mathlib `Algebra/Homology/ShortComplex/{HomologicalComplex,PreservesHomology}.lean`
  at repository pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

homological algebra, preserved kernel, degree-zero homology
-/

namespace CategoryTheory.Functor

open Limits

universe u v

/-- Mapping an `ℕ`-indexed cochain complex through a functor that preserves its
outgoing degree-zero kernel commutes with degree-zero homology, when both
homology objects exist. -/
noncomputable def mapCochainComplexHomologyZeroIso
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ)
    [K.HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).HasHomology 0]
    [PreservesLimit (parallelPair (K.sc 0).g 0) F] :
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
/-- The degree-zero homology comparison respects cochain maps through
naturality of the cycles-to-homology and preserved-cycles isomorphisms. -/
@[reassoc]
theorem mapCochainComplexHomologyZeroIso_naturality
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).HasHomology 0]
    [PreservesLimit (parallelPair (K.sc 0).g 0) F]
    [PreservesLimit (parallelPair (L.sc 0).g 0) F] :
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
