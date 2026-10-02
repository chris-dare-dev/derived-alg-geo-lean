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
For any complex shape and degree, the same local comparison holds whenever
the incoming differential at that degree is zero. Its integer-cochain H⁰
specialization is useful for strictly nonnegative representatives.

## Main definitions

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso`: the canonical
  degree-zero homology comparison under preservation of one outgoing kernel.
* `CategoryTheory.Functor.mapHomologicalComplexHomologyIsoOfZeroIncoming`:
  the zero-incoming comparison at any complex shape and degree.
* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIsoOfZeroIncoming`:
  the integer-cochain degree-zero specialization.

## Main results

* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIso_naturality`: the
  comparison commutes with every cochain map.
* `CategoryTheory.Functor.mapHomologicalComplexHomologyIsoOfZeroIncoming_naturality`:
  naturality at arbitrary shape and degree.
* `CategoryTheory.Functor.mapCochainComplexHomologyZeroIsoOfZeroIncoming_naturality`:
  naturality of the integer-cochain specialization.

## Implementation notes

The incoming differential at zero vanishes. Mathlib's canonical isomorphism
from cycles to homology and its preserved-cycles isomorphism give the result.
An additive left-exact functor between abelian categories supplies the local
homology and preservation instances in this statement.
For the arbitrary-shape form, Mathlib's short-complex homology comparison
replaces the natural-number-specific cycles normalization.

## References

* Mathlib `Algebra/Homology/ShortComplex/{HomologicalComplex,PreservesHomology}.lean`
  at repository pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

homological algebra, preserved kernel, degree-zero homology
-/

namespace CategoryTheory.Functor

open Limits

universe u v w

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

/-- Vanishing of the incoming differential identifies homology at `j` with
the outgoing kernel. Preserving that kernel therefore gives the canonical
comparison without global left exactness. -/
noncomputable def mapHomologicalComplexHomologyIsoOfZeroIncoming
    {C : Type u} {D : Type v} {ι : Type w} {c : ComplexShape ι}
    [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (j : ι) [K.HasHomology j]
    [((F.mapHomologicalComplex c).obj K).HasHomology j]
    (hzero : (K.sc j).f = 0)
    [PreservesLimit (parallelPair (K.sc j).g 0) F] :
    ((F.mapHomologicalComplex c).obj K).homology j ≅
      F.obj (K.homology j) := by
  haveI : F.PreservesLeftHomologyOf (K.sc j) :=
    F.preservesLeftHomology_of_zero_f (K.sc j) hzero
  haveI : ((K.sc j).map F).HasHomology := by
    change (((F.mapHomologicalComplex c).obj K).sc j).HasHomology
    infer_instance
  exact (K.sc j).mapHomologyIso F

/-- Apply short-complex homology naturality to the three-term window around
`j`. The two outgoing kernels are preserved to construct the endpoint
comparison isomorphisms. -/
@[reassoc]
theorem mapHomologicalComplexHomologyIsoOfZeroIncoming_naturality
    {C : Type u} {D : Type v} {ι : Type w} {c : ComplexShape ι}
    [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (j : ι)
    [K.HasHomology j] [L.HasHomology j]
    [((F.mapHomologicalComplex c).obj K).HasHomology j]
    [((F.mapHomologicalComplex c).obj L).HasHomology j]
    (hK : (K.sc j).f = 0) (hL : (L.sc j).f = 0)
    [PreservesLimit (parallelPair (K.sc j).g 0) F]
    [PreservesLimit (parallelPair (L.sc j).g 0) F] :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex c).map φ) j ≫
      (mapHomologicalComplexHomologyIsoOfZeroIncoming F L j hL).hom =
      (mapHomologicalComplexHomologyIsoOfZeroIncoming F K j hK).hom ≫
        F.map (HomologicalComplex.homologyMap φ j) := by
  haveI : F.PreservesLeftHomologyOf (K.sc j) :=
    F.preservesLeftHomology_of_zero_f (K.sc j) hK
  haveI : F.PreservesLeftHomologyOf (L.sc j) :=
    F.preservesLeftHomology_of_zero_f (L.sc j) hL
  haveI : ((K.sc j).map F).HasHomology := by
    change (((F.mapHomologicalComplex c).obj K).sc j).HasHomology
    infer_instance
  haveI : ((L.sc j).map F).HasHomology := by
    change (((F.mapHomologicalComplex c).obj L).sc j).HasHomology
    infer_instance
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C c j).map φ) F

/-- The degree-zero integer-cochain specialization of the zero-incoming
homology comparison. -/
noncomputable def mapCochainComplexHomologyZeroIsoOfZeroIncoming
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) [K.HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology 0]
    (hzero : (K.sc 0).f = 0)
    [PreservesLimit (parallelPair (K.sc 0).g 0) F] :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology 0 ≅
      F.obj (K.homology 0) :=
  mapHomologicalComplexHomologyIsoOfZeroIncoming F K 0 hzero

/-- Naturality of the integer-cochain specialization follows from the
arbitrary-shape three-term comparison. -/
@[reassoc]
theorem mapCochainComplexHomologyZeroIsoOfZeroIncoming_naturality
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [K.HasHomology 0] [L.HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).HasHomology 0]
    [((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).HasHomology 0]
    (hK : (K.sc 0).f = 0) (hL : (L.sc 0).f = 0)
    [PreservesLimit (parallelPair (K.sc 0).g 0) F]
    [PreservesLimit (parallelPair (L.sc 0).g 0) F] :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 ≫
      (mapCochainComplexHomologyZeroIsoOfZeroIncoming F L hL).hom =
      (mapCochainComplexHomologyZeroIsoOfZeroIncoming F K hK).hom ≫
        F.map (HomologicalComplex.homologyMap φ 0) :=
  mapHomologicalComplexHomologyIsoOfZeroIncoming_naturality F φ 0 hK hL

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
