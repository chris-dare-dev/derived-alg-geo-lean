/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.TStructure

/-!
# Exact functors between derived categories

Exact functors between arbitrary abelian categories preserve strict complex
bounds and therefore preserve the canonical derived t-structure and its
bounded objects.  No scheme, sheaf, or other geometric input occurs here.
-/

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]

/-- An additive functor sends a strictly bounded-above cochain complex to a
strictly bounded-above cochain complex with the same bound. -/
lemma mapHomologicalComplex_isStrictlyLE (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (n : ℤ) (hK : K.IsStrictlyLE n) :
    CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyLE_iff] at hK ⊢
  intro i hi
  exact F.map_isZero (hK i hi)

/-- An additive functor sends a strictly bounded-below cochain complex to a
strictly bounded-below cochain complex with the same bound. -/
lemma mapHomologicalComplex_isStrictlyGE (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (n : ℤ) (hK : K.IsStrictlyGE n) :
    CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff] at hK ⊢
  intro i hi
  exact F.map_isZero (hK i hi)

variable [HasDerivedCategory A] [HasDerivedCategory B]

/-- The functor on derived categories induced by an exact functor preserves
the canonical `≤ n` truncation bound. -/
lemma mapDerivedCategory_isLE (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (n : ℤ)
    (hE : (DerivedCategory.TStructure.t (C := A)).IsLE E n) :
    (DerivedCategory.TStructure.t (C := B)).IsLE
      (F.mapDerivedCategory.obj E) n := by
  obtain ⟨K, e, hK⟩ := hE
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
    mapHomologicalComplex_isStrictlyLE F K n hK⟩

/-- The functor on derived categories induced by an exact functor preserves
the canonical `≥ n` truncation bound. -/
lemma mapDerivedCategory_isGE (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A) (n : ℤ)
    (hE : (DerivedCategory.TStructure.t (C := A)).IsGE E n) :
    (DerivedCategory.TStructure.t (C := B)).IsGE
      (F.mapDerivedCategory.obj E) n := by
  obtain ⟨K, e, hK⟩ := hE
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
    mapHomologicalComplex_isStrictlyGE F K n hK⟩

/-- Exact functors preserve bounded objects in the canonical derived
t-structures. -/
lemma mapDerivedCategory_bounded (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (E : DerivedCategory A)
    (hE : (DerivedCategory.TStructure.t (C := A)).bounded E) :
    (DerivedCategory.TStructure.t (C := B)).bounded
      (F.mapDerivedCategory.obj E) :=
  ⟨⟨hE.1.choose, mapDerivedCategory_isGE F E hE.1.choose hE.1.choose_spec⟩,
    ⟨hE.2.choose, mapDerivedCategory_isLE F E hE.2.choose hE.2.choose_spec⟩⟩

end CategoryTheory
