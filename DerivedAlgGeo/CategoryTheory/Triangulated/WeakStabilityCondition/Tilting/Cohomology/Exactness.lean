/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Homological
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Exact sequences from heart cohomology

`originalHeartCohFunctor t n` is homological in every degree
(`originalHeartCohFunctor_isHomological`), so a distinguished triangle in `C`
maps to an exact short complex in the heart of `t` at every `n`.

## Main results

* `originalHeartCoh_exact_of_distTriang`: the degree-`n` short complex of a
  distinguished triangle is exact in the heart.
* `originalHeartCoh_isZero_of_isZero`: degree-zero cohomology kills zero objects.
* `heart_map_originalHeartCoh`: a t-exact functor carries `H⁰_t(X)` into the
  heart of the target t-structure, so degree-zero cohomology transports along it
  at the level of objects.

The associated connecting maps and five-term exact fragments are supplied in
`Cohomology.Sequence` via the shift-sequence API.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.Tilting

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C)

-- `ShortComplex.Exact` in the heart needs the heart's abelian structure at statement
-- time, and `heartFullSubcategoryAbelian` is a `def`, not an instance. Scope it locally
-- rather than making it global: a global `Abelian` instance on every t-structure heart
-- is exactly the kind of thing that creates diamonds later.
attribute [local instance]
  CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

/-- A distinguished triangle maps to an exact short complex under degree-`n`
heart cohomology. -/
theorem originalHeartCoh_exact_of_distTriang
    (n : ℤ) (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map (originalHeartCohFunctor t n)).Exact :=
  Functor.map_distinguished_exact (originalHeartCohFunctor t n) T hT

/-- Degree-zero heart cohomology sends zero objects to zero objects. -/
theorem originalHeartCoh_isZero_of_isZero {X : C} (hX : IsZero X) :
    IsZero ((originalHeartCohFunctor t 0).obj X) := by
  have : IsZero (((originalHeartCohFunctor t 0).obj X).obj) := by
    change IsZero ((shiftFunctor C 0).obj ((t.truncGELE 0 0).obj X))
    exact (t.truncGELE 0 0 ⋙ shiftFunctor C 0).map_isZero hX
  exact CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero this

section TExact

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : C ⥤ D} {t' : TStructure D}

/-- A t-exact functor carries heart objects to heart objects, so it is defined on
the targets of `originalHeartCohFunctor`.

This is the object-level statement. The natural transformation
`F ∘ H⁰_t ⟶ H⁰_{t'} ∘ F` needs the truncation–shift API described in the module
docstring and is deliberately not asserted here. -/
theorem heart_map_originalHeartCoh [Functor.IsTExact F t t'] (X : C) :
    t'.heart (F.obj ((originalHeartCohFunctor t 0).obj X).obj) :=
  Functor.heart_map_of_isTExact _ ((originalHeartCohFunctor t 0).obj X).property

end TExact

end CategoryTheory.Triangulated.Tilting
