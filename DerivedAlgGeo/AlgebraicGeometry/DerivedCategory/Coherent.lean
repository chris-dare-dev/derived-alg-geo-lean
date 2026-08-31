/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.TStructure
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.StructureSheaf

/-!
# Derived categories of coherent sheaves on schemes

For a locally Noetherian scheme `X`, this module supplies the canonical
geometric specialization of Mathlib's generic derived-category construction:
`SchemeCoherentDerivedCategory X` and its bounded subcategory
`SchemeBoundedCoherentDerivedCategory X = Dᵇ(Coh X)`.

Perfect objects are defined in `D(Coh X)` as the thick triangulated envelope
of degree-zero finite locally free coherent sheaves. The structure sheaf gives
a genuine object in that envelope. Nothing in this module depends on a family
of schemes or on pullback; those consumers live under `DerivedCategory/Families/`.
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

attribute [local instance]
  preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The standard derived-category localization for coherent sheaves on a
locally Noetherian scheme. -/
noncomputable instance schemeCoherentHasDerivedCategory
    (X : Scheme.{u}) [IsLocallyNoetherian X] : HasDerivedCategory (Coh X) :=
  HasDerivedCategory.standard (Coh X)

/-- The derived category of coherent sheaves on a locally Noetherian scheme. -/
abbrev SchemeCoherentDerivedCategory (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  DerivedCategory (Coh X)

/-- The bounded derived category `Dᵇ(Coh X)` of coherent sheaves on a locally
Noetherian scheme. -/
abbrev SchemeBoundedCoherentDerivedCategory
    (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  DerivedCategory.Bounded (Coh X)

/-- Degree-zero derived objects represented by finite locally free coherent
sheaves. Shifts, finite sums, cones, and retracts are added by
`ObjectProperty.triangEnvelope`. -/
def schemeFiniteLocallyFreeGenerator
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ObjectProperty (SchemeCoherentDerivedCategory X) :=
  fun E ↦ ∃ (F : Coh X) (n : ℕ),
    Nonempty (Scheme.Modules.FiniteLocallyFreeData F.1 n) ∧
      Nonempty (E ≅ (DerivedCategory.singleFunctor (Coh X) 0).obj F)

/-- The perfect-object property on the coherent derived category: the thick
triangulated envelope of finite locally free coherent sheaves. -/
def schemePerfect :
    (X : Scheme.{u}) → [IsLocallyNoetherian X] →
      ObjectProperty (SchemeCoherentDerivedCategory X) :=
  fun X _ ↦ (schemeFiniteLocallyFreeGenerator X).triangEnvelope

/-- Every finite-locally-free degree-zero generator is bounded for the
canonical t-structure. -/
theorem schemeFiniteLocallyFreeGenerator_le_bounded
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    schemeFiniteLocallyFreeGenerator X ≤
      (DerivedCategory.TStructure.t (C := Coh X)).bounded := by
  rintro E ⟨F, n, _, ⟨e⟩⟩
  exact (DerivedCategory.TStructure.t (C := Coh X)).bounded.prop_of_iso e.symm
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

/-- Every perfect complex is bounded coherent. This is the universal-property
proof from the thick-envelope definition, not an additional assumption. -/
theorem schemePerfect_le_bounded (X : Scheme.{u}) [IsLocallyNoetherian X] :
    schemePerfect X ≤ (DerivedCategory.TStructure.t (C := Coh X)).bounded := by
  change (schemeFiniteLocallyFreeGenerator X).triangEnvelope ≤ _
  apply (ObjectProperty.triangEnvelope_le_iff
    (P := schemeFiniteLocallyFreeGenerator X)
    (Q := (DerivedCategory.TStructure.t (C := Coh X)).bounded)).2
  exact schemeFiniteLocallyFreeGenerator_le_bounded X

/-- `Perf(X)` as the full subcategory cut out by the thick envelope of finite
locally free coherent sheaves. -/
abbrev SchemePerfectDerivedCategory
    (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  (schemePerfect X).FullSubcategory

namespace SchemePerfectDerivedCategory

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The inclusion of perfect objects into the coherent derived category. -/
abbrev ι : SchemePerfectDerivedCategory X ⥤ SchemeCoherentDerivedCategory X :=
  (schemePerfect X).ι

/-- The fully faithful inclusion `Perf(X) ⥤ Dᵇ(Coh X)`. -/
abbrev toBounded :
    SchemePerfectDerivedCategory X ⥤ SchemeBoundedCoherentDerivedCategory X :=
  (schemePerfect X).ιOfLE (schemePerfect_le_bounded X)

/-- The degree-zero structure sheaf lies in the finite-locally-free generating
property. -/
theorem structureSheaf_mem_generator :
    schemeFiniteLocallyFreeGenerator X
      ((DerivedCategory.singleFunctor (Coh X) 0).obj (Scheme.structureSheafCoh X)) := by
  refine ⟨Scheme.structureSheafCoh X, 1, ⟨?_, ⟨Iso.refl _⟩⟩⟩
  exact ⟨(Scheme.Modules.LineBundleData.unit X).finiteLocallyFree⟩

/-- The degree-zero structure sheaf is a perfect object. -/
theorem structureSheaf_mem :
    schemePerfect X
      ((DerivedCategory.singleFunctor (Coh X) 0).obj (Scheme.structureSheafCoh X)) :=
  (schemeFiniteLocallyFreeGenerator X).le_triangEnvelope _
    (structureSheaf_mem_generator X)

/-- A canonical object of `Perf(X)` supplied by the structure sheaf. -/
noncomputable def structureSheaf : SchemePerfectDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor (Coh X) 0).obj (Scheme.structureSheafCoh X),
    structureSheaf_mem X⟩

/-- The finite-locally-free generating property is nonempty. -/
instance : (schemeFiniteLocallyFreeGenerator X).Nonempty :=
  ⟨_, structureSheaf_mem_generator X⟩

/-- The perfect-object property is nonempty. -/
instance : (schemePerfect X).Nonempty :=
  ⟨_, (structureSheaf X).property⟩

end SchemePerfectDerivedCategory

end

end AlgebraicGeometry.DerivedCategory
