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

The closing section gives every line bundle a canonical image in this
category: `LineBundleData.coh` packages the underlying sheaf with its
coherence proof, and `LineBundleData.derivedObject` places it in degree zero
of `D(Coh X)`, where it is perfect and bounded. This is the adapter geometric
consumers use to speak about a line bundle *as a derived object* without
re-deriving the `Coh`-object and `singleFunctor` plumbing each time.
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

/-! ### Line bundles as coherent derived objects

A line bundle is coherent outright — `LineBundleData.isCoherent` needs no
noetherian hypothesis — so it has a canonical `Coh X` avatar, and on a locally
Noetherian scheme a canonical degree-zero derived object. The declarations
live in the `LineBundleData` namespace for dot notation, following the
precedent of `LineBundleData.toPic_eq_iff` in `CoherentSheaf/StructureSheaf.lean`. -/

namespace AlgebraicGeometry.Scheme.Modules.LineBundleData

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.DerivedCategory

noncomputable section

universe u

variable {X : Scheme.{u}}

/-- A line bundle as an object of `Coh X`: the underlying sheaf paired with
its coherence proof. No noetherian hypothesis enters, for the same reason as
`Scheme.structureSheafCoh`: an invertible sheaf is of finite presentation
outright. -/
noncomputable def coh (L : LineBundleData X) : Coh X :=
  ⟨L.line, L.isCoherent⟩

@[simp]
theorem coh_obj (L : LineBundleData X) : L.coh.obj = L.line :=
  rfl

/-- The unit line bundle's `Coh` avatar is the structure sheaf. Both sides are
the same pair by definition; this records that the two routes to `O_X` in
`Coh X` cannot drift apart. -/
theorem unit_coh : (unit X).coh = Scheme.structureSheafCoh X :=
  rfl

/-- Lift an isomorphism of underlying sheaves to `Coh X`. The inclusion is
fully faithful, so this is `ObjectProperty.isoMk`; it is what makes
`coh` well-defined up to the choices a `LineBundleData` records. -/
noncomputable def cohIso {L M : LineBundleData X} (e : L.line ≅ M.line) :
    L.coh ≅ M.coh :=
  ObjectProperty.isoMk (P := Scheme.coherent X) e

variable [IsLocallyNoetherian X]

/-- A line bundle as a degree-zero object of the coherent derived category. -/
noncomputable def derivedObject (L : LineBundleData X) :
    SchemeCoherentDerivedCategory X :=
  (DerivedCategory.singleFunctor (Coh X) 0).obj L.coh

/-- A line bundle satisfies the finite-locally-free generating property: its
rank-one atlas `finiteLocallyFree` is exactly the witness the property asks
for, in degree zero. -/
theorem derivedObject_mem_generator (L : LineBundleData X) :
    schemeFiniteLocallyFreeGenerator X L.derivedObject :=
  ⟨L.coh, 1, ⟨L.finiteLocallyFree⟩, ⟨Iso.refl _⟩⟩

/-- **Every line bundle is a perfect object** of the coherent derived
category: it lies in the generating property itself, before the envelope
adds shifts, sums, cones, and retracts. -/
theorem derivedObject_perfect (L : LineBundleData X) :
    schemePerfect X L.derivedObject :=
  (schemeFiniteLocallyFreeGenerator X).le_triangEnvelope _
    L.derivedObject_mem_generator

/-- A line bundle is bounded for the canonical t-structure, through
`schemeFiniteLocallyFreeGenerator_le_bounded` rather than a fresh degree
computation. -/
theorem derivedObject_bounded (L : LineBundleData X) :
    (DerivedCategory.TStructure.t (C := Coh X)).bounded L.derivedObject :=
  schemeFiniteLocallyFreeGenerator_le_bounded X _ L.derivedObject_mem_generator

/-- Lift an isomorphism of underlying sheaves to the derived objects. Needed
by any collection of line bundles stated up to isomorphism: it is what makes
membership statements about `derivedObject` transportable along a change of
representative. -/
noncomputable def derivedObjectIso {L M : LineBundleData X}
    (e : L.line ≅ M.line) : L.derivedObject ≅ M.derivedObject :=
  (DerivedCategory.singleFunctor (Coh X) 0).mapIso (cohIso e)

/-- The unit line bundle's derived object is the underlying object of the
canonical perfect structure sheaf. Definitional, so the two routes to `O_X`
in `D(Coh X)` — through `LineBundleData` and through
`SchemePerfectDerivedCategory.structureSheaf` — are identified for free. -/
theorem unit_derivedObject :
    (unit X).derivedObject =
      (SchemePerfectDerivedCategory.structureSheaf X).obj :=
  rfl

end

end AlgebraicGeometry.Scheme.Modules.LineBundleData
