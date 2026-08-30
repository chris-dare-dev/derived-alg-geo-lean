/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.StructureSheaf
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback

/-!
# Bounded coherent and perfect scheme-derived fibers

This file supplies the geometric categories that were deliberately absent from
`Families.SchemeDerived`.

For a locally Noetherian scheme `X`, `SchemeBoundedCoherentDerivedCategory X`
is Mathlib's bounded derived category of the repository-owned abelian category
`Coh X`.  The perfect objects are defined inside the derived category of
`Coh X` as the triangulated envelope of the degree-zero objects represented by
finite locally free coherent sheaves.  Mathlib's `triangEnvelope` is the
smallest triangulated object property closed under retracts that contains those
generators, so this is the standard thick-envelope definition of `Perf(X)`.

The structure sheaf gives a genuine perfect generator object, preventing the
definition from being vacuous.  Scheme base changes and residue-field schemes
expose both categories.

Preservation under pullback is not automatic at this boundary.  In particular,
an arbitrary pullback functor on all module sheaves has not yet been proved to
preserve coherent sheaves or the perfect envelope.  The restriction contracts
at the end of the file therefore record those exact obligations and construct
actual lifted functors only after the corresponding objectwise preservation
proofs are supplied.  No geometric slicing, openness, relative-HN existence,
moduli theorem, or conclusion of Theorem 22.2 is asserted.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
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

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The `≤ n` part of a t-structure is stable under retracts. -/
lemma tStructureIsLE_of_retract (t : TStructure C) {X Y : C} (r : Retract X Y) (n : ℤ)
    (hY : t.IsLE Y n) : t.IsLE X n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Z f hZ
  have hzero : r.r ≫ f = 0 := t.zero_of_isLE_of_isGE (r.r ≫ f) n (n + 1)
    (by omega) hY hZ
  rw [← Category.id_comp f, ← r.retract, Category.assoc, hzero, comp_zero]

/-- The `≥ n` part of a t-structure is stable under retracts. -/
lemma tStructureIsGE_of_retract (t : TStructure C) {X Y : C} (r : Retract X Y) (n : ℤ)
    (hY : t.IsGE Y n) : t.IsGE X n := by
  rw [t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro Z f hZ
  have hzero : f ≫ r.i = 0 := t.zero_of_isLE_of_isGE (f ≫ r.i) (n - 1) n
    (by omega) hZ hY
  rw [← Category.comp_id f, ← r.retract, ← Category.assoc, hzero, zero_comp]

instance (t : TStructure C) : t.minus.IsStableUnderRetracts where
  of_retract r hY := ⟨hY.choose, tStructureIsLE_of_retract t r hY.choose hY.choose_spec⟩

instance (t : TStructure C) : t.plus.IsStableUnderRetracts where
  of_retract r hY := ⟨hY.choose, tStructureIsGE_of_retract t r hY.choose hY.choose_spec⟩

instance (t : TStructure C) : t.bounded.IsStableUnderRetracts := by
  constructor
  intro X Y r hY
  exact ⟨ObjectProperty.prop_of_retract t.plus r hY.1,
    ObjectProperty.prop_of_retract t.minus r hY.2⟩

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

/-- Degree-zero derived objects represented by finite locally free coherent
sheaves.  Shifts, finite sums, cones, and retracts are added by
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

/-- Every perfect complex is bounded coherent.  This is the universal-property
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
property.

`O_X` as a coherent sheaf is `Scheme.structureSheafCoh`, in `CoherentSheaf/`.
This module used to define its own copy: the object is a line bundle and its
coherence is `LineBundleData.isCoherent`, so it needs none of the derived
categories, triangulated generators or t-structures that this file imports, and
a general context could not reach it inside the stability-families namespace. -/
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

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The bounded coherent derived fiber over a locally Noetherian scheme base
change. -/
abbrev BoundedCoherentDerivedFiber (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] :=
  SchemeBoundedCoherentDerivedCategory T.left

/-- The perfect derived fiber over a locally Noetherian scheme base change. -/
abbrev PerfectDerivedFiber (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] :=
  SchemePerfectDerivedCategory T.left

/-- The bounded coherent derived category of the residue-field scheme. -/
abbrev ResidueBoundedCoherentDerivedFiber (T : SchemeBaseChange S)
    (x : T.left) [IsLocallyNoetherian (T.residue x).left] :=
  (T.residue x).BoundedCoherentDerivedFiber

/-- The perfect derived category of the residue-field scheme. -/
abbrev ResiduePerfectDerivedFiber (T : SchemeBaseChange S)
    (x : T.left) [IsLocallyNoetherian (T.residue x).left] :=
  (T.residue x).PerfectDerivedFiber

/-- The geometric data needed to restrict module-sheaf pullback to coherent
sheaves.  Exactness is part of the contract; it is what makes the induced
derived pullback preserve bounded objects. -/
class HasCoherentPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left] where
  /-- Pullback on coherent sheaves. -/
  sheafPullback : Coh U.left ⥤ Coh T.left
  /-- Coherent pullback preserves finite limits. -/
  preservesFiniteLimits : PreservesFiniteLimits sheafPullback
  /-- Coherent pullback preserves finite colimits. -/
  preservesFiniteColimits : PreservesFiniteColimits sheafPullback
  /-- After forgetting coherence, this is ordinary module-sheaf pullback. -/
  comparison : sheafPullback ⋙ Coh.ι T.left ≅ Coh.ι U.left ⋙ modulePullback f
  /-- The localized pullback on coherent derived categories. -/
  derivedPullback :
    SchemeCoherentDerivedCategory U.left ⥤ SchemeCoherentDerivedCategory T.left
  /-- The derived functor is induced by degreewise coherent-sheaf pullback. -/
  derivedFactors : DerivedCategory.Q ⋙ derivedPullback ≅
    sheafPullback.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  /-- Derived coherent pullback is additive. -/
  derivedAdditive : derivedPullback.Additive
  /-- Derived coherent pullback commutes with shifts. -/
  commShift : derivedPullback.CommShift ℤ
  /-- Derived coherent pullback is triangulated. -/
  isTriangulated : derivedPullback.IsTriangulated
  /-- Exact coherent pullback preserves canonical boundedness. -/
  preservesBounded (E : SchemeCoherentDerivedCategory U.left) :
    (DerivedCategory.TStructure.t (C := Coh U.left)).bounded E →
      (DerivedCategory.TStructure.t (C := Coh T.left)).bounded (derivedPullback.obj E)

attribute [instance] HasCoherentPullback.preservesFiniteLimits
  HasCoherentPullback.preservesFiniteColimits

/-- Coherent-sheaf pullback on unbounded derived categories. -/
def coherentDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    SchemeCoherentDerivedCategory U.left ⥤ SchemeCoherentDerivedCategory T.left :=
  HasCoherentPullback.derivedPullback f

instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (coherentDerivedPullback f).Additive := by
  dsimp [coherentDerivedPullback]
  exact HasCoherentPullback.derivedAdditive

instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (coherentDerivedPullback f).CommShift ℤ := by
  dsimp [coherentDerivedPullback]
  exact HasCoherentPullback.commShift

instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (coherentDerivedPullback f).IsTriangulated := by
  dsimp [coherentDerivedPullback]
  exact HasCoherentPullback.isTriangulated

/-- Exact coherent pullback restricts canonically to `Dᵇ(Coh)`. -/
def boundedCoherentDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    U.BoundedCoherentDerivedFiber ⥤ T.BoundedCoherentDerivedFiber :=
  (DerivedCategory.TStructure.t (C := Coh T.left)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedPullback f)
    (fun E ↦ HasCoherentPullback.preservesBounded E.obj E.property)

instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (boundedCoherentDerivedPullback f).Additive := by
  dsimp [boundedCoherentDerivedPullback]
  infer_instance

noncomputable instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (boundedCoherentDerivedPullback f).CommShift ℤ := by
  dsimp [boundedCoherentDerivedPullback]
  infer_instance

/-- The bounded lift forgets to coherent derived pullback. -/
def boundedCoherentDerivedPullbackCompInclusion
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    boundedCoherentDerivedPullback f ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ coherentDerivedPullback f :=
  (DerivedCategory.TStructure.t (C := Coh T.left)).bounded.liftCompιIso
    (DerivedCategory.Bounded.ι ⋙ coherentDerivedPullback f)
    (fun E ↦ HasCoherentPullback.preservesBounded E.obj E.property)

noncomputable instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] :
    NatTrans.CommShift (boundedCoherentDerivedPullbackCompInclusion f).hom ℤ := by
  dsimp [boundedCoherentDerivedPullbackCompInclusion]
  exact CategoryTheory.Functor.CommShift.ofComp_compatibility _ _

instance {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : (boundedCoherentDerivedPullback f).IsTriangulated := by
  rw [CategoryTheory.Functor.isTriangulated_iff_comp_right
    (boundedCoherentDerivedPullbackCompInclusion f)]
  infer_instance

/-- The remaining generator-level obligation for coherent pullback to
restrict to perfect complexes.  It is deliberately stated only on the finite
locally free generators; the thick-envelope theorem below propagates it to
every perfect complex. -/
class PreservesPerfectPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] : Prop where
  mapsGenerator : schemeFiniteLocallyFreeGenerator U.left ≤
    (schemePerfect T.left).inverseImage (coherentDerivedPullback f)

/-- Generator preservation by a triangulated pullback implies preservation
of the entire perfect thick envelope. -/
theorem coherentDerivedPullback_preservesPerfect
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [PreservesPerfectPullback f] :
    schemePerfect U.left ≤
      (schemePerfect T.left).inverseImage (coherentDerivedPullback f) := by
  letI : ((schemePerfect T.left).inverseImage
      (coherentDerivedPullback f)).IsStableUnderRetracts :=
    { of_retract := fun r h ↦ ObjectProperty.prop_of_retract
        (schemeFiniteLocallyFreeGenerator T.left).triangEnvelope
        (r.map (coherentDerivedPullback f)) h }
  letI : ((schemePerfect T.left).inverseImage
      (coherentDerivedPullback f)).IsTriangulated := by
    change (((schemeFiniteLocallyFreeGenerator T.left).triangEnvelope).inverseImage
      (coherentDerivedPullback f)).IsTriangulated
    infer_instance
  change (schemeFiniteLocallyFreeGenerator U.left).triangEnvelope ≤ _
  apply (ObjectProperty.triangEnvelope_le_iff
    (P := schemeFiniteLocallyFreeGenerator U.left)
    (Q := (schemePerfect T.left).inverseImage
      (coherentDerivedPullback f))).2
  exact PreservesPerfectPullback.mapsGenerator

/-- Pullback on perfect derived fibers, constructed from generator
preservation. -/
def perfectDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [PreservesPerfectPullback f] :
    U.PerfectDerivedFiber ⥤ T.PerfectDerivedFiber :=
  (schemePerfect T.left).lift
    ((schemePerfect U.left).ι ⋙ coherentDerivedPullback f)
    (fun E ↦ coherentDerivedPullback_preservesPerfect f E.obj E.property)

/-- The perfect lift forgets to coherent derived pullback. -/
def perfectDerivedPullbackCompInclusion
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f] [PreservesPerfectPullback f] :
    perfectDerivedPullback f ⋙ (schemePerfect T.left).ι ≅
      (schemePerfect U.left).ι ⋙ coherentDerivedPullback f :=
  Iso.refl _

/-- Identity compatibility for the bounded-coherent and perfect pullback
lifts on a locally Noetherian base change. -/
class GeometricDerivedPullbackIdentity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] [HasCoherentPullback (𝟙 T)]
    [PreservesPerfectPullback (𝟙 T)] where
  /-- Bounded coherent pullback along the identity is the identity functor. -/
  boundedIso : boundedCoherentDerivedPullback (𝟙 T) ≅
    𝟭 T.BoundedCoherentDerivedFiber
  /-- Perfect pullback along the identity is the identity functor. -/
  perfectIso : perfectDerivedPullback (𝟙 T) ≅ 𝟭 T.PerfectDerivedFiber

/-- Composition compatibility for the bounded-coherent and perfect pullback
lifts.  This is the typed geometric base-change compositor; coherence laws
can subsequently be imposed and proved on these canonical isomorphisms. -/
class GeometricDerivedPullbackComposition
    {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g]
    [HasCoherentPullback (f ≫ g)]
    [PreservesPerfectPullback f] [PreservesPerfectPullback g]
    [PreservesPerfectPullback (f ≫ g)] where
  /-- Bounded coherent pullback reverses composition up to isomorphism. -/
  boundedIso : boundedCoherentDerivedPullback g ⋙
      boundedCoherentDerivedPullback f ≅
    boundedCoherentDerivedPullback (f ≫ g)
  /-- Perfect pullback reverses composition up to isomorphism. -/
  perfectIso : perfectDerivedPullback g ⋙ perfectDerivedPullback f ≅
    perfectDerivedPullback (f ≫ g)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
