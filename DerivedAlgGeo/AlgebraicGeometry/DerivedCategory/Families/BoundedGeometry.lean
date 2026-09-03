/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback

/-!
# Bounded coherent and perfect derived categories in scheme families

The canonical geometric categories `D(Coh X)`, `Dᵇ(Coh X)`, and `Perf(X)`
live in `DerivedCategory/Coherent.lean`. This file evaluates them on scheme
base changes and records the contracts needed to lift coherent pullback to the
bounded and perfect subcategories.

Preservation under pullback is not automatic at this boundary.  Coherence is
preserved by every pullback (`Coh.pullback`, in `Modules/Coherent/Pullback.lean`),
but exactness of the pullback and preservation of the perfect envelope are
not.  The contracts at the end of the file therefore record the exact
obligations and construct actual lifted functors only after the corresponding
preservation proofs are supplied; `Families/CoherentPullback.lean` discharges
`HasCoherentPullback` for exact, in particular flat, pullback.  No geometric
slicing, openness, relative-HN existence, moduli theorem, or conclusion of
Theorem 22.2 is asserted.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

attribute [local instance]
  preservesBinaryBiproducts_of_preservesBinaryProducts

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

/-- Build the contract from an exact functor on coherent sheaves that forgets to module-sheaf
pullback: the derived fields are Mathlib's `Functor.mapDerivedCategory` of that functor with
its instances, and boundedness is `mapDerivedCategory_bounded`.  Every inhabitant whose
derived pullback is the degreewise one should come through here rather than restate those
fields. -/
def HasCoherentPullback.ofExactSheafPullback {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    (F : Coh U.left ⥤ Coh T.left) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    (e : F ⋙ Coh.ι T.left ≅ Coh.ι U.left ⋙ modulePullback f) :
    HasCoherentPullback f where
  sheafPullback := F
  preservesFiniteLimits := inferInstance
  preservesFiniteColimits := inferInstance
  comparison := e
  derivedPullback := F.mapDerivedCategory
  derivedFactors := F.mapDerivedCategoryFactors
  derivedAdditive := inferInstance
  commShift := inferInstance
  isTriangulated := inferInstance
  preservesBounded E hE := mapDerivedCategory_bounded F E hE

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
