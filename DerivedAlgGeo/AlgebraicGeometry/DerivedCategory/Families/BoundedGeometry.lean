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
base changes and records the contract needed to lift coherent pullback to the
bounded subcategory.

Coherence is preserved by every pullback (`Coh.pullback`, in
`Modules/Coherent/Pullback.lean`), but exactness of the pullback is not, so
the contract `HasCoherentPullback` records it and the bounded lift is
constructed only from an instance; `Families/CoherentPullback.lean` discharges
the contract for exact, in particular flat, pullback.  Preservation of the
perfect envelope is a theorem for every instance; the perfect lift, and the
identity and composition contracts for both the bounded lift defined here and
the perfect one, live in `Families/PerfectPullback.lean`.  No geometric
slicing, openness, relative-HN existence, moduli theorem, or conclusion of
Theorem 22.2 is asserted.

## Main definitions

* `SchemeBaseChange.BoundedCoherentDerivedFiber`, `SchemeBaseChange.PerfectDerivedFiber`,
  and their residue-field forms;
* `SchemeBaseChange.HasCoherentPullback`, with `HasCoherentPullback.ofExactSheafPullback`,
  the constructor every degreewise inhabitant should use;
* `SchemeBaseChange.coherentDerivedPullback`, `SchemeBaseChange.boundedCoherentDerivedPullback`,
  and `SchemeBaseChange.boundedCoherentDerivedPullbackCompInclusion`.
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
@[reducible]
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

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
