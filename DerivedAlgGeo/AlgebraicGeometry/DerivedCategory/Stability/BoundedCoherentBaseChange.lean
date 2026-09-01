/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.PreStabilityBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducingBoundary
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Bounded coherent realization of categorical pre-stability base change

This file connects the actual bounded coherent pullback from
`Families.BoundedGeometry` to `FiberPreStabilityBaseChangeData`.

The bridge has three layers.

* `BoundedCoherentPullbackPreimageData` is the explicit preimage witness for
  one geometric pullback.  Its identity and composition constructors use the
  bounded derived-pullback unit and compositor.
* `BoundedCoherentPullbackInducingData` records the actual phase-indexed A.17
  output for that pullback.  The owned Corollary-A.23 theorem converts this
  output into preimage data.
* `BoundedCoherentDerivedRealization` identifies an abstract strict fiber
  family with the genuine `Dᵇ(Coh)` fibers and their pullbacks.
  `GeometricPreStabilityBaseChangeData.toFiberPreStabilityBaseChangeData`
  then exports the downstream witness without accepting `Slicing.PreimageData`
  from the caller.

This file does not manufacture the scheme-specific A.17 realization from
flatness.  It does, however, consume its honest phase-indexed output directly:
there is no global theorem switch and no preconstructed `Slicing.PreimageData`
input.  Openness and relative-HN consequences are exported downstream.
-/

namespace AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

noncomputable section

universe u v uV

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Explicit preimage-slicing data for bounded coherent derived pullback along
one morphism of locally Noetherian scheme base changes. -/
structure BoundedCoherentPullbackPreimageData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f]
    (s : Slicing T.BoundedCoherentDerivedFiber) : Prop where
  /-- The two non-formal slicing axioms for the actual bounded coherent
  pullback. -/
  preimageData : s.PreimageData (boundedCoherentDerivedPullback f)

namespace BoundedCoherentPullbackPreimageData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPullback f]
  {s : Slicing T.BoundedCoherentDerivedFiber}

/-- The slicing constructed on the target bounded coherent fiber. -/
def preimage (h : BoundedCoherentPullbackPreimageData f s) :
    Slicing U.BoundedCoherentDerivedFiber :=
  s.preimage (boundedCoherentDerivedPullback f) h.preimageData

/-- The bounded coherent pullback unit supplies the identity preimage
witness. -/
theorem identity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left]
    [HasCoherentPullback (𝟙 T)] [PreservesPerfectPullback (𝟙 T)]
    [GeometricDerivedPullbackIdentity T]
    (s : Slicing T.BoundedCoherentDerivedFiber) :
    BoundedCoherentPullbackPreimageData (𝟙 T) s where
  preimageData := s.preimageData_id.ofIso
    (GeometricDerivedPullbackIdentity.boundedIso (T := T)).symm

/-- The slicing induced along the identity is the original slicing. -/
@[simp]
theorem preimage_identity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left]
    [HasCoherentPullback (𝟙 T)] [PreservesPerfectPullback (𝟙 T)]
    [GeometricDerivedPullbackIdentity T]
    (s : Slicing T.BoundedCoherentDerivedFiber) :
    (identity T s).preimage = s := by
  calc
    (identity T s).preimage =
        s.preimage (Functor.id T.BoundedCoherentDerivedFiber)
          s.preimageData_id :=
      Slicing.preimage_iso s _ _ s.preimageData_id
        (GeometricDerivedPullbackIdentity.boundedIso (T := T)).symm
    _ = s := s.preimage_id

/-- Geometric bounded coherent preimage witnesses compose through the actual
bounded derived-pullback compositor. -/
theorem comp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g]
    [HasCoherentPullback (f ≫ g)]
    [PreservesPerfectPullback f] [PreservesPerfectPullback g]
    [PreservesPerfectPullback (f ≫ g)]
    [GeometricDerivedPullbackComposition f g]
    {s : Slicing T.BoundedCoherentDerivedFiber}
    (hf : BoundedCoherentPullbackPreimageData f s)
    (hg : BoundedCoherentPullbackPreimageData g hf.preimage) :
    BoundedCoherentPullbackPreimageData (f ≫ g) s where
  preimageData := by
    have hgData := hg.preimageData
    change (s.preimage (boundedCoherentDerivedPullback f)
      hf.preimageData).PreimageData (boundedCoherentDerivedPullback g) at hgData
    exact (hf.preimageData.comp hgData).ofIso
      (GeometricDerivedPullbackComposition.boundedIso (f := f) (g := g))

/-- One-step and two-step geometric bounded coherent preimages agree. -/
@[simp]
theorem preimage_comp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g]
    [HasCoherentPullback (f ≫ g)]
    [PreservesPerfectPullback f] [PreservesPerfectPullback g]
    [PreservesPerfectPullback (f ≫ g)]
    [GeometricDerivedPullbackComposition f g]
    {s : Slicing T.BoundedCoherentDerivedFiber}
    (hf : BoundedCoherentPullbackPreimageData f s)
    (hg : BoundedCoherentPullbackPreimageData g hf.preimage) :
    (hf.comp f g hg).preimage = hg.preimage := by
  have hgData := hg.preimageData
  change (s.preimage (boundedCoherentDerivedPullback f)
    hf.preimageData).PreimageData (boundedCoherentDerivedPullback g) at hgData
  calc
    (hf.comp f g hg).preimage =
        s.preimage
          (boundedCoherentDerivedPullback g ⋙
            boundedCoherentDerivedPullback f)
          (hf.preimageData.comp hgData) :=
      Slicing.preimage_iso s _ _
        (hf.preimageData.comp hgData)
        (GeometricDerivedPullbackComposition.boundedIso (f := f) (g := g))
    _ = hg.preimage := by
      apply Slicing.ext
      rfl

end BoundedCoherentPullbackPreimageData

/-- The phase-indexed A.17 output specialized to actual bounded coherent
derived pullback. -/
structure BoundedCoherentPullbackInducingData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f]
    (s : Slicing T.BoundedCoherentDerivedFiber) where
  /-- The induced source t-structures with the A.8 recognition formulas. -/
  inducedTStructures :
    s.InducedTStructures (boundedCoherentDerivedPullback f)

namespace BoundedCoherentPullbackInducingData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPullback f]
  {s : Slicing T.BoundedCoherentDerivedFiber}

/-- The bounded derived-pullback unit transports the inhabited identity A.17
model to the concrete bounded-coherent identity pullback. -/
def identity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left]
    [HasCoherentPullback (𝟙 T)] [PreservesPerfectPullback (𝟙 T)]
    [GeometricDerivedPullbackIdentity T]
    (s : Slicing T.BoundedCoherentDerivedFiber) :
    BoundedCoherentPullbackInducingData (𝟙 T) s where
  inducedTStructures := s.inducedTStructuresId.ofIso
    (GeometricDerivedPullbackIdentity.boundedIso (T := T)).symm

/-- Apply the owned finite phase-truncation theorem to the actual A.17
output. -/
theorem toPreimageData (h : BoundedCoherentPullbackInducingData f s) :
    BoundedCoherentPullbackPreimageData f s where
  preimageData := h.inducedTStructures.preimageData

end BoundedCoherentPullbackInducingData

end SchemeBaseChange

/-- A pseudofunctorial triangulated fiber family realized by the genuine
bounded coherent derived categories, with every abstract pullback identified
with the actual bounded coherent pullback. -/
structure BoundedCoherentDerivedRealization
    {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
    [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
    [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
      SchemeBaseChange.HasCoherentPullback f] where
  /-- Equivalence from each abstract fiber to `Dᵇ(Coh)`. -/
  fiberEquivalence (T : SchemeBaseChange S) :
    F.Fiber T ≌ T.BoundedCoherentDerivedFiber
  /-- The chosen forward functor commutes with shifts.  Mathlib derives the
  unique compatible shift structure on the inverse functor from this one. -/
  fiberEquivalenceFunctorCommShift (T : SchemeBaseChange S) :
    (fiberEquivalence T).functor.CommShift ℤ
  /-- Unit and counit coherence for the derived inverse shift structure. -/
  fiberEquivalenceCommShift (T : SchemeBaseChange S) :
    letI := fiberEquivalenceFunctorCommShift T
    letI := (fiberEquivalence T).commShiftInverse ℤ
    (fiberEquivalence T).CommShift ℤ
  /-- The equivalence is triangulated.  Mathlib derives exactness and
  additivity for both directions from this equivalence-level property. -/
  fiberEquivalenceIsTriangulated (T : SchemeBaseChange S) :
    letI := fiberEquivalenceFunctorCommShift T
    letI := (fiberEquivalence T).commShiftInverse ℤ
    letI := fiberEquivalenceCommShift T
    (fiberEquivalence T).IsTriangulated
  /-- Abstract pullback is the actual bounded coherent pullback, transported
  through the two fiber equivalences. -/
  pullbackIso {T U : SchemeBaseChange S} (f : T ⟶ U) :
    F.pull f ≅
      (fiberEquivalence U).functor ⋙
        (SchemeBaseChange.boundedCoherentDerivedPullback f ⋙
          (fiberEquivalence T).inverse)

namespace BoundedCoherentDerivedRealization

variable {S : Scheme.{u}} {F : SchemeTriangulatedFiberFamily S}
  [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
  [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
    SchemeBaseChange.HasCoherentPullback f]

/-- The standard Mathlib triangulated-equivalence structure supplies preimage
data for the inverse fiber equivalence. -/
theorem inversePreimageData (R : BoundedCoherentDerivedRealization F)
    (T : SchemeBaseChange S) (s : Slicing (F.Fiber T)) :
    s.PreimageData (R.fiberEquivalence T).inverse := by
  letI : (R.fiberEquivalence T).functor.CommShift ℤ :=
    R.fiberEquivalenceFunctorCommShift T
  letI : (R.fiberEquivalence T).inverse.CommShift ℤ :=
    (R.fiberEquivalence T).commShiftInverse ℤ
  letI : (R.fiberEquivalence T).CommShift ℤ :=
    R.fiberEquivalenceCommShift T
  letI : (R.fiberEquivalence T).IsTriangulated :=
    R.fiberEquivalenceIsTriangulated T
  exact s.preimageData_equivalence (R.fiberEquivalence T).symm

/-- Transport a slicing from an abstract fiber to its bounded coherent
realization through the inverse equivalence. -/
noncomputable def inversePreimage
    (R : BoundedCoherentDerivedRealization F) (T : SchemeBaseChange S)
    (s : Slicing (F.Fiber T)) : Slicing T.BoundedCoherentDerivedFiber := by
  letI : (R.fiberEquivalence T).functor.CommShift ℤ :=
    R.fiberEquivalenceFunctorCommShift T
  letI : (R.fiberEquivalence T).inverse.CommShift ℤ :=
    (R.fiberEquivalence T).commShiftInverse ℤ
  letI : (R.fiberEquivalence T).CommShift ℤ :=
    R.fiberEquivalenceCommShift T
  letI : (R.fiberEquivalence T).IsTriangulated :=
    R.fiberEquivalenceIsTriangulated T
  exact s.preimage (R.fiberEquivalence T).inverse
    (R.inversePreimageData T s)

/-- Transport the genuine bounded coherent A.17 output through a bounded
coherent realization.  The result is preimage data for the abstract family
pullback, not a caller-supplied preimage witness. -/
theorem preimageData (R : BoundedCoherentDerivedRealization F)
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    (s : Slicing (F.Fiber T))
    (h : SchemeBaseChange.BoundedCoherentPullbackInducingData f
      (R.inversePreimage T s)) :
    s.PreimageData (F.pull f) := by
  letI : (R.fiberEquivalence T).functor.CommShift ℤ :=
    R.fiberEquivalenceFunctorCommShift T
  letI : (R.fiberEquivalence T).inverse.CommShift ℤ :=
    (R.fiberEquivalence T).commShiftInverse ℤ
  letI : (R.fiberEquivalence T).CommShift ℤ :=
    R.fiberEquivalenceCommShift T
  letI : (R.fiberEquivalence T).IsTriangulated :=
    R.fiberEquivalenceIsTriangulated T
  letI : (R.fiberEquivalence U).functor.CommShift ℤ :=
    R.fiberEquivalenceFunctorCommShift U
  letI : (R.fiberEquivalence U).inverse.CommShift ℤ :=
    (R.fiberEquivalence U).commShiftInverse ℤ
  letI : (R.fiberEquivalence U).CommShift ℤ :=
    R.fiberEquivalenceCommShift U
  letI : (R.fiberEquivalence U).IsTriangulated :=
    R.fiberEquivalenceIsTriangulated U
  let hT := R.inversePreimageData T s
  let hGeom := h.toPreimageData
  let hPost : s.PreimageData
      (SchemeBaseChange.boundedCoherentDerivedPullback f ⋙
        (R.fiberEquivalence T).inverse) :=
    hT.comp hGeom.preimageData
  let sU := s.preimage _ hPost
  let hU := sU.preimageData_equivalence (R.fiberEquivalence U)
  have hU' : (s.preimage _ hPost).PreimageData
      (R.fiberEquivalence U).functor := by
    simpa [sU] using hU
  exact (hPost.comp hU').ofIso (R.pullbackIso f).symm

end BoundedCoherentDerivedRealization

/-- Geometric inducing data for a pre-stability family.  Unlike
`FiberPreStabilityBaseChangeData`, this structure does not contain a
`Slicing.PreimageData` field: every such witness is constructed from the
actual bounded coherent pullback and its phase-indexed A.17 output. -/
structure GeometricPreStabilityBaseChangeData
    {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
    [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
    [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
      SchemeBaseChange.HasCoherentPullback f]
    (R : BoundedCoherentDerivedRealization F)
    {V : Type uV} [AddCommGroup V]
    (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
    (sigma : ∀ T, PreStabilityCondition.WithClassMap
      (F.Fiber T) (classMap T)) where
  /-- The common numerical class is invariant under pullback. -/
  classMapCompatible : F.CompatibleClassMaps V classMap
  /-- All fibers use the same central charge. -/
  chargeCompatible : ∀ {T U} (_ : T ⟶ U), (sigma T).Z = (sigma U).Z
  /-- The geometric inducing premises on the actual bounded coherent
  pullback. -/
  inducing : ∀ {T U} (f : T ⟶ U),
    SchemeBaseChange.BoundedCoherentPullbackInducingData f
      (R.inversePreimage T (sigma T).slicing)
  /-- The supplied target slicing is the one induced geometrically.  The
  preimage witness occurring here is constructed from `inducing`; it is not a
  field of this structure. -/
  slicingCompatible : ∀ {T U} (f : T ⟶ U),
    (sigma U).slicing = (sigma T).slicing.preimage (F.pull f)
    (R.preimageData f (sigma T).slicing (inducing f))

namespace GeometricPreStabilityBaseChangeData

variable {S : Scheme.{u}} {F : SchemeTriangulatedFiberFamily S}
  [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
  [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
    SchemeBaseChange.HasCoherentPullback f]
  {R : BoundedCoherentDerivedRealization F}
  {V : Type uV} [AddCommGroup V]
  {classMap : ∀ T, K₀ (F.Fiber T) →+ V}
  {sigma : ∀ T, PreStabilityCondition.WithClassMap
    (F.Fiber T) (classMap T)}

/-- Export the ordinary categorical base-change witness.  Its preimage field
is built from bounded coherent geometry and the inducing theorem. -/
theorem toFiberPreStabilityBaseChangeData
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    FiberPreStabilityBaseChangeData F classMap sigma where
  classMap_compatible := h.classMapCompatible
  charge_compatible := h.chargeCompatible
  preimageData := fun f ↦ R.preimageData f _ (h.inducing f)
  slicing_compatible := h.slicingCompatible

/-- Phase membership is detected by the geometrically realized bounded
coherent pullback. -/
theorem phase_iff
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma)
    {T U : SchemeBaseChange S} (f : T ⟶ U) (phi : ℝ) (E : F.Fiber U) :
    (sigma U).slicing.P phi E ↔
      (sigma T).slicing.P phi ((F.pull f).obj E) :=
  h.toFiberPreStabilityBaseChangeData.phase_iff f phi E

/-- The geometric witness inherits pseudofunctorial composition compatibility
after its pullbacks have been identified with bounded coherent derived
pullback. -/
theorem phase_iff_comp
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma)
    {T U V' : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V')
    (phi : ℝ) (E : F.Fiber V') :
    (sigma V').slicing.P phi E ↔
      (sigma T).slicing.P phi ((F.pull f).obj ((F.pull g).obj E)) :=
  h.toFiberPreStabilityBaseChangeData.phase_iff_comp f g phi E

end GeometricPreStabilityBaseChangeData

end

end AlgebraicGeometry.DerivedCategory.Families
