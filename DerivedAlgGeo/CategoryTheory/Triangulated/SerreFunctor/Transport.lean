/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Classification

/-!
# Ext profiles and transport by Serre-compatible equivalences

The special objects in the two Enriques papers have two logically separate
ingredients: a computation of all shifted self-Hom spaces and an isomorphism
between the Serre image and the appropriate shift.  `SphericalExtProfile` and
`PseudoprojectiveExtProfile` isolate the computation; their constructors add
the Serre isomorphism to recover `IsSphericalObject` and
`IsPseudoprojectiveObject`.

The second part proves the equivalence-transport step used in both refined
Torelli arguments.  A `SerreCompatibleEquivalence` is an equivalence equipped
with the linear, additive, shift, and Serre comparison data that the proof
actually consumes.  These fields are explicit because the general Serre
uniqueness/conjugation lane (#896--#898) has not yet produced them
automatically.
-/

universe w v v' u u'

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasShift C ℤ]

/-- The shifted self-Hom computation for an `n`-spherical object, before the
Serre-action statement is added. -/
structure SphericalExtProfile (n : ℕ) (E : C) : Prop where
  /-- Self-Homs vanish away from degrees zero and `n`. -/
  vanishing : ∀ i : ℤ, i ≠ 0 → i ≠ (n : ℤ) → ∀ f : E ⟶ E⟦i⟧, f = 0
  /-- The degree-zero self-Hom is one-dimensional. -/
  end_one : Nonempty ((E ⟶ E) ≃ₗ[k] k)
  /-- The degree-`n` self-Hom is one-dimensional. -/
  top_one : Nonempty ((E ⟶ E⟦(n : ℤ)⟧) ≃ₗ[k] k)

/-- The shifted self-Hom computation for an `n`-pseudoprojective object,
before the Serre-action statement is added. -/
structure PseudoprojectiveExtProfile (n : ℕ) (E : C) : Prop where
  /-- Every self-Hom in degrees zero through `n` is one-dimensional. -/
  inRange_one : ∀ i : ℕ, i ≤ n → Nonempty ((E ⟶ E⟦(i : ℤ)⟧) ≃ₗ[k] k)
  /-- Self-Homs vanish outside degrees zero through `n`. -/
  vanishing : ∀ i : ℤ, (i < 0 ∨ (n : ℤ) < i) → ∀ f : E ⟶ E⟦i⟧, f = 0

namespace SphericalExtProfile

variable {n : ℕ} {E : C} (h : SphericalExtProfile (k := k) n E)

include h

/-- Add the Serre-shift identification to an Ext computation. -/
theorem toIsSphericalObject (D : SerreFunctorData k C)
    (serreShift : Nonempty (D.S.obj E ≅ E⟦(n : ℤ)⟧)) :
    IsSphericalObject D n E where
  vanishing := h.vanishing
  end_one := h.end_one
  top_one := h.top_one
  serre_shift := serreShift

end SphericalExtProfile

namespace PseudoprojectiveExtProfile

variable {n : ℕ} {E : C} (h : PseudoprojectiveExtProfile (k := k) n E)

include h

/-- Add the Serre-shift identification to an Ext computation. -/
theorem toIsPseudoprojectiveObject (D : SerreFunctorData k C)
    (serreShift : Nonempty (D.S.obj E ≅ E⟦(n : ℤ)⟧)) :
    IsPseudoprojectiveObject D n E where
  inRange_one := h.inRange_one
  vanishing := h.vanishing
  serre_shift := serreShift

end PseudoprojectiveExtProfile

section Transport

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
  [HasShift D ℤ]

/-- The Hom-bijection of a fully faithful linear functor, bundled as a linear
equivalence. -/
private noncomputable def homLinearEquiv (F : Functor C D) [F.Additive]
    [F.Linear k] (hF : F.FullyFaithful) (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  map_add' _ _ := F.map_add
  map_smul' := by intro r f; exact F.map_smul r f
  invFun := hF.preimage
  left_inv := hF.preimage_map
  right_inv := hF.map_preimage

/-- A fully faithful linear functor commuting with shifts identifies every
shifted Hom-space with the corresponding shifted Hom-space of the images. -/
private noncomputable def homShiftLinearEquiv (F : Functor C D) [F.Additive]
    [F.Linear k] [F.CommShift ℤ] (hF : F.FullyFaithful) (X Y : C) (i : ℤ) :
    (X ⟶ Y⟦i⟧) ≃ₗ[k] (F.obj X ⟶ (F.obj Y)⟦i⟧) :=
  (homLinearEquiv (k := k) F hF X (Y⟦i⟧)).trans
    (Linear.homCongr k (Iso.refl (F.obj X)) ((F.commShiftIso i).app Y))

namespace SphericalExtProfile

variable {n : ℕ} {E : C} (h : SphericalExtProfile (k := k) n E)

include h

/-- Spherical Ext computations transport through a fully faithful linear
shift-compatible functor. -/
theorem map (F : Functor C D) [F.Additive] [F.Linear k]
    [F.CommShift ℤ] (hF : F.FullyFaithful) :
    SphericalExtProfile (k := k) n (F.obj E) where
  vanishing i hi₀ hin f := by
    let e := homShiftLinearEquiv (k := k) F hF E E i
    apply e.symm.injective
    simpa using h.vanishing i hi₀ hin (e.symm f)
  end_one :=
    ⟨(homLinearEquiv (k := k) F hF E E).symm.trans h.end_one.some⟩
  top_one :=
    ⟨(homShiftLinearEquiv (k := k) F hF E E (n : ℤ)).symm.trans h.top_one.some⟩

end SphericalExtProfile

namespace PseudoprojectiveExtProfile

variable {n : ℕ} {E : C} (h : PseudoprojectiveExtProfile (k := k) n E)

include h

/-- Pseudoprojective Ext computations transport through a fully faithful
linear shift-compatible functor. -/
theorem map (F : Functor C D) [F.Additive] [F.Linear k]
    [F.CommShift ℤ] (hF : F.FullyFaithful) :
    PseudoprojectiveExtProfile (k := k) n (F.obj E) where
  inRange_one i hi :=
    ⟨(homShiftLinearEquiv (k := k) F hF E E (i : ℤ)).symm.trans
      (h.inRange_one i hi).some⟩
  vanishing i hi f := by
    let e := homShiftLinearEquiv (k := k) F hF E E i
    apply e.symm.injective
    simpa using h.vanishing i hi (e.symm f)

end PseudoprojectiveExtProfile

/-- An equivalence together with the exact comparison data needed to transport
Serre-theoretic objects.

The functor is already fully faithful and essentially surjective because it
is an equivalence.  Additivity, linearity, shift compatibility, and the
intertwining of the two chosen Serre functors are kept as visible fields. -/
structure SerreCompatibleEquivalence
    (S_C : SerreFunctorData k C) (S_D : SerreFunctorData k D) where
  /-- The underlying equivalence. -/
  equiv : C ≌ D
  /-- The forward functor is additive. -/
  functorAdditive : equiv.functor.Additive
  /-- The forward functor is `k`-linear. -/
  functorLinear : equiv.functor.Linear k
  /-- The forward functor commutes coherently with integral shifts. -/
  functorCommShift : equiv.functor.CommShift ℤ
  /-- The forward functor intertwines the chosen Serre functors. -/
  serreIso : S_C.S ⋙ equiv.functor ≅ equiv.functor ⋙ S_D.S
  /-- The inverse functor is additive. -/
  inverseAdditive : equiv.inverse.Additive
  /-- The inverse functor is `k`-linear. -/
  inverseLinear : equiv.inverse.Linear k
  /-- The inverse functor commutes coherently with integral shifts. -/
  inverseCommShift : equiv.inverse.CommShift ℤ
  /-- The inverse functor intertwines the chosen Serre functors. -/
  inverseSerreIso : S_D.S ⋙ equiv.inverse ≅ equiv.inverse ⋙ S_C.S

namespace SerreCompatibleEquivalence

variable {S_C : SerreFunctorData k C} {S_D : SerreFunctorData k D}
  (F : SerreCompatibleEquivalence S_C S_D)

/-- Reverse a Serre-compatible equivalence, retaining all of its linear and
shift comparison data. -/
def symm : SerreCompatibleEquivalence S_D S_C where
  equiv := F.equiv.symm
  functorAdditive := F.inverseAdditive
  functorLinear := F.inverseLinear
  functorCommShift := F.inverseCommShift
  serreIso := F.inverseSerreIso
  inverseAdditive := F.functorAdditive
  inverseLinear := F.functorLinear
  inverseCommShift := F.functorCommShift
  inverseSerreIso := F.serreIso

/-- A spherical object remains spherical under a Serre-compatible
equivalence. -/
theorem mapSpherical {n : ℕ} {E : C}
    (h : IsSphericalObject S_C n E) :
    IsSphericalObject S_D n (F.equiv.functor.obj E) := by
  letI : F.equiv.functor.Additive := F.functorAdditive
  letI : F.equiv.functor.Linear k := F.functorLinear
  letI : F.equiv.functor.CommShift ℤ := F.functorCommShift
  let ext : SphericalExtProfile (k := k) n E :=
    { vanishing := h.vanishing
      end_one := h.end_one
      top_one := h.top_one }
  apply (ext.map F.equiv.functor F.equiv.fullyFaithfulFunctor).toIsSphericalObject S_D
  exact ⟨(F.serreIso.app E).symm ≪≫
    F.equiv.functor.mapIso h.serre_shift.some ≪≫
    (F.equiv.functor.commShiftIso (n : ℤ)).app E⟩

/-- A pseudoprojective object remains pseudoprojective under a
Serre-compatible equivalence. -/
theorem mapPseudoprojective {n : ℕ} {E : C}
    (h : IsPseudoprojectiveObject S_C n E) :
    IsPseudoprojectiveObject S_D n (F.equiv.functor.obj E) := by
  letI : F.equiv.functor.Additive := F.functorAdditive
  letI : F.equiv.functor.Linear k := F.functorLinear
  letI : F.equiv.functor.CommShift ℤ := F.functorCommShift
  let ext : PseudoprojectiveExtProfile (k := k) n E :=
    { inRange_one := h.inRange_one
      vanishing := h.vanishing }
  apply (ext.map F.equiv.functor F.equiv.fullyFaithfulFunctor).toIsPseudoprojectiveObject S_D
  exact ⟨(F.serreIso.app E).symm ≪≫
    F.equiv.functor.mapIso h.serre_shift.some ≪≫
    (F.equiv.functor.commShiftIso (n : ℤ)).app E⟩

/-- A Serre-compatible equivalence preserves and reflects spherical
objects. -/
theorem spherical_iff {n : ℕ} {E : C} :
    IsSphericalObject S_D n (F.equiv.functor.obj E) ↔
      IsSphericalObject S_C n E := by
  constructor
  · intro h
    exact (F.symm.mapSpherical h).of_iso (F.equiv.unitIso.app E).symm
  · exact F.mapSpherical

/-- A Serre-compatible equivalence preserves and reflects pseudoprojective
objects. -/
theorem pseudoprojective_iff {n : ℕ} {E : C} :
    IsPseudoprojectiveObject S_D n (F.equiv.functor.obj E) ↔
      IsPseudoprojectiveObject S_C n E := by
  constructor
  · intro h
    exact (F.symm.mapPseudoprojective h).of_iso
      (F.equiv.unitIso.app E).symm
  · exact F.mapPseudoprojective

/-- Being a shift of an object is preserved by a shift-compatible
equivalence. -/
theorem mapIsShiftOf {E E' : C} (h : IsShiftOf E E') :
    IsShiftOf (F.equiv.functor.obj E) (F.equiv.functor.obj E') := by
  letI : F.equiv.functor.CommShift ℤ := F.functorCommShift
  obtain ⟨p, ⟨e⟩⟩ := h
  exact ⟨p, ⟨F.equiv.functor.mapIso e ≪≫
    (F.equiv.functor.commShiftIso p).app E'⟩⟩

/-- A Serre-compatible equivalence preserves and reflects the relation of
being an integral shift. -/
theorem isShiftOf_iff {E E' : C} :
    IsShiftOf (F.equiv.functor.obj E) (F.equiv.functor.obj E') ↔
      IsShiftOf E E' := by
  constructor
  · intro h
    obtain ⟨p, ⟨e⟩⟩ := F.symm.mapIsShiftOf h
    exact ⟨p, ⟨F.equiv.unitIso.app E ≪≫ e ≪≫
      (shiftFunctor C p).mapIso (F.equiv.unitIso.app E').symm⟩⟩
  · exact F.mapIsShiftOf

/-- Graded orthogonality is preserved by a shift-compatible equivalence. -/
theorem mapIsGradedOrthogonal {E E' : C} (h : IsGradedOrthogonal E E') :
    IsGradedOrthogonal (F.equiv.functor.obj E)
      (F.equiv.functor.obj E') := by
  letI : F.equiv.functor.Additive := F.functorAdditive
  letI : F.equiv.functor.Linear k := F.functorLinear
  letI : F.equiv.functor.CommShift ℤ := F.functorCommShift
  intro p f
  let e := homShiftLinearEquiv (k := k) F.equiv.functor
    F.equiv.fullyFaithfulFunctor E E' p
  apply e.symm.injective
  simpa using h p (e.symm f)

/-- A Serre-compatible equivalence preserves and reflects graded
orthogonality. -/
theorem isGradedOrthogonal_iff {E E' : C} :
    IsGradedOrthogonal (F.equiv.functor.obj E)
        (F.equiv.functor.obj E') ↔
      IsGradedOrthogonal E E' := by
  constructor
  · intro h p f
    have h' := F.symm.mapIsGradedOrthogonal h
    let e := Linear.homCongr k (F.equiv.unitIso.app E)
      ((shiftFunctor C p).mapIso (F.equiv.unitIso.app E'))
    exact e.injective ((h' p (e f)).trans e.map_zero.symm)
  · exact F.mapIsGradedOrthogonal

end SerreCompatibleEquivalence

end Transport

end CategoryTheory.SerreFunctor
