/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackCoherence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducingBoundary

/-!
# Scheme-derived pullback realizes categorical inducing data

This file connects the concrete exact derived pullback on scheme fibers to the
honest preimage-slicing boundary.  A `DerivedPullbackInducingData` records the
actual phase-indexed t-structures produced by the owned A.17 theorem for
`SchemeBaseChange.derivedPullback f`.  The owned Corollary-A.23 truncation
argument then constructs the preimage slicing; no global theorem parameter or
caller-supplied `Slicing.PreimageData` is accepted.  Flatness is used only to
install exact derived pullback.

Once explicit preimage data has been obtained, identity and composition use
the coherence from `Phase.Transfer.Basic` and the exact derived-pullback unit
and compositor.  No geometric slicing, openness, relative HN, bounded
coherent/perfect restriction, or conclusion of Theorem 22.2 is asserted.
-/

namespace AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Explicit preimage-slicing data for the concrete exact derived pullback
along one morphism of scheme base changes. -/
structure DerivedPullbackPreimageData {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsExactPullback f]
    (s : Slicing T.DerivedFiber) : Prop where
  /-- The two non-formal slicing axioms for detecting phases by derived
  pullback. -/
  preimageData : s.PreimageData (derivedPullback f)

namespace DerivedPullbackPreimageData

variable {T U : SchemeBaseChange S} {f : T ⟶ U} [IsExactPullback f]
  {s : Slicing T.DerivedFiber}

/-- The slicing on the target derived fiber constructed from the explicit
preimage witness. -/
def preimage (h : DerivedPullbackPreimageData f s) : Slicing U.DerivedFiber :=
  s.preimage (derivedPullback f) h.preimageData

/-- Exact derived pullback along an identity carries the canonical identity
preimage witness across the derived unit isomorphism. -/
theorem identity (T : SchemeBaseChange S) (s : Slicing T.DerivedFiber) :
    DerivedPullbackPreimageData (f := 𝟙 T) s where
  preimageData :=
    s.preimageData_id.ofIso (derivedPullbackId T).symm

/-- The slicing induced through exact derived pullback along an identity is
the original slicing. -/
@[simp]
theorem preimage_identity (T : SchemeBaseChange S)
    (s : Slicing T.DerivedFiber) :
    (identity T s).preimage = s := by
  calc
    (identity T s).preimage =
        s.preimage (Functor.id T.DerivedFiber) s.preimageData_id :=
      Slicing.preimage_iso s _ _ s.preimageData_id
        (derivedPullbackId T).symm
    _ = s := s.preimage_id

/-- Explicit derived-pullback preimage witnesses compose and are transported
from the iterated functor to pullback along the composite by the derived
compositor. -/
theorem comp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] [IsExactPullback g]
    {s : Slicing T.DerivedFiber}
    (hf : DerivedPullbackPreimageData f s)
    (hg : DerivedPullbackPreimageData g hf.preimage) :
    DerivedPullbackPreimageData (f ≫ g) s where
  preimageData :=
    (hf.preimageData.comp hg.preimageData).ofIso
      (derivedPullbackComp f g)

/-- The slicing induced along a composite exact derived pullback agrees with
the slicing obtained in two stages. -/
@[simp]
theorem preimage_comp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] [IsExactPullback g]
    {s : Slicing T.DerivedFiber}
    (hf : DerivedPullbackPreimageData f s)
    (hg : DerivedPullbackPreimageData g hf.preimage) :
    (hf.comp f g hg).preimage = hg.preimage := by
  calc
    (hf.comp f g hg).preimage =
        s.preimage (derivedPullback g ⋙ derivedPullback f)
          (hf.preimageData.comp hg.preimageData) :=
      Slicing.preimage_iso s _ _
        (hf.preimageData.comp hg.preimageData)
        (derivedPullbackComp f g)
    _ = hg.preimage := Slicing.preimage_comp s _ _ _ _

end DerivedPullbackPreimageData

/-- The phase-indexed A.17 output specialized to concrete exact derived
pullback.  This is the recognition-formula output consumed by the owned
Corollary-A.23 theorem, not a preconstructed slicing witness. -/
structure DerivedPullbackInducingData {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsExactPullback f]
    (s : Slicing T.DerivedFiber) where
  /-- The induced source t-structures with the A.8 recognition formulas. -/
  inducedTStructures : s.InducedTStructures (derivedPullback f)

namespace DerivedPullbackInducingData

variable {T U : SchemeBaseChange S} {f : T ⟶ U} [IsExactPullback f]
  {s : Slicing T.DerivedFiber}

/-- The exact derived-pullback unit transports the inhabited identity A.17
model to the concrete scheme-derived identity pullback. -/
def identity (T : SchemeBaseChange S) (s : Slicing T.DerivedFiber) :
    DerivedPullbackInducingData (𝟙 T) s where
  inducedTStructures := s.inducedTStructuresId.ofIso
    (derivedPullbackId T).symm

/-- Apply the owned finite phase-truncation theorem to the actual A.17
output. -/
theorem toPreimageData (h : DerivedPullbackInducingData f s) :
    DerivedPullbackPreimageData f s where
  preimageData := h.inducedTStructures.preimageData

/-- For a flat scheme morphism, Mathlib flatness supplies exact derived
pullback; the A.17 output remains the honest geometric input. -/
theorem toPreimageData_of_flat {T U : SchemeBaseChange S}
    (f : T ⟶ U) [Flat f.left] (s : Slicing T.DerivedFiber)
    (h : DerivedPullbackInducingData f s) :
    DerivedPullbackPreimageData f s :=
  h.toPreimageData

end DerivedPullbackInducingData

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
