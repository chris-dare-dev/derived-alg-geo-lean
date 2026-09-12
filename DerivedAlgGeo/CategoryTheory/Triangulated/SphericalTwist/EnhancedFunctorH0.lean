/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeExactness
import DerivedAlgGeo.Algebra.Homology.DGCategory.QuasiEquivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The four Anno--Logvinenko triangles, as functors on `H⁰`

`EnhancedAdjunctionCones` holds the four dg cone choices attached to a dg
functor with a left and a right dg adjoint.  Each one is a `CounitConeData` or
a `UnitConeData`, so each gives a functor into triangles of `H⁰` by the
generic construction, with every value distinguished:

| triangle | in | shape |
| --- | --- | --- |
| twist | `H⁰ B` | `S R X ⟶ X ⟶ T X ⟶ (S R X)⟦1⟧` |
| dual twist | `H⁰ B` | `C X⟦-1⟧ ⟶ X ⟶ S L X ⟶ C X` |
| cotwist | `H⁰ A` | `C' X⟦-1⟧ ⟶ X ⟶ R S X ⟶ C' X` |
| dual cotwist | `H⁰ A` | `L S X ⟶ X ⟶ T' X ⟶ (L S X)⟦1⟧` |

These are Anno--Logvinenko's four triangles read as triangles *of functors*,
which is the form their argument uses.

## The shift on two of the four is one inverse rotation

`EnhancedAdjunctionCones` stores the dual twist and the cotwist as *unshifted*
cones, because the conventional functors are their `⟦-1⟧` shifts.  Rather than
shift the cone functor and then rebuild a triangle, the triangle of the
unshifted cone is inversely rotated: `invRotate` sends `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` to
`Z⟦-1⟧ ⟶ X ⟶ Y ⟶ Z`, so it applies the shift and reorders in one step, and
`Pretriangulated.inv_rot_of_distTriang` carries distinguishedness across for
free.

The unshifted triangles are kept under their `Cone` names, since the
`TwistCotwistEquivalenceConditions` are stated against the unshifted cone
functors.

The conventional shifted dg functors are named `dualTwistFunctor` and
`cotwistFunctor`.  Their `H⁰` functors are naturally isomorphic to the
corresponding unshifted cone functor followed by the ordinary `[-1]` shift.
Thus the first vertices below are values of the named dg functors on the nose,
while ordinary categorical properties can be transported through a reusable
comparison.

## What is not claimed

That the functor is spherical, or that any relation among the four triangles
holds.  `TwistCotwistEquivalenceConditions` records the usual equivalence pair
as data
and no theorem upgrades it; that implication is Anno--Logvinenko's, and it runs
through Morita quasi-functors and higher cone coherence that this repository
does not have.  Exactness below does include the conventional shifted dual
twist and cotwist: it is transported from their unshifted cones through the
sign-correct shifted-functor interface.

Nothing here is new mathematics.  Every declaration is a thin wrapper over
the generic cone-triangle, cone-exactness/3-by-3, or shifted-functor exactness
layer, which is the point of having built those layers first.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

namespace EnhancedAdjunctionCones

variable {A : Type u} {B : Type u'} [DGCategory.{v} A] [DGCategory.{v} B]
  {S : DGFunctor A B} {L R : DGFunctor B A} (P : EnhancedAdjunctionCones S L R)

/-! ### The two triangles in `H⁰ B` -/

section Target

variable [IsPretriangulated B]

/-- **The twist triangle.**  `S R X ⟶ X ⟶ T X ⟶ (S R X)⟦1⟧`, from the counit
of the right adjunction. -/
noncomputable def twistTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  DGAdjunction.CounitConeData.twistTriangleFunctor P.rightAdj P.twist

theorem twistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.twistTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
    P.rightAdj P.twist X

/-- The first map of the twist triangle is the right adjunction's counit. -/
theorem twistTriangleFunctor_obj_mor₁ (X : H0 B) :
    ((P.twistTriangleFunctor).obj X).mor₁ = P.rightAdj.h0Counit.app X :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₁ P.rightAdj P.twist X

/-- **The unshifted dual-twist triangle.**  `X ⟶ S L X ⟶ C X ⟶ X⟦1⟧`, from the
unit of the left adjunction.  The conventional dual twist is `C⟦-1⟧`. -/
noncomputable def dualTwistConeTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  DGAdjunction.UnitConeData.unitTriangleFunctor P.leftAdj P.dualTwistCone

theorem dualTwistConeTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.dualTwistConeTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mem_distinguishedTriangles
    P.leftAdj P.dualTwistCone X

/-- The first map of the unshifted dual-twist triangle is the left
adjunction's unit. -/
theorem dualTwistConeTriangleFunctor_obj_mor₁ (X : H0 B) :
    ((P.dualTwistConeTriangleFunctor).obj X).mor₁ = P.leftAdj.h0Unit.app X :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mor₁ P.leftAdj
    P.dualTwistCone X

/-- **The dual-twist triangle.**  The inverse rotation of the unshifted one,
so its first vertex is `C X⟦-1⟧`, the dual twist:

`C X⟦-1⟧ ⟶ X ⟶ S L X ⟶ C X`.

Inverse rotation applies the shift and reorders in one step, so the triangle
construction itself need not be rebuilt from the separately named shifted
cone functor. -/
noncomputable def dualTwistTriangleFunctor : H0 B ⥤ Triangle (H0 B) :=
  P.dualTwistConeTriangleFunctor ⋙ invRotate (H0 B)

theorem dualTwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 B) :
    (P.dualTwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles B :=
  inv_rot_of_distTriang _
    (P.dualTwistConeTriangleFunctor_obj_mem_distinguishedTriangles X)

/-- The first vertex of the dual-twist triangle is the dual twist: the value of
the dg cone functor, shifted by `-1`. -/
theorem dualTwistTriangleFunctor_obj_obj₁ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₁ =
      P.dualTwistFunctor.h0.obj X :=
  rfl

/-- The `H⁰` dual twist is naturally the unshifted cone followed by `[-1]`. -/
noncomputable def dualTwistFunctorH0Iso :
    P.dualTwistFunctor.h0 ≅
      P.dualTwistConeFunctor.h0 ⋙ shiftFunctor (H0 B) (-1 : ℤ) :=
  DGFunctor.shiftedFunctorH0Iso P.dualTwistConeFunctor (-1 : ℤ)

@[simp]
theorem dualTwistTriangleFunctor_obj_obj₂ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₂ = X :=
  rfl

@[simp]
theorem dualTwistTriangleFunctor_obj_obj₃ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).obj₃ = (L.comp S).h0.obj X :=
  rfl

/-- The second map of the dual-twist triangle is the left adjunction's unit:
inverse rotation moves the old first map into second place. -/
theorem dualTwistTriangleFunctor_obj_mor₂ (X : H0 B) :
    ((P.dualTwistTriangleFunctor).obj X).mor₂ = P.leftAdj.h0Unit.app X :=
  P.dualTwistConeTriangleFunctor_obj_mor₁ X

end Target

/-! ### The two triangles in `H⁰ A` -/

section Source

variable [IsPretriangulated A]

/-- **The unshifted cotwist triangle.**  `X ⟶ R S X ⟶ C' X ⟶ X⟦1⟧`, from the
unit of the right adjunction.  The conventional cotwist is `C'⟦-1⟧`. -/
noncomputable def cotwistConeTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  DGAdjunction.UnitConeData.unitTriangleFunctor P.rightAdj P.cotwistCone

theorem cotwistConeTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.cotwistConeTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mem_distinguishedTriangles
    P.rightAdj P.cotwistCone X

/-- The first map of the unshifted cotwist triangle is the right adjunction's
unit. -/
theorem cotwistConeTriangleFunctor_obj_mor₁ (X : H0 A) :
    ((P.cotwistConeTriangleFunctor).obj X).mor₁ = P.rightAdj.h0Unit.app X :=
  DGAdjunction.UnitConeData.unitTriangleFunctor_obj_mor₁ P.rightAdj
    P.cotwistCone X

/-- **The cotwist triangle.**  The inverse rotation of the unshifted one, so
its first vertex is `C' X⟦-1⟧`, the cotwist:

`C' X⟦-1⟧ ⟶ X ⟶ R S X ⟶ C' X`. -/
noncomputable def cotwistTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  P.cotwistConeTriangleFunctor ⋙ invRotate (H0 A)

theorem cotwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.cotwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  inv_rot_of_distTriang _
    (P.cotwistConeTriangleFunctor_obj_mem_distinguishedTriangles X)

/-- The first vertex of the cotwist triangle is the cotwist: the value of the
dg cone functor, shifted by `-1`. -/
theorem cotwistTriangleFunctor_obj_obj₁ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₁ =
      P.cotwistFunctor.h0.obj X :=
  rfl

/-- The `H⁰` cotwist is naturally the unshifted cone followed by `[-1]`. -/
noncomputable def cotwistFunctorH0Iso :
    P.cotwistFunctor.h0 ≅
      P.cotwistConeFunctor.h0 ⋙ shiftFunctor (H0 A) (-1 : ℤ) :=
  DGFunctor.shiftedFunctorH0Iso P.cotwistConeFunctor (-1 : ℤ)

@[simp]
theorem cotwistTriangleFunctor_obj_obj₂ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₂ = X :=
  rfl

@[simp]
theorem cotwistTriangleFunctor_obj_obj₃ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).obj₃ = (S.comp R).h0.obj X :=
  rfl

/-- The second map of the cotwist triangle is the right adjunction's unit. -/
theorem cotwistTriangleFunctor_obj_mor₂ (X : H0 A) :
    ((P.cotwistTriangleFunctor).obj X).mor₂ = P.rightAdj.h0Unit.app X :=
  P.cotwistConeTriangleFunctor_obj_mor₁ X

/-- **The dual-cotwist triangle.**  `L S X ⟶ X ⟶ T' X ⟶ (L S X)⟦1⟧`, from the
counit of the left adjunction. -/
noncomputable def dualCotwistTriangleFunctor : H0 A ⥤ Triangle (H0 A) :=
  DGAdjunction.CounitConeData.twistTriangleFunctor P.leftAdj P.dualCotwist

theorem dualCotwistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 A) :
    (P.dualCotwistTriangleFunctor).obj X ∈ H0.distinguishedTriangles A :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mem_distinguishedTriangles
    P.leftAdj P.dualCotwist X

/-- The first map of the dual-cotwist triangle is the left adjunction's
counit. -/
theorem dualCotwistTriangleFunctor_obj_mor₁ (X : H0 A) :
    ((P.dualCotwistTriangleFunctor).obj X).mor₁ = P.leftAdj.h0Counit.app X :=
  DGAdjunction.CounitConeData.twistTriangleFunctor_obj_mor₁ P.leftAdj
    P.dualCotwist X

end Source

/-! ### The equivalence conditions, spent -/

section Equivalences

/-- **The twist is an autoequivalence of `H⁰ B`.**

`TwistCotwistEquivalenceConditions` records that the twist is a
quasi-equivalence, and `DGFunctor.h0Equivalence` turns a quasi-equivalence into
an equivalence on `H⁰`.  This is the first categorical invertibility statement
about a twist in this repository: everything before it was either numerical, on
`K₀`, or a construction with no invertibility attached.

No pretriangulated hypothesis is needed: this is an equivalence of ordinary
categories, and the cone triangles above play no part in it.  This definition
alone says nothing about exactness; `twistH0EquivalenceIsTriangulated` combines
it with the exactness package below.  Nothing here calls the functor spherical:
the Anno--Logvinenko implication from this pair of conditions to all four
spherical conditions is still out of reach. -/
noncomputable def twistH0Equivalence
    (h : TwistCotwistEquivalenceConditions P) : H0 B ≌ H0 B :=
  P.twistFunctor.h0Equivalence h.twist

/-- **The unshifted cotwist cone is an autoequivalence of `H⁰ A`.**

The conventional cotwist is its `⟦-1⟧` shift; requiring the unshifted cone
functor to be a quasi-equivalence is the shift-free form of the same
condition. -/
noncomputable def cotwistConeH0Equivalence
    (h : TwistCotwistEquivalenceConditions P) : H0 A ≌ H0 A :=
  P.cotwistConeFunctor.h0Equivalence h.cotwist

/-- **The conventional cotwist is an autoequivalence of `H⁰ A`.**

The recorded condition is stated for the unshifted cone.  The reusable
shifted-functor comparison transports its induced `H⁰` equivalence across the
conventional `[-1]` shift.  This remains an equivalence of ordinary categories;
`cotwistH0EquivalenceIsTriangulated` separately packages its exactness, and no
sphericality is inferred here. -/
noncomputable def cotwistH0Equivalence
    [IsPretriangulated A]
    (h : TwistCotwistEquivalenceConditions P) : H0 A ≌ H0 A :=
  DGFunctor.shiftedFunctorH0Equivalence P.cotwistConeFunctor (-1 : ℤ)
    (P.cotwistConeFunctor.isEquivalence_h0 h.cotwist)

end Equivalences

/-! ### Exactness -/

section Shifts

/-- **The twist preserves shifts.**

Unconditional: every dg functor preserves shifts
(`DGFunctor.preservesShifts`), because a shift element is a closed two-sided
invertible element.  Half of exactness, and the free half; the cone half is
`twistPreservesChosenCones`, which does need `S` and `R` to carry it. -/
noncomputable def twistPreservesShifts :
    DGFunctor.PreservesShifts P.twistFunctor :=
  DGAdjunction.CounitConeData.preservesShifts P.rightAdj P.twist

/-- The unshifted cotwist cone preserves shifts too. -/
noncomputable def cotwistConePreservesShifts :
    DGFunctor.PreservesShifts P.cotwistConeFunctor :=
  DGAdjunction.UnitConeData.preservesShifts P.rightAdj P.cotwistCone

/-- The unshifted dual-twist cone preserves shifts. -/
noncomputable def dualTwistConePreservesShifts :
    DGFunctor.PreservesShifts P.dualTwistConeFunctor :=
  DGAdjunction.UnitConeData.preservesShifts P.leftAdj P.dualTwistCone

/-- The dual cotwist preserves shifts. -/
noncomputable def dualCotwistPreservesShifts :
    DGFunctor.PreservesShifts P.dualCotwistFunctor :=
  DGAdjunction.CounitConeData.preservesShifts P.leftAdj P.dualCotwist

/-- **The twist preserves chosen cones.**  The 3-by-3 lemma for the counit's
cone. -/
noncomputable def twistPreservesChosenCones
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    DGFunctor.PreservesChosenCones P.twistFunctor :=
  DGAdjunction.CounitConeData.preservesChosenCones P.rightAdj P.twist hSc hRc

/-- The unshifted cotwist cone preserves chosen cones too. -/
noncomputable def cotwistConePreservesChosenCones
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    DGFunctor.PreservesChosenCones P.cotwistConeFunctor :=
  DGAdjunction.UnitConeData.preservesChosenCones P.rightAdj P.cotwistCone hSc hRc

/-- The unshifted dual-twist cone preserves chosen cones when the left adjoint
and the original functor do. -/
noncomputable def dualTwistConePreservesChosenCones
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    DGFunctor.PreservesChosenCones P.dualTwistConeFunctor :=
  DGAdjunction.UnitConeData.preservesChosenCones P.leftAdj P.dualTwistCone hLc hSc

/-- The dual cotwist preserves chosen cones under the same left-adjunction
hypotheses. -/
noncomputable def dualCotwistPreservesChosenCones
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    DGFunctor.PreservesChosenCones P.dualCotwistFunctor :=
  DGAdjunction.CounitConeData.preservesChosenCones P.leftAdj P.dualCotwist hLc hSc

/-- The shift comparison on `H⁰` of the unshifted cotwist cone. -/
@[reducible]
noncomputable def cotwistConeH0CommShift [IsPretriangulated A] :
    P.cotwistConeFunctor.h0.CommShift ℤ :=
  DGFunctor.commShift _ P.cotwistConePreservesShifts

/-- The unshifted cotwist cone is exact on `H⁰` when `S` and `R` preserve the
chosen cones. -/
theorem cotwistConeH0IsTriangulated [IsPretriangulated A]
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : P.cotwistConeFunctor.h0.CommShift ℤ :=
      P.cotwistConeH0CommShift
    P.cotwistConeFunctor.h0.IsTriangulated :=
  DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
    P.cotwistConePreservesShifts (P.cotwistConePreservesChosenCones hSc hRc)

/-- The sign-correct shift comparison on the conventional cotwist. -/
@[reducible]
noncomputable def cotwistH0CommShift [IsPretriangulated A] :
    P.cotwistFunctor.h0.CommShift ℤ :=
  DGFunctor.shiftedFunctorH0CommShift P.cotwistConeFunctor (-1 : ℤ)
    P.cotwistConePreservesShifts

/-- The conventional cotwist is exact on `H⁰` when `S` and `R` preserve the
chosen cones. -/
theorem cotwistH0IsTriangulated [IsPretriangulated A]
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : P.cotwistFunctor.h0.CommShift ℤ := P.cotwistH0CommShift
    P.cotwistFunctor.h0.IsTriangulated :=
  DGFunctor.shiftedFunctorH0IsTriangulated P.cotwistConeFunctor (-1 : ℤ)
    P.cotwistConePreservesShifts (P.cotwistConePreservesChosenCones hSc hRc)

/-- The shift comparison on `H⁰` of the unshifted dual-twist cone. -/
@[reducible]
noncomputable def dualTwistConeH0CommShift [IsPretriangulated B] :
    P.dualTwistConeFunctor.h0.CommShift ℤ :=
  DGFunctor.commShift _ P.dualTwistConePreservesShifts

/-- The unshifted dual-twist cone is exact on `H⁰` when `L` and `S` preserve
the chosen cones. -/
theorem dualTwistConeH0IsTriangulated [IsPretriangulated B]
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    letI : P.dualTwistConeFunctor.h0.CommShift ℤ :=
      P.dualTwistConeH0CommShift
    P.dualTwistConeFunctor.h0.IsTriangulated :=
  DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
    P.dualTwistConePreservesShifts
      (P.dualTwistConePreservesChosenCones hLc hSc)

/-- The sign-correct shift comparison on the conventional dual twist. -/
@[reducible]
noncomputable def dualTwistH0CommShift [IsPretriangulated B] :
    P.dualTwistFunctor.h0.CommShift ℤ :=
  DGFunctor.shiftedFunctorH0CommShift P.dualTwistConeFunctor (-1 : ℤ)
    P.dualTwistConePreservesShifts

/-- The conventional dual twist is exact on `H⁰` when `L` and `S` preserve
the chosen cones. -/
theorem dualTwistH0IsTriangulated [IsPretriangulated B]
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    letI : P.dualTwistFunctor.h0.CommShift ℤ := P.dualTwistH0CommShift
    P.dualTwistFunctor.h0.IsTriangulated :=
  DGFunctor.shiftedFunctorH0IsTriangulated P.dualTwistConeFunctor (-1 : ℤ)
    P.dualTwistConePreservesShifts
      (P.dualTwistConePreservesChosenCones hLc hSc)

/-- The shift comparison on `H⁰` of the dual cotwist. -/
@[reducible]
noncomputable def dualCotwistH0CommShift [IsPretriangulated A] :
    P.dualCotwistFunctor.h0.CommShift ℤ :=
  DGFunctor.commShift _ P.dualCotwistPreservesShifts

/-- The dual cotwist is exact on `H⁰` when `L` and `S` preserve the chosen
cones. -/
theorem dualCotwistH0IsTriangulated [IsPretriangulated A]
    (hLc : DGFunctor.PreservesChosenCones L)
    (hSc : DGFunctor.PreservesChosenCones S) :
    letI : P.dualCotwistFunctor.h0.CommShift ℤ := P.dualCotwistH0CommShift
    P.dualCotwistFunctor.h0.IsTriangulated :=
  DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
    P.dualCotwistPreservesShifts (P.dualCotwistPreservesChosenCones hLc hSc)

/-- **The twist is exact on `H⁰`.**

Both dg-level capabilities are available for the twist, so `H⁰` of it is a
triangulated functor: it commutes with the shift and carries distinguished
triangles to distinguished triangles.  With the equivalence supplied by the
twist/cotwist conditions this is an exact autoequivalence, which is what the
word "twist" is supposed to mean.

Only the cone capabilities are hypotheses; the shift ones are free. -/
theorem twistH0IsTriangulated [IsPretriangulated B]
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : P.twistFunctor.h0.CommShift ℤ :=
      DGFunctor.commShift _ P.twistPreservesShifts
    P.twistFunctor.h0.IsTriangulated :=
  DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
    P.twistPreservesShifts (P.twistPreservesChosenCones hSc hRc)

/-- **The twist commutes with the shift on `H⁰`.**

`DGFunctor.commShift` spends the dg-level shift preservation on the ordinary
functor.  `twistH0IsTriangulated` adds the cone half. -/
@[reducible]
noncomputable def twistH0CommShift [IsPretriangulated B] :
    P.twistFunctor.h0.CommShift ℤ :=
  DGFunctor.commShift _ P.twistPreservesShifts

end Shifts

/-! ### Exact equivalences -/

section ExactEquivalences

set_option backward.isDefEq.respectTransparency false in
/-- Under the recorded equivalence condition and endpoint cone-preservation
hypotheses, the twist is a triangulated equivalence of `H⁰ B`.

The inverse shift comparison and its triangulatedness are the canonical ones
transported by Mathlib from the exact forward functor. -/
theorem twistH0EquivalenceIsTriangulated [IsPretriangulated B]
    (h : TwistCotwistEquivalenceConditions P)
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : (P.twistH0Equivalence h).functor.CommShift ℤ := P.twistH0CommShift
    letI : (P.twistH0Equivalence h).inverse.CommShift ℤ :=
      (P.twistH0Equivalence h).commShiftInverse ℤ
    letI : (P.twistH0Equivalence h).CommShift ℤ :=
      (P.twistH0Equivalence h).commShift_of_functor ℤ
    (P.twistH0Equivalence h).IsTriangulated := by
  letI : (P.twistH0Equivalence h).functor.CommShift ℤ := P.twistH0CommShift
  letI : (P.twistH0Equivalence h).inverse.CommShift ℤ :=
    (P.twistH0Equivalence h).commShiftInverse ℤ
  letI : (P.twistH0Equivalence h).CommShift ℤ :=
    (P.twistH0Equivalence h).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ (P.twistH0IsTriangulated hSc hRc)

set_option backward.isDefEq.respectTransparency false in
/-- Under the recorded equivalence condition and endpoint cone-preservation
hypotheses, the conventional cotwist is a triangulated equivalence of `H⁰ A`.

Its forward exactness uses the sign-correct `[-1]` package; Mathlib then
transports the compatible shift structure and exactness to the inverse. -/
theorem cotwistH0EquivalenceIsTriangulated [IsPretriangulated A]
    (h : TwistCotwistEquivalenceConditions P)
    (hSc : DGFunctor.PreservesChosenCones S)
    (hRc : DGFunctor.PreservesChosenCones R) :
    letI : (P.cotwistH0Equivalence h).functor.CommShift ℤ := P.cotwistH0CommShift
    letI : (P.cotwistH0Equivalence h).inverse.CommShift ℤ :=
      (P.cotwistH0Equivalence h).commShiftInverse ℤ
    letI : (P.cotwistH0Equivalence h).CommShift ℤ :=
      (P.cotwistH0Equivalence h).commShift_of_functor ℤ
    (P.cotwistH0Equivalence h).IsTriangulated := by
  letI : (P.cotwistH0Equivalence h).functor.CommShift ℤ := P.cotwistH0CommShift
  letI : (P.cotwistH0Equivalence h).inverse.CommShift ℤ :=
    (P.cotwistH0Equivalence h).commShiftInverse ℤ
  letI : (P.cotwistH0Equivalence h).CommShift ℤ :=
    (P.cotwistH0Equivalence h).commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ (P.cotwistH0IsTriangulated hSc hRc)

end ExactEquivalences

end EnhancedAdjunctionCones

end CategoryTheory.Triangulated.SphericalTwist
