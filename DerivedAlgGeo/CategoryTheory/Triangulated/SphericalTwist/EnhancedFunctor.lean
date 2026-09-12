/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory

/-!
# Enhanced cone data for spherical-functor constructions

Anno--Logvinenko attach four functorial triangles to a functor with left and
right dg adjoints: twist, dual twist, cotwist, and dual cotwist.  This file
packages the four underlying dg cone choices without calling the functor
spherical.

That distinction is essential.  Sphericality additionally requires
autoequivalence and adjoint-comparison conditions (or a theorem deriving all
four conditions from a sufficient pair in the Morita-enhanced setting).
`TwistCotwistEquivalenceConditions` records the commonly used equivalence pair
as explicit data, but no theorem here upgrades it to sphericality.  Doing so
requires the specific adjoint-comparison transformations and higher cone
coherence developed in the literature, neither of which is yet a repository
primitive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory

variable {A : Type u} {B : Type u'}
  [DGCategory.{v} A] [DGCategory.{v} B]

/-- The four dg adjunction maps and their chosen objectwise cones for a dg
functor `S : A ⟶ B` with left adjoint `L` and right adjoint `R`.

The fields named `dualTwistCone` and `cotwistCone` are unshifted cones.  The
conventional dual twist and cotwist are their shifts by `-1`. -/
structure EnhancedAdjunctionCones
    (S : DGFunctor A B) (L R : DGFunctor B A) where
  /-- The left adjunction `L ⊣ S`. -/
  leftAdj : DGAdjunction L S
  /-- The right adjunction `S ⊣ R`. -/
  rightAdj : DGAdjunction S R
  /-- Cone of `S R ⟶ id_B`: the twist. -/
  twist : rightAdj.CounitConeData
  /-- Cone of `id_B ⟶ S L`; its `[-1]` shift is the dual twist. -/
  dualTwistCone : leftAdj.UnitConeData
  /-- Cone of `id_A ⟶ R S`; its `[-1]` shift is the cotwist. -/
  cotwistCone : rightAdj.UnitConeData
  /-- Cone of `L S ⟶ id_A`: the dual cotwist. -/
  dualCotwist : leftAdj.CounitConeData

namespace EnhancedAdjunctionCones

variable {S : DGFunctor A B} {L R : DGFunctor B A}
  (P : EnhancedAdjunctionCones S L R)

/-- A pretriangulated source and target provide all four objectwise cone
choices associated to supplied left and right dg adjunctions. -/
noncomputable def chosen [IsPretriangulated A] [IsPretriangulated B]
    (leftAdj : DGAdjunction L S) (rightAdj : DGAdjunction S R) :
    EnhancedAdjunctionCones S L R where
  leftAdj := leftAdj
  rightAdj := rightAdj
  twist := rightAdj.chosenCounitConeData
  dualTwistCone := leftAdj.chosenUnitConeData
  cotwistCone := rightAdj.chosenUnitConeData
  dualCotwist := leftAdj.chosenCounitConeData

/-- The dg twist endofunctor `Cone(S R ⟶ id_B)`. -/
noncomputable abbrev twistFunctor : DGFunctor B B := P.twist.twist

/-- The unshifted cone underlying the dual twist. -/
noncomputable abbrev dualTwistConeFunctor : DGFunctor B B :=
  P.dualTwistCone.unitCone

/-- The unshifted cone underlying the cotwist. -/
noncomputable abbrev cotwistConeFunctor : DGFunctor A A :=
  P.cotwistCone.unitCone

/-- The conventional dg dual twist: the `[-1]` shift of its stored unit
cone. -/
noncomputable abbrev dualTwistFunctor [IsPretriangulated B] : DGFunctor B B :=
  P.dualTwistConeFunctor.shiftedFunctor (-1 : ℤ)

/-- The conventional dg cotwist: the `[-1]` shift of its stored unit cone. -/
noncomputable abbrev cotwistFunctor [IsPretriangulated A] : DGFunctor A A :=
  P.cotwistConeFunctor.shiftedFunctor (-1 : ℤ)

/-- The dg dual-cotwist endofunctor `Cone(L S ⟶ id_A)`. -/
noncomputable abbrev dualCotwistFunctor : DGFunctor A A :=
  P.dualCotwist.twist

end EnhancedAdjunctionCones

/-- The twist/cotwist equivalence pair used by the main spherical-functor
criterion, expressed at the repository's current dg level.

The cotwist is conventionally `cotwistConeFunctor[-1]`; requiring the
unshifted cone functor to be a quasi-equivalence is the shift-free form of the
same condition.  This structure is deliberately not named `IsSpherical`: the
Anno--Logvinenko implication from this pair to all spherical conditions uses
Morita quasi-functors and higher cone coherence not yet formalized here. -/
structure TwistCotwistEquivalenceConditions
    {S : DGFunctor A B} {L R : DGFunctor B A}
    (P : EnhancedAdjunctionCones S L R) : Prop where
  /-- The counit-cone twist is a quasi-equivalence. -/
  twist : P.twistFunctor.IsQuasiEquivalence
  /-- The unshifted cone underlying the cotwist is a quasi-equivalence. -/
  cotwist : P.cotwistConeFunctor.IsQuasiEquivalence

end CategoryTheory.Triangulated.SphericalTwist
