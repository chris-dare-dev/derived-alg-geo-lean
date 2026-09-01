/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# The twist `F(d) = F ⊗ O(d)` of a module sheaf on `Proj`

`#584` asks for the twist of an arbitrary module sheaf, its two coherence isomorphisms, coherence
preservation, and the comparison with `twistingSheaf`. This file supplies the definition, the
normalization at zero, and the comparison — the three that need nothing beyond the tensor product
`TwistInvertible.lean` made applicable by proving `O(d)` invertible.

## What is here, and what each costs

* `tensorTwist F d` — the definition. `Modules/Tensor/Basic.lean`'s machinery is stated for a locally
  free rank-one factor, so this is well-behaved only because `twistingSheaf_isInvertible` holds;
* `tensorTwistZeroIso` — `F(0) ≅ F`, which is `twistingSheafZeroIso` and `associatedSheafSelfIso`
  transported through the tensor and then `tensorUnitRightIso`;
* `associatedSelfTensorTwistIso` — `(Ã)(d) ≅ O(d)`, deliverable 4, which is `tensorUnitLeftIso`
  once `Ã` is recognised as the unit.

## What is not here, and why it cannot be got the easy way

`F(d)(e) ≅ F(d + e)` is **not** here, and it is not an oversight. `tensorAssocIso` requires *both*
outer factors to be invertible, and `F` is an arbitrary module sheaf; commuting the factors with
`tensorCommIso` does not help, because every rearrangement of `(F ⊗ O(d)) ⊗ O(e)` still leaves a
non-invertible factor on an outer slot. So the monoidal structure cannot deliver it.

What can is the comparison identifying `F ⊗ O(d)` with the *graded shift* `sheafTwist 𝒜 𝓜 d`,
after which the composition is `sheafTwistAddIso` and needs no associator at all. Coherence
preservation waits on it for the same reason, since coherence of `F(d)` is visible on the graded
side and not through the tensor. `TwistComparison.lean` proves that comparison for `F` an
associated sheaf and reads both off it.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-- **The twist `F(d) = F ⊗ O(d)` of a module sheaf on `Proj`.** -/
noncomputable def tensorTwist (F : (AlgebraicGeometry.Proj 𝒜).Modules) (d : ℤ) :
    (AlgebraicGeometry.Proj 𝒜).Modules :=
  AlgebraicGeometry.Scheme.Modules.tensorObj F (twistingSheaf 𝒜 d)

/-- **`F(0) ≅ F`.**

`O(0)` is the structure sheaf in two steps — `twistingSheafZeroIso` reaches `Ã`, and
`associatedSheafSelfIso` reaches the unit — and tensoring with the unit is `tensorUnitRightIso`. -/
noncomputable def tensorTwistZeroIso (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    tensorTwist 𝒜 F 0 ≅ F :=
  AlgebraicGeometry.Scheme.Modules.tensorObjIso (Iso.refl F)
      (twistingSheafZeroIso 𝒜 ≪≫ associatedSheafSelfIso 𝒜) ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso F

/-- **`(Ã)(d) ≅ O(d)`**, so the tensor twist agrees with `twistingSheaf` on the structure module.

Deliverable 4 of `#584`. The graded ring as a module over itself is the unit, so this is
`tensorUnitLeftIso`. -/
noncomputable def associatedSelfTensorTwistIso (d : ℤ) :
    tensorTwist 𝒜 (associatedSheaf 𝒜 𝒜) d ≅ twistingSheaf 𝒜 d :=
  AlgebraicGeometry.Scheme.Modules.tensorObjIso (associatedSheafSelfIso 𝒜) (Iso.refl _) ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso _

end AlgebraicGeometry.Proj
