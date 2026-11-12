/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# The twist `F(d) = F ⊗ O(d)` of a module sheaf on `Proj`

The twist of an arbitrary module sheaf `F` on `Proj 𝒜` is the sheafified tensor product with the
twisting sheaf `O(d)`. This file supplies the definition, the normalization at zero, and the
comparison with `twistingSheaf` on the structure module.

## Main definitions

* `AlgebraicGeometry.Proj.tensorTwist`: the twist `F(d) = F ⊗ O(d)` of a module sheaf on `Proj`.
* `AlgebraicGeometry.Proj.tensorTwistZeroIso`: `F(0) ≅ F`.
* `AlgebraicGeometry.Proj.associatedSelfTensorTwistIso`: `(Ã)(d) ≅ O(d)`, so the tensor twist
  agrees with `twistingSheaf` on the structure module.

## Main results

This file proves no theorems; its content is the definition and the two isomorphisms above.

## Implementation notes

### What is here, and what each costs

* `tensorTwist F d` — the definition, `Scheme.Modules.tensorObj F (twistingSheaf 𝒜 d)`;
  `TwistInvertible.lean` proves `O(d)` invertible (`twistingSheaf_isInvertible`) when degree-one
  elements generate `A` over `𝒜 0`;
* `tensorTwistZeroIso` — `F(0) ≅ F`, which is `twistingSheafZeroIso` and `associatedSheafSelfIso`
  transported through the tensor and then `tensorUnitRightIso`;
* `associatedSelfTensorTwistIso` — `(Ã)(d) ≅ O(d)`, which is `tensorUnitLeftIso` once `Ã` is
  recognised as the unit.

### What is not here

`F(d)(e) ≅ F(d + e)` and preservation of coherence are **not** here. Both are read off the
comparison identifying `F ⊗ O(d)` with the *graded shift* `sheafTwist 𝒜 𝓜 d`: after it the
composition is `sheafTwistAddIso` and needs no associator at all, and coherence of `F(d)` is
visible on the graded side and not through the tensor. `TwistComparison.lean` proves that
comparison for `F` an associated sheaf and reads both off it.

## References

`AlgebraicGeometry.Scheme.Modules.tensorObj`, `AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso`
and `AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso`.

## Tags

projective spectrum, twisting sheaf, Serre twist, tensor product
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

The graded ring as a module over itself is the unit, so this is `tensorUnitLeftIso`. -/
noncomputable def associatedSelfTensorTwistIso (d : ℤ) :
    tensorTwist 𝒜 (associatedSheaf 𝒜 𝒜) d ≅ twistingSheaf 𝒜 d :=
  AlgebraicGeometry.Scheme.Modules.tensorObjIso (associatedSheafSelfIso 𝒜) (Iso.refl _) ≪≫
    AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso _

end AlgebraicGeometry.Proj
