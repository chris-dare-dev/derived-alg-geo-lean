/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Degree-zero Hom-complex classes in the homotopy category

Mathlib identifies `CohomologyClass K L 0` with morphisms from `K` to `L⟦0⟧`
in the homotopy category. Composing with the canonical `shiftFunctorZero`
isomorphism gives an additive equivalence with morphisms from `K` to `L`.
On representatives it sends a cocycle `z` to the homotopy class of
`Cocycle.homOf z`.

This neutral comparison uses no module localization or derived-category API.
The downstream K-projective and K-injective derived comparisons reuse this
equivalence before applying localization.

## Main definitions

* `CochainComplex.HomComplex.cohomologyClassHomotopyAddEquiv` is the neutral
  additive comparison with homotopy-category morphisms.

## Main results

* `CochainComplex.HomComplex.cohomologyClassHomotopyAddEquiv_mk` identifies the
  image of a cocycle class with the homotopy class of its chain map.

## Implementation notes

The zero-shift isomorphism normalizes Mathlib's shifted Hom-complex
cohomology comparison before any derived localization is applied.

## References

Mathlib's `HomComplexCohomology.lean` and `HomComplexShift.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

Hom complex, homotopy category, cohomology class, zero shift
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace CochainComplex.HomComplex

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K L : CochainComplex C ℤ)

/-- Degree-zero Hom-complex cohomology classes as morphisms of the homotopy
category, using the canonical zero-shift isomorphism. -/
def cohomologyClassHomotopyAddEquiv :
    CohomologyClass K L 0 ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj L) := by
  let e : (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦(0 : ℤ)⟧) ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj L :=
    (HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app L)
  let e₁ : ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦(0 : ℤ)⟧)) ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj L) :=
    { toFun := fun f => f ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := by intro f; simp
      right_inv := by intro g; simp
      map_add' := by intro f g; simp [Preadditive.add_comp] }
  exact CohomologyClass.homAddEquiv.trans e₁

private theorem cocycle_equivHomShift_symm_comp_shiftZero (z : Cocycle K L 0) :
    Cocycle.equivHomShift.symm z ≫
      (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L =
      Cocycle.homOf z := by
  ext i
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]
  -- The remaining inverse/forward `XIsoOfEq` composite contains dependent casts.
  -- Ordinary `rw` fails at instances transparency; `erw` closes it.
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The class of a degree-zero cocycle corresponds to the homotopy class of its
associated chain map. -/
@[simp] theorem cohomologyClassHomotopyAddEquiv_mk (z : Cocycle K L 0) :
    cohomologyClassHomotopyAddEquiv K L (CohomologyClass.mk z) =
      (HomotopyCategory.quotient C (.up ℤ)).map z.homOf := by
  change CohomologyClass.homAddEquiv (CohomologyClass.mk z) ≫
    (HomotopyCategory.quotient C (.up ℤ)).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L) =
    (HomotopyCategory.quotient C (.up ℤ)).map z.homOf
  rw [CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  rw [← Functor.map_comp]
  rw [cocycle_equivHomShift_symm_comp_shiftZero K L z]
  rfl

end

end CochainComplex.HomComplex
