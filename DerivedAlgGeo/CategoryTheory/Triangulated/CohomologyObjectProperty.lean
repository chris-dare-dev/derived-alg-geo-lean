/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.WeakSerreExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Cohomology in a weak Serre subcategory cuts out a triangulated subcategory

Let `A` be an abelian category and `P : ObjectProperty A` a **weak Serre
subcategory** — closed under kernels, cokernels and extensions, and containing
the zero object. This file proves that

`cohomologyIn P := fun E ↦ ∀ n, P (Hⁿ E)`

is a triangulated subcategory of `DerivedCategory A`, so that
`(cohomologyIn P).FullSubcategory` inherits a pretriangulated structure from
Mathlib's `ObjectProperty.instPretriangulatedFullSubcategory`, with the
inclusion triangulated.

## The one mathematical input

Closure under cones is the only field with content, and it is exactly the
five-term statement of `WeakSerreExact.lean` applied to the long exact homology
sequence. For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` the sequence

`Hⁿ⁻¹X₃ ⟶ HⁿX₁ ⟶ HⁿX₂ ⟶ HⁿX₃ ⟶ Hⁿ⁺¹X₁`

is exact at its three inner spots, and if `X₁` and `X₃` have all cohomology in
`P` then the four outer terms are in `P`. This is why a *weak* Serre
subcategory suffices and no closure under subobjects or quotients is needed:
the two extra terms of the five-term sequence pay for exactly that gap.

## Why this is not in Mathlib

Mathlib has the three closure classes and the long exact sequence, and it has
`ObjectProperty.IsTriangulated`, but nothing connects them. The `t`-structure
route (`DerivedCategory.TStructure`) answers a different question — boundedness,
not cohomological support in a subcategory.

## Main results

* `DerivedCategory.cohomologyIn` — the object property.
* `DerivedCategory.cohomologyIn_isTriangulated` — it is a triangulated
  subcategory, hence `Pretriangulated` on the full subcategory and the
  inclusion is triangulated.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The objects of `DerivedCategory A` all of whose cohomology objects satisfy
`P`. For `P` quasi-coherence on a scheme this is the honest `Dqc(X)`. -/
def cohomologyIn (P : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun E ↦ ∀ n : ℤ, P ((homologyFunctor A n).obj E)

lemma mem_cohomologyIn_iff (P : ObjectProperty A) (E : DerivedCategory A) :
    cohomologyIn P E ↔ ∀ n : ℤ, P ((homologyFunctor A n).obj E) :=
  Iff.rfl

variable (P : ObjectProperty A)

instance [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).IsClosedUnderIsomorphisms where
  of_iso e hE n := P.prop_of_iso ((homologyFunctor A n).mapIso e) (hE n)

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (DerivedCategory A)).zero
    exact ⟨Z, hZ, fun n ↦ P.prop_of_isZero (Functor.map_isZero (homologyFunctor A n) hZ)⟩

instance [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).IsStableUnderShift ℤ where
  isStableUnderShiftBy m :=
    { le_shift := by
        intro E hE n
        exact P.prop_of_iso
          (((homologyFunctor A 0).shiftIso m n (m + n) rfl).app E).symm (hE (m + n)) }

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
  [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]

/-- **Closure under cones**: the only field of `IsTriangulated` with content.

The long exact homology sequence of the distinguished triangle supplies the
three exactness hypotheses of `ObjectProperty.prop_X₃_of_exact₅`, and the four
outer terms come from `X₁` and `X₃` in adjacent degrees. -/
instance cohomologyIn_isTriangulatedClosed₂ :
    (cohomologyIn P).IsTriangulatedClosed₂ :=
  .mk' (by
    intro T hT h₁ h₃ n
    exact P.prop_X₃_of_exact₅
      (HomologySequence.exact₁ T hT (n - 1) n (by lia))
      (HomologySequence.exact₂ T hT n)
      (HomologySequence.exact₃ T hT n (n + 1) rfl)
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1)))

/-- **`cohomologyIn P` is a triangulated subcategory** when `P` is a weak Serre
subcategory containing zero.

Two consequences come for free from Mathlib: `(cohomologyIn P).FullSubcategory`
is `Pretriangulated` (and `IsTriangulated` when `DerivedCategory A` is), and
`(cohomologyIn P).ι` is a triangulated functor. -/
instance cohomologyIn_isTriangulated [P.ContainsZero] :
    (cohomologyIn P).IsTriangulated where

end DerivedCategory
