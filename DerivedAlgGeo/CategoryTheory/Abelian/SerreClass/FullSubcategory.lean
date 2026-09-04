/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# A Serre subcategory of an abelian category is abelian

Mathlib has both ends of this and not the join. `ObjectProperty.IsSerreClass` is closure under
subobjects, quotients and extensions, and it already supplies `ContainsZero`,
`IsClosedUnderKernels` and `IsClosedUnderCokernels`. Mathlib's abelian-subcategory instance
(`CategoryTheory/Abelian/Subcategory.lean`) asks for those three **and**
`IsClosedUnderFiniteProducts`, which is not among a Serre class's defining closures and does
not follow by instance search.

It does follow mathematically, and the object-level step is Mathlib's too:
`ObjectProperty.prop_biprod` derives `P (X ⊞ Y)` from closure under extensions, because
`X ⊞ Y` is a split extension of `Y` by `X`. This file packages that as the two closure
instances, after which the abelian structure is Mathlib's.

## Main results

* `ObjectProperty.serreIsClosedUnderBinaryProducts` and
  `ObjectProperty.serreIsClosedUnderFiniteProducts`: a Serre class is closed under finite
  products.

Together with Mathlib's instance these give `Abelian P.FullSubcategory`, recorded as a
regression check below rather than restated as an instance.

## Why this is needed

Stacks 13.17.4 (tag 0FCL) states that `D⁻(𝓑) → D⁻_𝓑(𝓐)` is an equivalence for a Serre
subcategory `𝓑 ⊆ 𝓐` in which every object of `𝓑` admitting a surjection from an object of `𝓐`
admits one from a subobject lying in `𝓑`. Its source `D⁻(𝓑)` cannot be formed at all without
an abelian structure on `𝓑`, so this is that theorem's first prerequisite.

`AlgebraicGeometry/Modules/Coherent/Abelian/Basic.lean` runs the same binary-product argument
by hand for coherent sheaves. That instance could be derived from this one once
`Scheme.coherent` is known to be a Serre class; it is left alone here.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A) [P.IsSerreClass]

/-- A Serre class is closed under binary products: the limit of a pair is its biproduct, and
`prop_biprod` puts that in `P` by closure under extensions.

The proof shape is the one `AlgebraicGeometry.Scheme.coherent_isClosedUnderBinaryProducts`
uses for coherent sheaves, transporting the biproduct's limit cone onto the given one. -/
noncomputable instance serreIsClosedUnderBinaryProducts : P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    refine P.prop_of_iso ?_ (P.prop_biprod
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- A Serre class is closed under finite products, the one hypothesis of Mathlib's
abelian-subcategory instance that `IsSerreClass` does not already provide. -/
noncomputable instance serreIsClosedUnderFiniteProducts : P.IsClosedUnderFiniteProducts := .mk'

/-- **A Serre subcategory of an abelian category is abelian.** Stated as a check rather than an
instance: with the two above in scope it is Mathlib's instance, and restating it would create a
second path to the same structure. -/
example : Abelian P.FullSubcategory := inferInstance

end CategoryTheory.ObjectProperty
