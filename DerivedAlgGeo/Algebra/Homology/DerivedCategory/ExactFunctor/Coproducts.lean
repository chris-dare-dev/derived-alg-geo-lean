/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Coproducts

/-!
# The derived functor of an exact functor preserves coproducts

Let `F : C₁ ⥤ C₂` be an exact functor of abelian categories which preserves
coproducts of shape `κ`.  If both categories have exact coproducts of that
shape — AB4 at `κ`, `HasExactColimitsOfShape (Discrete κ)` — then
`F.mapDerivedCategory` preserves coproducts of shape `κ`.

## The shape of the argument

Everything happens in the localization square.  `mapDerivedCategoryFactors`
identifies `Q ⋙ F.mapDerivedCategory` with `F.mapHomologicalComplex _ ⋙ Q`.
Coproducts of cochain complexes are computed degreewise, so the first factor of
the right-hand composite preserves them as soon as `F` does, and `Q` preserves
them by `DerivedCategory.Q_preservesCoproductsOfShape`.  The right-hand
composite therefore preserves them, hence so does the left-hand one; and `Q` is
essentially surjective, so `preservesCoproductsOfShape_of_essSurj` transfers
preservation from the composite to `F.mapDerivedCategory` itself.

## Both AB4 hypotheses are used, and neither is discharged

`HasExactColimitsOfShape (Discrete κ) C₂` is what gives the target derived
category its coproducts at all, so the statement does not typecheck without it.
`HasExactColimitsOfShape (Discrete κ) C₁` is less obviously needed and is not a
convenience: it is what makes the *source* `Q` preserve coproducts, and without
that the transfer along `Q` has no starting point.  Neither is proved here.  An
abelian category with coproducts need not have exact ones, and a caller that
cannot supply AB4 on both sides does not get this theorem.

## Main results

* `CategoryTheory.Functor.mapDerivedCategory_preservesCoproductsOfShape`
-/

open CategoryTheory Category Limits

universe w w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (κ : Type w) [HasCoproductsOfShape κ C₁] [HasExactColimitsOfShape (Discrete κ) C₁]
  [HasCoproductsOfShape κ C₂] [HasExactColimitsOfShape (Discrete κ) C₂]
  [PreservesColimitsOfShape (Discrete κ) F]

/-- **The derived functor of an exact, coproduct-preserving functor preserves
coproducts**, when both abelian categories satisfy AB4 at the indexing shape.

This is not automatic from triangulatedness of `F.mapDerivedCategory`: a
triangulated functor preserves finite direct sums, and an arbitrary coproduct is
not one.  The content is that the coproduct in `D(C)` is represented by the
degreewise coproduct of complexes, which is the AB4 half of
`DerivedCategory.Q_preservesCoproductsOfShape`, applied on both sides. -/
theorem mapDerivedCategory_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete κ) F.mapDerivedCategory := by
  haveI : PreservesColimitsOfShape (Discrete κ)
      (DerivedCategory.Q (C := C₁) ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact preservesCoproductsOfShape_of_essSurj DerivedCategory.Q F.mapDerivedCategory

end CategoryTheory.Functor
