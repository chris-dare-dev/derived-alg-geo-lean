/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits
import DerivedAlgGeo.Algebra.Homology.Localization
import DerivedAlgGeo.Algebra.Homology.ShortComplex.Limits
import DerivedAlgGeo.CategoryTheory.Localization.Coproducts

/-!
# Coproducts in the derived category

For an abelian category `C` with coproducts of shape `κ` that are exact
(`HasExactColimitsOfShape (Discrete κ) C`, the axiom AB4 for that shape), the derived category
`D(C)` has coproducts of shape `κ`, and the localization functors `Q` and `Qh` and the homology
functors `Hⁿ : D(C) ⥤ C` preserve them.

The argument is the composite of three facts.  The homotopy category has coproducts of shape
`κ` and the quotient functor preserves them; quasi-isomorphisms are stable under them because
homology commutes with exact coproducts; and a localization at a class with a right calculus of
fractions, stable under coproducts, has them and is preserved by the localization functor.

## Main results

* `DerivedCategory.hasCoproductsOfShape`, `Qh_preservesCoproductsOfShape`,
  `Q_preservesCoproductsOfShape`, `homologyFunctor_preservesCoproductsOfShape`: the instances.

## References

* Neeman, *Triangulated categories*, Lemma 3.2.10: a Verdier quotient by a localizing
  subcategory has the coproducts and the quotient functor preserves them
* [Stacks, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L), Lemma 13.33.5, the
  countable case
-/

open CategoryTheory Category Limits

universe w w' v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {κ : Type w'} [HasCoproductsOfShape κ C] [HasExactColimitsOfShape (Discrete κ) C]

/-- The class of morphisms with acyclic cone is stable under coproducts: it is the class of
quasi-isomorphisms. -/
instance trW_subcategoryAcyclic_isStableUnderCoproductsOfShape :
    (HomotopyCategory.subcategoryAcyclic C).trW.IsStableUnderCoproductsOfShape κ := by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- `D(C)` has coproducts of shape `κ` when `C` has exact ones, Neeman's Lemma 3.2.10 taken
at the localization `Qh : K(C) ⥤ D(C)`: the homotopy category has them
(`HomotopyCategory.hasColimitsOfShape_discrete`), quasi-isomorphisms are stable under them
because homology commutes with exact coproducts
(`HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape`), and a localization at a class
with a right calculus of fractions that is stable under coproducts inherits them
(`Localization.hasCoproductsOfShape`). -/
instance hasCoproductsOfShape : HasCoproductsOfShape κ (DerivedCategory C) :=
  Localization.hasCoproductsOfShape Qh (HomotopyCategory.subcategoryAcyclic C).trW κ

/-- `Qh` preserves coproducts of shape `κ`: the coproduct in `D(C)` of a family is the image of
its coproduct in the homotopy category. -/
instance Qh_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete κ)
      (Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C) :=
  Localization.preservesCoproductsOfShape Qh (HomotopyCategory.subcategoryAcyclic C).trW κ

/-- `Q` preserves coproducts of shape `κ`, so the coproduct in `D(C)` of a family of complexes
is their termwise coproduct (Stacks 0A5L in the countable case): `Q` is the quotient followed
by `Qh`, and both preserve them. -/
instance Q_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete κ) (Q : CochainComplex C ℤ ⥤ DerivedCategory C) :=
  preservesColimitsOfShape_of_natIso (quotientCompQhIso C)

/-- Homology on the derived category preserves coproducts of shape `κ`: it factors through the
essentially surjective `Q`, which preserves them, as homology of complexes, which commutes
with exact coproducts. -/
instance homologyFunctor_preservesCoproductsOfShape (n : ℤ) :
    PreservesColimitsOfShape (Discrete κ) (homologyFunctor C n) := by
  haveI : PreservesColimitsOfShape (Discrete κ) (Q ⋙ homologyFunctor C n) :=
    preservesColimitsOfShape_of_natIso (homologyFunctorFactors C n).symm
  exact preservesCoproductsOfShape_of_essSurj Q (homologyFunctor C n)

end DerivedCategory
