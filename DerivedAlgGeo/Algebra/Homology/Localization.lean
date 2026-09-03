/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.MorphismProperty.Limits
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Coproducts

/-!
# Quasi-isomorphisms are stable under coproducts

Quasi-isomorphisms in the homotopy category are stable under coproducts of a shape along which
homology of complexes commutes with coproducts, in particular under coproducts of every shape
when `C` is abelian with exact coproducts (AB4), by
`ShortComplex.homologyFunctor_preservesColimitsOfShape`.  This is the last input to coproducts
in the derived category: with coproducts in the homotopy category and the localization theorem
for coproducts, `D(C)` has coproducts of every such shape.

## Main results

* `HomotopyCategory.quasiIso_isStableUnderCoproductsOfShape`: the instance.
-/

open CategoryTheory Category Limits

universe w v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C] {ι : Type*}
  {c : ComplexShape ι}
  {κ : Type w} [HasCoproductsOfShape κ C]
  [∀ n, PreservesColimitsOfShape (Discrete κ) (HomologicalComplex.homologyFunctor C c n)]

/-- Quasi-isomorphisms in the homotopy category are stable under coproducts of shape `κ` when
homology of complexes preserves them: `Sigma.map` of a family of quasi-isomorphisms is
inverted by homology in every degree. -/
instance quasiIso_isStableUnderCoproductsOfShape :
    (quasiIso C c).IsStableUnderCoproductsOfShape κ := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X₁ X₂ _ _ f hf n
  haveI : ∀ j, IsIso ((homologyFunctor C c n).map (f j)) := fun j => hf j n
  exact isIso_map_sigma_map (homologyFunctor C c n) f

end HomotopyCategory
