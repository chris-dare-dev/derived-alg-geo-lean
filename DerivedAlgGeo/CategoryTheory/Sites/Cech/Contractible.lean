/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Simplicial.ExtraCodegeneracy
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Contractible Čech complexes

A member of a cover receiving a map from a terminal object contracts the
positive-degree Čech complex of every presheaf on that cover.
-/

universe w v v' u u'

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C) {T : C} (hT : IsTerminal T)
  {i₀ : ι} (d : T ⟶ U i₀) (P : Cᵒᵖ ⥤ A)

include hT d

/-- A member of a family receiving a map from a terminal object contracts the positive-degree
Čech complex of every presheaf on that family. -/
theorem cechComplex_exactAt_succ_of_isTerminal (n : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  let V : FormalCoproduct.{w} C := FormalCoproduct.mk ι U
  let X := V.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl T hT)
  let ed : X.ExtraDegeneracy := V.extraDegeneracyCech hT d
  let G := (FormalCoproduct.evalOp C A).obj P
  let Y := (FormalCoproduct.cosimplicialObjectFunctor V.cech).obj P
  change ((AlgebraicTopology.alternatingCofaceMapComplex A).obj Y).ExactAt (n + 1)
  apply AlgebraicTopology.exactAt_succ_of_extraDegeneracy_map ed G (Y := Y) (n := n)
  exact Iso.refl _

end CategoryTheory
