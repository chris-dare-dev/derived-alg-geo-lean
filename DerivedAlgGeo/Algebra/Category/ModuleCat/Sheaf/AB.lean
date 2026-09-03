/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf.AB

/-!
# Exact colimits of sheaves of modules

Colimits of sheaves of modules of a shape `K` are exact when colimits of that shape are exact
in abelian groups: the sheafification adjunction has a fully faithful right adjoint and a left
adjoint preserving finite limits, so exactness descends from presheaves of modules by
Mathlib's `Adjunction.hasExactColimitsOfShape`.  In particular sheaves of modules on a ringed
site satisfy AB4 and AB5 in the universes where abelian groups do, the input to coproducts in
their derived category.

## Main results

* `SheafOfModules.hasExactColimitsOfShape`: the per-shape instance.
* `SheafOfModules.ab4OfSize`, `SheafOfModules.ab5OfSize`: the Grothendieck axioms.
-/

open CategoryTheory Limits

universe w' w v' u' u v

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Colimits of shape `K` of sheaves of modules are exact when they are in abelian groups,
through the sheafification adjunction: its right adjoint is fully faithful and its left adjoint
preserves finite limits, which is what `Adjunction.hasExactColimitsOfShape` needs.
`HasSheafify` (not merely `HasWeakSheafify`) is required because Mathlib proves
`PreservesFiniteLimits (sheafification α)` and `Abelian (SheafOfModules R)` only under it. -/
instance hasExactColimitsOfShape (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] [HasExactColimitsOfShape K AddCommGrpCat.{v}] :
    HasExactColimitsOfShape K (SheafOfModules.{v} R) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

instance hasFilteredColimitsOfSize [HasFilteredColimitsOfSize.{w', w} AddCommGrpCat.{v}] :
    HasFilteredColimitsOfSize.{w', w} (SheafOfModules.{v} R) where
  HasColimitsOfShape _ _ _ := inferInstance

/-- Sheaves of modules satisfy AB4 when abelian groups do. -/
instance ab4OfSize [HasCoproducts.{w} AddCommGrpCat.{v}] [AB4OfSize.{w} AddCommGrpCat.{v}] :
    AB4OfSize.{w} (SheafOfModules.{v} R) where
  ofShape _ := inferInstance

/-- Sheaves of modules satisfy AB5 when abelian groups do. -/
instance ab5OfSize [HasFilteredColimitsOfSize.{w', w} AddCommGrpCat.{v}]
    [AB5OfSize.{w', w} AddCommGrpCat.{v}] :
    AB5OfSize.{w', w} (SheafOfModules.{v} R) where
  ofShape _ _ _ := inferInstance

end SheafOfModules
