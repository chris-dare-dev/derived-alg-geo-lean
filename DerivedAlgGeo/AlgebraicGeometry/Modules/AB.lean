/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.AB

/-!
# Grothendieck's axioms for module sheaves on a scheme

`X.Modules` satisfies AB4 and AB5: colimits of every shape along which colimits in `Ab` are
exact are exact, in particular coproducts indexed by a type in the universe of the scheme and
filtered colimits.  Mathlib defines `X.Modules` as a copy of `SheafOfModules X.ringCatSheaf`
with its own category instance, so the instance on sheaves of modules is transported by
`inferInstanceAs`, as Mathlib does for limits and colimits.

## Main results

* `AlgebraicGeometry.Scheme.Modules.hasExactColimitsOfShape`: the per-shape instance.
* `AlgebraicGeometry.Scheme.Modules.ab4`, `AlgebraicGeometry.Scheme.Modules.ab5`.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- Colimits in `X.Modules` of every shape along which colimits in `Ab` are exact are exact.
`X.Modules` is a copy of `SheafOfModules X.ringCatSheaf` with its own category instance, so the
instance on sheaves of modules is not found by search and is transported by `inferInstanceAs`,
as Mathlib transports `Abelian`, `HasLimits` and `HasColimits`. -/
instance hasExactColimitsOfShape (K : Type u) [Category.{u} K]
    [HasExactColimitsOfShape K AddCommGrpCat.{u}] : HasExactColimitsOfShape K X.Modules :=
  inferInstanceAs (HasExactColimitsOfShape K (SheafOfModules.{u} X.ringCatSheaf))

/-- `X.Modules` satisfies AB4: coproducts indexed by a type in the universe of `X` are exact. -/
instance ab4 : AB4 X.Modules := ⟨fun _ => inferInstance⟩

/-- `X.Modules` satisfies AB5: filtered colimits are exact. -/
instance ab5 : AB5 X.Modules := ⟨fun _ _ _ => inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
