/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The linear-dual functor on module categories

Mathlib supplies `Module.Dual` and `LinearMap.dualMap`, but at the pinned
revision it does not bundle them as a functor on `ModuleCat`.  This file is
the category-theoretic owner of that functor.  In particular it has no
dependency on algebraic geometry, so abstract Serre functors can use it.

For `k : Type u` and modules in universe `max u w`, algebraic duality stays in
the same module category: `Module.Dual k V` lives in `Type (max u w)`.  The
older geometric use at `ModuleCat.{u + 1} k` is the specialization `w := u + 1`.

Only the functor, its two reduction lemmas, and additivity live here.  Exactness
over a field remains in `Algebra/Category/ModuleCat/LinearDual.lean`.
-/

universe u w

open CategoryTheory

namespace ModuleCat

variable (k : Type u) [Field k]

/-- Algebraic linear dual, viewed as a contravariant functor on `k`-modules. -/
noncomputable def linearDualFunctor :
    (ModuleCat.{max u w} k)ᵒᵖ ⥤ ModuleCat.{max u w} k where
  obj V := ModuleCat.of k (Module.Dual k V.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id V := by
    apply ModuleCat.hom_ext
    exact LinearMap.dualMap_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.dualMap_comp_dualMap g.unop.hom f.unop.hom

@[simp]
theorem linearDualFunctor_obj (V : (ModuleCat.{max u w} k)ᵒᵖ) :
    (linearDualFunctor k).obj V = ModuleCat.of k (Module.Dual k V.unop) :=
  rfl

@[simp]
theorem linearDualFunctor_map {V W : (ModuleCat.{max u w} k)ᵒᵖ} (f : V ⟶ W) :
    (linearDualFunctor k).map f = ModuleCat.ofHom f.unop.hom.dualMap :=
  rfl

noncomputable instance : (linearDualFunctor k).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro x
    change (show Module.Dual k X.unop from phi) (f.unop.hom x + g.unop.hom x) =
      (show Module.Dual k X.unop from phi) (f.unop.hom x) +
        (show Module.Dual k X.unop from phi) (g.unop.hom x)
    exact map_add (show Module.Dual k X.unop from phi) _ _

end ModuleCat
