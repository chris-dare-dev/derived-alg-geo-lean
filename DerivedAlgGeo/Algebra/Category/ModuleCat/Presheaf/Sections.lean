/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Sections of a presheaf of modules over a terminal object

When the index category has a terminal object `T`, a compatible family of sections of a
presheaf of modules is determined by its value at `T`, and every value at `T` extends by
restriction. So `M.sections ≃ M.obj (op T)`. With `PresheafOfModules.unitHomEquiv` this
identifies maps out of the unit module with sections over `T`, which is what the degree-zero
comparison between `Ext (unit R) M` and sheaf cohomology of `M` needs.
-/

universe v u

open CategoryTheory Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a presheaf of modules on a category with a terminal object are its values at
the terminal object. -/
@[simps]
noncomputable def sectionsEquivOfIsTerminal (M : PresheafOfModules.{v} R) {T : C}
    (hT : IsTerminal T) :
    M.sections ≃ M.obj (op T) where
  toFun s := s.val (op T)
  invFun x := M.sectionsMk (fun X ↦ M.map (hT.from X.unop).op x) (fun X Y f ↦ by
    have h : (hT.from X.unop).op ≫ f = (hT.from Y.unop).op :=
      Quiver.Hom.unop_inj (hT.hom_ext _ _)
    rw [← map_comp_apply, h])
  left_inv s := by
    ext X
    exact s.property _
  right_inv x := by
    show M.map (hT.from T).op x = x
    rw [hT.hom_ext (hT.from T) (𝟙 T)]
    simp

end PresheafOfModules
