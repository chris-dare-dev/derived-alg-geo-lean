/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Whiskering

/-!
# Lifting bifunctors to full subcategories

If a bifunctor preserves an object property in two inputs satisfying that property, it restricts
to the corresponding full subcategory in both variables. The construction below is the
two-variable analogue of Mathlib's `ObjectProperty.lift`.
-/

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C]

/-- Restrict a bifunctor to a full subcategory when it preserves the defining property in both
variables. -/
@[simps]
def lift₂ (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ X Y, P X → P Y → P ((F.obj X).obj Y)) :
    P.FullSubcategory ⥤ P.FullSubcategory ⥤ P.FullSubcategory where
  obj X := P.lift (P.ι ⋙ F.obj X.obj) (fun Y ↦ hF X.obj Y.obj X.property Y.property)
  map {X Y} f :=
    { app := fun Z ↦ homMk ((F.map f.hom).app Z.obj)
      naturality := fun {Z W} g ↦ by
        apply P.hom_ext
        exact (F.map f.hom).naturality g.hom }
  map_id X := by
    ext Y
    simp
    rfl
  map_comp f g := by
    ext Y
    simp
    rfl

/-- Forgetting the output of `lift₂` recovers the original bifunctor restricted along the
inclusion in both inputs. This is definitionally an identity isomorphism. -/
def lift₂CompιIso (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ X Y, P X → P Y → P ((F.obj X).obj Y)) :
    P.lift₂ F hF ⋙ (Functor.whiskeringRight _ _ _).obj P.ι ≅
      P.ι ⋙ F ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι :=
  Iso.refl _

end CategoryTheory.ObjectProperty
