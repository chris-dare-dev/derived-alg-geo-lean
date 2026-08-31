/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat

/-!
# Ordinary adjoint functors as bicategorical adjunctions

Categories, functors, and natural transformations form the bicategory `Cat`.
Mathlib supplies `Adjunction.toCat` and `Adjunction.ofCat`; this file packages
those mutually inverse conversions as an equivalence. Thus ordinary adjoint
functors are a specialization of the canonical bicategorical notion, not a
second repository-owned hierarchy.
-/

universe v u

namespace CategoryTheory.Adjunction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {F : C ⥤ D} {G : D ⥤ C}

/-- Ordinary adjunctions between `F` and `G` are exactly adjunctions between
the corresponding 1-morphisms in the bicategory `Cat`. -/
def bicategoricalEquiv :
    (F ⊣ G) ≃ Bicategory.Adjunction F.toCatHom G.toCatHom where
  toFun := toCat
  invFun := ofCat
  left_inv := ofCat_toCat
  right_inv := toCat_ofCat

end CategoryTheory.Adjunction
