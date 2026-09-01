/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.StalkTensor
import DerivedAlgGeo.Topology.Sheaves.StalkW

/-!
# Tensoring local equivalences of module presheaves on a space

On a topological space, sheafification inverts the result of whiskering a stalkwise isomorphism
of module presheaves by an arbitrary module presheaf. Unlike the arbitrary-site result for an
invertible factor, this needs no flatness or rank-one hypothesis: stalks commute with the tensor
product, and tensoring an isomorphism remains an isomorphism.
-/

open CategoryTheory MonoidalCategory

universe u

namespace PresheafOfModules

variable {Y : TopCat.{u}} {R : Y.Presheaf CommRingCat.{u}}

attribute [local instance] PresheafOfModules.monoidalCategory

/-- Sheafification inverts `M ◁ g` on a topological space whenever every stalk map of `g` is an
isomorphism. -/
lemma W_whiskerLeft_of_isIso_stalk
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {G₁ G₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : G₁ ⟶ G₂)
    (hg : ∀ y : Y, IsIso (stalkMapAdd g y)) :
    (Opens.grothendieckTopology Y).W
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ g)) := by
  haveI := hg
  haveI : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (M ◁ g))) :=
    fun y => isIso_stalkMapAdd_whiskerLeft M g y
  exact TopCat.Presheaf.W_of_isIso_stalkFunctor_map _

end PresheafOfModules
