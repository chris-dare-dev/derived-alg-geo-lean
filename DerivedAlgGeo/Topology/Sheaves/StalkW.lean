/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Stalkwise isomorphisms are inverted by sheafification

`TopCat.Presheaf.W_of_isIso_stalkFunctor_map`: a morphism of presheaves of abelian groups on a
topological space whose stalk maps are all isomorphisms lies in
`(Opens.grothendieckTopology X).W`, the class sheafification inverts.

This is one direction of the stalkwise characterisation of `J.W` on a space. It matters because
`J.W` unfolds to `IsLocallyInjective` *and* `IsLocallySurjective`, and Mathlib has no stalkwise
criterion for the injective half — so a proof that goes through the halves separately cannot use
stalks, while this lemma can.

The proof is the naturality square of `toSheafify` read on stalks: three of its four edges are
isomorphisms, so the fourth is one too.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace TopCat.Presheaf

/-- **A stalkwise isomorphism of presheaves of abelian groups on a space is inverted by
sheafification.** One half of the stalkwise characterisation of `J.W`; the half needed to
conclude local bijectivity from a stalk computation, without ever mentioning
`IsLocallyInjective` — for which no stalkwise criterion exists in `Mathlib`.

The proof is the naturality square of `toSheafify` read on stalks: three of its four edges are
isomorphisms, so the fourth is one too. -/
lemma W_of_isIso_stalkFunctor_map {X : TopCat.{u}} {F G : X.Presheaf AddCommGrpCat.{u}}
    (f : F ⟶ G) [∀ x : X, IsIso ((stalkFunctor AddCommGrpCat.{u} x).map f)] :
    (Opens.grothendieckTopology X).W f := by
  rw [GrothendieckTopology.W_iff]
  haveI : ∀ x : X, IsIso ((stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) f)) := by
    intro x
    haveI h1 := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} F
    haveI h2 := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} G
    have hsq : (stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) ≫
        (stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) f)
        = (stalkFunctor AddCommGrpCat.{u} x).map f ≫
          (stalkFunctor AddCommGrpCat.{u} x).map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology X) G) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology X) f).symm
    haveI hc : IsIso ((stalkFunctor AddCommGrpCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F) ≫
        (stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) f)) := by
      rw [hsq]; infer_instance
    exact IsIso.of_isIso_comp_left ((stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) _
  exact isIso_of_stalkFunctor_map_iso _

end TopCat.Presheaf
