/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.ModuleStalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Module stalks and sheafification

Module sheafification preserves stalks over a sheaf of rings. The comparison is
natural in the presheaf of modules. A chosen colimit cocone gives the same
construction for ordinary ring and commutative-ring stalk presentations.

## Main definitions

* `PresheafOfModules.stalkRingSheaf` packages the ring sheaf.
* `PresheafOfModules.sheafStalkFunctor` takes stalks of module sheaves.
* `PresheafOfModules.stalkSheafificationApp` is the stalk of the unit.

## Main results

* `PresheafOfModules.stalkSheafificationApp_isIso` proves the unit is an
  isomorphism on module stalks.
* `PresheafOfModules.stalkSheafificationIso` bundles the natural isomorphism.

## Implementation notes

The underlying additive comparison is the usual stalk map from a presheaf to
its sheafification. The forgetful functor from modules to additive groups
reflects the isomorphism; naturality follows from the sheafification unit.

## References

Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` supplies the
underlying stalk isomorphism.

## Tags

module sheaf, sheafification, stalk, natural isomorphism
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace PresheafOfModules

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{u}) (R : X.Presheaf RingCat.{u}) (x : X)
  {c : Cocone ((OpenNhds.inclusion x).op ⋙ R)} (hc : IsColimit c)
  (hR : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    R)

/-- Package a ring presheaf with its sheaf property. -/
abbrev stalkRingSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨R, hR⟩

/-- The module-valued stalk functor on sheaves over the ring sheaf. -/
def sheafStalkFunctor : SheafOfModules.{u} (stalkRingSheaf X R hR) ⥤
    ModuleCat.{u} c.pt :=
  SheafOfModules.forget _ ⋙ stalkFunctorOfIsColimit X R x hc

/-- Apply the stalk functor to the unit of module sheafification. -/
def stalkSheafificationApp
    (M : PresheafOfModules.{u} R) :
    (stalkFunctorOfIsColimit X R x hc).obj M ⟶
      (sheafStalkFunctor X R x hc hR).obj
        ((PresheafOfModules.sheafification
          (R := stalkRingSheaf X R hR) (𝟙 R)).obj M) :=
  (stalkFunctorOfIsColimit X R x hc).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := stalkRingSheaf X R hR) (𝟙 R)).unit.app M)

/-- The sheafification unit is an isomorphism on every module stalk because
its underlying additive stalk map is an isomorphism. -/
theorem stalkSheafificationApp_isIso
    (M : PresheafOfModules.{u} R) :
    IsIso (stalkSheafificationApp X R x hc hR M) := by
  rw [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{u} c.pt) AddCommGrpCat.{u})]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat M.presheaf

/-- Taking module stalks commutes naturally with module sheafification. -/
def stalkSheafificationIso : stalkFunctorOfIsColimit X R x hc ≅
    PresheafOfModules.sheafification (R := stalkRingSheaf X R hR)
      (𝟙 R) ⋙ sheafStalkFunctor X R x hc hR :=
  NatIso.ofComponents
    (fun M => @asIso _ _ _ _ (stalkSheafificationApp X R x hc hR M)
      (stalkSheafificationApp_isIso X R x hc hR M))
    (fun {M N} f => by
      rw [asIso_hom, asIso_hom]
      change (stalkFunctorOfIsColimit X R x hc).map f ≫
          (stalkFunctorOfIsColimit X R x hc).map ((PresheafOfModules.sheafificationAdjunction
            (R := stalkRingSheaf X R hR) (𝟙 R)).unit.app N) =
        (stalkFunctorOfIsColimit X R x hc).map ((PresheafOfModules.sheafificationAdjunction
            (R := stalkRingSheaf X R hR) (𝟙 R)).unit.app M) ≫
          (stalkFunctorOfIsColimit X R x hc).map (((PresheafOfModules.sheafification
            (R := stalkRingSheaf X R hR) (𝟙 R)).map f).val)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congr_arg (stalkFunctorOfIsColimit X R x hc).map
        ((PresheafOfModules.sheafificationAdjunction (R := stalkRingSheaf X R hR)
          (𝟙 R)).unit.naturality f))

end

end PresheafOfModules
