/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Module-valued stalks over a topological space

For a commutative-ring presheaf `R` on `X`, the stalk of a presheaf of `R`-modules is a
module over the ring stalk. The functor here uses Mathlib's module-colimit construction; its
underlying module is linearly equivalent to the usual germ stalk.

## Main definitions

* `PresheafOfModules.stalkRingCocone` and `PresheafOfModules.stalkRingIsColimit` lift the
  ring-stalk colimit through the forgetful functor to rings.
* `PresheafOfModules.neighborhoodStalkFunctor` takes the module colimit on open neighborhoods.
* `PresheafOfModules.stalkFunctor` first restricts a module presheaf to neighborhoods.
* `PresheafOfModules.stalkLinearEquiv` identifies its value with the usual germ stalk.

## Main results

`PresheafOfModules.stalkLinearEquiv` identifies the two stalk presentations as modules over
the commutative-ring stalk, with no sheaf or scheme hypothesis.

## Implementation notes

The ring stalk is a colimit in commutative rings. Its underlying-ring cocone is also colimiting,
so Mathlib's module-colimit functor supplies the scalar action. The linear comparison checks
scalar multiplication on germ representatives using `PresheafOfModules.germ_smul`.

## References

Mathlib's `PresheafOfModules.colimitFunctor`, `PresheafOfModules.pushforward₀`, and
`TopCat.Presheaf.stalkFunctor` provide the constructions used here.

## Tags

module presheaf, stalk, germs, colimit
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace PresheafOfModules

noncomputable section

variable (X : TopCat.{u}) (R : X.Presheaf CommRingCat.{u}) (x : X)

/-- The underlying-ring cocone of the commutative-ring stalk diagram. -/
def stalkRingCocone : Cocone ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ CommRingCat RingCat) :=
  (forget₂ CommRingCat RingCat).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ R))

/-- The underlying-ring stalk cocone is colimiting. -/
def stalkRingIsColimit : IsColimit (stalkRingCocone X R x) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))

/-- Module colimit over the open neighborhoods of a point. -/
def neighborhoodStalkFunctor :
    PresheafOfModules.{u} ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ CommRingCat RingCat) ⥤
      ModuleCat.{u} (R.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.colimitFunctor (stalkRingIsColimit X R x)

/-- The module-valued stalk functor for an arbitrary ring presheaf on a topological space. -/
def stalkFunctor : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
    ModuleCat.{u} (R.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.pushforward₀ (OpenNhds.inclusion x) (R ⋙ forget₂ CommRingCat RingCat) ⋙
    PresheafOfModules.colimitFunctor (stalkRingIsColimit X R x)

/-- The bundled module stalk and the germ stalk have the same elements and scalar action. -/
def stalkLinearEquiv (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (stalkFunctor X R x).obj M ≃ₗ[R.stalk x] ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  refine { toFun := fun m => m
           invFun := fun m => m
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxU
  rw [← TopCat.Presheaf.germ_res_apply R (homOfLE hVU) x hxV r]
  simp only [RingHom.id_apply]
  erw [← PresheafOfModules.germ_smul M x V hxV]
  exact PresheafOfModules.ModuleColimit.smul_eq
    (stalkRingIsColimit X R x) (colimit.isColimit _) _ _

end

end PresheafOfModules
