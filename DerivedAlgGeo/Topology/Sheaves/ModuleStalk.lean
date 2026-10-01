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

For a ring presheaf `R` on `X`, the stalk of a presheaf of `R`-modules is a module
over the ring stalk. The functor uses Mathlib's module-colimit construction; its
underlying module is linearly equivalent to the usual germ stalk. A commutative-ring
specialization retains the scalar presentation used by scheme stalks.

## Main definitions

* `PresheafOfModules.stalkRingCocone` and `PresheafOfModules.stalkRingIsColimit` lift the
  ring-stalk colimit through the forgetful functor to rings.
* `PresheafOfModules.neighborhoodStalkFunctor` takes the module colimit on open neighborhoods
  over a general ring presheaf.
* `PresheafOfModules.stalkFunctor` first restricts a module presheaf to neighborhoods.
* `PresheafOfModules.stalkLinearEquiv` identifies its value with the usual germ stalk.
* `PresheafOfModules.stalkRingComparisonIso` compares the general and commutative
  stalk rings; `PresheafOfModules.commStalkAddEquiv` compares their module objects.

## Main results

`PresheafOfModules.stalkLinearEquiv` identifies the two stalk presentations as modules over
the commutative-ring stalk, with no sheaf or scheme hypothesis.

## Implementation notes

The ring stalk is a colimit in rings. For a commutative-ring presheaf, forgetting
commutativity preserves this colimit and yields the scheme-compatible cocone. The two
colimit points are canonically isomorphic. The linear comparisons check scalar
multiplication on germ representatives using the corresponding germ scalar lemma.

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

/-- Forgetting commutativity makes the ring-stalk cocone available to Mathlib's
module-colimit construction. -/
def stalkRingCocone : Cocone ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ CommRingCat RingCat) :=
  (forget₂ CommRingCat RingCat).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ R))

/-- Forgetting commutativity preserves this filtered colimit, supplying the witness
needed by `PresheafOfModules.colimitFunctor`. -/
def stalkRingIsColimit : IsColimit (stalkRingCocone X R x) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))

/-- The general-ring stalk and the underlying ring of the commutative stalk
are the two colimit points of the same neighborhood diagram. -/
def stalkRingComparisonIso :
    ((show X.Presheaf RingCat.{u} from R ⋙ forget₂ CommRingCat RingCat).stalk x) ≅
      (forget₂ CommRingCat RingCat).obj (R.stalk x) :=
  (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R ⋙
    forget₂ CommRingCat RingCat)).coconePointUniqueUpToIso (stalkRingIsColimit X R x)

/-- Module colimit on neighborhoods of a point over an arbitrary ring presheaf. -/
def neighborhoodStalkFunctor (X : TopCat.{u}) (S : X.Presheaf RingCat.{u}) (x : X) :
    PresheafOfModules.{u} ((OpenNhds.inclusion x).op ⋙ S) ⥤ ModuleCat.{u} (S.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.colimitFunctor (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ S))

/-- For a ring presheaf, restrict modules to neighborhoods and take their colimit
over the ring stalk. -/
def stalkFunctor (X : TopCat.{u}) (S : X.Presheaf RingCat.{u}) (x : X) :
    PresheafOfModules.{u} S ⥤ ModuleCat.{u} (S.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.pushforward₀ (OpenNhds.inclusion x) S ⋙
    PresheafOfModules.colimitFunctor (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ S))

/-- The bundled module stalk and the germ stalk have the same elements and scalar action. -/
def stalkLinearEquiv (X : TopCat.{u}) (S : X.Presheaf RingCat.{u}) (x : X)
    (M : PresheafOfModules.{u} S) :
    (stalkFunctor X S x).obj M ≃ₗ[S.stalk x] ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  refine { toFun := fun m => m
           invFun := fun m => m
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq S r
  obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxU
  rw [← TopCat.Presheaf.germ_res_apply S (homOfLE hVU) x hxV r]
  simp only [RingHom.id_apply]
  erw [← PresheafOfModules.germ_ringCat_smul M x V hxV]
  exact PresheafOfModules.ModuleColimit.smul_eq
    (colimit.isColimit _) (colimit.isColimit _) _ _

/-- Module colimit over neighborhoods in the commutative stalk-ring presentation. -/
def commNeighborhoodStalkFunctor :
    PresheafOfModules.{u} ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ CommRingCat RingCat) ⥤
      ModuleCat.{u} (R.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.colimitFunctor (stalkRingIsColimit X R x)

/-- The commutative stalk-ring presentation, used by scheme stalks. -/
def commStalkFunctor : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
    ModuleCat.{u} (R.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  PresheafOfModules.pushforward₀ (OpenNhds.inclusion x) (R ⋙ forget₂ CommRingCat RingCat) ⋙
    PresheafOfModules.colimitFunctor (stalkRingIsColimit X R x)

/-- Identity on germs identifies the commutative stalk-ring presentation with
the ordinary germ stalk as modules over the commutative-ring stalk. -/
def commStalkLinearEquiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (commStalkFunctor X R x).obj M ≃ₗ[R.stalk x]
      ↑(TopCat.Presheaf.stalk M.presheaf x) := by
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

/-- The two module-colimit presentations have the same germ elements. This
objectwise additive comparison complements `stalkRingComparisonIso` on scalars. -/
def commStalkAddEquiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (commStalkFunctor X R x).obj M ≃+
      (stalkFunctor X
        (show X.Presheaf RingCat.{u} from R ⋙ forget₂ CommRingCat RingCat) x).obj M :=
  (commStalkLinearEquiv X R x M).toAddEquiv.trans
    (stalkLinearEquiv X
      (show X.Presheaf RingCat.{u} from R ⋙ forget₂ CommRingCat RingCat) x M).toAddEquiv.symm

end

end PresheafOfModules
