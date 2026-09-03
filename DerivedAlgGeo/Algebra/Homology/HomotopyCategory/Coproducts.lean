/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory
import DerivedAlgGeo.Algebra.Homology.Homotopy.Sigma

/-!
# Coproducts in the homotopy category

The homotopy category has coproducts of every shape the underlying category has, computed on
complexes, and the quotient functor preserves them.  The description out of the quotient of a
coproduct is the quotient of the description by lifted legs; uniqueness is `Homotopy.sigma`,
which assembles the homotopies witnessing agreement on each summand into one homotopy.

## Main definitions

* `HomotopyCategory.cofanDesc`: the morphism out of the quotient of `∐ X` induced by a cofan.
* `HomotopyCategory.isColimitCofan`: the quotient of `∐ X` is a coproduct of the quotients.

## Main results

* `HomotopyCategory.hasColimitsOfShape_discrete`: the homotopy category has coproducts of
  shape `κ` when the underlying category does.
* `HomotopyCategory.quotient_preservesColimitsOfShape_discrete`: the quotient functor
  preserves them.

## Implementation notes

An object of the homotopy category is an object of a `Quotient`, but `HomotopyCategory` is a
`def` over it and `t.pt.as` does not elaborate under the default
`backward.isDefEq.respectTransparency`; the vertex of a cofan is therefore represented through
Mathlib's `Functor.objPreimage` for the essentially surjective `quotient C c`, and legs are
lifted with `Functor.preimage`.  The description, its factorization, and its uniqueness are
separate declarations with explicit types, because the vertex of `Cofan.mk` does not reduce
syntactically inside `Cofan.IsColimit.mk`.

With `Localization.isColimitCofan` at the localization `Qh : K(A) ⥤ D(A)`, these are two of
the three inputs to coproducts in the derived category; the third, stability of
quasi-isomorphisms under coproducts, is where exactness of coproducts in `A` enters.
-/

open CategoryTheory Category Limits

universe w v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {κ : Type w} [HasColimitsOfShape (Discrete κ) C] (X : κ → HomologicalComplex C c)

/-- The morphism out of the quotient of `∐ X` induced by a cofan: the quotient of the
description by `Functor.preimage`s of the legs, then the identification of the vertex. -/
noncomputable def cofanDesc (t : Cofan fun k => (quotient C c).obj (X k)) :
    (quotient C c).obj (∐ X) ⟶ t.pt :=
  (quotient C c).map (Sigma.desc fun k =>
    (quotient C c).preimage (t.inj k ≫ ((quotient C c).objObjPreimageIso t.pt).inv)) ≫
    ((quotient C c).objObjPreimageIso t.pt).hom

/-- The `fac` field of `Cofan.IsColimit.mk` for `isColimitCofan`. -/
lemma cofanDesc_fac (t : Cofan fun k => (quotient C c).obj (X k)) (k : κ) :
    (quotient C c).map (Sigma.ι X k) ≫ cofanDesc X t = t.inj k := by
  unfold cofanDesc
  rw [← assoc, ← Functor.map_comp, Sigma.ι_desc, Functor.map_preimage, assoc, Iso.inv_hom_id,
    comp_id]

/-- A morphism out of the quotient of `∐ X` is determined by its restrictions to the summands:
it lifts to a chain map, the two lifts are homotopic on each summand, and `Homotopy.sigma`
assembles those homotopies. -/
lemma cofanDesc_uniq (t : Cofan fun k => (quotient C c).obj (X k))
    (m : (quotient C c).obj (∐ X) ⟶ t.pt)
    (hm : ∀ k, (quotient C c).map (Sigma.ι X k) ≫ m = t.inj k) : m = cofanDesc X t := by
  obtain ⟨g, hg⟩ := (quotient C c).map_surjective
    (m ≫ ((quotient C c).objObjPreimageIso t.pt).inv)
  have hmg : m = (quotient C c).map g ≫ ((quotient C c).objObjPreimageIso t.pt).hom := by
    rw [hg, assoc, Iso.inv_hom_id, comp_id]
  rw [hmg]
  unfold cofanDesc
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  apply Homotopy.sigma
  intro k
  apply HomotopyCategory.homotopyOfEq
  rw [Functor.map_comp, hg, ← assoc, hm k, Sigma.ι_desc, Functor.map_preimage]

/-- The quotient of a coproduct of complexes is a coproduct in the homotopy category. -/
noncomputable def isColimitCofan :
    IsColimit (Cofan.mk ((quotient C c).obj (∐ X)) fun k => (quotient C c).map (Sigma.ι X k)) :=
  Cofan.IsColimit.mk _ (cofanDesc X) (cofanDesc_fac X) (fun t m hm => cofanDesc_uniq X t m hm)

/-- The quotient functor preserves the coproduct of a family of complexes. -/
instance preservesColimit_discrete_functor :
    PreservesColimit (Discrete.functor X) (quotient C c) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm (isColimitCofan X))

/-- The quotient functor preserves coproducts of shape `κ`. -/
instance quotient_preservesColimitsOfShape_discrete :
    PreservesColimitsOfShape (Discrete κ) (quotient C c) :=
  preservesColimitsOfShape_of_discrete _

/-- The homotopy category has coproducts of shape `κ` when the underlying category does:
every family is isomorphic to the image of a family of complexes, whose coproduct
`isColimitCofan` exhibits. -/
instance hasColimitsOfShape_discrete : HasColimitsOfShape (Discrete κ) (HomotopyCategory C c) := by
  constructor
  intro F
  choose X hX using fun k => quotient_obj_surjective (F.obj ⟨k⟩)
  have e : F ≅ Discrete.functor fun k => (quotient C c).obj (X k) :=
    Discrete.natIso fun ⟨k⟩ => eqToIso (hX k).symm
  haveI : HasColimit (Discrete.functor fun k => (quotient C c).obj (X k)) :=
    ⟨⟨_, isColimitCofan X⟩⟩
  exact hasColimit_of_iso e

end HomotopyCategory
