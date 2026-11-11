/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData

/-!
# Invariance of the stack condition

A strong transformation `α : F ⟶ G` of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose
components are equivalences of categories identifies the descent problems of `F` and `G`.
Hence `F` is a prestack (a stack) for a Grothendieck topology exactly when `G` is. An
equivalence in the bicategory of pseudofunctors is a special case.

## Main definitions

None. The comparison functor `Pseudofunctor.DescentData.map` and the square
`Pseudofunctor.toDescentDataCompMapIso` are in
`DerivedAlgGeo/CategoryTheory/Sites/Descent/DescentData.lean`.

## Main results

* `Pseudofunctor.isPrestack_iff_of_isEquivalence`
* `Pseudofunctor.isStack_iff_of_isEquivalence`
* `Pseudofunctor.isStack_iff_of_equivalence`

## Implementation notes

The argument runs one covering sieve at a time. In the square
`toDescentDataCompMapIso f α`, the functors `DescentData.map f α` and
`(α.app _).toFunctor` are equivalences, so the restriction functor of `F` is fully
faithful (an equivalence) exactly when that of `G` is. The stack condition of `G` is never
assumed, and no inverse strong transformation is constructed.

## References

* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)

## Tags

stack, prestack, descent, strong transformation, equivalence
-/

universe v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

private lemma isPrestackFor_iff_of_isEquivalence (α : F ⟶ G)
    [∀ X, (α.app X).toFunctor.IsEquivalence] {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ G.IsPrestackFor R.arrows := by
  let e := toDescentDataCompMapIso (fun (a : R.arrows.category) ↦ a.obj.hom) α
  let a := (α.app (.mk (op S))).toFunctor.asEquivalence
  simp only [isPrestackFor_iff]
  refine ⟨fun ⟨h⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · exact (a.fullyFaithfulInverse.comp
      ((h.comp (DescentData.map _ α).asEquivalence.fullyFaithfulFunctor).ofIso e)).ofIso
      (a.invFunIdAssoc _)
  · exact Functor.FullyFaithful.ofCompFaithful (G := DescentData.map _ α)
      ((a.fullyFaithfulFunctor.comp h).ofIso e.symm)

private lemma isStackFor_iff_of_isEquivalence (α : F ⟶ G)
    [∀ X, (α.app X).toFunctor.IsEquivalence] {S : C} (R : Sieve S) :
    F.IsStackFor R.arrows ↔ G.IsStackFor R.arrows := by
  let e := toDescentDataCompMapIso (fun (a : R.arrows.category) ↦ a.obj.hom) α
  simp only [isStackFor_iff]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := Functor.isEquivalence_of_iso e
    exact Functor.isEquivalence_of_comp_left (α.app (.mk (op S))).toFunctor _
  · have := Functor.isEquivalence_of_iso e.symm
    exact Functor.isEquivalence_of_comp_right _ (DescentData.map _ α)

/-- Descent of morphisms is invariant under a strong transformation whose components are
equivalences of categories. -/
theorem isPrestack_iff_of_isEquivalence (α : F ⟶ G)
    [∀ X, (α.app X).toFunctor.IsEquivalence] (J : GrothendieckTopology C) :
    F.IsPrestack J ↔ G.IsPrestack J :=
  ⟨fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_iff_of_isEquivalence α R).1 (F.isPrestackFor' R hR),
    fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_iff_of_isEquivalence α R).2 (G.isPrestackFor' R hR)⟩

/-- Being a stack is invariant under a strong transformation whose components are
equivalences of categories: this is [Stacks Project, Tag 042W] for pseudofunctors, and
[Stacks Project, Tag 042X] when the fibres are groupoids.

The hypothesis is needed at every object. On the open sets of the two-point discrete
space `{p, q}` with the open-cover topology, let `Q` be the presheaf with `Q {p, q} = Bool`
and `Q U = PUnit` for every other open `U`; it is not separated, since `true` and `false`
agree on the cover by `{p}` and `{q}`. The global section `true` induces a strong
transformation from `discretePseudofunctor` of the terminal presheaf, which is a stack, to
`discretePseudofunctor Q`, which is not. Its component at `{p, q}` is
`Discrete PUnit ⥤ Discrete Bool`, the only one that is not an equivalence. -/
theorem isStack_iff_of_isEquivalence (α : F ⟶ G)
    [∀ X, (α.app X).toFunctor.IsEquivalence] (J : GrothendieckTopology C) :
    F.IsStack J ↔ G.IsStack J :=
  ⟨fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_iff_of_isEquivalence α R).1 (F.isStackFor' R hR),
    fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_iff_of_isEquivalence α R).2 (G.isStackFor' R hR)⟩

/-- The component at `X` of an invertible modification. -/
private def appIso {α α' : F ⟶ G} (e : α ≅ α') (X : LocallyDiscrete Cᵒᵖ) :
    α.app X ≅ α'.app X where
  hom := e.hom.as.app X
  inv := e.inv.as.app X
  hom_inv_id := congr_arg (fun m ↦ m.as.app X) e.hom_inv_id
  inv_hom_id := congr_arg (fun m ↦ m.as.app X) e.inv_hom_id

/-- Being a stack is invariant under an equivalence in the bicategory of pseudofunctors.
The unit and counit of `e` make every component of `e.hom` an equivalence of categories. -/
theorem isStack_iff_of_equivalence (e : Bicategory.Equivalence F G)
    (J : GrothendieckTopology C) : F.IsStack J ↔ G.IsStack J :=
  have (X : LocallyDiscrete Cᵒᵖ) : (e.hom.app X).toFunctor.IsEquivalence :=
    (CategoryTheory.Equivalence.mk (e.hom.app X).toFunctor (e.inv.app X).toFunctor
      (Cat.Hom.toNatIso (appIso e.unit X))
      (Cat.Hom.toNatIso (appIso e.counit X))).isEquivalence_functor
  isStack_iff_of_isEquivalence e.hom J

end CategoryTheory.Pseudofunctor
