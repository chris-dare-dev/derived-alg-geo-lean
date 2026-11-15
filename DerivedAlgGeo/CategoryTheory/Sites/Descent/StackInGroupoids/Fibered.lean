/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Yoneda
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

/-!
# Stacks in groupoids are categories fibred in groupoids

For a stack in groupoids `X` on a site `(C, J)`, Mathlib's Grothendieck construction
`∫ᶜ X.presheaf`, with its projection `Pseudofunctor.CoGrothendieck.forget X.presheaf` to `C`,
is a category fibred in groupoids. On a subcanonical site, stack morphisms out of the
representable stack of `U` form a category equivalent to the fibre of `X` over `U`.

## Main definitions

* `CategoryTheory.StackInGroupoids.yonedaEquivalence`: the 2-Yoneda equivalence between stack
  morphisms out of `StackInGroupoids.representable J U` and the fibre `X(U)`.

## Main results

* `CategoryTheory.StackInGroupoids.isStronglyCartesian`: every morphism of `∫ᶜ X.presheaf` is
  strongly cartesian over its image in `C`.
* `CategoryTheory.StackInGroupoids.representable_presheaf`: the underlying pseudofunctor of the
  representable stack is `Pseudofunctor.representable`, definitionally.

## Implementation notes

Fibred categories are reached only through this comparison; the module adds no fibred-category
carrier and no class. Being fibred in groupoids is the conjunction of Mathlib's instances
`Pseudofunctor.CoGrothendieck.instIsFiberedForget` and
`Pseudofunctor.CoGrothendieck.instHasFibersForget`, whose fibre over `S` is `X(S)`, with
`StackInGroupoids.isStronglyCartesian`. A stack morphism `f` induces Mathlib's functor
`Pseudofunctor.CoGrothendieck.map f` over `C`.

`StackInGroupoids.representable J U` has underlying pseudofunctor
`(discretePseudofunctor (yoneda.obj U)).ulift`, and `discretePseudofunctor` unfolds to the
`(yoneda.obj U ⋙ typeToCat).toPseudofunctor'` used by `Pseudofunctor.representable`, so
`StackInGroupoids.yonedaEquivalence` is `Pseudofunctor.yonedaEquivalence` itself. Its source is
the hom-category `(representable J U).presheaf ⟶ X.presheaf` of Mathlib's scoped instance
`Pseudofunctor.StrongTrans.homCategory`. Its objects are exactly the stack morphisms
`StackMorphism (representable J U) X`, but instance search does not unfold the abbreviation
`StackMorphism`, so the statement names the hom-category.

Subcanonicity is used only to make the representable pseudofunctor a stack; the equivalence
itself needs no topology.

## References

* [Stacks Project, Tag 003T](https://stacks.math.columbia.edu/tag/003T): categories fibred in
  groupoids.
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V): a fibred category with
  groupoid fibres has only strongly cartesian morphisms.
* [Stacks Project, Tag 0049](https://stacks.math.columbia.edu/tag/0049): the category attached
  to a presheaf of groupoids is fibred in groupoids.
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B): the 2-Yoneda lemma.

## Tags

stack in groupoids, fibred category, category fibred in groupoids, 2-Yoneda lemma
-/

namespace CategoryTheory.StackInGroupoids

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck
open scoped Pseudofunctor.StrongTrans

universe w₁ w₂ v' u' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every morphism of the Grothendieck construction `∫ᶜ X.presheaf` of a stack in groupoids is
strongly cartesian over its image in `C` (Stacks Project, Tag 003V). Together with Mathlib's
instances `Pseudofunctor.CoGrothendieck.instIsFiberedForget`, which makes the projection fibred,
and `Pseudofunctor.CoGrothendieck.instHasFibersForget`, whose fibre over `S` is `X(S)`, this
makes `∫ᶜ X.presheaf` a category fibred in groupoids over `C` (Stacks Project, Tag 003T).

The groupoid fibres are what the proof uses: a morphism `φ` factors as the fibre inclusion of
`φ.fiber`, an isomorphism because `X(S)` is a groupoid, followed by the strongly cartesian lift
of `φ.base`. -/
theorem isStronglyCartesian (X : StackInGroupoids.{v', v, u', u} C J) {a b : ∫ᶜ X.presheaf}
    (φ : a ⟶ b) :
    (CoGrothendieck.forget X.presheaf).IsStronglyCartesian
      ((CoGrothendieck.forget X.presheaf).map φ) φ := by
  obtain ⟨R, x⟩ := a
  obtain ⟨S, y⟩ := b
  obtain ⟨f, h⟩ := φ
  let ψ : (⟨R, x⟩ : ∫ᶜ X.presheaf) ⟶ domainCartesianLift y f :=
    ⟨𝟙 R, h ≫ (X.presheaf.mapId ⟨op R⟩).inv.toNatTrans.app _⟩
  have hψ : ψ ≫ cartesianLift y f = ⟨f, h⟩ := by
    fapply Hom.ext
    · exact Category.id_comp f
    · simp [ψ, X.presheaf.mapComp_id_right_inv_app, Bicategory.Strict.rightUnitor_eqToIso,
        PrelaxFunctor.map₂_eqToHom]
  have : IsIso ψ := (inferInstance : IsIso ((ι X.presheaf R).map h))
  have : (CoGrothendieck.forget X.presheaf).IsHomLift (𝟙 R) ψ :=
    Functor.IsHomLift.map (p := CoGrothendieck.forget X.presheaf) ψ
  have : (CoGrothendieck.forget X.presheaf).IsStronglyCartesian f (cartesianLift y f) :=
    isStronglyCartesian_homCartesianLift y f
  have hcomp : (CoGrothendieck.forget X.presheaf).IsStronglyCartesian (𝟙 R ≫ f)
      (ψ ≫ cartesianLift y f) := inferInstance
  rw [hψ, Category.id_comp] at hcomp
  exact hcomp

/-- The underlying pseudofunctor of the representable stack is the representable pseudofunctor,
definitionally: `CategoryTheory.discretePseudofunctor` unfolds to
`(yoneda.obj U ⋙ typeToCat).toPseudofunctor'`. -/
lemma representable_presheaf [J.Subcanonical] (U : C) :
    (representable.{w₁, w₂} J U).presheaf = Pseudofunctor.representable.{w₁, w₂} U :=
  rfl

/-- **The 2-Yoneda lemma for stacks in groupoids** (Stacks Project, Tag 004B). On a subcanonical
site, evaluation at the universal point `𝟙 U` identifies the stack morphisms from
`StackInGroupoids.representable J U` to `X`, with modifications as morphisms, with the fibre
`X(U)`. It is `CategoryTheory.Pseudofunctor.yonedaEquivalence` for the underlying
pseudofunctors. -/
def yonedaEquivalence [J.Subcanonical] (X : StackInGroupoids.{max v w₁, v, max v w₂, u} C J)
    (U : C) :
    ((representable.{w₁, w₂} J U).presheaf ⟶ X.presheaf) ≌ X.presheaf.obj (.mk (op U)) :=
  Pseudofunctor.yonedaEquivalence X.presheaf U

/-- `CategoryTheory.StackInGroupoids.yonedaEquivalence` evaluates a stack morphism at the
universal point `𝟙 U`. -/
lemma yonedaEquivalence_functor_obj [J.Subcanonical]
    (X : StackInGroupoids.{max v w₁, v, max v w₂, u} C J) (U : C)
    (α : StackMorphism (representable.{w₁, w₂} J U) X) :
    (yonedaEquivalence X U).functor.obj α = (α.app U).obj (representableObj J (𝟙 U)) :=
  rfl

/-- The inverse of `CategoryTheory.StackInGroupoids.yonedaEquivalence` sends `x : X(U)` to the
stack morphism `g ↦ g^* x`. -/
lemma yonedaEquivalence_inverse_obj_app_obj [J.Subcanonical]
    (X : StackInGroupoids.{max v w₁, v, max v w₂, u} C J) {U T : C}
    (x : X.presheaf.obj (.mk (op U))) (g : T ⟶ U) :
    (StackMorphism.app (F := representable.{w₁, w₂} J U) (G := X)
        ((yonedaEquivalence X U).inverse.obj x) T).obj (representableObj J g) =
      (X.presheaf.map g.op.toLoc).toFunctor.obj x :=
  rfl

end CategoryTheory.StackInGroupoids
