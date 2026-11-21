/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.Over
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

/-!
# The total stack of a stack in groupoids on a slice site

Let `J` be a Grothendieck topology on `C` and `S : C` an object for which `yoneda.obj S` is a
`J`-sheaf. A stack in groupoids `X` on `Over S`, for the slice topology `J.over S`, has a total
stack in groupoids on `C`, whose fibre over `Y` is `Σ (p : Y ⟶ S), X(Y, p)`. When `J` is
subcanonical, forgetting the second component is a morphism of stacks to the stack represented by
`S`.

## Main definitions

* `CategoryTheory.StackInGroupoids.overTotal`: the total stack in groupoids of a stack in
  groupoids on `Over S`.
* `CategoryTheory.StackInGroupoids.overTotalπ`: its projection to
  `CategoryTheory.StackInGroupoids.representable J S`.

## Main results

None; the stack property of the total is
`CategoryTheory.Pseudofunctor.isStack_overTotal_iff`.

## Implementation notes

The underlying pseudofunctor is `CategoryTheory.Pseudofunctor.overTotal`, and its stack property
is `CategoryTheory.Pseudofunctor.isStack_overTotal_of_isStack`, whose hypothesis is that
`yoneda.obj S` is a sheaf. A disjoint union of groupoids is a groupoid, because a morphism of the
disjoint union lies in one summand. The projection needs the represented stack, so it assumes
that `J` is subcanonical.

The total stack has fibres in `Cat.{max v v' u', max v u'}` when `X` has fibres in
`Cat.{v', u'}`, so the projection targets the universe lift
`CategoryTheory.StackInGroupoids.representable.{max v' u', u'} J S`. When `v' = u' = v`, both
stacks have fibres in `Cat.{v, v}`. The fibres of the represented stack are discrete, so the
coherence conditions of the projection hold because parallel morphisms there are equal.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)

## Tags

stack in groupoids, slice site, total stack, representable stack
-/

namespace CategoryTheory

open Opposite

noncomputable section

universe v' v u' u

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {S : C}

/-- The total stack in groupoids of a stack in groupoids `X` on `Over S`, when `yoneda.obj S` is
a `J`-sheaf: its fibre over `Y` is `Σ (p : Y ⟶ S), X(Y, p)`, and its underlying pseudofunctor is
`CategoryTheory.Pseudofunctor.overTotal`. -/
def overTotal (hS : Presieve.IsSheaf J (yoneda.obj S))
    (X : StackInGroupoids.{v', v, u', max u v} (Over S) (J.over S)) :
    StackInGroupoids.{max v v' u', v, max v u', u} C J where
  presheaf := X.presheaf.overTotal
  fiberIsGroupoid Y := ⟨fun {_ _} φ ↦ by
    obtain ⟨φ⟩ := φ
    exact (Sigma.incl (C := fun p : Y.as.unop ⟶ S ↦ X.presheaf.obj ⟨op (Over.mk p)⟩) _).map_isIso
      φ⟩
  isStack := X.presheaf.isStack_overTotal_of_isStack J hS

variable [J.Subcanonical]

/-- On a subcanonical site, the projection of the total stack of `X` to the stack represented by
`S`: it sends an object `(p, x)` of the fibre over `Y` to the morphism `p : Y ⟶ S`. -/
def overTotalπ (X : StackInGroupoids.{v', v, u', max u v} (Over S) (J.over S)) :
    StackMorphism
      (overTotal J (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj S)) X)
      (representable.{max v' u', u'} J S) where
  app _ := (Sigma.desc fun p ↦ (Functor.const _).obj (representableObj J p)).toCatHom
  naturality _ := Cat.Hom.isoMk (NatIso.ofComponents (fun _ ↦ eqToIso rfl)
    (fun _ ↦ Subsingleton.elim _ _))
  naturality_naturality _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))
  naturality_id _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))
  naturality_comp _ _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))

/-- The projection sends `(p, x)` to the object of the represented stack given by `p`,
definitionally. -/
@[simp]
theorem overTotalπ_app_obj (X : StackInGroupoids.{v', v, u', max u v} (Over S) (J.over S))
    {Y : C} (p : Y ⟶ S) (x : X.presheaf.obj ⟨op (Over.mk p)⟩) :
    ((overTotalπ J X).app Y).obj ⟨p, x⟩ = representableObj J p :=
  rfl

end StackInGroupoids

end

end CategoryTheory
