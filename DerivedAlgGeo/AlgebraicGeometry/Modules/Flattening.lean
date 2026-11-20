/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# The flattening functor

For `p : X ⟶ S` and a module sheaf `F` on `X`, the flattening functor sends an `S`-scheme `T` to a
point if the base change `F_T` of `F` to `X ×_S T` is flat over `T`, and to the empty type
otherwise. Flatness over the base is stable under base change, so a morphism `T' ⟶ T` over `S`
carries the point over `T` to the point over `T'`. The functor is a subfunctor of the terminal
presheaf on `Over S`. Representing it is the universal flattening of Stacks 05P6.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.flatteningFunctor`: the functor `(Over S)ᵒᵖ ⥤ Type u`,
  `T ↦ {∗}` if `F_T` is flat over `T` and `∅` otherwise.
* `AlgebraicGeometry.Scheme.Modules.flatteningFunctor.toPUnit`: the inclusion into the terminal
  presheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.flatteningFunctor.map_of_isFlatOver`: if `F_T` is flat over
  `T`, so is `F_{T'}` over `T'`, for every morphism `T' ⟶ T` over `S`.
* `AlgebraicGeometry.Scheme.Modules.flatteningFunctor.instMonoToPUnit`: the inclusion into the
  terminal presheaf is a monomorphism.

## Implementation notes

The functor lives on `Over S` (a stack over `S` lives on `Over S`), with values in `Type u`
through `ULift (PLift _)`. Since the values are subsingletons, functoriality has no coherence to
check. The comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` is `quotFunctor.baseChangeIso`.

## References

* [Stacks, Tag 05P6](https://stacks.math.columbia.edu/tag/05P6): Definition 38.21.1, the
  universal flattening.
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, §4.

## Tags

flattening functor, flat, base change, representable functor
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.Modules

noncomputable section

variable {X S : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)

/-- **The flattening functor** (Stacks 05P6): `T ↦ {∗}` if the pullback `F_T` of `F` to
`X ×_S T` is flat over `T`, and `T ↦ ∅` otherwise. A morphism `T' ⟶ T` over `S` acts through the
stability of flatness under base change. -/
def flatteningFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (IsFlatOver (pullback.snd p T.unop.hom) (quotBaseChange p F T.unop)))
  map {T' T} g := TypeCat.ofHom fun x ↦
    ⟨⟨((x.down.down.of_isPullback (quotFunctor.isPullback_baseChangeHom p g.unop)).of_iso
      (quotFunctor.baseChangeIso p F g.unop).symm)⟩⟩
  map_id _ := by
    ext x
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    ext x
    exact Subsingleton.elim _ _

namespace flatteningFunctor

variable {p F}

/-- The values of the flattening functor have at most one element. -/
instance (T : (Over S)ᵒᵖ) : Subsingleton ((flatteningFunctor p F).obj T) :=
  ⟨fun x y ↦ by obtain ⟨⟨_⟩⟩ := x; obtain ⟨⟨_⟩⟩ := y; rfl⟩

/-- The flattening functor has a point over `T` exactly when `F_T` is flat over `T`. -/
theorem nonempty_obj_iff (T : Over S) :
    Nonempty ((flatteningFunctor p F).obj (op T)) ↔
      IsFlatOver (pullback.snd p T.hom) (quotBaseChange p F T) :=
  ⟨fun ⟨x⟩ ↦ x.down.down, fun h ↦ ⟨⟨⟨h⟩⟩⟩⟩

/-- **Flatness of the base change is stable under base change.** If `F_T` is flat over `T`, then
`F_{T'}` is flat over `T'` for every morphism `T' ⟶ T` over `S`. -/
theorem map_of_isFlatOver {T' T : Over S} (g : T' ⟶ T)
    (h : IsFlatOver (pullback.snd p T.hom) (quotBaseChange p F T)) :
    IsFlatOver (pullback.snd p T'.hom) (quotBaseChange p F T') :=
  ((flatteningFunctor p F).map g.op ⟨⟨h⟩⟩).down.down

variable (p F) in
/-- The flattening functor is a subfunctor of the terminal presheaf on `Over S`. -/
def toPUnit : flatteningFunctor p F ⟶ (Functor.const (Over S)ᵒᵖ).obj PUnit.{u + 1} where
  app _ := TypeCat.ofHom fun _ ↦ PUnit.unit

/-- The flattening functor is a subfunctor of the terminal presheaf: the inclusion is a
monomorphism. -/
instance instMonoToPUnit : Mono (toPUnit p F) :=
  haveI : ∀ T, Mono ((toPUnit p F).app T) := fun _ ↦
    (mono_iff_injective _).2 fun _ _ _ ↦ Subsingleton.elim _ _
  NatTrans.mono_of_mono_app _

end flatteningFunctor

end

end Scheme.Modules

end AlgebraicGeometry
