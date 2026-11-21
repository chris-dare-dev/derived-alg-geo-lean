/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Free
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic

/-!
# The Grassmannian functor

For `n k : ℕ`, `AlgebraicGeometry.Grassmannian.functor n k : Scheme.{u}ᵒᵖ ⥤ Type u` sends a
scheme `T` to the isomorphism classes of quotients `𝒪_T^n ↠ Q` with `Q` locally free of rank `k`.
A morphism `f : T' ⟶ T` acts by pullback: `f^* 𝒪_T^n ≅ 𝒪_{T'}^n` identifies the source of the
pulled-back quotient with `𝒪_{T'}^n`, and `f^* Q` is again locally free of rank `k`. Two
quotients are the same point when they are isomorphic under `𝒪_T^n`.

This is the quotient convention of Mathlib's `Module.Grassmannian`: the points over a ring `A`
are the quotients of `A ⊗ M` that are finite projective of rank `k`, not subspaces. The
agreement of the two, the Zariski sheaf property and representability by a scheme are separate
statements.

## Main definitions

* `AlgebraicGeometry.Grassmannian.pointProperty`: the quotients of `𝒪_T^n` that are locally free
  of rank `k`.
* `AlgebraicGeometry.Grassmannian.functor`: the functor of isomorphism classes of such quotients.
* `AlgebraicGeometry.Grassmannian.point`: the point of the functor given by a quotient.

## Main results

* `AlgebraicGeometry.Grassmannian.point_eq_point_iff`: two quotients give the same point exactly
  when they are isomorphic as quotients of `𝒪_T^n`.
* `AlgebraicGeometry.Grassmannian.functor_map_point`: the action of a morphism on a point is the
  pullback of the quotient.

## Implementation notes

The points over `T` are `Shrink.{u}` of the isomorphism classes, in Mathlib's
`isIsomorphicSetoid`, of the full subcategory of rank-`k` quotients of `free (ULift (Fin n))`;
these live in `Type u` because `T.Modules` is well-powered
(`ModuleQuotient.small_isIsomorphicSetoid`). The index type `Fin n` is lifted to `Type u`
because `SheafOfModules.free` takes an index type in the universe of the sheaf of rings.

The functor laws are the coherences of `ModuleQuotient.pullbackVia`, applied to the identification
`f^* (free I) ≅ free I` of `Modules/Pullback/Free.lean`.

## References

* [Stacks, Tag 089R](https://stacks.math.columbia.edu/tag/089R): the Grassmannian of a module.
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, §1.

## Tags

Grassmannian, quotient, locally free sheaf, functor of points
-/

open CategoryTheory Opposite SheafOfModules

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

noncomputable section

variable (n k : ℕ)

/-- The quotients of `𝒪_T^n` whose target is locally free of rank `k`. -/
def pointProperty (T : Scheme.{u}) :
    ObjectProperty (ModuleQuotient (free (ULift.{u} (Fin n)) : T.Modules)) :=
  fun q ↦ IsLocallyFreeOfRank.{u, u, u} (show SheafOfModules T.ringCatSheaf from q.target) k

instance (T : Scheme.{u}) : (pointProperty n k T).IsClosedUnderIsomorphisms where
  of_iso e h := h.ofIso ((ModuleQuotient.targetFunctor _).mapIso e)

variable {n k} {T T' T'' : Scheme.{u}}

/-- Pull a rank-`k` quotient of `𝒪_T^n` back along `f : T' ⟶ T`, as a quotient of `𝒪_{T'}^n`:
the pullback of the quotient arrow, read on `𝒪_{T'}^n` through `f^* 𝒪_T^n ≅ 𝒪_{T'}^n`. -/
def pullbackPoint (f : T' ⟶ T) (r : (pointProperty n k T).FullSubcategory) :
    (pointProperty n k T').FullSubcategory :=
  ⟨ModuleQuotient.pullbackVia f (pullbackFreeIso (ULift.{u} (Fin n)) f).symm r.obj,
    isLocallyFreeOfRank_pullback f _ r.property⟩

/-- Base change of isomorphism classes of rank-`k` quotients. -/
def pullbackClass (f : T' ⟶ T) :
    Quotient (isIsomorphicSetoid (pointProperty n k T).FullSubcategory) →
      Quotient (isIsomorphicSetoid (pointProperty n k T').FullSubcategory) :=
  Quotient.map (pullbackPoint f) fun _ _ ⟨i⟩ ↦
    ⟨ObjectProperty.isoMk _ (ModuleQuotient.pullbackViaIso _ _ ((ObjectProperty.ι _).mapIso i))⟩

lemma pullbackClass_id
    (x : Quotient (isIsomorphicSetoid (pointProperty n k T).FullSubcategory)) :
    pullbackClass (𝟙 T) x = x := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound ⟨ObjectProperty.isoMk _
    (ModuleQuotient.pullbackViaId (b := 𝟙 T) rfl _ ?_ r.obj)⟩
  have h : (pullbackCongr (rfl : 𝟙 T = 𝟙 T)).hom.app
      (free (ULift.{u} (Fin n)) : T.Modules) = 𝟙 _ := by
    simp [pullbackCongr]
  simp only [Iso.symm_hom]
  rw [h, Category.id_comp, ← pullbackFreeIso_id]
  exact Iso.inv_hom_id _

lemma pullbackClass_comp (g : T'' ⟶ T') (f : T' ⟶ T)
    (x : Quotient (isIsomorphicSetoid (pointProperty n k T).FullSubcategory)) :
    pullbackClass (g ≫ f) x = pullbackClass g (pullbackClass f x) := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound ⟨ObjectProperty.isoMk _
    (ModuleQuotient.pullbackViaComp g f rfl _ _ _ ?_ r.obj).symm⟩
  simp only [Iso.symm_hom]
  refine (cancel_mono (pullbackFreeIso (ULift.{u} (Fin n)) (g ≫ f)).hom).1 ?_
  rw [Iso.inv_hom_id, ← pullbackFreeIso_comp (ULift.{u} (Fin n)) g f]
  simp [pullbackCongr, ← Functor.map_comp_assoc]

variable (n k)

/-- **The Grassmannian functor.** It sends a scheme `T` to the isomorphism classes of quotients
`𝒪_T^n ↠ Q` with `Q` locally free of rank `k`, and a morphism `T' ⟶ T` to pullback of quotients.
This is the quotient convention of Mathlib's `Module.Grassmannian`. -/
def functor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (Quotient (isIsomorphicSetoid (pointProperty n k T.unop).FullSubcategory))
  map f := TypeCat.ofHom fun x ↦ equivShrink _ (pullbackClass f.unop ((equivShrink _).symm x))
  map_id T := by
    ext x
    simp [pullbackClass_id]
  map_comp f g := by
    ext x
    simp [pullbackClass_comp]

variable {n k}

/-- The point of the Grassmannian functor over `T` given by a quotient of `𝒪_T^n` that is locally
free of rank `k`. -/
def point (q : ModuleQuotient (free (ULift.{u} (Fin n)) : T.Modules))
    (hq : pointProperty n k T q) : (functor n k).obj (op T) :=
  equivShrink _ (Quotient.mk _ ⟨q, hq⟩)

/-- Two quotients give the same point of the Grassmannian functor exactly when they are
isomorphic as quotients of `𝒪_T^n`. -/
theorem point_eq_point_iff {q q' : ModuleQuotient (free (ULift.{u} (Fin n)) : T.Modules)}
    (hq : pointProperty n k T q) (hq' : pointProperty n k T q') :
    point q hq = point q' hq' ↔ Nonempty (q ≅ q') := by
  rw [point, point, (equivShrink _).apply_eq_iff_eq]
  refine ⟨fun h ↦ ?_, fun ⟨i⟩ ↦ Quotient.sound ⟨ObjectProperty.isoMk _ i⟩⟩
  obtain ⟨i⟩ := Quotient.exact h
  exact ⟨(ObjectProperty.ι _).mapIso i⟩

/-- Every point of the Grassmannian functor is given by a quotient. -/
theorem exists_eq_point (x : (functor n k).obj (op T)) :
    ∃ (q : ModuleQuotient (free (ULift.{u} (Fin n)) : T.Modules)) (hq : pointProperty n k T q),
      x = point q hq := by
  obtain ⟨⟨q, hq⟩, h⟩ := Quotient.exists_rep ((equivShrink _).symm x)
  exact ⟨q, hq, by rw [point, h, Equiv.apply_symm_apply]⟩

/-- A morphism acts on a point by pullback of the quotient. -/
theorem functor_map_point (f : T' ⟶ T) (q : ModuleQuotient (free (ULift.{u} (Fin n)) : T.Modules))
    (hq : pointProperty n k T q) :
    (functor n k).map f.op (point q hq) =
      point (ModuleQuotient.pullbackVia f (pullbackFreeIso (ULift.{u} (Fin n)) f).symm q)
        (isLocallyFreeOfRank_pullback f _ hq) := by
  change equivShrink _ (pullbackClass f ((equivShrink _).symm (equivShrink _ _))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end

end AlgebraicGeometry.Grassmannian
