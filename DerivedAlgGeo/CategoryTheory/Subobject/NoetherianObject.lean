/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Noetherian objects detected by finitely many functors

A mono-preserving functor carries a chain of subobjects to a chain. If finitely many such
functors jointly reflect isomorphisms, and every image of an object is Noetherian, the original
object is Noetherian: choose a stabilization index in every target, take their finite supremum,
and reflect that the resulting chain step is an isomorphism.

The targets are allowed to depend on the index. This is essential for geometric applications:
restriction to the members `Uᵢ` of an open cover lands in the different categories `Coh Uᵢ`.

## Main results

* `isNoetherianObject_of_finite_jointlyReflectsIsomorphisms` — finite-family detection.
* `isNoetherianObject_of_reflectsIsomorphisms` — the one-functor specialization.
-/

universe w v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

variable {ι : Type w} [Finite ι]
  {A : Type u₁} [Category.{v₁} A]
  {B : ι → Type u₂} [∀ i, Category.{v₂} (B i)]
  (F : ∀ i, A ⥤ B i) [∀ i, (F i).PreservesMonomorphisms]
  {X : A}

private lemma isIso_ofLE_of_eq {C : Type u₁} [Category.{v₁} C]
    {Y : C} {P Q : Subobject Y} (h : P ≤ Q) (e : P = Q) :
    IsIso (Subobject.ofLE P Q h) := by
  subst Q
  rw [Subobject.ofLE_refl]
  infer_instance

/-- **A finite family of mono-preserving functors which jointly reflects isomorphisms detects
Noetherian objects.**

The family may have dependent target categories. The reflection hypothesis is correspondingly
stated pointwise instead of using Mathlib's fixed `JointlyReflectIsomorphisms`, whose functors have
a common target. -/
theorem isNoetherianObject_of_finite_jointlyReflectsIsomorphisms
    (hX : ∀ i, IsNoetherianObject ((F i).obj X))
    (hreflect : ∀ {Y Z : A} (f : Y ⟶ Z),
      (∀ i, IsIso ((F i).map f)) → IsIso f) :
    IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro c
  have hi (i : ι) : ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      Subobject.mapFunctor (F i) (c n) = Subobject.mapFunctor (F i) (c m) := by
    letI : IsNoetherianObject ((F i).obj X) := hX i
    exact monotone_chain_condition_of_isNoetherianObject
      ⟨fun n ↦ Subobject.mapFunctor (F i) (c n),
        Subobject.mapFunctor_monotone (F i) |>.comp c.monotone⟩
  choose n hn using hi
  letI := Fintype.ofFinite ι
  let N := Finset.univ.sup n
  refine ⟨N, fun m hm ↦ ?_⟩
  let step := Subobject.ofLE (c N) (c m) (c.monotone hm)
  haveI : IsIso step := hreflect step fun i ↦ by
    let hNi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    have heq : Subobject.mapFunctor (F i) (c N) =
        Subobject.mapFunctor (F i) (c m) :=
      (hn i N hNi).symm.trans (hn i m (hNi.trans hm))
    let localStep := Subobject.ofLE
      (Subobject.mapFunctor (F i) (c N))
      (Subobject.mapFunctor (F i) (c m))
      (Subobject.mapFunctor_monotone (F i) (c.monotone hm))
    haveI : IsIso localStep := isIso_ofLE_of_eq _ heq
    have hfac := Subobject.ofLE_mapFunctor (F i) (c.monotone hm)
    haveI : IsIso
        ((Subobject.mapFunctorIso (F i) (c N)).hom ≫ (F i).map step) := by
      rw [← hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left (Subobject.mapFunctorIso (F i) (c N)).hom _
  calc
    c N = Subobject.mk (c N).arrow := (Subobject.mk_arrow _).symm
    _ = Subobject.mk (c m).arrow :=
      Subobject.mk_eq_mk_of_comm _ _ (asIso step) (Subobject.ofLE_arrow _)
    _ = c m := Subobject.mk_arrow _

/-- A mono-preserving, isomorphism-reflecting functor detects Noetherian objects. -/
theorem isNoetherianObject_of_reflectsIsomorphisms
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] (F : A ⥤ B)
    [F.PreservesMonomorphisms] [F.ReflectsIsomorphisms] {X : A}
    [IsNoetherianObject (F.obj X)] : IsNoetherianObject X := by
  apply isNoetherianObject_of_finite_jointlyReflectsIsomorphisms
    (fun _ : Fin 1 ↦ F) (fun _ ↦ inferInstance)
  intro Y Z f hf
  letI : IsIso (F.map f) := hf 0
  exact isIso_of_reflects_iso f F

end CategoryTheory
