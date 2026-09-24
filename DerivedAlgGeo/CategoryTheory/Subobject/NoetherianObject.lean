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

In the other direction, a chain of subobjects in a target object stabilizes if
it lifts to subobjects of one Noetherian source object. This requires a fixed
ambient object for the whole chain, not merely Noetherianity of each term.

The targets are allowed to depend on the index. This is essential for geometric applications:
restriction to the members `Uᵢ` of an open cover lands in the different categories `Coh Uᵢ`.

## Main results

* `isNoetherianObject_of_finite_jointlyReflectsIsomorphisms` — finite-family detection.
* `isNoetherianObject_of_liftedSubobjectChains` — transfer from anchored chain lifts.
* `anchored_chain_of_pointwise_lifts_iso` — build an anchored chain from pointwise lifts
  when the functor preserves binary joins of subobjects.
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

The family may have dependent target categories. The reflection hypothesis is stated pointwise
in the form consumed by the proof; Mathlib's `JointlyReflectIsomorphisms` also supports
dependent targets. -/
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

/-- A mono-preserving functor transfers Noetherianity to a target object if
every increasing chain of its subobjects lifts, up to an isomorphism of the
ambient object, to a chain of subobjects of one Noetherian source object.
The source object may depend on the chain. No isomorphism reflection is needed:
stabilization is carried forward by the functor. -/
theorem isNoetherianObject_of_liftedSubobjectChains
    {D : Type u₂} [Category.{v₂} D] (G : A ⥤ D)
    [G.PreservesMonomorphisms] (Y : D)
    (hlift : ∀ c : ℕ →o Subobject Y,
      ∃ (X : A) (e : G.obj X ≅ Y) (d : ℕ →o Subobject X),
        IsNoetherianObject X ∧
          ∀ n, (Subobject.map e.hom).obj (Subobject.mapFunctor G (d n)) = c n) :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro c
  obtain ⟨X, e, d, hX, hd⟩ := hlift c
  letI : IsNoetherianObject X := hX
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject d
  refine ⟨n, fun m hm ↦ ?_⟩
  calc
    c n = (Subobject.map e.hom).obj (Subobject.mapFunctor G (d n)) := (hd n).symm
    _ = (Subobject.map e.hom).obj (Subobject.mapFunctor G (d m)) := by rw [hn m hm]
    _ = c m := hd m

/-- Pointwise lifts of an increasing target-subobject chain can be made increasing
in one source ambient object by taking successive binary joins. Preservation of
these joins is an explicit hypothesis; preservation of monomorphisms alone does
not supply it. -/
theorem anchored_chain_of_pointwise_lifts
    {D : Type u₂} [Category.{v₂} D]
    [HasImages A] [HasBinaryCoproducts A]
    [HasImages D] [HasBinaryCoproducts D]
    (G : A ⥤ D) [G.PreservesMonomorphisms] (X : A)
    (hjoin : ∀ p q : Subobject X,
      Subobject.mapFunctor G (p ⊔ q) =
        Subobject.mapFunctor G p ⊔ Subobject.mapFunctor G q)
    (c : ℕ →o Subobject (G.obj X))
    (hpt : ∀ n : ℕ, ∃ p : Subobject X, Subobject.mapFunctor G p = c n) :
    ∃ d : ℕ →o Subobject X, ∀ n, Subobject.mapFunctor G (d n) = c n := by
  classical
  choose p hp using hpt
  let d : ℕ → Subobject X := fun n => Nat.rec (p 0) (fun k acc => acc ⊔ p (k + 1)) n
  have hstep (n : ℕ) : d n ≤ d (n + 1) := by
    change d n ≤ d n ⊔ p (n + 1)
    exact le_sup_left
  have hm : Monotone d := monotone_nat_of_le_succ hstep
  refine ⟨⟨d, hm⟩, ?_⟩
  intro n
  induction n with
  | zero => exact hp 0
  | succ n ih =>
      change Subobject.mapFunctor G (d n) = c n at ih
      change Subobject.mapFunctor G (d n ⊔ p (n + 1)) = c (n + 1)
      rw [hjoin, ih, hp]
      exact sup_eq_right.mpr (c.monotone (Nat.le_succ n))

/-- The pointwise-to-anchored construction when the target ambient object is
identified with the functor image by an isomorphism. -/
theorem anchored_chain_of_pointwise_lifts_iso
    {D : Type u₂} [Category.{v₂} D]
    [HasImages A] [HasBinaryCoproducts A]
    [HasImages D] [HasBinaryCoproducts D]
    (G : A ⥤ D) [G.PreservesMonomorphisms]
    (X : A) {Y : D} (e : G.obj X ≅ Y)
    (hjoin : ∀ p q : Subobject X,
      Subobject.mapFunctor G (p ⊔ q) =
        Subobject.mapFunctor G p ⊔ Subobject.mapFunctor G q)
    (c : ℕ →o Subobject Y)
    (hpt : ∀ n : ℕ, ∃ p : Subobject X,
      (Subobject.map e.hom).obj (Subobject.mapFunctor G p) = c n) :
    ∃ d : ℕ →o Subobject X, ∀ n,
      (Subobject.map e.hom).obj (Subobject.mapFunctor G (d n)) = c n := by
  let E := Subobject.mapIsoToOrderIso e
  let c' : ℕ →o Subobject (G.obj X) :=
    ⟨fun n => E.symm (c n), fun a b h => E.symm.monotone (c.monotone h)⟩
  have hp : ∀ n : ℕ, ∃ p : Subobject X, Subobject.mapFunctor G p = c' n := by
    intro n
    obtain ⟨p, hp⟩ := hpt n
    refine ⟨p, ?_⟩
    apply E.injective
    change E (Subobject.mapFunctor G p) = E (E.symm (c n))
    change E (Subobject.mapFunctor G p) = c n at hp
    simpa only [E.apply_symm_apply] using hp
  obtain ⟨d, hd⟩ := anchored_chain_of_pointwise_lifts G X hjoin c' hp
  refine ⟨d, ?_⟩
  intro n
  change E (Subobject.mapFunctor G (d n)) = c n
  rw [hd]
  exact E.apply_symm_apply (c n)

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
