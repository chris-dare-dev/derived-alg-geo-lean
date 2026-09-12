/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Ext along an exact functor, from a class of acyclic generators

Let `F : D ⥤ C` be an exact functor between abelian categories, and let `Q` be a class of
objects of `D` such that

* every object of `D` receives an epimorphism from an object of `Q`,
* `Ext^(n+1) P Y = 0` in `D` for `P ∈ Q` and every `Y`,
* `Ext^(n+1) (F P) (F Y) = 0` in `C` for `P ∈ Q` and every `Y`, and
* `F` is bijective on `Ext⁰`, for instance because it is fully faithful.

Then `F` induces bijections `Ext^n X Y → Ext^n (F X) (F Y)` for all `X`, `Y` and `n`. The
proof is dimension shifting in the *first* variable along `K ↪ P ↠ X`, using the
contravariant long exact sequences of `Ext` in both categories; it is the mirror image of
`extComparisonAddEquiv` in `Ext/AcyclicComparison.lean`, which shifts in the second variable
along injective presentations.

The intended use is the inclusion of coherent sheaves on an affine noetherian scheme into
all module sheaves, with `Q` the free sheaves `𝒪^k`: they are projective among coherent
sheaves, and `Ext^(n+1) (𝒪^k, G)` in all module sheaves is `H^(n+1)(G)^k`, which vanishes
for quasi-coherent `G` on an affine scheme.

## Main results

* `Ext.subsingleton_of_iso_left`, `Ext.subsingleton_biproduct_left` — vanishing of `Ext`
  transports along isomorphisms and finite biproducts in the first variable;
  `Ext.subsingleton_coproduct_left` is the corresponding arbitrary-coproduct
  statement when the derived single functor preserves that coproduct.
* `Functor.bijective_mapExtAddHom_zero_iff`, `Functor.bijective_mapExtAddHom_zero` — degree
  zero.
* `Functor.surjective_mapExtAddHom_of_generators`,
  `Functor.injective_mapExtAddHom_of_generators`,
  `Functor.bijective_mapExtAddHom_of_generators` — the theorem.
-/

universe w w' w'' v v' u u'

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

section Vanishing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Vanishing of `Ext` transports along an isomorphism in the first variable. -/
lemma Ext.subsingleton_of_iso_left {X X' Y : C} (e : X ≅ X') (n : ℕ)
    (h : Subsingleton (Ext.{w} X' Y n)) : Subsingleton (Ext.{w} X Y n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    have h : x = (Ext.mk₀ (e.hom ≫ e.inv)).comp x (zero_add n) := by
      rw [e.hom_inv_id, Ext.mk₀_id_comp]
    rw [h, ← Ext.mk₀_comp_mk₀_assoc,
      Subsingleton.elim ((Ext.mk₀ e.inv).comp x (zero_add n)) 0, Ext.comp_zero]

/-- `Ext` out of a finite biproduct vanishes when `Ext` out of each summand does. -/
lemma Ext.subsingleton_biproduct_left {J : Type} [Fintype J] (f : J → C) [HasBiproduct f]
    (Y : C) (n : ℕ) (h : ∀ j, Subsingleton (Ext.{w} (f j) Y n)) :
    Subsingleton (Ext.{w} (⨁ f) Y n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    have h1 : Ext.mk₀ (∑ j : J, biproduct.π f j ≫ biproduct.ι f j) =
        ∑ j : J, Ext.mk₀ (biproduct.π f j ≫ biproduct.ι f j) := by
      simpa using map_sum Ext.addEquiv₀.symm (fun j ↦ biproduct.π f j ≫ biproduct.ι f j)
        Finset.univ
    have h2 := map_sum ((Ext.bilinearComp (⨁ f) (⨁ f) Y 0 n n (zero_add n)).flip x)
      (fun j ↦ Ext.mk₀ (biproduct.π f j ≫ biproduct.ι f j)) Finset.univ
    simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply] at h2
    calc x = (Ext.mk₀ (𝟙 (⨁ f))).comp x (zero_add n) := (Ext.mk₀_id_comp x).symm
      _ = ∑ j : J, (Ext.mk₀ (biproduct.π f j ≫ biproduct.ι f j)).comp x (zero_add n) := by
          rw [← biproduct.total, h1, h2]
      _ = 0 := Finset.sum_eq_zero fun j _ ↦ by
          rw [← Ext.mk₀_comp_mk₀_assoc,
            @Subsingleton.elim _ (h j) ((Ext.mk₀ (biproduct.ι f j)).comp x (zero_add n)) 0,
            Ext.comp_zero]

/-- `Ext` out of an arbitrary coproduct vanishes when it vanishes on every
summand, provided the derived single functor preserves that coproduct.

The preservation hypothesis is deliberately stated on `singleFunctor`
rather than derived here from AB4.  This keeps the lemma applicable to any
abelian category whose relevant coproduct survives into the derived
category, while `DerivedCategory.Coproducts` supplies the instance for the
scheme-module application. -/
lemma Ext.subsingleton_coproduct_left {J : Type w'} (f : J → C)
    [HasCoproduct f]
    [HasDerivedCategory.{w''} C]
    [PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.singleFunctor C 0)]
    (Y : C) (n : ℕ) (h : ∀ j, Subsingleton (Ext.{w} (f j) Y n)) :
    Subsingleton (Ext.{w} (∐ f) Y n) := by
  let c := Cofan.mk (P := ∐ f) (Sigma.ι f)
  let hc : IsColimit c := coproductIsCoproduct f
  let hc' := isColimitOfPreserves (DerivedCategory.singleFunctor C 0) hc
  apply subsingleton_of_forall_eq 0
  intro x
  apply Ext.ext
  apply IsColimit.hom_ext hc'
  intro j
  change (DerivedCategory.singleFunctor C 0).map (Sigma.ι f j.as) ≫ x.hom = _
  rw [Ext.singleFunctor_map_comp_hom]
  haveI := h j.as
  rw [Subsingleton.elim ((Ext.mk₀ (Sigma.ι f j.as)).comp x (zero_add n)) 0]
  rw [Ext.zero_hom, Ext.zero_hom]
  change (0 : (DerivedCategory.singleFunctor C 0).obj (f j.as) ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) = _ ≫ 0
  rw [comp_zero]

end Vanishing

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : D ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- In degree zero, `F.mapExtAddHom` is `F.map` up to the identifications `Ext⁰ = Hom`. -/
lemma Functor.bijective_mapExtAddHom_zero_iff (X Y : D) :
    Function.Bijective (F.mapExtAddHom X Y 0) ↔ Function.Bijective (F.map : (X ⟶ Y) → _) := by
  have : (F.mapExtAddHom X Y 0 : Ext X Y 0 → _) = Ext.mk₀ ∘ F.map ∘ Ext.homEquiv₀ := by
    funext e
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).2 e
    have hf : Ext.homEquiv₀ (Ext.mk₀ f) = f :=
      (Equiv.ofBijective _ (Ext.mk₀_bijective X Y)).symm_apply_apply f
    simp only [Function.comp, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_mk₀, hf]
  rw [this, (Ext.mk₀_bijective _ _).of_comp_iff',
    Function.Bijective.of_comp_iff _ Ext.homEquiv₀.bijective]

/-- A fully faithful exact functor is bijective on `Ext⁰`. -/
lemma Functor.bijective_mapExtAddHom_zero [F.Full] [F.Faithful] (X Y : D) :
    Function.Bijective (F.mapExtAddHom X Y 0) :=
  (F.bijective_mapExtAddHom_zero_iff X Y).2 ⟨F.map_injective, F.map_surjective⟩

section Generators

variable (Q : ObjectProperty D)
  (hpres : ∀ X : D, ∃ (P : D) (p : P ⟶ X), Q P ∧ Epi p)
  (hD : ∀ (P : D), Q P → ∀ (Y : D) (n : ℕ), Subsingleton (Ext.{w'} P Y (n + 1)))
  (hC : ∀ (P : D), Q P → ∀ (Y : D) (n : ℕ), Subsingleton (Ext.{w} (F.obj P) (F.obj Y) (n + 1)))
  (h₀ : ∀ X Y : D, Function.Bijective (F.mapExtAddHom X Y 0))
include hpres hD hC h₀

omit hD in
/-- **Surjectivity in every degree.** Present `X` by `K ↪ P ↠ X` with `P ∈ Q`; downstairs
`Ext^n (F K) (F Y) → Ext^(n+1) (F X) (F Y)` is surjective because `Ext^(n+1) (F P) (F Y)`
vanishes, so a class lifts by induction and pushes forward. -/
theorem Functor.surjective_mapExtAddHom_of_generators (n : ℕ) (X Y : D) :
    Function.Surjective (F.mapExtAddHom X Y n) := by
  induction n generalizing X with
  | zero => exact (h₀ X Y).2
  | succ n ih =>
    intro y
    obtain ⟨P, p, hP, hp⟩ := hpres X
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    have hFS := hS.map_of_exact F
    haveI : Subsingleton (Ext.{w} (S.map F).X₂ (F.obj Y) (n + 1)) := hC P hP Y n
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hFS (F.obj Y) y
      (Subsingleton.elim _ _) (by lia : 1 + n = n + 1)
    obtain ⟨x, hx⟩ := ih S.X₁ z
    refine ⟨hS.extClass.comp x (by lia), ?_⟩
    rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      ← Functor.mapExtAddHom_apply, hx]
    exact hz

/-- **Injectivity in every degree.** The successor case uses surjectivity in degree `n`, so
the two theorems are not independent. -/
theorem Functor.injective_mapExtAddHom_of_generators (n : ℕ) (X Y : D) :
    Function.Injective (F.mapExtAddHom X Y n) := by
  induction n generalizing X with
  | zero => exact (h₀ X Y).1
  | succ n ih =>
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨P, p, hP, hp⟩ := hpres X
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    have hFS := hS.map_of_exact F
    haveI : Subsingleton (Ext.{w'} S.X₂ Y (n + 1)) := hD P hP Y n
    obtain ⟨x', rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _)
      (by lia : 1 + n = n + 1)
    rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass] at hx
    obtain ⟨w, hw⟩ := Ext.contravariant_sequence_exact₁ hFS (F.obj Y) _ (by lia : 1 + n = n + 1) hx
    obtain ⟨v, rfl⟩ := F.surjective_mapExtAddHom_of_generators Q hpres hC h₀ n S.X₂ Y w
    have hv : (Ext.mk₀ S.f).comp v (zero_add n) = x' := by
      apply ih S.X₁
      rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
      exact hw
    rw [← hv]
    exact hS.extClass_comp_assoc v

/-- **Ext comparison from acyclic generators.** An exact functor bijective on `Ext⁰` is
bijective on every `Ext` as soon as a generating class of objects is acyclic on both sides. -/
theorem Functor.bijective_mapExtAddHom_of_generators (n : ℕ) (X Y : D) :
    Function.Bijective (F.mapExtAddHom X Y n) :=
  ⟨F.injective_mapExtAddHom_of_generators Q hpres hD hC h₀ n X Y,
    F.surjective_mapExtAddHom_of_generators Q hpres hC h₀ n X Y⟩

end Generators

end CategoryTheory
