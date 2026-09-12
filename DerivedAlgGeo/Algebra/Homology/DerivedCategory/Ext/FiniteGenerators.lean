/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.Adjunction
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomFinite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Ext-finiteness from quotient generators

This file isolates the degreewise homological-algebra reduction used by coherent-sheaf
applications.  Suppose every object in a class is the quotient of an object whose Ext groups
against the class are finite-dimensional, with kernel still in the class.  The contravariant
long exact Ext sequence then proves finite-dimensionality for every pair in the class, by
induction on the Ext degree.

The conclusion is deliberately only degreewise finiteness.  It does not manufacture a uniform
Ext-amplitude or finite support in the degree variable; those require a separate geometric input
before `DerivedCategory.ExtFiniteBounded.of_ext` can be applied.

## Main results

* `Abelian.Ext.biproductLinearEquiv` refines the additive finite-biproduct comparison to a
  linear equivalence;
* `Abelian.Ext.module_finite_coproduct_left` propagates Ext-finiteness from finitely many
  summands to their coproduct;
* `Abelian.Ext.module_finite_of_quotient_generators` performs the degreewise dévissage.
-/

universe w v u t

open CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

variable {k : Type t} [Field k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [HasExt.{w} C]

/-- The standard comparison from Ext out of a finite biproduct is linear. -/
noncomputable def biproductLinearEquiv {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) :
    Ext.{w} c.pt Y n ≃ₗ[k] ∀ j, Ext.{w} (X j) Y n where
  __ := Ext.biproductAddEquiv hc Y n
  map_smul' r x := by
    ext j
    exact Ext.comp_smul _ _ (zero_add n) r

/-- Ext out of a finite coproduct is finite-dimensional when Ext out of every summand is. -/
theorem module_finite_coproduct_left {J : Type*} [Fintype J] (X : J → C) (Y : C) (n : ℕ)
    [∀ j, Module.Finite k (Ext.{w} (X j) Y n)] :
    Module.Finite k (Ext.{w} (∐ X) Y n) := by
  letI : HasBiproduct X := HasBiproduct.of_hasCoproduct X
  letI : Module.Finite k (∀ j, Ext.{w} (X j) Y n) := inferInstance
  exact Module.Finite.equiv
    ((Ext.precompLinearEquiv (S := k) (biproduct.isoCoproduct X) Y n).trans
      (Ext.biproductLinearEquiv (k := k) (biproduct.isBilimit X) Y n)).symm

/-- **Degreewise Ext-finiteness from quotient generators.**

For each object satisfying `Q`, the hypothesis supplies a short exact sequence
`K ⟶ G ⟶ X` with `Q K`, and asks that Ext out of `G` against every object satisfying `Q` be
finite-dimensional in every degree.  Exactness gives the induction step

`Extⁿ(K,Y) ⟶ Extⁿ⁺¹(X,Y) ⟶ Extⁿ⁺¹(G,Y)`.

In degree zero, the epimorphism `G ⟶ X` makes `Hom(X,Y) ⟶ Hom(G,Y)` injective.  No projectivity,
resolution, boundedness, or finite-support claim is used. -/
theorem module_finite_of_quotient_generators (Q : ObjectProperty C)
    (hpresentation : ∀ X : C, Q X →
      ∃ (S : ShortComplex C) (_ : S.ShortExact) (_ : S.X₃ ≅ X), Q S.X₁ ∧
        ∀ (Y : C), Q Y → ∀ n : ℕ, Module.Finite k (Ext.{w} S.X₂ Y n))
    (X Y : C) (hX : Q X) (hY : Q Y) (n : ℕ) :
    Module.Finite k (Ext.{w} X Y n) := by
  induction n generalizing X with
  | zero =>
      obtain ⟨S, hS, e, -, hfinite⟩ := hpresentation X hX
      letI : Epi S.g := hS.epi_g
      letI : Module.Finite k (Ext.{w} S.X₂ Y 0) := hfinite Y hY 0
      letI : Module.Finite k (Ext.{w} S.X₃ Y 0) :=
        FiniteDimensional.of_injective
          ((Ext.mk₀ S.g).precompOfLinear k Y (zero_add 0))
          (Ext.precomp_mk₀_injective_of_epi Y S.g)
      exact Module.Finite.equiv (Ext.precompLinearEquiv (S := k) e Y 0).symm
  | succ n ih =>
      obtain ⟨S, hS, e, hkernel, hfinite⟩ := hpresentation X hX
      letI : Module.Finite k (Ext.{w} S.X₁ Y n) := ih S.X₁ hkernel
      letI : Module.Finite k (Ext.{w} S.X₂ Y (n + 1)) := hfinite Y hY (n + 1)
      let d : Ext.{w} S.X₁ Y n →ₗ[k] Ext.{w} S.X₃ Y (n + 1) :=
        hS.extClass.precompOfLinear k Y (by omega)
      let p : Ext.{w} S.X₃ Y (n + 1) →ₗ[k] Ext.{w} S.X₂ Y (n + 1) :=
        (Ext.mk₀ S.g).precompOfLinear k Y (zero_add (n + 1))
      letI : Module.Finite k (Ext.{w} S.X₃ Y (n + 1)) :=
        Module.Finite.of_exact_middle d p
          (by
            have hexact := Ext.contravariant_sequence_exact₃' hS Y n (n + 1) (by omega)
            rw [ShortComplex.ab_exact_iff_function_exact] at hexact
            change Function.Exact
              (hS.extClass.precomp Y (by omega))
              ((Ext.mk₀ S.g).precomp Y (zero_add (n + 1)))
            exact hexact)
      exact Module.Finite.equiv
        (Ext.precompLinearEquiv (S := k) e Y (n + 1)).symm

end CategoryTheory.Abelian.Ext
