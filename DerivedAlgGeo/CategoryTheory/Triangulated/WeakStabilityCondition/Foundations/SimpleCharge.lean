/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.PhaseGeometry
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-!
# Charges on the free lattice of simples

Bridgeland's worked example (§5) says that for an abelian category `A` of
finite length with `n` simple objects, a stability function on `A` is exactly a
choice of `Z(Sᵢ)` in the semi-closed upper half plane, one for each simple —
so that component of the stability manifold is `ℍ̄ⁿ`.

This file formalizes the **lattice half** of that statement, and only that.

## What is proved, and what it is a statement about

The carrier is `Fin n → ℤ`, exactly as `LinearAlgebra/Lattice/Numerical.lean`
uses `Fin 2 → ℤ`. **It is not `K₀(A)`.** Identifying the two is the Jordan–Hölder
theorem for a finite-length abelian category — that `K₀(A)` is free abelian on
the classes of the simples — and:

* **Mathlib does not have it.** There is no Jordan–Hölder or composition
  series for abelian categories at the pin; `Mathlib/Order/JordanHolder.lean`
  is about modular lattices and is not connected to `K₀` of a category.
* **This repository does not have it either.**
  `CategoryTheory/Triangulated/GrothendieckGroup/` builds `K₀` as a quotient of
  a free abelian group by a relation subgroup, and nothing there or anywhere
  else in the library says that quotient is free on the simples.

So the identification is an unrealized assumption, exactly like the one
`LinearAlgebra/Lattice/Numerical.lean` records, and it is never discharged
here. Every
theorem below is a theorem about `Fin n → ℤ` and would hold if no abelian
category existed.

## Relation to the stability-function foundation

`semiClosedUpperHalfPlane` and its basic API are defined in
`WeakStabilityCondition/Foundation/StabilityFunction/Basic.lean`. What that module
does **not** carry, and what is added here, is closure under positive scaling
and closure under a nonempty finite sum — the two facts a positive-integer
combination of simple charges needs.

Those two live in this file's own namespace rather than extending the
foundation module's, because nothing else needs to find them by dot notation
and the foundation module is the one every stability-function consumer imports.

## Main results

* `mem_cone_sum` — a nonempty finite sum of cone elements is in the cone.
* `mem_cone_natCombination` — the key one: if every simple charge is in the
  cone, so is every nonzero `ℕ`-combination of them.
* `existsUnique_charge` — the parametrization. Charges of the simples are
  exactly the additive maps out of the lattice, freely and uniquely.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.FiniteLength

open CategoryTheory.Triangulated
open CategoryTheory Complex

/-! ### Two closure properties the stability-function foundation does not carry -/

/-- The cone is closed under multiplication by a positive real. -/
theorem mem_cone_smul {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : (r : ℂ) * z ∈ semiClosedUpperHalfPlane := by
  rcases hz with him | ⟨him, hre⟩
  · exact Or.inl (by simpa using mul_pos hr him)
  · exact Or.inr ⟨by simp [him], by simpa using mul_neg_of_pos_of_neg hr hre⟩

/-- The cone is closed under nonempty finite sums. -/
theorem mem_cone_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℂ}
    (hf : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane) :
    (∑ i ∈ s, f i) ∈ semiClosedUpperHalfPlane := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simpa using hf a (by simp)
    · exact add_mem_semiClosedUpperHalfPlane (hf a (by simp))
        (ih ht fun i hi => hf i (by simp [hi]))

/-! ### The lattice model

`Fin n → ℤ` stands in for `K₀(A)`; see the module docstring for why that is a
model and not an identification. -/

variable {n : ℕ}

/-- The additive charge determined by a choice of charge for each simple. -/
noncomputable def chargeOf (w : Fin n → ℂ) : (Fin n → ℤ) →+ ℂ where
  toFun m := ∑ i, (m i : ℂ) * w i
  map_zero' := by simp
  map_add' m m' := by
    simp only [Pi.add_apply, Int.cast_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Not `@[simp]`: it would rewrite the left-hand side of `chargeOf_single`
into a sum before that lemma could fire, and `simpNF` rejects the pair. It is
the unfolding lemma, used by explicit `rw`. -/
theorem chargeOf_apply (w : Fin n → ℂ) (m : Fin n → ℤ) :
    chargeOf w m = ∑ i, (m i : ℂ) * w i := rfl

/-- The charge of the `i`-th basis vector is the `i`-th chosen value: the
lattice-model form of "`Z` restricted to the simples is the chosen data". -/
@[simp]
theorem chargeOf_single (w : Fin n → ℂ) (i : Fin n) :
    chargeOf w (Pi.single i 1) = w i := by
  classical
  rw [chargeOf_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- Every additive map out of the lattice is the charge of its values on the
basis. This is the surjectivity half of the parametrization. -/
theorem eq_chargeOf (Z : (Fin n → ℤ) →+ ℂ) :
    Z = chargeOf fun i => Z (Pi.single i 1) := by
  classical
  refine AddMonoidHom.ext fun m => ?_
  have key : Z m = ∑ i, Z (Pi.single i (m i)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [key, chargeOf_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : Pi.single (M := fun _ : Fin n => ℤ) i (m i) = m i • Pi.single i 1 := by
    ext j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  rw [hsingle, map_zsmul, zsmul_eq_mul]

/-- **The parametrization.** A choice of charge for each simple determines a
unique additive charge on the lattice, and every additive charge arises this
way. This is the lattice-model form of Bridgeland's `ℍ̄ⁿ` count; the
half-plane constraint is imposed separately by `mem_cone_natCombination`. -/
theorem existsUnique_charge (w : Fin n → ℂ) :
    ∃! Z : (Fin n → ℤ) →+ ℂ, ∀ i, Z (Pi.single i 1) = w i := by
  refine ⟨chargeOf w, fun i => chargeOf_single w i, fun Z hZ => ?_⟩
  rw [eq_chargeOf Z]
  simp only [hZ]

/-! ### The half-plane constraint

The content of "any choice of charges in `ℍ̄` gives a stability function" is
that the cone absorbs positive integer combinations. On the lattice side that
is the following statement, and it is the whole of it. -/

/-- **If every simple charge lies in the cone, so does every nonzero
`ℕ`-combination of them.**

In the intended reading `m i` is the multiplicity of the `i`-th simple in a
Jordan–Hölder filtration, so this says a nonzero object has charge in the
half plane. That reading is *not* formalized — see the module docstring. -/
theorem mem_cone_natCombination {w : Fin n → ℂ}
    (hw : ∀ i, w i ∈ semiClosedUpperHalfPlane) {m : Fin n → ℕ} (hm : m ≠ 0) :
    (∑ i, (m i : ℂ) * w i) ∈ semiClosedUpperHalfPlane := by
  classical
  set s : Finset (Fin n) := Finset.univ.filter fun i => m i ≠ 0 with hs
  have hsne : s.Nonempty := by
    rcases Function.ne_iff.mp hm with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hi
  have hrestrict : (∑ i, (m i : ℂ) * w i) = ∑ i ∈ s, (m i : ℂ) * w i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  rw [hrestrict]
  refine mem_cone_sum hsne fun i hi => ?_
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hpos : (0 : ℝ) < (m i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi
  simpa using mem_cone_smul hpos (hw i)

/-- The `ℕ`-combination statement in the form the parametrization produces. -/
theorem chargeOf_mem_cone {w : Fin n → ℂ} (hw : ∀ i, w i ∈ semiClosedUpperHalfPlane)
    {m : Fin n → ℕ} (hm : m ≠ 0) :
    chargeOf w (fun i => (m i : ℤ)) ∈ semiClosedUpperHalfPlane := by
  rw [chargeOf_apply]
  simpa using mem_cone_natCombination hw hm

/-- A nonzero `ℕ`-combination of cone elements is nonzero. The lattice-model
form of "a nonzero object has nonzero charge", which is what makes the phase
well defined. -/
theorem chargeOf_ne_zero {w : Fin n → ℂ} (hw : ∀ i, w i ∈ semiClosedUpperHalfPlane)
    {m : Fin n → ℕ} (hm : m ≠ 0) :
    chargeOf w (fun i => (m i : ℤ)) ≠ 0 :=
  semiClosedUpperHalfPlane_ne_zero (chargeOf_mem_cone hw hm)

end CategoryTheory.Triangulated.StabilityCondition.FiniteLength
