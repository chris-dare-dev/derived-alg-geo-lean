/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.Vanishing

/-!
# The top degree keeps exactly one block

`Cech/Vanishing.lean` closes every degree strictly between the two ends, and it does so by
contracting *every* block: `cechPrimitive` needs a cone point `i₀ ∉ F` for each block `F`, and
below the top the only block without one — the full block `F = univ` — is unreachable, because a
tuple of length `n + 2` supports at most `n + 2` variables and so cannot contain all of them.

At the top degree that counting argument runs out: a tuple *can* meet every variable, and the full
block is exactly what survives. This file separates the surviving block from the rest.

## The splitting

`cechFace_cechBlockProj` says the differential preserves every block, so a cocycle splits into its
full-block part and the remainder, each again a cocycle. The remainder carries no full block at
all, and `cechPrimitive_isPrimitive` — whose block hypothesis constrains only the cochain handed
to it, rather than every term — contracts it. So the two differ by a coboundary, which is
`exists_fullBlock_add_coboundary`: **every class is carried by the full block.**

Nothing here is about the top degree specifically; the statement holds in every degree, and it is
only at the top that it says anything the vanishing theorem does not already say better.

## What is not here

Finiteness. The full block of one term is spanned by the monomial fractions whose Laurent exponent
is negative in every variable and has total degree `d`, a finite set by
`finite_setOf_degree_eq_of_neg` — but turning that into `Module.Finite k` needs the base-field
action, and the interface it has to meet is `cechCohomologyModule` through
`module_finite_linearCoherentH_of_cech`. That is #666's remaining half, and none of it is claimed
here.

## Scope

`Fintype ι` is genuine here — `Finset.univ` is the full block — and this is the statement in the
lane the issue means when it says finiteness of the variable set enters at the top.
-/

universe u

open CategoryTheory TopologicalSpace

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-- The full-block part of a Čech cochain, index by index. -/
noncomputable def intCechFullBlock [Fintype ι] (d : ℤ) {m : ℕ}
    (s : ∀ x : Fin (m + 1) → ι, polynomialVariableIntCechTerm ι k d m x)
    (y : Fin (m + 1) → ι) : polynomialVariableIntCechTerm ι k d m y :=
  cechBlockProj ι k (isPolynomialTwist_intShift (R := k) d) y Finset.univ (s y)

/-- The full-block part of a cocycle is a cocycle: the faces commute with the projections. -/
theorem intCechFullBlock_cocycle [Fintype ι] (d : ℤ) {m : ℕ}
    (s : ∀ x : Fin (m + 1) → ι, polynomialVariableIntCechTerm ι k d m x)
    (hs : ∀ x : Fin (m + 2) → ι,
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
        cechFace ι k (intShift (polynomialGrading ι k) d) x j (s (x ∘ j.succAbove)) = 0)
    (x : Fin (m + 2) → ι) :
    ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
      cechFace ι k (intShift (polynomialGrading ι k) d) x j
        (intCechFullBlock ι k d s (x ∘ j.succAbove)) = 0 := by
  have hcomm : ∀ j : Fin (m + 2),
      (-1 : ℤ) ^ (j : ℕ) • cechFace ι k (intShift (polynomialGrading ι k) d) x j
          (intCechFullBlock ι k d s (x ∘ j.succAbove)) =
        cechBlockProj ι k (isPolynomialTwist_intShift (R := k) d) x Finset.univ
          ((-1 : ℤ) ^ (j : ℕ) • cechFace ι k (intShift (polynomialGrading ι k) d) x j
            (s (x ∘ j.succAbove))) := by
    intro j
    rw [map_zsmul, intCechFullBlock, cechFace_cechBlockProj]
  rw [Finset.sum_congr rfl fun j _ => hcomm j, ← map_sum, hs x, map_zero]

/-- **Every class is carried by the full block.**

Splitting a cocycle into its full block and the rest leaves a cocycle that misses the full block
outright, and `cechPrimitive_isPrimitive` — whose block hypothesis constrains only the cochain
handed to it — contracts that remainder. So the two differ by a coboundary. -/
theorem exists_fullBlock_add_coboundary [Fintype ι] (d : ℤ) {n : ℕ}
    (s : ∀ x : Fin (n + 2) → ι, polynomialVariableIntCechTerm ι k d (n + 1) x)
    (hs : ∀ x : Fin (n + 3) → ι,
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
        cechFace ι k (intShift (polynomialGrading ι k) d) x j (s (x ∘ j.succAbove)) = 0) :
    ∃ p : ∀ y : Fin (n + 1) → ι, polynomialVariableIntCechTerm ι k d n y,
      ∀ x : Fin (n + 2) → ι,
        s x = intCechFullBlock ι k d s x +
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
            cechFace ι k (intShift (polynomialGrading ι k) d) x j (p (x ∘ j.succAbove)) := by
  classical
  have hcoc : ∀ x : Fin (n + 3) → ι,
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) •
        cechFace ι k (intShift (polynomialGrading ι k) d) x j
          (s (x ∘ j.succAbove) - intCechFullBlock ι k d s (x ∘ j.succAbove)) = 0 := by
    intro x
    have hsmul : ∀ (j : Fin (n + 3))
        (a b : polynomialVariableIntCechTerm ι k d (n + 2) x),
        ((-1 : ℤ) ^ (j : ℕ)) • (a - b) =
          ((-1 : ℤ) ^ (j : ℕ)) • a - ((-1 : ℤ) ^ (j : ℕ)) • b := fun j a b =>
      (AddMonoidHom.mk' (fun z : polynomialVariableIntCechTerm ι k d (n + 2) x =>
        ((-1 : ℤ) ^ (j : ℕ)) • z) fun p q => smul_add ((-1 : ℤ) ^ (j : ℕ)) p q).map_sub a b
    have hsub : ∀ j : Fin (n + 3),
        (-1 : ℤ) ^ (j : ℕ) • cechFace ι k (intShift (polynomialGrading ι k) d) x j
            (s (x ∘ j.succAbove) - intCechFullBlock ι k d s (x ∘ j.succAbove)) =
          (-1 : ℤ) ^ (j : ℕ) • cechFace ι k (intShift (polynomialGrading ι k) d) x j
              (s (x ∘ j.succAbove)) -
            (-1 : ℤ) ^ (j : ℕ) • cechFace ι k (intShift (polynomialGrading ι k) d) x j
              (intCechFullBlock ι k d s (x ∘ j.succAbove)) := by
      intro j
      rw [map_sub, hsmul j]
    rw [Finset.sum_congr rfl fun j _ => hsub j, Finset.sum_sub_distrib, hs x,
      intCechFullBlock_cocycle ι k d s hs x, sub_zero]
  have hfull : ∀ {G : Finset ι}, (∀ j : ι, j ∈ G) → ∀ y : Fin (n + 2) → ι,
      cechBlockProj ι k (isPolynomialTwist_intShift (R := k) d) y G
        (s y - intCechFullBlock ι k d s y) = 0 := by
    intro G hG y
    rw [Finset.eq_univ_iff_forall.mpr hG, map_sub, intCechFullBlock,
      cechBlockProj_cechBlockProj_self, sub_self]
  refine ⟨cechPrimitive ι k (isPolynomialTwist_intShift (R := k) d)
    (fun y => s y - intCechFullBlock ι k d s y), fun x => ?_⟩
  rw [cechPrimitive_isPrimitive ι k (isPolynomialTwist_intShift (R := k) d)
    (fun y => s y - intCechFullBlock ι k d s y) hcoc hfull x]
  abel

end AlgebraicGeometry.Proj
