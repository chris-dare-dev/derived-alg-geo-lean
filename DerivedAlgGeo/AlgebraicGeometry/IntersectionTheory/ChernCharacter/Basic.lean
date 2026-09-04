/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.ChernCharacter.Surface
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.CharacteristicClasses
import Mathlib.LinearAlgebra.Lagrange

/-!
# Numerical Chern-character reconstruction from twist polynomials

This file is the bounded, no-Chow reconstruction layer between Snapper polynomials and the
components consumed by `NumericalVarietyData`.  There are two deliberately separate steps.

First, `homogeneousPicardCoefficient` extracts the ordinary rational homogeneous coefficient of
a Picard Euler polynomial.  Raw finite differences below top degree are not sufficient: they
mix the desired term with higher-degree terms.  We remove that mixing by interpolating the
scaled mixed coefficient and taking its lowest possible ordinary coefficient.

Second, `PairingContext` and `ReconstructionData` state exactly when those divisor-tested
functionals are represented by elements of a chosen `NumericalRingData`.  Representability gives
existence; `divisorPairing_ext` gives uniqueness.  Neither is inferred from the intersection
numbers.  In particular, on a higher-dimensional variety products of divisors need not separate
all middle-codimension numerical classes.

The represented Todd-weighted components are denoted `tauComponent`.  The structure-sheaf
components supply the reconstructed Todd class, and Chern-character components are recovered by
the triangular identities

`tau_i(F) = sum_{a+b=i} ch_a(F) * td_b(X)`.

The formulas are implemented through codimension four, the current bound of
`AlgebraicGeometry/Numerical/Core/CharacteristicClasses.lean`.  Isomorphism and
exact-sequence results use explicit
rank and Euler-polynomial comparisons.  The line-bundle theorem uses an explicit coefficient
comparison rather than silently assuming a perfect intersection pairing or Riemann--Roch.
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.IntersectionTheory.ChernCharacter

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.IntersectionTheory.Number
open Polynomial
open scoped BigOperators

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

noncomputable section

/-! ## Rational homogeneous coefficients -/

/-- Scale every Picard direction by the same integer and take the resulting mixed coefficient. -/
def scaledPicardCoefficient (classes : List (Pic X))
    (f : Pic X → ℤ) (z : ℤ) : ℤ :=
  picardCoefficient (classes.map fun L ↦ L ^ z) f

/-- The degree-`d` rational interpolation of an integer-valued function, using the nodes
`0, ..., d`. -/
noncomputable def interpolatingPolynomial (d : ℕ) (q : ℤ → ℤ) : ℚ[X] :=
  Lagrange.interpolate (Finset.range (d + 1)) (fun j : ℕ ↦ (j : ℚ))
    (fun j : ℕ ↦ (q (j : ℤ) : ℚ))

/-- The ordinary homogeneous coefficient polarized in `classes`.

For `r = classes.length`, this is the coefficient of `z^r` in the degree-`d` interpolation of
`z ↦ Δ_{L₁^z}⋯Δ_{Lᵣ^z} f(1)`.  In top degree it agrees with the usual top mixed
coefficient; below top degree it removes the higher-degree contamination present in a raw
finite difference. -/
noncomputable def homogeneousPicardCoefficient (d : ℕ)
    (classes : List (Pic X)) (f : Pic X → ℤ) : ℚ :=
  (interpolatingPolynomial d (scaledPicardCoefficient classes f)).coeff classes.length

theorem picardMixedDifference_add (classes : List (Pic X))
    (f g : Pic X → ℤ) :
    picardMixedDifference classes (f + g) =
      picardMixedDifference classes f + picardMixedDifference classes g := by
  induction classes with
  | nil => rfl
  | cons L classes ih =>
      funext M
      simp only [picardMixedDifference_cons, picardDifference, Pi.add_apply, ih]
      omega

theorem picardCoefficient_add (classes : List (Pic X))
    (f g : Pic X → ℤ) :
    picardCoefficient classes (f + g) =
      picardCoefficient classes f + picardCoefficient classes g := by
  simp only [picardCoefficient, picardMixedDifference_add, Pi.add_apply]

@[simp]
theorem scaledPicardCoefficient_add (classes : List (Pic X))
    (f g : Pic X → ℤ) :
    scaledPicardCoefficient classes (f + g) =
      scaledPicardCoefficient classes f + scaledPicardCoefficient classes g := by
  funext z
  exact picardCoefficient_add _ _ _

theorem interpolatingPolynomial_add (d : ℕ) (q r : ℤ → ℤ) :
    interpolatingPolynomial d (q + r) =
      interpolatingPolynomial d q + interpolatingPolynomial d r := by
  simp only [interpolatingPolynomial]
  rw [← map_add]
  congr 1
  funext j
  simp

theorem homogeneousPicardCoefficient_add (d : ℕ)
    (classes : List (Pic X)) (f g : Pic X → ℤ) :
    homogeneousPicardCoefficient d classes (f + g) =
      homogeneousPicardCoefficient d classes f +
        homogeneousPicardCoefficient d classes g := by
  rw [homogeneousPicardCoefficient, homogeneousPicardCoefficient,
    homogeneousPicardCoefficient, scaledPicardCoefficient_add,
    interpolatingPolynomial_add, coeff_add]

theorem scaledPicardCoefficient_eq_of_perm {classes classes' : List (Pic X)}
    (h : classes.Perm classes') (f : Pic X → ℤ) :
    scaledPicardCoefficient classes f = scaledPicardCoefficient classes' f := by
  funext z
  exact picardCoefficient_eq_of_perm (h.map fun L ↦ L ^ z) f

/-- Homogeneous coefficients are symmetric in their Picard directions. -/
theorem homogeneousPicardCoefficient_eq_of_perm
    {classes classes' : List (Pic X)} (h : classes.Perm classes')
    (d : ℕ) (f : Pic X → ℤ) :
    homogeneousPicardCoefficient d classes f =
      homogeneousPicardCoefficient d classes' f := by
  rw [homogeneousPicardCoefficient, homogeneousPicardCoefficient,
    scaledPicardCoefficient_eq_of_perm h]
  exact congrArg _ h.length_eq

/-! ## Explicit realization in a numerical ring -/

variable {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
variable {d : ℕ} {A : Type v} [CommRing A] [Algebra ℚ A]

/-- The product of the degree-one realizations of a list of Picard classes. -/
def divisorProduct (divisorClass : Additive (Pic X) →+ A)
    (classes : List (Pic X)) : A :=
  (classes.map fun L ↦ divisorClass (Additive.ofMul L)).prod

omit [Algebra ℚ A] in
@[simp] theorem divisorProduct_nil (divisorClass : Additive (Pic X) →+ A) :
    divisorProduct divisorClass [] = 1 :=
  rfl

/-- A chosen numerical ring realization of the divisor intersection theory.

`divisorPairing_ext` is the required nondegeneracy statement: divisor products separate the
chosen graded pieces.  It is intentionally a field rather than an instance or theorem. -/
structure PairingContext (D : FiniteCohomology k X) (C : D.LinearConnectingSystem)
    (d : ℕ) (A : Type v) [CommRing A] [Algebra ℚ A] where
  /-- The selected numerical-ring presentation. -/
  ring : NumericalRingData d A
  intersection : IntersectionContext D C d
  divisorClass : Additive (Pic X) →+ A
  divisorClass_mem : ∀ L, divisorClass L ∈ ring.piece 1
  degree_divisorProduct : ∀ (L : Fin d → Pic X),
    ring.degree (divisorProduct divisorClass (List.ofFn L)) =
      (intersection.picardIntersectionNumber L : ℚ)
  divisorPairing_ext : ∀ (i : ℕ), i ≤ d → ∀ {x y : A},
    x ∈ ring.piece i →
    y ∈ ring.piece i →
    (∀ classes : List (Pic X), classes.length = d - i →
      ring.degree (x * divisorProduct divisorClass classes) =
        ring.degree (y * divisorProduct divisorClass classes)) →
    x = y

namespace PairingContext

variable (P : PairingContext D C d A)

/-- The divisor-tested rational functional extracted from a coherent sheaf's twist polynomial. -/
noncomputable def twistPairing {F : Coh X}
    (T : TwistContext D F d) (_i : ℕ) (classes : List (Pic X)) : ℚ :=
  homogeneousPicardCoefficient d classes T.eulerPic

/-- Existence data for representatives of all Todd-weighted components of one coherent sheaf.

This is separate from `PairingContext.divisorPairing_ext`: existence and uniqueness are distinct
hypotheses. -/
structure ReconstructionData (F : Coh X) where
  twists : TwistContext D F d
  rank : ℤ
  representable : ∀ (i : ℕ), i ≤ d → ∃ x : A,
    x ∈ P.ring.piece i ∧
      ∀ classes : List (Pic X), classes.length = d - i →
        P.ring.degree (x * divisorProduct P.divisorClass classes) =
          twistPairing twists i classes

namespace ReconstructionData

variable {P : PairingContext D C d A} {F G H : Coh X}

/-- The unique chosen representative of the Todd-weighted component `tau_i(F)` when `i ≤ d`,
and zero above the dimension. -/
noncomputable def tauComponent (R : P.ReconstructionData F) (i : ℕ) : A :=
  if hi : i ≤ d then Classical.choose (R.representable i hi) else 0

theorem tauComponent_mem (R : P.ReconstructionData F) (i : ℕ) :
    R.tauComponent i ∈ P.ring.piece i := by
  by_cases hi : i ≤ d
  · rw [tauComponent, dif_pos hi]
    exact (Classical.choose_spec (R.representable i hi)).1
  · rw [tauComponent, dif_neg hi]
    exact Submodule.zero_mem _

theorem degree_tauComponent_mul_divisorProduct (R : P.ReconstructionData F)
    (i : ℕ) (hi : i ≤ d) (classes : List (Pic X))
    (hlength : classes.length = d - i) :
    P.ring.degree
        (R.tauComponent i * divisorProduct P.divisorClass classes) =
      twistPairing R.twists i classes := by
  rw [tauComponent, dif_pos hi]
  exact (Classical.choose_spec (R.representable i hi)).2 classes hlength

theorem tauComponent_eq_of_twistPairing_eq
    (R : P.ReconstructionData F) (S : P.ReconstructionData G) (i : ℕ)
    (hpair : ∀ classes : List (Pic X), classes.length = d - i →
      twistPairing R.twists i classes = twistPairing S.twists i classes) :
    R.tauComponent i = S.tauComponent i := by
  by_cases hi : i ≤ d
  · apply P.divisorPairing_ext i hi (tauComponent_mem R i) (tauComponent_mem S i)
    intro classes hlength
    rw [R.degree_tauComponent_mul_divisorProduct i hi classes hlength,
      S.degree_tauComponent_mul_divisorProduct i hi classes hlength,
      hpair classes hlength]
  · simp [tauComponent, hi]

theorem tauComponent_eq_of_eulerPic_eq
    (R : P.ReconstructionData F) (S : P.ReconstructionData G)
    (h : R.twists.eulerPic = S.twists.eulerPic) (i : ℕ) :
    R.tauComponent i = S.tauComponent i := by
  apply tauComponent_eq_of_twistPairing_eq R S i
  intro classes _
  simp only [PairingContext.twistPairing, h]

theorem tauComponent_add
    (R : P.ReconstructionData F) (S : P.ReconstructionData G)
    (Q : P.ReconstructionData H)
    (heuler : Q.twists.eulerPic = R.twists.eulerPic + S.twists.eulerPic)
    (i : ℕ) :
    Q.tauComponent i = R.tauComponent i + S.tauComponent i := by
  by_cases hi : i ≤ d
  · apply P.divisorPairing_ext i hi (tauComponent_mem Q i)
      (Submodule.add_mem _ (tauComponent_mem R i) (tauComponent_mem S i))
    intro classes hlength
    rw [Q.degree_tauComponent_mul_divisorProduct i hi classes hlength]
    rw [PairingContext.twistPairing, heuler, homogeneousPicardCoefficient_add]
    rw [add_mul, map_add, R.degree_tauComponent_mul_divisorProduct i hi classes hlength,
      S.degree_tauComponent_mul_divisorProduct i hi classes hlength]
    rfl
  · simp [tauComponent, hi]

end ReconstructionData

end PairingContext

/-! ## Todd normalization and Chern-character components through degree four -/

open PairingContext.ReconstructionData

variable {P : PairingContext D C d A}
variable {O : Coh X} (RO : P.ReconstructionData O)

/-- The reconstructed Todd component is the Todd-weighted component of the structure sheaf. -/
noncomputable def toddComponent (i : ℕ) : A := RO.tauComponent i

variable {F : Coh X}

/-- Chern-character components recovered from `tau(F) = ch(F) * td(X)`, through degree four. -/
noncomputable def chernCharacterComponent (R : P.ReconstructionData F) : ℕ → A
  | 0 => algebraMap ℚ A (R.rank : ℚ)
  | 1 => R.tauComponent 1 -
      algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 1
  | 2 => R.tauComponent 2 -
      chernCharacterComponent R 1 * toddComponent RO 1 -
        algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 2
  | 3 => R.tauComponent 3 -
      chernCharacterComponent R 2 * toddComponent RO 1 -
        chernCharacterComponent R 1 * toddComponent RO 2 -
          algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 3
  | 4 => R.tauComponent 4 -
      chernCharacterComponent R 3 * toddComponent RO 1 -
        chernCharacterComponent R 2 * toddComponent RO 2 -
          chernCharacterComponent R 1 * toddComponent RO 3 -
            algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 4
  | _ => 0

@[simp] theorem chernCharacterComponent_zero (R : P.ReconstructionData F) :
    chernCharacterComponent RO R 0 = algebraMap ℚ A (R.rank : ℚ) := by
  simp [chernCharacterComponent]

@[simp] theorem chernCharacterComponent_one (R : P.ReconstructionData F) :
    chernCharacterComponent RO R 1 = R.tauComponent 1 -
      algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 1 := by
  simp [chernCharacterComponent]

@[simp] theorem chernCharacterComponent_two (R : P.ReconstructionData F) :
    chernCharacterComponent RO R 2 = R.tauComponent 2 -
      chernCharacterComponent RO R 1 * toddComponent RO 1 -
        algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 2 := by
  simp [chernCharacterComponent]

@[simp] theorem chernCharacterComponent_three (R : P.ReconstructionData F) :
    chernCharacterComponent RO R 3 = R.tauComponent 3 -
      chernCharacterComponent RO R 2 * toddComponent RO 1 -
        chernCharacterComponent RO R 1 * toddComponent RO 2 -
          algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 3 := by
  simp [chernCharacterComponent]

@[simp] theorem chernCharacterComponent_four (R : P.ReconstructionData F) :
    chernCharacterComponent RO R 4 = R.tauComponent 4 -
      chernCharacterComponent RO R 3 * toddComponent RO 1 -
        chernCharacterComponent RO R 2 * toddComponent RO 2 -
          chernCharacterComponent RO R 1 * toddComponent RO 3 -
            algebraMap ℚ A (R.rank : ℚ) * toddComponent RO 4 := by
  simp [chernCharacterComponent]

@[simp] theorem chernCharacterComponent_of_five_le (R : P.ReconstructionData F)
    {i : ℕ} (hi : 5 ≤ i) : chernCharacterComponent RO R i = 0 := by
  rcases i with _ | _ | _ | _ | _ | i <;>
    simp [chernCharacterComponent] at hi ⊢

theorem chernCharacterComponent_mem (R : P.ReconstructionData F) (i : ℕ) :
    chernCharacterComponent RO R i ∈ P.ring.piece i := by
  have h0 : chernCharacterComponent RO R 0 ∈ P.ring.piece 0 := by
    simpa using P.ring.algebraMap_mem_piece_zero (R.rank : ℚ)
  have h1 : chernCharacterComponent RO R 1 ∈ P.ring.piece 1 := by
    simpa [chernCharacterComponent, toddComponent] using
      Submodule.sub_mem _ (tauComponent_mem R 1)
        (P.ring.mul_mem_piece
          (P.ring.algebraMap_mem_piece_zero (R.rank : ℚ))
          (tauComponent_mem RO 1))
  have h2 : chernCharacterComponent RO R 2 ∈ P.ring.piece 2 := by
    simpa [chernCharacterComponent, toddComponent] using
      Submodule.sub_mem _
        (Submodule.sub_mem _ (tauComponent_mem R 2)
          (P.ring.mul_mem_piece h1 (tauComponent_mem RO 1)))
        (P.ring.mul_mem_piece
          (P.ring.algebraMap_mem_piece_zero (R.rank : ℚ))
          (tauComponent_mem RO 2))
  have h3 : chernCharacterComponent RO R 3 ∈ P.ring.piece 3 := by
    simpa [chernCharacterComponent, toddComponent] using
      Submodule.sub_mem _
        (Submodule.sub_mem _
          (Submodule.sub_mem _ (tauComponent_mem R 3)
            (P.ring.mul_mem_piece h2 (tauComponent_mem RO 1)))
          (P.ring.mul_mem_piece h1 (tauComponent_mem RO 2)))
        (P.ring.mul_mem_piece
          (P.ring.algebraMap_mem_piece_zero (R.rank : ℚ))
          (tauComponent_mem RO 3))
  have h4 : chernCharacterComponent RO R 4 ∈ P.ring.piece 4 := by
    simpa [chernCharacterComponent, toddComponent] using
      Submodule.sub_mem _
        (Submodule.sub_mem _
          (Submodule.sub_mem _
            (Submodule.sub_mem _ (tauComponent_mem R 4)
              (P.ring.mul_mem_piece h3 (tauComponent_mem RO 1)))
            (P.ring.mul_mem_piece h2 (tauComponent_mem RO 2)))
          (P.ring.mul_mem_piece h1 (tauComponent_mem RO 3)))
        (P.ring.mul_mem_piece
          (P.ring.algebraMap_mem_piece_zero (R.rank : ℚ))
          (tauComponent_mem RO 4))
  rcases i with _ | _ | _ | _ | _ | i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · simp

theorem chernCharacterComponent_eq_zero_of_dimension_lt
    (R : P.ReconstructionData F) {i : ℕ} (hi : d < i) :
    chernCharacterComponent RO R i = 0 :=
  P.ring.eq_zero_of_mem_piece_of_lt hi (chernCharacterComponent_mem RO R i)

/-! ## The triangular extraction principle -/

theorem tauComponent_one_eq (R : P.ReconstructionData F) :
    R.tauComponent 1 = chernCharacterComponent RO R 1 +
      chernCharacterComponent RO R 0 * toddComponent RO 1 := by
  simp only [chernCharacterComponent_zero, chernCharacterComponent_one]
  ring

theorem tauComponent_two_eq (R : P.ReconstructionData F) :
    R.tauComponent 2 = chernCharacterComponent RO R 2 +
      chernCharacterComponent RO R 1 * toddComponent RO 1 +
        chernCharacterComponent RO R 0 * toddComponent RO 2 := by
  simp only [chernCharacterComponent_zero, chernCharacterComponent_two]
  ring

theorem tauComponent_three_eq (R : P.ReconstructionData F) :
    R.tauComponent 3 = chernCharacterComponent RO R 3 +
      chernCharacterComponent RO R 2 * toddComponent RO 1 +
        chernCharacterComponent RO R 1 * toddComponent RO 2 +
          chernCharacterComponent RO R 0 * toddComponent RO 3 := by
  simp only [chernCharacterComponent_zero, chernCharacterComponent_three]
  ring

theorem tauComponent_four_eq (R : P.ReconstructionData F) :
    R.tauComponent 4 = chernCharacterComponent RO R 4 +
      chernCharacterComponent RO R 3 * toddComponent RO 1 +
        chernCharacterComponent RO R 2 * toddComponent RO 2 +
          chernCharacterComponent RO R 1 * toddComponent RO 3 +
            chernCharacterComponent RO R 0 * toddComponent RO 4 := by
  simp only [chernCharacterComponent_zero, chernCharacterComponent_four]
  ring

/-! ## Invariance and exact-sequence additivity -/

theorem chernCharacterComponent_eq_of_eulerPic_eq
    {G : Coh X} (R : P.ReconstructionData F) (S : P.ReconstructionData G)
    (hrank : R.rank = S.rank) (heuler : R.twists.eulerPic = S.twists.eulerPic) (i : ℕ) :
    chernCharacterComponent RO R i = chernCharacterComponent RO S i := by
  have htau : ∀ j, R.tauComponent j = S.tauComponent j :=
    fun j ↦ R.tauComponent_eq_of_eulerPic_eq S heuler j
  rcases i with _ | _ | _ | _ | _ | i <;>
    simp [hrank, htau]

/-- Isomorphism invariance once the chosen rank and twist-polynomial realizations have been
compared.  The comparison hypotheses stay explicit because a bare coherent-sheaf isomorphism
does not choose compatible `ReconstructionData`. -/
theorem chernCharacterComponent_iso
    {G : Coh X} (R : P.ReconstructionData F) (S : P.ReconstructionData G)
    (_e : F ≅ G) (hrank : R.rank = S.rank)
    (heuler : R.twists.eulerPic = S.twists.eulerPic) (i : ℕ) :
    chernCharacterComponent RO R i = chernCharacterComponent RO S i :=
  chernCharacterComponent_eq_of_eulerPic_eq RO R S hrank heuler i

theorem chernCharacterComponent_add
    {G H : Coh X} (R : P.ReconstructionData F)
    (S : P.ReconstructionData G) (Q : P.ReconstructionData H)
    (hrank : Q.rank = R.rank + S.rank)
    (heuler : Q.twists.eulerPic = R.twists.eulerPic + S.twists.eulerPic)
    (i : ℕ) :
    chernCharacterComponent RO Q i =
      chernCharacterComponent RO R i + chernCharacterComponent RO S i := by
  have htau : ∀ j, Q.tauComponent j = R.tauComponent j + S.tauComponent j :=
    fun j ↦ tauComponent_add R S Q heuler j
  have h0 : chernCharacterComponent RO Q 0 =
      chernCharacterComponent RO R 0 + chernCharacterComponent RO S 0 := by
    simp [hrank]
  have h1 : chernCharacterComponent RO Q 1 =
      chernCharacterComponent RO R 1 + chernCharacterComponent RO S 1 := by
    simp only [chernCharacterComponent_one]
    rw [htau 1, hrank]
    push_cast
    ring
  have h2 : chernCharacterComponent RO Q 2 =
      chernCharacterComponent RO R 2 + chernCharacterComponent RO S 2 := by
    simp only [chernCharacterComponent_two]
    rw [htau 2, h1, hrank]
    push_cast
    ring
  have h3 : chernCharacterComponent RO Q 3 =
      chernCharacterComponent RO R 3 + chernCharacterComponent RO S 3 := by
    simp only [chernCharacterComponent_three]
    rw [htau 3, h2, h1, hrank]
    push_cast
    ring
  have h4 : chernCharacterComponent RO Q 4 =
      chernCharacterComponent RO R 4 + chernCharacterComponent RO S 4 := by
    simp only [chernCharacterComponent_four]
    rw [htau 4, h3, h2, h1, hrank]
    push_cast
    ring
  rcases i with _ | _ | _ | _ | _ | i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · rw [chernCharacterComponent_of_five_le RO Q (by omega),
      chernCharacterComponent_of_five_le RO R (by omega),
      chernCharacterComponent_of_five_le RO S (by omega), add_zero]

/-! ## Explicit line-bundle comparison -/

/-- The degree-`i` exponential term `D^i / i!`. -/
noncomputable def expComponent (x : A) (i : ℕ) : A :=
  algebraMap ℚ A ((i.factorial : ℚ)⁻¹) * x ^ i

/-- The expected Todd-weighted component of a line bundle with first Chern class `x`. -/
noncomputable def lineTauCandidate (x : A) (i : ℕ) : A :=
  ∑ j ∈ Finset.range (i + 1), expComponent x j * toddComponent RO (i - j)

/-- Coefficient-level comparison identifying one reconstruction with a line bundle.

This is the precise missing translation/representability input.  It is stated on the extracted
twist coefficients, not as the desired Chern-character equality. -/
structure LineBundleComparison (R : P.ReconstructionData F) (L : Pic X) where
  rank_eq_one : R.rank = 1
  candidate_mem : ∀ (i : ℕ), i ≤ d → i ≤ 4 →
    lineTauCandidate RO (P.divisorClass (Additive.ofMul L)) i ∈
      P.ring.piece i
  coefficient_formula : ∀ (i : ℕ), i ≤ d → i ≤ 4 →
    ∀ classes : List (Pic X), classes.length = d - i →
      PairingContext.twistPairing R.twists i classes =
        P.ring.degree
          (lineTauCandidate RO (P.divisorClass (Additive.ofMul L)) i *
            divisorProduct P.divisorClass classes)

/-- The line-bundle coefficient comparison determines the represented Todd-weighted component.
The conclusion uses both the stated representability and the explicit divisor-pairing
nondegeneracy from `PairingContext`. -/
theorem tauComponent_eq_lineTauCandidate
    (R : P.ReconstructionData F) (L : Pic X)
    (Q : LineBundleComparison RO R L) (i : ℕ) (hi : i ≤ d) (hi4 : i ≤ 4) :
    R.tauComponent i = lineTauCandidate RO (P.divisorClass (Additive.ofMul L)) i := by
  apply P.divisorPairing_ext i hi (tauComponent_mem R i) (Q.candidate_mem i hi hi4)
  intro classes hlength
  rw [R.degree_tauComponent_mul_divisorProduct i hi classes hlength]
  exact Q.coefficient_formula i hi hi4 classes hlength

/-- Under the visible normalization `td₀ = 1`, the reconstructed Chern character of a line
bundle is `exp(c₁)` through the supported degree four. -/
theorem chernCharacterComponent_lineBundle
    (R : P.ReconstructionData F) (L : Pic X)
    (Q : LineBundleComparison RO R L) (htoddZero : toddComponent RO 0 = 1)
    (i : ℕ) (hi : i ≤ d) (hi4 : i ≤ 4) :
    chernCharacterComponent RO R i =
      expComponent (P.divisorClass (Additive.ofMul L)) i := by
  let x := P.divisorClass (Additive.ofMul L)
  rcases i with _ | _ | _ | _ | _ | i
  · simp [expComponent, Q.rank_eq_one]
  · norm_num at hi
    change chernCharacterComponent RO R 1 = expComponent x 1
    have htau1 := tauComponent_eq_lineTauCandidate RO R L Q 1 hi (by omega)
    simp only [chernCharacterComponent_one]
    rw [htau1, Q.rank_eq_one]
    simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
  · norm_num at hi
    change chernCharacterComponent RO R 2 = expComponent x 2
    have hi1 : 1 ≤ d := by omega
    have htau1 := tauComponent_eq_lineTauCandidate RO R L Q 1 hi1 (by omega)
    have htau2 := tauComponent_eq_lineTauCandidate RO R L Q 2 hi (by omega)
    have hch1 : chernCharacterComponent RO R 1 = expComponent x 1 := by
      simp only [chernCharacterComponent_one]
      rw [htau1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    simp only [chernCharacterComponent_two]
    rw [htau2, hch1, Q.rank_eq_one]
    simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    ring
  · norm_num at hi
    change chernCharacterComponent RO R 3 = expComponent x 3
    have hi1 : 1 ≤ d := by omega
    have hi2 : 2 ≤ d := by omega
    have htau1 := tauComponent_eq_lineTauCandidate RO R L Q 1 hi1 (by omega)
    have htau2 := tauComponent_eq_lineTauCandidate RO R L Q 2 hi2 (by omega)
    have htau3 := tauComponent_eq_lineTauCandidate RO R L Q 3 hi (by omega)
    have hch1 : chernCharacterComponent RO R 1 = expComponent x 1 := by
      simp only [chernCharacterComponent_one]
      rw [htau1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    have hch2 : chernCharacterComponent RO R 2 = expComponent x 2 := by
      simp only [chernCharacterComponent_two]
      rw [htau2, hch1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
      ring
    simp only [chernCharacterComponent_three]
    rw [htau3, hch2, hch1, Q.rank_eq_one]
    simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    ring
  · norm_num at hi
    change chernCharacterComponent RO R 4 = expComponent x 4
    have hi1 : 1 ≤ d := by omega
    have hi2 : 2 ≤ d := by omega
    have hi3 : 3 ≤ d := by omega
    have htau1 := tauComponent_eq_lineTauCandidate RO R L Q 1 hi1 (by omega)
    have htau2 := tauComponent_eq_lineTauCandidate RO R L Q 2 hi2 (by omega)
    have htau3 := tauComponent_eq_lineTauCandidate RO R L Q 3 hi3 (by omega)
    have htau4 := tauComponent_eq_lineTauCandidate RO R L Q 4 hi (by omega)
    have hch1 : chernCharacterComponent RO R 1 = expComponent x 1 := by
      simp only [chernCharacterComponent_one]
      rw [htau1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    have hch2 : chernCharacterComponent RO R 2 = expComponent x 2 := by
      simp only [chernCharacterComponent_two]
      rw [htau2, hch1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
      ring
    have hch3 : chernCharacterComponent RO R 3 = expComponent x 3 := by
      simp only [chernCharacterComponent_three]
      rw [htau3, hch2, hch1, Q.rank_eq_one]
      simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
      ring
    simp only [chernCharacterComponent_four]
    rw [htau4, hch3, hch2, hch1, Q.rank_eq_one]
    simp [lineTauCandidate, Finset.sum_range_succ, expComponent, htoddZero, x]
    ring
  · omega

/-! ## Compatibility with the degree-level surface construction -/

open AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface

/-- The reconstructed ring-valued `ch₂` has the degree constructed in issue #37 once the
chosen rank, determinant class, and Todd-weighted representatives are explicitly compared.
This does not turn the degree-level surface class into an unconditional element of `A`. -/
theorem degree_chernCharacterComponent_two_eq_surface
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    {A : Type v} [CommRing A] [Algebra ℚ A]
    (P : PairingContext D C 2 A) {O F : Coh X}
    (RO : P.ReconstructionData O) (R : P.ReconstructionData F)
    (Qdet : Coh.TwoTermPerfectDeterminantData F)
    (hrank : R.rank = virtualRank Qdet)
    (htauTop : P.ring.degree (R.tauComponent 2) =
      (D.eulerCharacteristic F : ℚ))
    (hfirst : chernCharacterComponent RO R 1 =
      P.divisorClass (picardFirstChernClass Qdet))
    (htoddOne : P.ring.degree
        (P.divisorClass (picardFirstChernClass Qdet) * toddComponent RO 1) =
      toddOnePairing P.intersection (picardFirstChernClass Qdet))
    (htoddTop : P.ring.degree (toddComponent RO 2) =
      toddTwoDegree P.intersection) :
    P.ring.degree (chernCharacterComponent RO R 2) =
      chernCharacterTwoDegree P.intersection Qdet := by
  rw [chernCharacterComponent_two, map_sub, map_sub, htauTop, hfirst, htoddOne,
    P.ring.degree_algebraMap_mul, hrank, htoddTop]
  simp only [chernCharacterTwoDegree]
  ring

/-! ## Compatibility with the universal A7 formulas -/

/-- Recover Chern classes whose universal formulas give the reconstructed character through
codimension four. -/
noncomputable def toChernClassData (R : P.ReconstructionData F) : ChernClassData A where
  rank := R.rank
  c := fun i ↦
    match i with
    | 1 => chernCharacterComponent RO R 1
    | 2 => algebraMap ℚ A (1 / 2) * chernCharacterComponent RO R 1 ^ 2 -
        chernCharacterComponent RO R 2
    | 3 => 2 * chernCharacterComponent RO R 3 -
        algebraMap ℚ A (1 / 3) * chernCharacterComponent RO R 1 ^ 3 +
          chernCharacterComponent RO R 1 *
            (algebraMap ℚ A (1 / 2) * chernCharacterComponent RO R 1 ^ 2 -
              chernCharacterComponent RO R 2)
    | 4 =>
        let c₁ := chernCharacterComponent RO R 1
        let c₂ := algebraMap ℚ A (1 / 2) * c₁ ^ 2 - chernCharacterComponent RO R 2
        let c₃ := 2 * chernCharacterComponent RO R 3 -
          algebraMap ℚ A (1 / 3) * c₁ ^ 3 + c₁ * c₂
        algebraMap ℚ A (1 / 4) * c₁ ^ 4 - c₁ ^ 2 * c₂ +
          algebraMap ℚ A (1 / 2) * c₂ ^ 2 + c₁ * c₃ -
            6 * chernCharacterComponent RO R 4
    | _ => 0

end

end AlgebraicGeometry.IntersectionTheory.ChernCharacter
