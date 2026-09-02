/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Duality.Serre.Cohomology
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Effective
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Surface.Number

/-!
# Riemann--Roch for Cartier divisors on smooth proper surfaces

This file proves the geometric surface formula

`χ(O_X(D)) = χ(O_X) + (D · (D - K_X)) / 2`

from the degree-two Snapper intersection pairing and the Picard Euler symmetry supplied by
Serre duality. It does not import or invoke the Layer A Hirzebruch--Riemann--Roch property.

The proof is first carried out intrinsically on `Pic X`.  The numerator is shown to be even over
`ℤ`, before division by two in `ℚ`.  It is then specialized to Cartier divisors, where
principal-equivalence invariance is formal.  Finally, `EffectiveSequenceRealization` connects the
formula to #25's genuine coherent short exact sequence

`0 → O_X(E-D) → O_X(E) → O_X(E) ⊗ i_*O_D → 0`.

Coherence and the comparison between chosen Picard representatives and the displayed associated
sheaves remain explicit because those closure/comparison constructors are not yet automatic in
the current geometric layer.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch.Surface

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Duality
open AlgebraicGeometry.IntersectionTheory.Number

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
variable {D : FiniteCohomology k X}
variable {C : D.LinearConnectingSystem}
variable (I : IntersectionContext D C 2)

noncomputable section

/-- The integral numerator in the surface divisor formula. -/
def correctionNumerator (K L : Pic X) : ℤ :=
  I.surfaceIntersectionNumber L L - I.surfaceIntersectionNumber L K

/-- Serre symmetry and bilinearity give the denominator-free surface formula. -/
theorem twice_eulerPic_sub
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (L : Pic X) :
    2 * (I.eulerPic L - I.eulerPic 1) = correctionNumerator I K L := by
  have hpair_inv :
      I.surfaceIntersectionNumber L L⁻¹ = -I.surfaceIntersectionNumber L L := by
    have h := map_neg (I.surfaceIntersectionPairing (Additive.ofMul L))
      (Additive.ofMul L)
    change I.surfaceIntersectionPairing (Additive.ofMul L)
        (Additive.ofMul L⁻¹) =
      -I.surfaceIntersectionPairing (Additive.ofMul L) (Additive.ofMul L)
    exact h
  have hpair_K_inv :
      I.surfaceIntersectionNumber K L⁻¹ = -I.surfaceIntersectionNumber K L := by
    have h := map_neg (I.surfaceIntersectionPairing (Additive.ofMul K))
      (Additive.ofMul L)
    change I.surfaceIntersectionPairing (Additive.ofMul K)
        (Additive.ofMul L⁻¹) =
      -I.surfaceIntersectionPairing (Additive.ofMul K) (Additive.ofMul L)
    exact h
  have hsymm : I.surfaceIntersectionNumber K L =
      I.surfaceIntersectionNumber L K := by
    exact I.surfaceIntersectionPairing_symm K L
  have hcanonical := P.canonical
  have hserre := P.symmetry L
  rw [I.surfaceIntersectionNumber_eq] at hpair_inv hpair_K_inv
  simp only [mul_inv_cancel] at hpair_inv
  unfold correctionNumerator
  omega

/-- The factor `1/2` is integral: the intersection numerator is even. -/
theorem correctionNumerator_even
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (L : Pic X) :
    Even (correctionNumerator I K L) := by
  refine ⟨I.eulerPic L - I.eulerPic 1, ?_⟩
  have h := twice_eulerPic_sub I P L
  unfold correctionNumerator at h ⊢
  omega

/-- Intrinsic Picard-group surface Riemann--Roch. -/
theorem eulerPic_eq
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (L : Pic X) :
    (I.eulerPic L : ℚ) = (I.eulerPic 1 : ℚ) +
      (correctionNumerator I K L : ℚ) / 2 := by
  have h := twice_eulerPic_sub I P L
  have hq :
      (2 : ℚ) * ((I.eulerPic L : ℚ) - (I.eulerPic 1 : ℚ)) =
        (I.surfaceIntersectionNumber L L : ℚ) -
          (I.surfaceIntersectionNumber L K : ℚ) := by
    exact_mod_cast h
  unfold correctionNumerator
  push_cast
  linarith

/-- The Euler characteristic of the Cartier line bundle `O_X(E)`, through its Picard class. -/
def cartierEulerCharacteristic (E : CartierDivisor X) : ℤ :=
  I.eulerPic (CartierDivisor.toPic E)

/-- The intersection numerator `E · (E-K)` for a Cartier divisor. -/
def cartierCorrectionNumerator (K : Pic X)
    (E : CartierDivisor X) : ℤ :=
  correctionNumerator I K (CartierDivisor.toPic E)

/-- Surface Riemann--Roch for an arbitrary Cartier divisor. -/
theorem cartier_eulerCharacteristic_eq
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (E : CartierDivisor X) :
    (cartierEulerCharacteristic I E : ℚ) = (I.eulerPic 1 : ℚ) +
      (cartierCorrectionNumerator I K E : ℚ) / 2 :=
  eulerPic_eq I P (CartierDivisor.toPic E)

/-- The Cartier numerator is even before passing to rational coefficients. -/
theorem cartierCorrectionNumerator_even
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (E : CartierDivisor X) :
    Even (cartierCorrectionNumerator I K E) :=
  correctionNumerator_even I P (CartierDivisor.toPic E)

/-- Principal-equivalent Cartier divisors have the same geometric Euler characteristic. -/
theorem cartierEulerCharacteristic_eq_of_principalEquivalent
    {E E' : CartierDivisor X}
    (h : CartierDivisor.toClass X E =
      CartierDivisor.toClass X E') :
    cartierEulerCharacteristic I E = cartierEulerCharacteristic I E' := by
  unfold cartierEulerCharacteristic
  congr 1
  change CartierDivisor.classToPic
      (Multiplicative.ofAdd (CartierDivisor.toClass X E)) =
    CartierDivisor.classToPic
      (Multiplicative.ofAdd (CartierDivisor.toClass X E'))
  rw [h]

/-- The full Riemann--Roch expression is invariant under Cartier divisor-class equivalence. -/
theorem cartier_formula_eq_of_principalEquivalent
    {K : Pic X}
    {E E' : CartierDivisor X}
    (h : CartierDivisor.toClass X E =
      CartierDivisor.toClass X E') :
    cartierEulerCharacteristic I E = cartierEulerCharacteristic I E' ∧
      cartierCorrectionNumerator I K E = cartierCorrectionNumerator I K E' := by
  have hPic : CartierDivisor.toPic E = CartierDivisor.toPic E' := by
    change CartierDivisor.classToPic
        (Multiplicative.ofAdd (CartierDivisor.toClass X E)) =
      CartierDivisor.classToPic
        (Multiplicative.ofAdd (CartierDivisor.toClass X E'))
    rw [h]
  constructor
  · exact cartierEulerCharacteristic_eq_of_principalEquivalent I h
  · unfold cartierCorrectionNumerator correctionNumerator
    rw [hPic]

/-! ## Effective divisors and the fundamental exact sequence -/

/-- Realization data connecting #25's twisted fundamental sequence to the intrinsic Picard
Euler function.  The quotient term needs no additional comparison: it is the actual coherent
third object of that sequence. -/
structure EffectiveSequenceRealization
    (A : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) where
  sourceCoherent : Scheme.coherent X
    (CartierDivisor.associatedSheaf (E - A.divisor))
  middleCoherent : Scheme.coherent X
    (CartierDivisor.associatedSheaf E)
  sourceEuler :
    D.eulerCharacteristic
        (A.cohTwistSequence E sourceCoherent middleCoherent).X₁ =
      I.eulerPic (CartierDivisor.toPic (E - A.divisor))
  middleEuler :
    D.eulerCharacteristic
        (A.cohTwistSequence E sourceCoherent middleCoherent).X₂ =
      I.eulerPic (CartierDivisor.toPic E)

namespace EffectiveSequenceRealization

variable {I}
variable {A : EffectiveCartierDivisor (X := X)}
variable {E : CartierDivisor X}
variable (R : EffectiveSequenceRealization I A E)

/-- The coherent quotient term `O_X(E) ⊗ i_*O_A`. -/
abbrev quotient : Coh X :=
  (A.cohTwistSequence E R.sourceCoherent R.middleCoherent).X₃

/-- Euler additivity for the genuine twisted fundamental sequence. -/
theorem euler_additivity :
    I.eulerPic (CartierDivisor.toPic E) =
      I.eulerPic (CartierDivisor.toPic (E - A.divisor)) +
        D.eulerCharacteristic R.quotient := by
  have h := D.eulerCharacteristic_additive
    (C (A.cohTwistSequence E R.sourceCoherent R.middleCoherent)
      (A.cohTwistSequence_shortExact E R.sourceCoherent R.middleCoherent))
  rw [R.middleEuler, R.sourceEuler] at h
  exact h

/-- For the effective divisor itself, the exact sequence reads
`χ(O_X(A)) = χ(O_X) + χ(O_X(A)|_A)`. -/
theorem effective_euler_additivity
    (hself : E = A.divisor) :
    I.eulerPic (CartierDivisor.toPic A.divisor) = I.eulerPic 1 +
      D.eulerCharacteristic R.quotient := by
  subst E
  have hzero :
      CartierDivisor.toPic (0 : CartierDivisor X) = 1 := by
    have h := map_zero
      (CartierDivisor.divisorToPicAdd (X := X))
    have h' := congrArg Additive.toMul h
    simpa using h'
  have h := R.euler_additivity
  simp only [sub_self] at h
  rw [hzero] at h
  exact h

/-- The geometric curve/intersection comparison needed to compute the quotient term in the
effective-divisor sequence.  Keeping this comparison explicit isolates the remaining adjunction
input from the already-constructed coherent short exact sequence. -/
structure QuotientIntersectionComparison
    (K : Pic X) where
  quotientEuler :
    (D.eulerCharacteristic R.quotient : ℚ) =
      (cartierCorrectionNumerator I K A.divisor : ℚ) / 2

/-- Surface Riemann--Roch for an effective divisor, obtained directly from #25's coherent
fundamental sequence and the geometric intersection computation on its quotient. -/
theorem effective_divisor_formula_from_sequence
    (hself : E = A.divisor)
    {K : Pic X}
    (Q : R.QuotientIntersectionComparison K) :
    (cartierEulerCharacteristic I A.divisor : ℚ) = (I.eulerPic 1 : ℚ) +
      (cartierCorrectionNumerator I K A.divisor : ℚ) / 2 := by
  have hadd := R.effective_euler_additivity hself
  have haddq :
      (I.eulerPic (CartierDivisor.toPic A.divisor) : ℚ) =
        (I.eulerPic 1 : ℚ) + (D.eulerCharacteristic R.quotient : ℚ) := by
    exact_mod_cast hadd
  unfold cartierEulerCharacteristic
  rw [haddq, Q.quotientEuler]

/-- The effective-divisor specialization of surface Riemann--Roch. -/
theorem effective_divisor_formula
    (_R : EffectiveSequenceRealization I A E)
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K) :
    (cartierEulerCharacteristic I A.divisor : ℚ) = (I.eulerPic 1 : ℚ) +
      (cartierCorrectionNumerator I K A.divisor : ℚ) / 2 :=
  cartier_eulerCharacteristic_eq I P A.divisor

/-- Combining the effective exact sequence with Riemann--Roch computes the quotient Euler
characteristic as half the intersection numerator. -/
theorem quotient_eulerCharacteristic_eq_half_correction
    (hself : E = A.divisor)
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K) :
    (D.eulerCharacteristic R.quotient : ℚ) =
      (cartierCorrectionNumerator I K A.divisor : ℚ) / 2 := by
  have hadd := R.effective_euler_additivity hself
  have hrr := effective_divisor_formula (I := I) R P
  have haddq :
      (I.eulerPic (CartierDivisor.toPic A.divisor) : ℚ) =
        (I.eulerPic 1 : ℚ) + (D.eulerCharacteristic R.quotient : ℚ) := by
    exact_mod_cast hadd
  unfold cartierEulerCharacteristic at hrr
  linarith

end EffectiveSequenceRealization

/-! ## Normalizations and K3 specialization -/

/-- `D = 0`: the correction term vanishes. -/
theorem eulerPic_one (K : Pic X)
    (P : Serre.Data.SurfacePicardSymmetry I K) :
    (I.eulerPic 1 : ℚ) = (I.eulerPic 1 : ℚ) +
      (correctionNumerator I K 1 : ℚ) / 2 := by
  simpa using eulerPic_eq I P 1

/-- `D = K_X`: Serre duality gives `χ(O_X(K_X)) = χ(O_X)`. -/
theorem eulerPic_canonical
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K) :
    I.eulerPic K = I.eulerPic 1 :=
  P.canonical

/-- K3 specialization: for trivial canonical class,
`χ(L) = χ(O_X) + L²/2`. -/
theorem k3_eulerPic_eq
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (hK : K = 1) (L : Pic X) :
    (I.eulerPic L : ℚ) = (I.eulerPic 1 : ℚ) +
      (I.surfaceIntersectionNumber L L : ℚ) / 2 := by
  have h := eulerPic_eq I P L
  subst K
  have hzero : I.surfaceIntersectionNumber L 1 = 0 := by
    change I.surfaceIntersectionPairing (Additive.ofMul L) 0 = 0
    exact map_zero (I.surfaceIntersectionPairing (Additive.ofMul L))
  unfold correctionNumerator at h
  rw [hzero] at h
  simpa using h

/-- K3 normalization with `χ(O_X)=2`, matching the audited Layer A numerical formula. -/
theorem k3_eulerPic_eq_two
    {K : Pic X}
    (P : Serre.Data.SurfacePicardSymmetry I K)
    (hK : K = 1) (hchi : I.eulerPic 1 = 2)
    (L : Pic X) :
    (I.eulerPic L : ℚ) = 2 +
      (I.surfaceIntersectionNumber L L : ℚ) / 2 := by
  have h := k3_eulerPic_eq I P hK L
  rw [hchi] at h
  norm_num at h ⊢
  exact h

end

end AlgebraicGeometry.RiemannRoch.Surface
