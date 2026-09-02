/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.RiemannRoch.Surface.Divisor
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.ChernCharacter.Basic
import DerivedAlgGeo.AlgebraicGeometry.Duality.Canonical.Basic
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3

/-!
# Numerical Todd data for smooth proper surfaces

This file constructs the three Todd components needed by surface Riemann--Roch.  The
codimension-zero and codimension-one terms are the expected explicit classes

`td₀ = 1`,  `td₁ = -K_X / 2`.

The top component is not postulated.  It is the representative reconstructed from the
structure-sheaf twist polynomial, and its degree is proved to be the geometric Euler
characteristic `χ(O_X)`.  Representability of the twist functional remains explicit through
`PairingContext.ReconstructionData`; no global Chow group or hidden existence instance is used.

The resulting component family carries the grading and normalization statements expected by
`NumericalVarietyData`. A final comparison theorem turns geometric K3 hypotheses into a Layer A
`K3.IsK3` witness for any proposed `NumericalVarietyData` using these components.
-/

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch.Surface.ToddData

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Duality
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface
open AlgebraicGeometry.IntersectionTheory.Number

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
variable {D : FiniteCohomology k X}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A]

noncomputable section

theorem homogeneousPicardCoefficient_nil
    (d : ℕ) (f : Pic X → ℤ) :
    homogeneousPicardCoefficient d [] f = (f 1 : ℚ) := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (j : ℚ))
      (Finset.range (d + 1) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.cast_inj.mp hab
  have h := Lagrange.eval_interpolate_at_node
    (s := Finset.range (d + 1)) (v := fun j : ℕ ↦ (j : ℚ))
    (r := fun _j : ℕ ↦ (f 1 : ℚ)) hinj (i := 0) (by simp)
  have h0 : Polynomial.eval (0 : ℚ)
      (Lagrange.interpolate (Finset.range (d + 1)) (fun j : ℕ ↦ (j : ℚ))
        (fun _j : ℕ ↦ (f 1 : ℚ))) = (f 1 : ℚ) := by
    simpa using h
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h0
  simpa [homogeneousPicardCoefficient, interpolatingPolynomial,
    scaledPicardCoefficient, picardCoefficient] using h0

private theorem coeff_interpolate_range_three (q : ℕ → ℚ) (hq0 : q 0 = 0) :
    (Lagrange.interpolate (Finset.range 3) (fun j : ℕ ↦ (j : ℚ)) q).coeff 1 =
      2 * q 1 - q 2 / 2 := by
  have h0 : (Finset.range 3).erase 0 = {1, 2} := by decide
  have h1 : (Finset.range 3).erase 1 = {0, 2} := by decide
  have h2 : (Finset.range 3).erase 2 = {0, 1} := by decide
  have hc0 : (Lagrange.basis (Finset.range 3)
      (fun j : ℕ ↦ (j : ℚ)) 0).coeff 1 = -(3 / 2 : ℚ) := by
    rw [Lagrange.basis, h0]
    norm_num [Lagrange.basisDivisor, Finset.prod_insert, Polynomial.coeff_mul,
      Finset.Nat.antidiagonal_succ, Polynomial.coeff_one]
  have hc1 : (Lagrange.basis (Finset.range 3)
      (fun j : ℕ ↦ (j : ℚ)) 1).coeff 1 = 2 := by
    rw [Lagrange.basis, h1]
    norm_num [Lagrange.basisDivisor, Finset.prod_insert, Polynomial.coeff_mul,
      Finset.Nat.antidiagonal_succ]
  have hc2 : (Lagrange.basis (Finset.range 3)
      (fun j : ℕ ↦ (j : ℚ)) 2).coeff 1 = -(1 / 2 : ℚ) := by
    rw [Lagrange.basis, h2]
    norm_num [Lagrange.basisDivisor, Finset.prod_insert, Polynomial.coeff_mul,
      Finset.Nat.antidiagonal_succ]
  norm_num [Lagrange.interpolate, Finset.sum_range_succ, hc0, hc1, hc2]
  rw [hq0]
  ring

/-- The degree-one homogeneous coefficient of a quadratic Picard Euler function in one
direction, written using its values at the first three powers. -/
theorem homogeneousPicardCoefficient_singleton
    (f : Pic X → ℤ) (L : Pic X) :
    homogeneousPicardCoefficient 2 [L] f =
      2 * ((f L - f 1 : ℤ) : ℚ) - ((f (L ^ 2) - f 1 : ℤ) : ℚ) / 2 := by
  unfold homogeneousPicardCoefficient interpolatingPolynomial
  norm_num only [List.length_cons, List.length_nil]
  rw [coeff_interpolate_range_three]
  · simp [scaledPicardCoefficient, picardCoefficient, picardMixedDifference,
      picardDifference]
    rfl
  · simp [scaledPicardCoefficient, picardCoefficient, picardMixedDifference,
      picardDifference]

/-- The explicit geometric data used to construct the surface Todd components.

The structure-sheaf representative is required to realize the same Picard Euler function as
the intersection context.  Serre symmetry is included because it is what identifies the
linear Todd term with `-K_X/2`. -/
structure Data
    (P : PairingContext D C 2 A)
    (K : SmoothProperVariety.CanonicalSheafData k X 2) where
  structureData : P.ReconstructionData
    (structureSheafObject P.intersection.structureSheafCoherent)
  structure_rank : structureData.rank = 1
  structure_twists : structureData.twists.eulerPic = P.intersection.eulerPic
  serre : Serre.Data.SurfacePicardSymmetry P.intersection K.canonicalClass

variable {P : PairingContext D C 2 A}
variable {K : SmoothProperVariety.CanonicalSheafData k X 2}

/-- The canonical divisor class inside the chosen numerical intersection ring. -/
noncomputable def numericalCanonicalClass : A :=
  P.divisorClass K.canonicalClassAdd

/-- The codimension-zero Todd component. -/
def toddZero : A := 1

/-- The codimension-one Todd component `-K_X/2`. -/
noncomputable def toddOne : A :=
  -(algebraMap ℚ A (1 / 2) * numericalCanonicalClass (P := P) (K := K))

/-- The top Todd component reconstructed from the structure-sheaf twist polynomial. -/
noncomputable def toddTwo (T : Data P K) : A :=
  T.structureData.tauComponent 2

/-- The surface Todd components, extended by zero above the dimension. -/
noncomputable def toddComponent (T : Data P K) : ℕ → A
  | 0 => toddZero
  | 1 => toddOne (P := P) (K := K)
  | 2 => toddTwo T
  | _ => 0

theorem numericalCanonicalClass_mem :
    numericalCanonicalClass (P := P) (K := K) ∈ P.ring.piece 1 :=
  P.divisorClass_mem K.canonicalClassAdd

theorem toddZero_mem :
    toddZero (A := A) ∈ P.ring.piece 0 :=
  P.ring.one_mem_piece_zero

theorem toddOne_mem :
    toddOne (P := P) (K := K) ∈ P.ring.piece 1 := by
  unfold toddOne
  exact Submodule.neg_mem _ <| by
    simpa using P.ring.mul_mem_piece
      (P.ring.algebraMap_mem_piece_zero (1 / 2))
      (numericalCanonicalClass_mem (P := P) (K := K))

theorem toddTwo_mem (T : Data P K) :
    toddTwo T ∈ P.ring.piece 2 :=
  T.structureData.tauComponent_mem 2

theorem toddComponent_mem (T : Data P K) (i : ℕ) :
    toddComponent T i ∈ P.ring.piece i := by
  rcases i with _ | _ | _ | i
  · exact toddZero_mem
  · exact toddOne_mem
  · exact toddTwo_mem T
  · exact Submodule.zero_mem _

@[simp] theorem toddComponent_zero (T : Data P K) :
    toddComponent T 0 = 1 :=
  rfl

@[simp] theorem toddComponent_one (T : Data P K) :
    toddComponent T 1 = toddOne (P := P) (K := K) :=
  rfl

@[simp] theorem toddComponent_two (T : Data P K) :
    toddComponent T 2 = toddTwo T :=
  rfl

theorem toddComponent_eq_zero_of_two_lt (T : Data P K)
    {i : ℕ} (hi : 2 < i) : toddComponent T i = 0 := by
  rcases i with _ | _ | _ | i <;> simp [toddComponent] at hi ⊢

/-- The reconstructed top Todd component has degree `χ(O_X)`, derived from the
structure-sheaf twist polynomial rather than supplied as a Todd axiom. -/
theorem degree_toddTwo_eq_eulerPic_one (T : Data P K) :
    P.ring.degree (toddTwo T) =
      (P.intersection.eulerPic 1 : ℚ) := by
  have h := T.structureData.degree_tauComponent_mul_divisorProduct
    2 (by omega) [] (by simp)
  rw [PairingContext.twistPairing, homogeneousPicardCoefficient_nil] at h
  simpa [toddTwo, divisorProduct, T.structure_twists] using h

/-- Geometric form of the top normalization: `∫td₂ = χ(O_X)`. -/
theorem degree_toddTwo_eq_structureSheafEulerCharacteristic (T : Data P K) :
    P.ring.degree (toddTwo T) =
      (D.eulerCharacteristic
        (structureSheafObject P.intersection.structureSheafCoherent) : ℚ) := by
  rw [degree_toddTwo_eq_eulerPic_one T,
    eulerPic_one_eq_eulerCharacteristic_structureSheaf P.intersection]

/-- Realization of the intersection of the numerical canonical class with a divisor class. -/
theorem degree_numericalCanonicalClass_mul_divisorClass
    (L : Additive (Pic X)) :
    P.ring.degree
        (numericalCanonicalClass (P := P) (K := K) * P.divisorClass L) =
      (P.intersection.surfaceIntersectionPairing K.canonicalClassAdd L : ℤ) := by
  have h := P.degree_divisorProduct ![K.canonicalClass, L.toMul]
  rw [P.intersection.picardIntersectionNumber_fin2] at h
  change P.ring.degree
      (P.divisorClass (Additive.ofMul K.canonicalClass) * P.divisorClass L) =
    (P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul : ℚ)
  simpa [divisorProduct, numericalCanonicalClass] using h

/-- Serre symmetry identifies the degree-one Todd functional with `-K_X/2`. -/
theorem toddOnePairing_eq_neg_half_canonical (T : Data P K)
    (L : Additive (Pic X)) :
    toddOnePairing P.intersection L =
      -(P.intersection.surfaceIntersectionPairing K.canonicalClassAdd L : ℚ) / 2 := by
  have hrr := Surface.eulerPic_eq P.intersection T.serre L.toMul
  have hsymm := P.intersection.surfaceIntersectionPairing_symm
    K.canonicalClass L.toMul
  have hself : P.intersection.surfaceIntersectionPairing L L =
      P.intersection.surfaceIntersectionNumber L.toMul L.toMul := by
    simpa using P.intersection.surfaceIntersectionPairing_apply L.toMul L.toMul
  rw [toddOnePairing_apply]
  push_cast
  rw [hrr]
  unfold Surface.correctionNumerator
  change _ = -(P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul : ℚ) / 2
  change P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul =
    P.intersection.surfaceIntersectionNumber L.toMul K.canonicalClass at hsymm
  rw [hsymm, hself]
  push_cast
  ring

/-- Ring-valued form of `td₁ = -K_X/2`, tested against every divisor class. -/
theorem degree_toddOne_mul_divisorClass (T : Data P K)
    (L : Additive (Pic X)) :
    P.ring.degree
        (toddOne (P := P) (K := K) * P.divisorClass L) =
      toddOnePairing P.intersection L := by
  rw [toddOne, neg_mul, map_neg]
  rw [mul_assoc, P.ring.degree_algebraMap_mul,
    degree_numericalCanonicalClass_mul_divisorClass (P := P) (K := K) L,
    toddOnePairing_eq_neg_half_canonical T L]
  ring

/-- The explicit class `-K_X/2` is the degree-one representative reconstructed from the
structure-sheaf twist polynomial.  Thus the Todd family used by surface assembly is exactly the
one used to extract reconstructed Chern characters, rather than an independently postulated
comparison. -/
theorem structureToddOne_eq_toddOne (T : Data P K) :
    AlgebraicGeometry.IntersectionTheory.ChernCharacter.toddComponent T.structureData 1 =
      toddOne (P := P) (K := K) := by
  apply P.divisorPairing_ext 1 (by omega)
    (PairingContext.ReconstructionData.tauComponent_mem T.structureData 1)
    toddOne_mem
  intro classes hlength
  cases classes with
  | nil => simp at hlength
  | cons L classes =>
    cases classes with
    | nil =>
      rw [T.structureData.degree_tauComponent_mul_divisorProduct 1 (by omega) [L] (by simp)]
      rw [divisorProduct, List.map_singleton, List.prod_singleton,
        degree_toddOne_mul_divisorClass T (Additive.ofMul L)]
      rw [PairingContext.twistPairing, T.structure_twists,
        homogeneousPicardCoefficient_singleton]
      rw [toddOnePairing_apply, P.intersection.surfaceIntersectionPairing_apply,
        P.intersection.surfaceIntersectionNumber_eq]
      push_cast
      simp only [toMul_ofMul, pow_two]
      ring
    | cons M classes => simp at hlength

/-- Trivial canonical class forces the geometric first Todd component to vanish. -/
theorem toddOne_eq_zero (hK : K.canonicalClass = 1) :
    toddOne (P := P) (K := K) = 0 := by
  simp [toddOne, numericalCanonicalClass, SmoothProperVariety.CanonicalSheafData.canonicalClassAdd,
    hK]

/-- K3 top normalization: `χ(O_X)=2` gives `∫td₂=2`. -/
theorem degree_toddTwo_eq_two (T : Data P K)
    (hchi : P.intersection.eulerPic 1 = 2) :
    P.ring.degree (toddTwo T) = 2 := by
  rw [degree_toddTwo_eq_eulerPic_one T, hchi]
  norm_num

/-- A proposed Layer A numerical variety uses the geometrically constructed Todd components. -/
structure NumericalVarietyComparison
    {B : Type v} [CommRing B] [Algebra ℚ B]
    {N : Type w} [AddCommGroup N] (V : NumericalVarietyData 2 B N)
    {PB : PairingContext D C 2 B}
    {KB : SmoothProperVariety.CanonicalSheafData k X 2}
    (T : Data PB KB) : Prop where
  ring_eq : V.ring = PB.ring
  toddComp_eq : ∀ i,
    V.toddComp i = toddComponent T i

namespace NumericalVarietyComparison

variable {B : Type v} [CommRing B] [Algebra ℚ B]
variable {N : Type w} [AddCommGroup N]
variable (V : NumericalVarietyData 2 B N)
variable {PB : PairingContext D C 2 B}
variable {KB : SmoothProperVariety.CanonicalSheafData k X 2}

theorem toddComp_zero_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison V T) : V.toddComp 0 = 1 := by
  rw [Q.toddComp_eq, toddComponent_zero]

theorem toddComp_one_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison V T) :
    V.toddComp 1 = toddOne (P := PB) (K := KB) := by
  rw [Q.toddComp_eq, toddComponent_one]

theorem degree_toddComp_two_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison V T) :
    V.ring.degree (V.toddComp 2) =
      (PB.intersection.eulerPic 1 : ℚ) := by
  rw [Q.toddComp_eq, toddComponent_two, Q.ring_eq,
    degree_toddTwo_eq_eulerPic_one]

/-- The geometric Todd construction supplies the existing Layer A K3 hypotheses whenever the
Layer A variety is explicitly compared with it. -/
theorem toIsK3
    (T : Data PB KB) (Q : NumericalVarietyComparison V T)
    (hK : KB.canonicalClass = 1)
    (hchi : PB.intersection.eulerPic 1 = 2) :
    AlgebraicGeometry.Numerical.K3.IsK3 V where
  toddComp_one := by
    rw [Q.toddComp_eq, toddComponent_one, toddOne_eq_zero hK]
  degree_toddComp_two := by
    rw [Q.toddComp_eq, toddComponent_two, Q.ring_eq,
      degree_toddTwo_eq_two T hchi]

end NumericalVarietyComparison

end

end AlgebraicGeometry.RiemannRoch.Surface.ToddData
