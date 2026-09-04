/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.RiemannRoch.Surface.ToddData
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-!
# Surface Riemann--Roch by finite locally free dévissage

This file extends the line-bundle surface formula to the strongest honest coherent scope
currently supported by the repository.

* A determinant-equipped finite locally free coherent sheaf gets degree-level `ch₂` and `c₂`
  coordinates, with the classical rank/`c₁`/`c₂` Riemann--Roch formula.
* Those coordinates satisfy the expected short-exact additivity and Whitney formula when the
  determinant and rank comparisons are supplied.
* A coherent sheaf is treated only when it carries `TwoTermPerfectDeterminantData`.  Its `ch₂`
  is proved to be the difference of the two finite locally free terms in that resolution.

No global resolution property or splitting principle is inferred from coherence.  The current
The Mathlib/DerivedAlgGeo API has no theorem producing a finite locally free resolution for every
coherent
sheaf on a smooth projective surface, so the perfectness certificate remains visible in every
coherent theorem.  Compatibility with issue #32 is recorded through the explicit geometric
Grothendieck group and its Euler homomorphism.
-/

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch.Surface.Devissage

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface
open AlgebraicGeometry.IntersectionTheory.Number
open AlgebraicGeometry.RiemannRoch.Surface.ToddData

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
variable {D : FiniteCohomology k X}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {P : PairingContext D C 2 A}
variable {K : SmoothProperVariety.CanonicalSheafData k X 2}

noncomputable section

/-! ## Finite locally free coherent sheaves -/

/-- The degree of `ch₂` of a determinant-equipped finite locally free coherent sheaf, recovered
from its Euler characteristic and the geometric Todd terms. -/
noncomputable def locallyFreeCh2Degree {F : Coh X}
    (_T : ToddData.Data P K) (E : Coh.DeterminantData F) : ℚ :=
  (D.eulerCharacteristic F : ℚ) -
    (E.rank : ℚ) * (P.intersection.eulerPic 1 : ℚ) -
      toddOnePairing P.intersection E.firstChernClassAdd

/-- The degree of `c₂`, using `ch₂ = (c₁² - 2c₂)/2`. -/
noncomputable def locallyFreeC2Degree {F : Coh X}
    (T : ToddData.Data P K) (E : Coh.DeterminantData F) : ℚ :=
  (P.intersection.surfaceIntersectionPairing E.firstChernClassAdd
      E.firstChernClassAdd : ℤ) / 2 - locallyFreeCh2Degree T E

/-- Riemann--Roch for a finite locally free sheaf in Todd-coordinate form. -/
theorem locallyFree_eulerCharacteristic_eq_ch2
    {F : Coh X}
    (T : ToddData.Data P K) (E : Coh.DeterminantData F) :
    (D.eulerCharacteristic F : ℚ) =
      (E.rank : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        toddOnePairing P.intersection E.firstChernClassAdd +
          locallyFreeCh2Degree T E := by
  simp only [locallyFreeCh2Degree]
  ring

/-- Classical finite locally free surface formula
`χ(E) = rχ(O_X) + (c₁²-c₁K_X)/2 - c₂`. -/
theorem locallyFree_eulerCharacteristic_eq
    {F : Coh X}
    (T : ToddData.Data P K) (E : Coh.DeterminantData F) :
    (D.eulerCharacteristic F : ℚ) =
      (E.rank : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        ((P.intersection.surfaceIntersectionPairing E.firstChernClassAdd
              E.firstChernClassAdd : ℤ) -
          (P.intersection.surfaceIntersectionPairing E.firstChernClassAdd
              K.canonicalClassAdd : ℤ)) / 2 -
        locallyFreeC2Degree T E := by
  have hTodd := toddOnePairing_eq_neg_half_canonical T E.firstChernClassAdd
  have hsymm := P.intersection.surfaceIntersectionPairing_symm
    K.canonicalClass E.firstChernClass
  have hbase := locallyFree_eulerCharacteristic_eq_ch2 T E
  change P.intersection.surfaceIntersectionPairing K.canonicalClassAdd
      E.firstChernClassAdd =
    P.intersection.surfaceIntersectionPairing E.firstChernClassAdd
      K.canonicalClassAdd at hsymm
  rw [hTodd, hsymm] at hbase
  unfold locallyFreeC2Degree
  linarith

/-- Degree-level `ch₂` is additive in a determinant-compatible short exact sequence of finite
locally free coherent sheaves, once the chosen fixed ranks are explicitly compatible. -/
theorem locallyFreeCh2Degree_shortExact
    {S : ShortComplex (Coh X)}
    (T : ToddData.Data P K) (E : Coh.ShortExactDeterminantData S)
    (hrank : E.middle.rank = E.left.rank + E.right.rank) :
    locallyFreeCh2Degree T E.middle =
      locallyFreeCh2Degree T E.left + locallyFreeCh2Degree T E.right := by
  have hchi := D.eulerCharacteristic_additive (C S E.shortExact)
  have hc₁ := E.firstChernClassAdd_eq_add
  unfold locallyFreeCh2Degree
  rw [hchi, hrank, hc₁, map_add]
  push_cast
  ring

/-- The degree-level Whitney formula
`c₂(E₂)=c₂(E₁)+c₂(E₃)+c₁(E₁)c₁(E₃)`. -/
theorem locallyFreeC2Degree_shortExact
    {S : ShortComplex (Coh X)}
    (T : ToddData.Data P K) (E : Coh.ShortExactDeterminantData S)
    (hrank : E.middle.rank = E.left.rank + E.right.rank) :
    locallyFreeC2Degree T E.middle =
      locallyFreeC2Degree T E.left + locallyFreeC2Degree T E.right +
        (P.intersection.surfaceIntersectionPairing E.left.firstChernClassAdd
          E.right.firstChernClassAdd : ℤ) := by
  have hc₁ := E.firstChernClassAdd_eq_add
  have hch₂ := locallyFreeCh2Degree_shortExact T E hrank
  have hsymm := P.intersection.surfaceIntersectionPairing_symm
    E.right.firstChernClass E.left.firstChernClass
  change P.intersection.surfaceIntersectionPairing E.right.firstChernClassAdd
      E.left.firstChernClassAdd =
    P.intersection.surfaceIntersectionPairing E.left.firstChernClassAdd
      E.right.firstChernClassAdd at hsymm
  unfold locallyFreeC2Degree
  rw [hc₁, hch₂]
  simp only [map_add, LinearMap.add_apply]
  rw [hsymm]
  push_cast
  ring

/-! ## Explicit two-term perfect resolutions -/

/-- The virtual first Chern class is the difference of the two finite locally free terms. -/
theorem picardFirstChernClass_eq_middle_sub_left
    {F : Coh X}
    (Q : Coh.TwoTermPerfectDeterminantData F) :
    picardFirstChernClass Q =
      Q.middle.firstChernClassAdd - Q.left.firstChernClassAdd := by
  apply Additive.toMul.injective
  change Q.firstChernClass =
    Q.middle.firstChernClass * Q.left.firstChernClass⁻¹
  exact Q.firstChernClass_eq

/-- Euler dévissage along the recorded finite locally free resolution. -/
theorem eulerCharacteristic_eq_middle_sub_left
    {F : Coh X}
    (C : D.LinearConnectingSystem)
    (Q : Coh.TwoTermPerfectDeterminantData F) :
    D.eulerCharacteristic F =
      D.eulerCharacteristic Q.resolution.X₂ -
        D.eulerCharacteristic Q.resolution.X₁ := by
  have hseq := D.eulerCharacteristic_additive (C Q.resolution Q.shortExact)
  have hiso := D.eulerCharacteristic_iso Q.targetIso
  omega

/-- The reconstructed `ch₂` of a perfect coherent sheaf is the difference of the `ch₂` values
of the two finite locally free terms in its recorded resolution. -/
theorem chernCharacterTwoDegree_eq_middle_sub_left
    {F : Coh X}
    (T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) :
    chernCharacterTwoDegree P.intersection Q =
      locallyFreeCh2Degree T Q.middle - locallyFreeCh2Degree T Q.left := by
  have hchi := eulerCharacteristic_eq_middle_sub_left (D := D) C Q
  have hc₁ := picardFirstChernClass_eq_middle_sub_left Q
  unfold chernCharacterTwoDegree locallyFreeCh2Degree virtualRank
  rw [hchi, toddTwoDegree_eq_eulerPic_one P.intersection, hc₁, map_sub]
  push_cast
  ring

/-- The degree of the second Chern class of a perfect coherent sheaf. -/
noncomputable def perfectC2Degree {F : Coh X}
    (_T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) : ℚ :=
  (P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
      (picardFirstChernClass Q) : ℤ) / 2 -
    chernCharacterTwoDegree P.intersection Q

/-- Surface Riemann--Roch for a coherent sheaf with an explicit two-term finite locally free
resolution, in rank/`c₁`/`ch₂` form. -/
theorem perfect_eulerCharacteristic_eq_ch2
    {F : Coh X}
    (T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) :
    (D.eulerCharacteristic F : ℚ) =
      (virtualRank Q : ℚ) * (P.intersection.eulerPic 1 : ℚ) -
        (P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
          K.canonicalClassAdd : ℤ) / 2 +
        chernCharacterTwoDegree P.intersection Q := by
  have hbase :=
    eulerCharacteristic_eq_rank_mul_toddTwo_add_toddOne_add_chernCharacterTwo
      P.intersection Q
  have hTodd := toddOnePairing_eq_neg_half_canonical T (picardFirstChernClass Q)
  have hsymm := P.intersection.surfaceIntersectionPairing_symm
    K.canonicalClass (picardFirstChernClass Q).toMul
  change P.intersection.surfaceIntersectionPairing K.canonicalClassAdd
      (picardFirstChernClass Q) =
    P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
      K.canonicalClassAdd at hsymm
  rw [toddTwoDegree_eq_eulerPic_one P.intersection, hTodd, hsymm] at hbase
  linarith

/-- Classical rank/`c₁`/`c₂` surface formula for explicitly perfect coherent sheaves. -/
theorem perfect_eulerCharacteristic_eq
    {F : Coh X}
    (T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) :
    (D.eulerCharacteristic F : ℚ) =
      (virtualRank Q : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        ((P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              (picardFirstChernClass Q) : ℤ) -
          (P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              K.canonicalClassAdd : ℤ)) / 2 -
        perfectC2Degree T Q := by
  have h := perfect_eulerCharacteristic_eq_ch2 T Q
  unfold perfectC2Degree
  linarith

/-- The discriminant in `c₂` form:
`Δ = 2r c₂ - (r-1)c₁²`. -/
theorem discriminantDegree_eq_c2
    {F : Coh X}
    (T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) :
    discriminantDegree P.intersection Q =
      2 * (virtualRank Q : ℚ) * perfectC2Degree T Q -
        ((virtualRank Q : ℚ) - 1) *
          (P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
            (picardFirstChernClass Q) : ℤ) := by
  unfold discriminantDegree perfectC2Degree
  ring

/-! ## Grothendieck-group compatibility -/

/- `coherentGrothendieckClass_shortExact` stood here: fourteen lines deriving the
defining relation of the coherent Grothendieck group by hand, through
`QuotientAddGroup.mk'`, `AddSubgroup.subset_closure` and the `shortExact`
constructor. It is `K₀Ab.of_shortExact`, proved once. Nothing referenced it but
its own audit record. -/

/-- The perfect surface formula computes exactly the value of the Grothendieck Euler
homomorphism on the coherent-sheaf class. -/
theorem grothendieckEulerHom_class_eq_perfect_formula
    {F : Coh X}
    (T : ToddData.Data P K) (Q : Coh.TwoTermPerfectDeterminantData F) :
    (D.grothendieckEulerHom C (K₀Ab.of F) : ℚ) =
      (virtualRank Q : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        ((P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              (picardFirstChernClass Q) : ℤ) -
          (P.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              K.canonicalClassAdd : ℤ)) / 2 -
        perfectC2Degree T Q := by
  rw [D.grothendieckEulerHom_class]
  exact perfect_eulerCharacteristic_eq T Q

/-! ## Term-by-term Layer A comparison -/

/-- Explicit comparison between one Layer A numerical class and the geometric data of an
explicitly perfect coherent sheaf.  Each term of `Numerical.Surface.chi_eq` is compared
separately; no equality of characteristic classes is inferred from equality of Euler numbers. -/
structure NumericalVarietyComparison
    {B : Type v} [CommRing B] [Algebra ℚ B]
    {N : Type w} [AddCommGroup N] (V : NumericalVarietyData 2 B N)
    {PB : PairingContext D C 2 B}
    {KB : SmoothProperVariety.CanonicalSheafData k X 2}
    {F : Coh X}
    (Q : Coh.TwoTermPerfectDeterminantData F) (E : N) : Prop where
  euler_eq : V.chi E = D.eulerCharacteristic F
  rank_eq : V.rank E = virtualRank Q
  toddTwo_degree : V.ring.degree (V.toddComp 2) =
    (PB.intersection.eulerPic 1 : ℚ)
  toddOne_degree : V.ring.degree (V.chComp E 1 * V.toddComp 1) =
    toddOnePairing PB.intersection (picardFirstChernClass Q)
  chTwo_degree : V.ring.degree (V.chComp E 2) =
    chernCharacterTwoDegree PB.intersection Q

namespace NumericalVarietyComparison

variable {B : Type v} [CommRing B] [Algebra ℚ B]
variable {N : Type w} [AddCommGroup N]
variable (V : NumericalVarietyData 2 B N)
variable {PB : PairingContext D C 2 B}
variable {KB : SmoothProperVariety.CanonicalSheafData k X 2}
variable {F : Coh X}
variable {Q : Coh.TwoTermPerfectDeterminantData F} {E : N}

/-- The Layer A surface expansion becomes exactly the geometric rank/Todd/`ch₂` expansion. -/
theorem chi_eq_geometric_terms (hV : V.SatisfiesHRR)
    (R : NumericalVarietyComparison V (PB := PB) (KB := KB) Q E) :
    (V.chi E : ℚ) =
      (virtualRank Q : ℚ) * (PB.intersection.eulerPic 1 : ℚ) +
        toddOnePairing PB.intersection (picardFirstChernClass Q) +
          chernCharacterTwoDegree PB.intersection Q := by
  rw [AlgebraicGeometry.Numerical.Surface.chi_eq V hV E, R.rank_eq,
    R.toddTwo_degree, R.toddOne_degree, R.chTwo_degree]

/-- The compared Layer A Euler homomorphism agrees with the geometric one on this class. -/
theorem chi_eq_geometric (R : NumericalVarietyComparison V (PB := PB) (KB := KB) Q E) :
    V.chi E = D.eulerCharacteristic F :=
  R.euler_eq

/-- After the explicit term comparisons, Layer A and geometric surface Riemann--Roch give the
same classical rank/`c₁`/`c₂` formula. -/
theorem chi_eq_classical
    (T : ToddData.Data PB KB)
    (R : NumericalVarietyComparison V (PB := PB) (KB := KB) Q E) :
    (V.chi E : ℚ) =
      (virtualRank Q : ℚ) * (PB.intersection.eulerPic 1 : ℚ) +
        ((PB.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              (picardFirstChernClass Q) : ℤ) -
          (PB.intersection.surfaceIntersectionPairing (picardFirstChernClass Q)
              KB.canonicalClassAdd : ℤ)) / 2 -
        perfectC2Degree T Q := by
  rw [R.euler_eq]
  exact perfect_eulerCharacteristic_eq T Q

end NumericalVarietyComparison

end

end AlgebraicGeometry.RiemannRoch.Surface.Devissage
