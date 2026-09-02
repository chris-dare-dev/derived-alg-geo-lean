/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.RiemannRoch.Surface.Devissage
import DerivedAlgGeo.AlgebraicGeometry.RiemannRoch.Surface.NumericalVariety

/-!
# Geometric assembly of the surface numerical variety

This file closes the surface bridge from the geometric Todd and reconstruction data to the
Layer A `NumericalVarietyData` interface.

The crucial all-coherent HRR theorem comes from reconstruction, not from an unproved global
resolution theorem.  For every coherent sheaf, the degree of its reconstructed top
Todd-weighted component is its Euler characteristic, while triangular extraction identifies
that component with the degree-two part of `ch(F) td(X)`.  The explicit-perfect dévissage API
then supplies the classical rank/`c₁`/`c₂` interpretation whenever a two-term finite locally
free resolution is actually present.
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch.Surface.Assembly

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface
open AlgebraicGeometry.IntersectionTheory.Number
open AlgebraicGeometry.IntersectionTheory.Snapper
open AlgebraicGeometry.RiemannRoch.Surface.ToddData

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X]
variable {D : FiniteCohomology k X}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {P : PairingContext D C 2 A}
variable {K : SmoothProperVariety.CanonicalSheafData k X 2}

noncomputable section

/-! ## Reconstruction computes the geometric Euler characteristic -/

/-- The Picard Euler function in any reconstruction package takes the trivial class to the
actual Euler characteristic of its coherent sheaf. -/
theorem reconstruction_eulerPic_one {F : Coh X}
    (Q : P.ReconstructionData F) :
    Q.twists.eulerPic 1 = D.eulerCharacteristic F := by
  let L : Fin 0 → Pic X := fun i ↦ Fin.elim0 i
  have h := Q.twists.realization 0 L (0 : Fin 0 → ℤ)
  rw [picardMonomial_zero] at h
  calc
    Q.twists.eulerPic 1 =
        D.eulerCharacteristic ((Q.twists.twistFamily 0 L).obj 0) := h
    _ = D.eulerCharacteristic F := by
      apply D.eulerCharacteristic_iso
      apply ObjectProperty.isoMk (Scheme.coherent X)
      simpa [CoherentTwistFamily.obj, twistModules, twistModulesAlong] using
        (Iso.refl F.1)

/-- The degree of the top reconstructed Todd-weighted component is the coherent Euler
characteristic. -/
theorem degree_tauComponent_two_eq_eulerCharacteristic
    {F : Coh X} (Q : P.ReconstructionData F) :
    P.ring.degree (Q.tauComponent 2) =
      (D.eulerCharacteristic F : ℚ) := by
  have h := Q.degree_tauComponent_mul_divisorProduct 2 (by omega) [] (by simp)
  rw [divisorProduct_nil, mul_one, PairingContext.twistPairing,
    homogeneousPicardCoefficient_nil] at h
  calc
    P.ring.degree (Q.tauComponent 2) =
        (Q.twists.eulerPic 1 : ℚ) := h
    _ = (D.eulerCharacteristic F : ℚ) := by
      exact_mod_cast reconstruction_eulerPic_one Q

private theorem degree_surface_total
    (c0 c1 c2 t0 t1 t2 : A) (r : ℚ)
    (hc0m : c0 ∈ P.ring.piece 0)
    (hc1m : c1 ∈ P.ring.piece 1)
    (hc2m : c2 ∈ P.ring.piece 2)
    (ht0m : t0 ∈ P.ring.piece 0)
    (ht1m : t1 ∈ P.ring.piece 1)
    (ht2m : t2 ∈ P.ring.piece 2)
    (hc0 : c0 = algebraMap ℚ A r) (ht0 : t0 = 1) :
    P.ring.degree ((c0 + c1 + c2) * (t0 + t1 + t2)) =
      r * P.ring.degree t2 +
        P.ring.degree (c1 * t1) +
          P.ring.degree c2 := by
  have h00 : P.ring.degree (c0 * t0) = 0 :=
    P.ring.degree_eq_zero_of_mem (by omega)
      (P.ring.mul_mem_piece hc0m ht0m)
  have h01 : P.ring.degree (c0 * t1) = 0 :=
    P.ring.degree_eq_zero_of_mem (by omega)
      (P.ring.mul_mem_piece hc0m ht1m)
  have h10 : P.ring.degree (c1 * t0) = 0 :=
    P.ring.degree_eq_zero_of_mem (by omega)
      (P.ring.mul_mem_piece hc1m ht0m)
  have hprod : (c0 + c1 + c2) * (t0 + t1 + t2) =
      c0 * t0 + c0 * t1 + c0 * t2 +
        c1 * t0 + c1 * t1 + c1 * t2 +
          c2 * t0 + c2 * t1 + c2 * t2 := by ring
  rw [hprod]
  simp only [map_add]
  have h12 : c1 * t2 = 0 := P.ring.eq_zero_of_mem_piece_of_lt (by omega)
    (P.ring.mul_mem_piece hc1m ht2m)
  have h21 : c2 * t1 = 0 := P.ring.eq_zero_of_mem_piece_of_lt (by omega)
    (P.ring.mul_mem_piece hc2m ht1m)
  have h22 : c2 * t2 = 0 := P.ring.eq_zero_of_mem_piece_of_lt (by omega)
    (P.ring.mul_mem_piece hc2m ht2m)
  rw [h00, h01, h10, h12, h21, h22, map_zero, add_zero, zero_add, hc0,
    P.ring.degree_algebraMap_mul, ht0, mul_one]
  ring

/-! ## The concrete geometric HRR datum -/

/-- Surface HRR for a coherent sheaf, proved from its reconstruction data and the geometrically
constructed Todd components. -/
theorem sheaf_hirzebruch_riemannRoch
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X) :
    (D.eulerCharacteristic F : ℚ) = P.ring.degree
      ((∑ i ∈ Finset.range 3,
          chernCharacterComponent T.structureData (R.reconstruction F) i) *
        (∑ j ∈ Finset.range 3, ToddData.toddComponent T j)) := by
  let Q := R.reconstruction F
  let c0 := chernCharacterComponent T.structureData Q 0
  let c1 := chernCharacterComponent T.structureData Q 1
  let c2 := chernCharacterComponent T.structureData Q 2
  let t0 := ToddData.toddComponent T 0
  let t1 := ToddData.toddComponent T 1
  let t2 := ToddData.toddComponent T 2
  have hsurface := degree_surface_total c0 c1 c2 t0 t1 t2 (Q.rank : ℚ)
    (chernCharacterComponent_mem T.structureData Q 0)
    (chernCharacterComponent_mem T.structureData Q 1)
    (chernCharacterComponent_mem T.structureData Q 2)
    (ToddData.toddComponent_mem T 0) (ToddData.toddComponent_mem T 1)
    (ToddData.toddComponent_mem T 2) (by simp [c0]) (by simp [t0])
  have htauDegree := degree_tauComponent_two_eq_eulerCharacteristic Q
  have htau := tauComponent_two_eq T.structureData Q
  have ht2 :
      AlgebraicGeometry.IntersectionTheory.ChernCharacter.toddComponent T.structureData 2 = t2 :=
    rfl
  have hdegree := congrArg (P.ring.degree) htau
  simp only [map_add] at hdegree
  rw [ToddData.structureToddOne_eq_toddOne T, ht2] at hdegree
  change P.ring.degree (Q.tauComponent 2) =
    P.ring.degree c2 +
      P.ring.degree (c1 * t1) +
        P.ring.degree (c0 * t2) at hdegree
  have hc0 : c0 = algebraMap ℚ A (Q.rank : ℚ) := by simp [c0]
  rw [hc0, P.ring.degree_algebraMap_mul] at hdegree
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsurface]
  calc
    (D.eulerCharacteristic F : ℚ) =
        P.ring.degree (Q.tauComponent 2) := htauDegree.symm
    _ = (Q.rank : ℚ) * P.ring.degree t2 +
        P.ring.degree (c1 * t1) +
          P.ring.degree c2 := by
      linarith [hdegree]

/-- The concrete geometric input to the surface numerical-variety assembly. The theorem above
supplies its separate HRR witness rather than adding proof data here. -/
noncomputable def toGeometricData
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P)) :
    GeometricData T.structureData R where
  toddComponent := ToddData.toddComponent T
  toddComponent_mem := ToddData.toddComponent_mem T
  toddComponent_zero := ToddData.toddComponent_zero T

/-- The constructed geometric data satisfies sheaf-level HRR. -/
theorem toGeometricData_satisfiesSheafHRR
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P)) :
    (toGeometricData T R).SatisfiesSheafHRR :=
  ⟨sheaf_hirzebruch_riemannRoch T R⟩

/-- The scheme-derived numerical surface obtained from the concrete Todd and reconstruction
data. -/
@[reducible]
noncomputable def toNumericalVariety
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P)) :
    NumericalVarietyData 2 A (K₀Ab (Coh X)) :=
  (toGeometricData T R).toNumericalVariety

/-- The assembled numerical presentation satisfies HRR. -/
theorem toNumericalVariety_satisfiesHRR
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P)) :
    (toNumericalVariety T R).SatisfiesHRR :=
  GeometricData.toNumericalVariety_satisfiesHRR
    (RO := T.structureData) (toGeometricData T R)
      (toGeometricData_satisfiesSheafHRR T R)

/-! ## Explicit-perfect comparison with dévissage -/

/-- Compatibility data between the twist-polynomial reconstruction of one coherent sheaf and
an actually supplied two-term finite locally free resolution.  No resolution is inferred from
coherence. -/
structure PerfectReconstructionComparison
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X) where
  resolution : Coh.TwoTermPerfectDeterminantData F
  rank_eq : (R.reconstruction F).rank = virtualRank resolution
  firstChern_eq : chernCharacterComponent T.structureData (R.reconstruction F) 1 =
    P.divisorClass (picardFirstChernClass resolution)

/-- The reconstructed rank of an explicitly perfect coherent sheaf is its virtual rank. -/
theorem perfect_rank_eq
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X)
    (Q : PerfectReconstructionComparison T R F) :
    (R.reconstruction F).rank = virtualRank Q.resolution :=
  Q.rank_eq

/-- The top Todd term in the assembled numerical surface is `χ(O_X)`. -/
theorem perfect_toddTwo_degree
    (T : ToddData.Data P K) :
    P.ring.degree (ToddData.toddComponent T 2) =
      (P.intersection.eulerPic 1 : ℚ) := by
  simpa using ToddData.degree_toddTwo_eq_eulerPic_one T

/-- The mixed `ch₁ td₁` term of an explicitly perfect coherent sheaf is its classical
Todd-one pairing. -/
theorem perfect_toddOne_degree
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X)
    (Q : PerfectReconstructionComparison T R F) :
    P.ring.degree
      (chernCharacterComponent T.structureData (R.reconstruction F) 1 *
        ToddData.toddComponent T 1) =
      toddOnePairing P.intersection (picardFirstChernClass Q.resolution) := by
  rw [Q.firstChern_eq, ToddData.toddComponent_one, mul_comm]
  exact ToddData.degree_toddOne_mul_divisorClass T
    (picardFirstChernClass Q.resolution)

/-- The reconstructed `ch₂` term of an explicitly perfect coherent sheaf has the classical
degree computed by its supplied two-term resolution. -/
theorem perfect_chTwo_degree
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X)
    (Q : PerfectReconstructionComparison T R F) :
    P.ring.degree
      (chernCharacterComponent T.structureData (R.reconstruction F) 2) =
      chernCharacterTwoDegree P.intersection Q.resolution := by
  apply degree_chernCharacterComponent_two_eq_surface P T.structureData
    (R.reconstruction F) Q.resolution Q.rank_eq
  · exact degree_tauComponent_two_eq_eulerCharacteristic (R.reconstruction F)
  · exact Q.firstChern_eq
  · rw [ToddData.structureToddOne_eq_toddOne T, mul_comm]
    exact ToddData.degree_toddOne_mul_divisorClass T
      (picardFirstChernClass Q.resolution)
  · change P.ring.degree (ToddData.toddTwo T) =
      toddTwoDegree P.intersection
    rw [ToddData.degree_toddTwo_eq_eulerPic_one,
      toddTwoDegree_eq_eulerPic_one]

/-- On an explicitly perfect coherent sheaf, the assembled surface expansion is exactly the
rank/Todd/`ch₂` expansion supplied by geometric dévissage. -/
theorem perfect_surface_expansion
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X)
    (Q : PerfectReconstructionComparison T R F) :
    (D.eulerCharacteristic F : ℚ) =
      (virtualRank Q.resolution : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        toddOnePairing P.intersection (picardFirstChernClass Q.resolution) +
          chernCharacterTwoDegree P.intersection Q.resolution := by
  have h := GeometricData.surface_chi_class_eq (RO := T.structureData)
    (toGeometricData T R) (toGeometricData_satisfiesSheafHRR T R) F
  change (D.eulerCharacteristic F : ℚ) =
    ((R.reconstruction F).rank : ℚ) *
        P.ring.degree (ToddData.toddComponent T 2) +
      P.ring.degree
        (chernCharacterComponent T.structureData (R.reconstruction F) 1 *
          ToddData.toddComponent T 1) +
      P.ring.degree
        (chernCharacterComponent T.structureData (R.reconstruction F) 2) at h
  rw [perfect_rank_eq T R F Q, perfect_toddTwo_degree T,
    perfect_toddOne_degree T R F Q, perfect_chTwo_degree T R F Q] at h
  exact h

/-- The termwise comparison specializes the assembled Layer A theorem to the classical
rank/`c₁`/`c₂` formula for every explicitly perfect coherent sheaf. -/
theorem perfect_chi_eq_classical
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (F : Coh X)
    (Q : PerfectReconstructionComparison T R F) :
    (D.eulerCharacteristic F : ℚ) =
      (virtualRank Q.resolution : ℚ) * (P.intersection.eulerPic 1 : ℚ) +
        ((P.intersection.surfaceIntersectionPairing
              (picardFirstChernClass Q.resolution)
              (picardFirstChernClass Q.resolution) : ℤ) -
          (P.intersection.surfaceIntersectionPairing
              (picardFirstChernClass Q.resolution)
              K.canonicalClassAdd : ℤ)) / 2 -
        Devissage.perfectC2Degree T Q.resolution := by
  exact Devissage.perfect_eulerCharacteristic_eq T Q.resolution

/-! ## Geometric K3 specialization -/

/-- Trivial canonical class and `χ(O_X)=2` prove the Layer A K3 property for the
scheme-derived numerical surface. -/
theorem toIsK3
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (hK : K.canonicalClass = 1)
    (hchi : P.intersection.eulerPic 1 = 2) :
    K3.IsK3 (toNumericalVariety T R) := by
  let G := toGeometricData T R
  apply GeometricData.toIsK3 (RO := T.structureData) G
  · exact ToddData.toddOne_eq_zero hK
  · exact ToddData.degree_toddTwo_eq_two T hchi

/-- The geometric K3 hypotheses turn the assembled Layer A formula into the K3 Euler formula
for every coherent sheaf. -/
theorem k3_eulerCharacteristic_eq
    (T : ToddData.Data P K)
    (R : ReconstructionSystem (X := X) (P := P))
    (hK : K.canonicalClass = 1)
    (hchi : P.intersection.eulerPic 1 = 2)
    (F : Coh X) :
    (D.eulerCharacteristic F : ℚ) =
      2 * ((R.reconstruction F).rank : ℚ) +
        P.ring.degree
          (chernCharacterComponent T.structureData (R.reconstruction F) 2) := by
  exact GeometricData.k3_eulerCharacteristic_eq (RO := T.structureData)
    (toGeometricData T R) (toGeometricData_satisfiesSheafHRR T R)
      (ToddData.toddOne_eq_zero hK)
      (ToddData.degree_toddTwo_eq_two T hchi) F

end

end AlgebraicGeometry.RiemannRoch.Surface.Assembly
