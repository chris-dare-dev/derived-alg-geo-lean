/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtToddK3
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.VectorClass
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

/-! # The Mukai class specialized to numerical K3 data -/

open Finset
universe u v

namespace AlgebraicGeometry.Numerical.K3

open NumericalVarietyData

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable {N : Type v} [AddCommGroup N]
variable {V : NumericalVarietyData 2 A N}

theorem mukaiComp_one (hK3 : IsK3 V) (E : N) : V.mukaiComp E 1 = V.chComp E 1 := by
  rw [mukaiComp, Finset.sum_range_succ, Finset.sum_range_one]
  simp [K3.sqrtToddComp_one hK3]

theorem mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.mukaiComp E 2 =
      V.chComp E 2 + algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 2 := by
  simp [mukaiComp, Finset.sum_range_succ, K3.sqrtToddComp_one hK3, V.chComp_zero]
  ring

theorem degree_mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.ring.degree (V.mukaiComp E 2) = mukaiS V E := by
  rw [mukaiComp_two hK3, map_add, NumericalRingData.degree_algebraMap_mul,
    K3.degree_sqrtToddComp_two hK3, mukaiS]
  ring

section Comparison

variable {Λ : Type*} [AddCommGroup Λ] (D : IntegralMukaiData V Λ)

theorem mukaiVector_fst_eq (E : N) : (D.mukaiVector E).1 = V.rank E := rfl

theorem b_mukaiVector_snd_eq_degree (hK3 : IsK3 V) (E F : N) :
    ((D.b (D.mukaiVector E).2.1 (D.c₁ F) : ℤ) : ℚ) =
      V.ring.degree (V.mukaiComp E 1 * V.chComp F 1) := by
  rw [mukaiComp_one hK3]
  exact D.b_spec E F

theorem mukaiVector_thd_eq_degree (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (((D.mukaiVector E).2.2 : ℤ) : ℚ) = V.ring.degree (V.mukaiComp E 2) := by
  rw [degree_mukaiComp_two hK3]
  exact mukaiSInt_spec V hHRR hK3 E

end Comparison

end AlgebraicGeometry.Numerical.K3
