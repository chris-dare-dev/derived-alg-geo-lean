/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.JordanHolder
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.Semistable
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.ChargeRayCone

/-!
# The support property is detected on stable objects

Let `Q` be a quadratic form on the class space whose restriction to the kernel of the
charge is negative semidefinite. If every stable object has `0 ≤ Q`, then so does
every semistable object. This is Lemma A.6 of Bayer–Macrì–Stellari,
arXiv:1410.1585, and Lemma 6.1 of Bayer, arXiv:1606.02169. It is the step of the
proof of Theorem 12.11 of arXiv:1902.08184v4 showing that the inequality `0 ≤ Q`
survives wall-crossing.

A semistable object of phase `φ` is an iterated extension of stable objects of phase
`φ` (`Slicing.HasJordanHolderFiltrations`). All their charges lie on the ray
`ℝ_{>0} e^{iπφ}`, and the classes on that ray with `0 ≤ Q` form a convex cone
(`QuadraticMap.chargeRayCone`, BMS16 Lemma A.7).

## Main results

* `PreStabilityCondition.WithClassMap.class_mem_chargeRayCone_of_extensionClosure`:
  an iterated extension of objects of phase `φ` with `0 ≤ Q` has class in the cone
  over the ray of phase `φ`.
* `PreStabilityCondition.WithClassMap.apply_nonneg_of_mem_semistableClasses`: under
  Jordan--Hölder filtrations, `0 ≤ Q` on stable objects gives `0 ≤ Q` on every
  semistable class.
* `StabilityCondition.WithClassMap.isCompatible_of_isStableAt`: a stability
  condition has the support property with respect to `Q` as soon as `ker Z` is
  `Q`-negative definite and `0 ≤ Q` on its stable objects.

## References

* Bayer, Macrì, Stellari, arXiv:1410.1585, Lemmas A.6 and A.7.
* Bayer, *A short proof of the deformation property of Bridgeland stability
  conditions*, arXiv:1606.02169, Lemma 6.1.
* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, arXiv:1902.08184v4, Theorem 12.11.

## Tags

stability condition, support property, Jordan--Hölder filtration, quadratic form
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

namespace CategoryTheory.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {v : K₀ C →+ V}

namespace PreStabilityCondition.WithClassMap

/-- **Classes of same-phase extensions lie in one cone.** If every object of `S` lies
in the slice of phase `φ` and has `0 ≤ Q`, and `ker Zlin` is `Q`-negative
semidefinite, then every iterated extension of objects of `S` has class in the cone
over the ray `ℝ_{>0} e^{iπφ}`. -/
theorem class_mem_chargeRayCone_of_extensionClosure (σ : WithClassMap C v)
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) {Q : QuadraticForm ℝ V}
    (hker : ∀ k, Zlin k = 0 → Q k ≤ 0) {φ : ℝ} {S : ObjectProperty C}
    (hS : ∀ X, S X → σ.slicing.P φ X ∧ 0 ≤ Q (v (K₀.of C X))) {E : C}
    (hE : ExtensionClosure S E) :
    v (K₀.of C E) ∈
      QuadraticMap.chargeRayCone Q Zlin (Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) := by
  induction hE with
  | zero hzero =>
    rw [K₀.of_isZero C hzero, map_zero]
    exact QuadraticMap.zero_mem_chargeRayCone
  | @mem X hX =>
    by_cases hX0 : IsZero X
    · rw [K₀.of_isZero C hX0, map_zero]
      exact QuadraticMap.zero_mem_chargeRayCone
    obtain ⟨hP, hQ⟩ := hS X hX
    obtain ⟨m, hm, hmZ⟩ := σ.compatible φ X hP hX0
    exact QuadraticMap.mem_chargeRayCone_of_charge_eq hQ hm (by rw [hZ]; exact hmZ)
  | @ext X E Y f g h hT _ _ ihX ihY =>
    have hK := K₀.of_triangle C (Triangle.mk f g h) hT
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at hK
    rw [hK, map_add]
    exact QuadraticMap.add_mem_chargeRayCone hker ihX ihY

/-- **The support inequality is detected on stable objects** (BMS16, Lemma A.6;
Bayer, Lemma 6.1).

If semistable objects have Jordan--Hölder filtrations, `ker Zlin` is `Q`-negative
semidefinite, and every stable object has `0 ≤ Q`, then every class of a nonzero
semistable object has `0 ≤ Q`. -/
theorem apply_nonneg_of_mem_semistableClasses (σ : WithClassMap C v)
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) {Q : QuadraticForm ℝ V}
    (hker : ∀ k, Zlin k = 0 → Q k ≤ 0) (hJH : σ.slicing.HasJordanHolderFiltrations)
    (hstable : ∀ φ E, σ.slicing.IsStableAt φ E → 0 ≤ Q (v (K₀.of C E)))
    {x : V} (hx : x ∈ σ.semistableClasses) : 0 ≤ Q x := by
  obtain ⟨φ, E, hP, -, rfl⟩ := hx
  exact QuadraticMap.apply_nonneg_of_mem_chargeRayCone
    (σ.class_mem_chargeRayCone_of_extensionClosure hZ hker
      (fun X hX => ⟨hX.1, hstable φ X hX⟩) (hJH φ E hP))

end PreStabilityCondition.WithClassMap

namespace StabilityCondition.WithClassMap

variable [IsTriangulated C]

/-- **Support with respect to `Q` from the stable objects.** A stability condition
whose charge has `Q`-negative definite kernel, and whose stable objects all have
`0 ≤ Q`, has the support property with respect to `Q`. Local finiteness supplies the
Jordan--Hölder filtrations. -/
theorem isCompatible_of_isStableAt (σ : StabilityCondition.WithClassMap C v)
    {Zlin : V →ₗ[ℝ] ℂ} (hZ : ∀ x, Zlin x = σ.Z x) {Q : QuadraticForm ℝ V}
    (hneg : ∀ k, Zlin k = 0 → k ≠ 0 → Q k < 0)
    (hstable : ∀ φ E, σ.slicing.IsStableAt φ E → 0 ≤ Q (v (K₀.of C E))) :
    IsCompatible Zlin σ.semistableClasses Q where
  nonneg_of_mem _ hx := σ.apply_nonneg_of_mem_semistableClasses hZ
    (fun k hk => by
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · exact (hneg k hk hk0).le)
    (Slicing.IsLocallyFinite.hasJordanHolderFiltrations C σ.locallyFinite) hstable hx
  neg_of_ker := hneg

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
