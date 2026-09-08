/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.GradedBasis
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Numerical intersection data for a smooth quadric surface

For a smooth quadric surface `Q = P¹ × P¹`, the rational numerical
intersection ring is

`ℚ[f₁,f₂] / (f₁²,f₂²)`

with `∫ f₁f₂ = 1`.  We realize it as dual numbers in `f₂` over the dual
numbers in `f₁`.  Its product basis has weights `0,1,1,2`; this produces an
honest `NumericalRingData` rather than merely a coordinate formula.

The real divisor realization sends `c f₁ + d f₂` to `(c,d)` and recovers the
intersection form `((c,d),(c',d')) ↦ c d' + d c'` used by the divisorial
surface charge.  This remains an explicit numerical presentation: it does not
identify the carrier with the geometric `K_num(Q)` or construct the geometric
Chern-character map from coherent sheaves.
-/

open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical.Examples.SmoothQuadric

noncomputable section

/-! ### The rational intersection ring -/

/-- The four-dimensional algebra `ℚ[f₁,f₂]/(f₁²,f₂²)`. -/
abbrev Ring : Type := DualNumber (DualNumber ℚ)

/-- The first ruling class. -/
def rulingOneQ : Ring := ((0, 1), (0, 0))

/-- The second ruling class. -/
def rulingTwoQ : Ring := ((0, 0), (1, 0))

/-- The point class `f₁f₂`. -/
def pointQ : Ring := ((0, 0), (0, 1))

@[simp]
theorem rulingOneQ_mul_self : rulingOneQ * rulingOneQ = 0 := by
  ext <;> simp [rulingOneQ]

@[simp]
theorem rulingOneQ_sq : rulingOneQ ^ 2 = 0 := by
  simpa only [pow_two] using rulingOneQ_mul_self

@[simp]
theorem rulingTwoQ_mul_self : rulingTwoQ * rulingTwoQ = 0 := by
  ext <;> simp [rulingTwoQ]

@[simp]
theorem rulingTwoQ_sq : rulingTwoQ ^ 2 = 0 := by
  simpa only [pow_two] using rulingTwoQ_mul_self

@[simp]
theorem rulingOneQ_mul_rulingTwoQ : rulingOneQ * rulingTwoQ = pointQ := by
  ext <;> simp [rulingOneQ, rulingTwoQ, pointQ]

@[simp]
theorem rulingTwoQ_mul_rulingOneQ : rulingTwoQ * rulingOneQ = pointQ := by
  ext <;> simp [rulingOneQ, rulingTwoQ, pointQ]

@[simp]
theorem rulingOneQ_mul_pointQ : rulingOneQ * pointQ = 0 := by
  ext <;> simp [rulingOneQ, pointQ]

@[simp]
theorem rulingTwoQ_mul_pointQ : rulingTwoQ * pointQ = 0 := by
  ext <;> simp [rulingTwoQ, pointQ]

@[simp]
theorem pointQ_mul_rulingOneQ : pointQ * rulingOneQ = 0 := by
  ext <;> simp [rulingOneQ, pointQ]

@[simp]
theorem pointQ_mul_rulingTwoQ : pointQ * rulingTwoQ = 0 := by
  ext <;> simp [rulingTwoQ, pointQ]

@[simp]
theorem pointQ_mul_self : pointQ * pointQ = 0 := by
  ext <;> simp [pointQ]

@[simp]
theorem pointQ_sq : pointQ ^ 2 = 0 := by
  simpa only [pow_two] using pointQ_mul_self

/-- Coordinates in the ordered basis `1,f₁,f₂,f₁f₂`.

This equivalence is explicit because the scalar-module instance on a trivial
square-zero extension is not definitionally the product-module instance. -/
def coordEquiv : Ring ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![x.1.1, x.1.2, x.2.1, x.2.2]
  invFun x := ((x 0, x 1), (x 2, x 3))
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' _ _ := by
    funext i
    fin_cases i <;> rfl
  map_smul' _ _ := by
    funext i
    fin_cases i <;> rfl

/-- The product basis `1,f₁,f₂,f₁f₂`. -/
def basis : Module.Basis (Fin 4) ℚ Ring :=
  Module.Basis.ofEquivFun coordEquiv

/-- Codimension weights on the product basis. -/
def weight : Fin 4 → ℕ := ![0, 1, 1, 2]

@[simp]
theorem basis_zero : basis 0 = 1 := by
  change basis 0 = (((1, 0), (0, 0)) : Ring)
  apply coordEquiv.injective
  funext i
  fin_cases i <;> simp [basis, coordEquiv]

@[simp]
theorem basis_one : basis 1 = rulingOneQ := by
  apply coordEquiv.injective
  funext i
  fin_cases i <;> simp [basis, coordEquiv, rulingOneQ]

@[simp]
theorem basis_two : basis 2 = rulingTwoQ := by
  apply coordEquiv.injective
  funext i
  fin_cases i <;> simp [basis, coordEquiv, rulingTwoQ]

@[simp]
theorem basis_three : basis 3 = pointQ := by
  apply coordEquiv.injective
  funext i
  fin_cases i <;> simp [basis, coordEquiv, pointQ]

@[simp]
theorem weight_zero : weight 0 = 0 := rfl

@[simp]
theorem weight_one : weight 1 = 1 := rfl

@[simp]
theorem weight_two : weight 2 = 1 := rfl

@[simp]
theorem weight_three : weight 3 = 2 := rfl

/-- Every basis weight is at most the surface dimension. -/
theorem weight_le_two (i : Fin 4) : weight i ≤ 2 := by
  fin_cases i <;> decide

/-- The multiplicative grading, checked on the four basis vectors. -/
theorem basis_mul_mem (p q : Fin 4) :
    basis p * basis q ∈ gradedPiece (basis : Fin 4 → Ring) weight
      (weight p + weight q) := by
  fin_cases p <;> fin_cases q
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 0)
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 1)
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 2)
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 3)
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 1)
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 2))
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 3)
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 3))
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 2)
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 3)
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 2))
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 3))
  · simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 3)
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 3))
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 3))
  · simpa using (Submodule.zero_mem
      (gradedPiece (basis : Fin 4 → Ring) weight 4))

/-- Integration extracts the coefficient of `f₁f₂`. -/
def degree : Ring →ₗ[ℚ] ℚ where
  toFun x := x.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem degree_one : degree 1 = 0 := rfl

@[simp]
theorem degree_rulingOneQ : degree rulingOneQ = 0 := rfl

@[simp]
theorem degree_rulingTwoQ : degree rulingTwoQ = 0 := rfl

@[simp]
theorem degree_pointQ : degree pointQ = 1 := rfl

/-- Integration vanishes on every basis vector outside codimension two. -/
theorem degree_basis_of_ne (i : Fin 4) (hi : weight i ≠ 2) :
    degree (basis i) = 0 := by
  fin_cases i
  · simpa using degree_one
  · simpa using degree_rulingOneQ
  · simpa using degree_rulingTwoQ
  · exact (hi rfl).elim

/-- The rational numerical intersection ring of the smooth quadric. -/
@[reducible]
def numericalRing : NumericalRingData 2 Ring :=
  NumericalRingData.ofGradedBasis 2 basis weight weight_le_two
    (by
      simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring))
        (w := weight) 0))
    basis_mul_mem degree degree_basis_of_ne

@[simp]
theorem degree_ruling_product : numericalRing.degree (rulingOneQ * rulingTwoQ) = 1 := by
  rw [rulingOneQ_mul_rulingTwoQ]
  rfl

/-- Integration of a product in the four coordinates
`1,f₁,f₂,f₁f₂`. -/
theorem degree_mul (x y : Ring) :
    degree (x * y) =
      TrivSqZeroExt.fst (TrivSqZeroExt.fst x) *
          TrivSqZeroExt.snd (TrivSqZeroExt.snd y) +
        TrivSqZeroExt.snd (TrivSqZeroExt.fst x) *
          TrivSqZeroExt.fst (TrivSqZeroExt.snd y) +
        TrivSqZeroExt.fst (TrivSqZeroExt.snd x) *
          TrivSqZeroExt.snd (TrivSqZeroExt.fst y) +
        TrivSqZeroExt.snd (TrivSqZeroExt.snd x) *
          TrivSqZeroExt.fst (TrivSqZeroExt.fst y) := by
  change TrivSqZeroExt.snd (TrivSqZeroExt.snd (x * y)) = _
  simp
  abel

/-! ### Numerical Chern and Todd data -/

/-- Numerical classes in coordinates `(rank, f₁ coefficient, f₂ coefficient, ch₂)`.

Unlike the projective-plane lattice, no half-integral reparametrization is
needed: for `O(a,b)`, the top Chern-character coefficient is `ab`. -/
abbrev NumericalClass := ℤ × ℤ × ℤ × ℤ

/-- The Chern-character components in the quadric intersection ring. -/
noncomputable def chComp (E : NumericalClass) : ℕ → Ring
  | 0 => algebraMap ℚ Ring (E.1 : ℚ)
  | 1 => (E.2.1 : ℚ) • rulingOneQ + (E.2.2.1 : ℚ) • rulingTwoQ
  | 2 => (E.2.2.2 : ℚ) • pointQ
  | _ + 3 => 0

/-- The four basis vectors lie in their stated codimensions. -/
theorem rulingOneQ_mem : rulingOneQ ∈ numericalRing.piece 1 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 1)

theorem rulingTwoQ_mem : rulingTwoQ ∈ numericalRing.piece 1 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 2)

theorem pointQ_mem : pointQ ∈ numericalRing.piece 2 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 4 → Ring)) (w := weight) 3)

theorem chComp_mem (E : NumericalClass) (i : ℕ) :
    chComp E i ∈ numericalRing.piece i := by
  match i with
  | 0 => exact numericalRing.algebraMap_mem_piece_zero _
  | 1 =>
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ rulingOneQ_mem)
        (Submodule.smul_mem _ _ rulingTwoQ_mem)
  | 2 => exact Submodule.smul_mem _ _ pointQ_mem
  | _ + 3 => exact Submodule.zero_mem _

theorem chComp_add (E F : NumericalClass) (i : ℕ) :
    chComp (E + F) i = chComp E i + chComp F i := by
  match i with
  | 0 => simp [chComp]
  | 1 =>
      simp only [chComp]
      change (((E.2.1 + F.2.1 : ℤ) : ℚ) • rulingOneQ +
          ((E.2.2.1 + F.2.2.1 : ℤ) : ℚ) • rulingTwoQ) = _
      push_cast
      module
  | 2 =>
      simp only [chComp]
      change (((E.2.2.2 + F.2.2.2 : ℤ) : ℚ) • pointQ) = _
      push_cast
      rw [add_smul]
  | _ + 3 => simp [chComp]

/-- The total Chern character in the explicit four-coordinate carrier. -/
theorem ch_sum (E : NumericalClass) :
    (∑ i ∈ Finset.range (2 + 1), chComp E i) =
      ((((E.1 : ℚ), (E.2.1 : ℚ)),
        ((E.2.2.1 : ℚ), (E.2.2.2 : ℚ))) : Ring) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext <;> simp [chComp, rulingOneQ, rulingTwoQ, pointQ]

/-- The Todd class of `P¹ × P¹` is
`1 + (f₁+f₂) + f₁f₂`. -/
def toddComp : ℕ → Ring
  | 0 => 1
  | 1 => rulingOneQ + rulingTwoQ
  | 2 => pointQ
  | _ + 3 => 0

theorem toddComp_mem (i : ℕ) : toddComp i ∈ numericalRing.piece i := by
  match i with
  | 0 => exact numericalRing.one_mem_piece_zero
  | 1 => exact Submodule.add_mem _ rulingOneQ_mem rulingTwoQ_mem
  | 2 => exact pointQ_mem
  | _ + 3 => exact Submodule.zero_mem _

/-- The total Todd class in the explicit four-coordinate carrier. -/
theorem todd_sum :
    (∑ i ∈ Finset.range (2 + 1), toddComp i) =
      ((((1 : ℚ), 1), ((1 : ℚ), 1)) : Ring) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext <;> norm_num [toddComp, rulingOneQ, rulingTwoQ, pointQ]

/-- Euler characteristic in the chosen integral coordinates. -/
def chi : NumericalClass →+ ℤ :=
  AddMonoidHom.mk'
    (fun E => E.1 + E.2.1 + E.2.2.1 + E.2.2.2)
    (by
      intro E F
      simp
      ring)

/-- The rational numerical presentation of a smooth quadric surface. -/
@[reducible]
noncomputable def numericalVariety : NumericalVarietyData 2 Ring NumericalClass where
  ring := numericalRing
  rank := AddMonoidHom.mk' (fun E => E.1) (by intro E F; rfl)
  chComp := chComp
  chComp_mem := chComp_mem
  chComp_zero := fun _ => rfl
  chComp_add := chComp_add
  toddComp := toddComp
  toddComp_mem := toddComp_mem
  toddComp_zero := rfl
  chi := chi

/-- The selected presentation satisfies Hirzebruch--Riemann--Roch. -/
theorem numericalVariety_satisfiesHRR : numericalVariety.SatisfiesHRR := by
  refine ⟨fun E => ?_⟩
  change ((E.1 + E.2.1 + E.2.2.1 + E.2.2.2 : ℤ) : ℚ) =
    degree
      ((∑ i ∈ Finset.range (2 + 1), chComp E i) *
        (∑ j ∈ Finset.range (2 + 1), toddComp j))
  rw [ch_sum, todd_sum, degree_mul]
  norm_num

/-- The Segre polarization `f₁+f₂` in the rational intersection ring. -/
def segreQ : Ring := rulingOneQ + rulingTwoQ

@[simp]
theorem segreQ_eq : segreQ = (((0, 1), (1, 0)) : Ring) := by
  ext <;> norm_num [segreQ, rulingOneQ, rulingTwoQ]

theorem segreQ_mem : segreQ ∈ numericalRing.piece 1 :=
  Submodule.add_mem _ rulingOneQ_mem rulingTwoQ_mem

@[simp]
theorem degree_segreQ_sq : numericalRing.degree (segreQ ^ 2) = 2 := by
  change degree (segreQ ^ 2) = 2
  rw [pow_two]
  rw [segreQ_eq, degree_mul]
  norm_num

/-- A rational divisor class in ruling coordinates. -/
def polarizationClass (h₁ h₂ : ℚ) : Ring :=
  h₁ • rulingOneQ + h₂ • rulingTwoQ

theorem polarizationClass_mem (h₁ h₂ : ℚ) :
    polarizationClass h₁ h₂ ∈ numericalRing.piece 1 :=
  Submodule.add_mem _
    (Submodule.smul_mem _ _ rulingOneQ_mem)
    (Submodule.smul_mem _ _ rulingTwoQ_mem)

@[simp]
theorem degree_polarizationClass_sq (h₁ h₂ : ℚ) :
    numericalRing.degree (polarizationClass h₁ h₂ ^ 2) =
      2 * h₁ * h₂ := by
  change degree (polarizationClass h₁ h₂ ^ 2) = _
  rw [pow_two, degree_mul]
  simp [polarizationClass, rulingOneQ, rulingTwoQ]
  ring

/-- An ample rational polarization `h₁f₁+h₂f₂` with both ruling
coefficients positive. -/
def polarization (h₁ h₂ : ℚ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    Polarization numericalVariety.ring where
  cls := polarizationClass h₁ h₂
  cls_mem := polarizationClass_mem h₁ h₂
  degree_pow_pos := by
    rw [degree_polarizationClass_sq]
    positivity

/-- The Segre class as a rational polarization. -/
def segrePolarization : Polarization numericalVariety.ring where
  cls := segreQ
  cls_mem := segreQ_mem
  degree_pow_pos := by
    rw [degree_segreQ_sq]
    norm_num

/-- An arbitrary rational `B = b₁f₁+b₂f₂`. -/
def bField (b₁ b₂ : ℚ) : BField numericalVariety.ring where
  cls := b₁ • rulingOneQ + b₂ • rulingTwoQ
  cls_mem := Submodule.add_mem _
    (Submodule.smul_mem _ _ rulingOneQ_mem)
    (Submodule.smul_mem _ _ rulingTwoQ_mem)

/-! ### Real divisor realization -/

/-- Real numerical divisor classes, in the ruling basis. -/
abbrev Divisor := ℝ × ℝ

/-- The first real ruling class. -/
def rulingOne : Divisor := (1, 0)

/-- The second real ruling class. -/
def rulingTwo : Divisor := (0, 1)

/-- The real Segre class `f₁+f₂`. -/
def segre : Divisor := (1, 1)

/-- The intersection form in ruling coordinates. -/
def intersectionForm : LinearMap.BilinForm ℝ Divisor :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.2 + x.2 * y.1)
    (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring)

@[simp]
theorem intersectionForm_apply (x y : Divisor) :
    intersectionForm x y = x.1 * y.2 + x.2 * y.1 := rfl

/-- The rank-two real divisor space of the smooth quadric. -/
def divisorSpace : Surface.DivisorSpace Divisor where
  intersection := intersectionForm
  intersection_symm := ⟨by intro x y; simp [intersectionForm]; ring⟩

@[simp]
theorem rulingOne_sq : divisorSpace.pair rulingOne rulingOne = 0 := by
  norm_num [Surface.DivisorSpace.pair, divisorSpace, intersectionForm, rulingOne]

@[simp]
theorem rulingTwo_sq : divisorSpace.pair rulingTwo rulingTwo = 0 := by
  norm_num [Surface.DivisorSpace.pair, divisorSpace, intersectionForm, rulingTwo]

@[simp]
theorem rulingOne_pair_rulingTwo : divisorSpace.pair rulingOne rulingTwo = 1 := by
  norm_num [Surface.DivisorSpace.pair, divisorSpace, intersectionForm, rulingOne, rulingTwo]

/-- The weight-one basis vectors are precisely the two rational rulings. -/
theorem weightOneBasis :
    basis '' (weight ⁻¹' ({1} : Set ℕ)) =
      ({rulingOneQ, rulingTwoQ} : Set Ring) := by
  have hpre : weight ⁻¹' ({1} : Set ℕ) = ({1, 2} : Set (Fin 4)) := by
    ext i
    fin_cases i <;> simp [weight]
  rw [hpre, Set.image_insert_eq, Set.image_singleton, basis_one, basis_two]

/-- The rational divisor piece is the two-dimensional span of the rulings. -/
theorem pieceOne_eq_span_rulings :
    numericalRing.piece 1 =
      Submodule.span ℚ ({rulingOneQ, rulingTwoQ} : Set Ring) := by
  change gradedPiece (basis : Fin 4 → Ring) weight 1 = _
  rw [gradedPiece, weightOneBasis]

/-- Extend a rational divisor class to real ruling coordinates. -/
noncomputable def divisorClass : numericalRing.piece 1 →+ Divisor :=
  AddMonoidHom.mk'
    (fun x =>
      (((TrivSqZeroExt.snd (TrivSqZeroExt.fst x.1) : ℚ) : ℝ),
        ((TrivSqZeroExt.fst (TrivSqZeroExt.snd x.1) : ℚ) : ℝ)))
    (by
      intro x y
      ext <;> simp)

/-- The divisor realization commutes with extension of scalars
` ℚ → ℝ`. -/
theorem divisorClass_map_rat_smul (q : ℚ) (x : numericalRing.piece 1) :
    divisorClass (q • x) = (q : ℝ) • divisorClass x := by
  ext <;> simp [divisorClass]

/-- Multiplication in the rational ring realizes to the ruling intersection
form. -/
theorem divisorClass_intersection (x y : numericalRing.piece 1) :
    divisorSpace.pair (divisorClass x) (divisorClass y) =
      ((numericalRing.degree (x.1 * y.1) : ℚ) : ℝ) := by
  have hx : x.1 ∈ Submodule.span ℚ
      ({rulingOneQ, rulingTwoQ} : Set Ring) := by
    rw [← pieceOne_eq_span_rulings]
    exact x.2
  have hy : y.1 ∈ Submodule.span ℚ
      ({rulingOneQ, rulingTwoQ} : Set Ring) := by
    rw [← pieceOne_eq_span_rulings]
    exact y.2
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hy
  change
    (((TrivSqZeroExt.snd (TrivSqZeroExt.fst x.1) : ℚ) : ℝ) *
        ((TrivSqZeroExt.fst (TrivSqZeroExt.snd y.1) : ℚ) : ℝ) +
      ((TrivSqZeroExt.fst (TrivSqZeroExt.snd x.1) : ℚ) : ℝ) *
        ((TrivSqZeroExt.snd (TrivSqZeroExt.fst y.1) : ℚ) : ℝ)) = _
  rw [← hab, ← hcd]
  change _ = ((degree
    ((a • rulingOneQ + b • rulingTwoQ) *
      (c • rulingOneQ + d • rulingTwoQ)) : ℚ) : ℝ)
  rw [degree_mul]
  simp [rulingOneQ, rulingTwoQ]

/-- The rational numerical ring realized in `N¹(Q)_ℝ`. -/
noncomputable def numericalRealization :
    Surface.NumericalRealization numericalVariety.ring (D := Divisor) where
  divisorSpace := divisorSpace
  divisorClass := divisorClass
  map_rat_smul := divisorClass_map_rat_smul
  intersection_eq := divisorClass_intersection

/-- The full real Chern character induced from the rational numerical
presentation. -/
noncomputable def chernCharacter :
    Surface.ChernCharacter NumericalClass Divisor :=
  Surface.NumericalRealization.chernCharacter
    (V := numericalVariety) numericalRealization

@[simp]
theorem chernCharacter_rank (E : NumericalClass) :
    chernCharacter.rank E = (E.1 : ℝ) := by
  rfl

@[simp]
theorem chernCharacter_chOne (E : NumericalClass) :
    chernCharacter.chOne E = ((E.2.1 : ℝ), (E.2.2.1 : ℝ)) := by
  change divisorClass ⟨chComp E 1, chComp_mem E 1⟩ = _
  ext <;> simp [divisorClass, chComp, rulingOneQ, rulingTwoQ]

@[simp]
theorem chernCharacter_chTwo (E : NumericalClass) :
    chernCharacter.chTwo E = (E.2.2.2 : ℝ) := by
  change ((degree (chComp E 2) : ℚ) : ℝ) = _
  simp [chComp, degree, pointQ]

@[simp]
theorem numericalRealization_segre :
    numericalRealization.realizePolarization segrePolarization = segre := by
  change divisorClass ⟨segreQ, segreQ_mem⟩ = segre
  ext <;> norm_num [divisorClass, segreQ, rulingOneQ, rulingTwoQ, segre]

@[simp]
theorem numericalRealization_polarization
    (h₁ h₂ : ℚ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    numericalRealization.realizePolarization
        (polarization h₁ h₂ hh₁ hh₂) =
      ((h₁ : ℝ), (h₂ : ℝ)) := by
  change divisorClass
    ⟨polarizationClass h₁ h₂, polarizationClass_mem h₁ h₂⟩ = _
  ext <;> simp [divisorClass, polarizationClass, rulingOneQ, rulingTwoQ]

@[simp]
theorem numericalRealization_bField (b₁ b₂ : ℚ) :
    numericalRealization.realizeBField (bField b₁ b₂) =
      ((b₁ : ℝ), (b₂ : ℝ)) := by
  change divisorClass
    ⟨b₁ • rulingOneQ + b₂ • rulingTwoQ, (bField b₁ b₂).cls_mem⟩ = _
  ext <;> simp [divisorClass, rulingOneQ, rulingTwoQ]

end

end AlgebraicGeometry.Numerical.Examples.SmoothQuadric
