/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Scalar extension for divisorial surface charges

The numerical intersection ring is naturally defined over `ℚ`, while the
`B`-field and ample class of a surface stability condition are arbitrary real
divisor classes.  This file makes the passage between those two coefficient
fields explicit.

For a numerical surface ring `S`, its canonical real divisor space is

`RealDivisorClass S = ℝ ⊗[ℚ] S.piece 1`.

The rational intersection product extends to this tensor product by base
change.  Every `Surface.NumericalRealization S D` then extends uniquely to an
`ℝ`-linear map from `RealDivisorClass S` to the concrete divisor space `D`, and
that map preserves the intersection form.  Consequently arbitrary real
`B, omega : RealDivisorClass S` may be used at the ring-presentation level,
not merely rational classes or real multiples of one polarization.

The final compatibility theorem says that the intrinsic central charge is
unchanged when all divisor data are transported to any concrete realization.
No basis, Picard-rank hypothesis, or choice of generators occurs here.
-/

open Complex
open scoped TensorProduct

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

universe u v w

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-- The rational codimension-one part of a numerical surface ring. -/
abbrev RationalDivisorClass (S : NumericalRingData 2 A) := S.piece 1

namespace RationalDivisorClass

variable (S : NumericalRingData 2 A)

/-- The rational intersection pairing on the codimension-one piece of a
numerical surface ring. -/
def intersection : LinearMap.BilinForm ℚ (RationalDivisorClass S) :=
  LinearMap.mk₂ ℚ
    (fun x y => S.degree (x.1 * y.1))
    (by
      intro x y z
      simp only [Submodule.coe_add, add_mul, map_add])
    (by
      intro q x y
      change S.degree ((q • x.1) * y.1) = q • S.degree (x.1 * y.1)
      rw [Algebra.smul_def, mul_assoc, S.degree_algebraMap_mul, smul_eq_mul])
    (by
      intro x y z
      simp only [Submodule.coe_add, mul_add, map_add])
    (by
      intro q x y
      change S.degree (x.1 * (q • y.1)) = q • S.degree (x.1 * y.1)
      rw [Algebra.smul_def]
      rw [show x.1 * (algebraMap ℚ A q * y.1) =
          algebraMap ℚ A q * (x.1 * y.1) by ring]
      rw [S.degree_algebraMap_mul, smul_eq_mul])

/-- The rational divisor intersection pairing is symmetric. -/
theorem intersection_symm : (intersection S).IsSymm := by
  constructor
  intro x y
  simp only [intersection, LinearMap.mk₂_apply]
  rw [mul_comm]

end RationalDivisorClass

/-- The canonical real scalar extension of the rational codimension-one
piece.  This is the presentation-level model of `N¹(X)_ℝ`. -/
abbrev RealDivisorClass (S : NumericalRingData 2 A) :=
  ℝ ⊗[ℚ] (RationalDivisorClass S)

namespace RealDivisorClass

variable (S : NumericalRingData 2 A)

/-- Include a rational divisor class into its real scalar extension. -/
def ofRational (x : S.piece 1) : RealDivisorClass S :=
  (1 : ℝ) ⊗ₜ[ℚ] x

/-- The real intersection form obtained by scalar extension from `ℚ`. -/
def intersection : LinearMap.BilinForm ℝ (RealDivisorClass S) :=
  (RationalDivisorClass.intersection S).baseChange ℝ

/-- The canonical real divisor space attached to a rational numerical surface
ring. -/
def divisorSpace : DivisorSpace (RealDivisorClass S) where
  intersection := intersection S
  intersection_symm := by
    rw [LinearMap.BilinForm.isSymm_iff]
    apply LinearMap.BilinForm.IsSymm.baseChange ℝ
    rw [← LinearMap.BilinForm.isSymm_iff]
    exact RationalDivisorClass.intersection_symm S

@[simp]
theorem pair_tmul (a b : ℝ) (x y : S.piece 1) :
    (divisorSpace S).pair (a ⊗ₜ[ℚ] x) (b ⊗ₜ[ℚ] y) =
      ((S.degree (x.1 * y.1) : ℚ) : ℝ) * (a * b) := by
  simp only [divisorSpace, intersection, DivisorSpace.pair,
    LinearMap.BilinForm.baseChange_tmul,
    RationalDivisorClass.intersection, LinearMap.mk₂_apply]
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [smul_eq_mul]

@[simp]
theorem pair_ofRational (x y : S.piece 1) :
    (divisorSpace S).pair (ofRational S x) (ofRational S y) =
      ((S.degree (x.1 * y.1) : ℚ) : ℝ) := by
  simp [ofRational, pair_tmul]

end RealDivisorClass

namespace NumericalRealization

variable {S : NumericalRingData 2 A}
variable (R : NumericalRealization S (D := D))

/-- Extend a rational divisor realization uniquely to the real scalar
extension. -/
def extendDivisorClass : RealDivisorClass S →ₗ[ℝ] D := by
  letI : Module ℚ D := Module.compHom D (algebraMap ℚ ℝ)
  let rationalMap : S.piece 1 →ₗ[ℚ] D :=
    { R.divisorClass with
      map_smul' := by
        intro q x
        change R.divisorClass (q • x) = q • R.divisorClass x
        rw [R.map_rat_smul]
        exact Rat.cast_smul_eq_qsmul ℝ q (R.divisorClass x) }
  let scalarMap : ℝ →ₗ[ℝ] S.piece 1 →ₗ[ℚ] D :=
    { toFun := fun a => a • rationalMap
      map_add' := by
        intro a b
        ext x
        simp only [add_smul, LinearMap.add_apply, LinearMap.smul_apply]
      map_smul' := by
        intro a b
        ext x
        change (a * b) • rationalMap x = a • (b • rationalMap x)
        exact mul_smul a b (rationalMap x) }
  exact TensorProduct.AlgebraTensorModule.lift scalarMap

@[simp]
theorem extendDivisorClass_tmul (a : ℝ) (x : S.piece 1) :
    R.extendDivisorClass (a ⊗ₜ[ℚ] x) = a • R.divisorClass x := by
  rfl

@[simp]
theorem extendDivisorClass_ofRational (x : S.piece 1) :
    R.extendDivisorClass (RealDivisorClass.ofRational S x) =
      R.divisorClass x := by
  simp [RealDivisorClass.ofRational]

/-- `extendDivisorClass` is the unique real-linear extension of the rational
divisor realization. -/
theorem extendDivisorClass_unique
    (f : RealDivisorClass S →ₗ[ℝ] D)
    (hf : ∀ x : S.piece 1,
      f (RealDivisorClass.ofRational S x) = R.divisorClass x) :
    f = R.extendDivisorClass := by
  letI : Module ℚ D := Module.compHom D (algebraMap ℚ ℝ)
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  calc
    f (a ⊗ₜ[ℚ] x) = f (a • RealDivisorClass.ofRational S x) := by
      apply congrArg f
      simpa only [RealDivisorClass.ofRational] using
        (TensorProduct.tmul_eq_smul_one_tmul a x)
    _ = a • f (RealDivisorClass.ofRational S x) := by rw [map_smul]
    _ = a • R.divisorClass x := by rw [hf]
    _ = R.extendDivisorClass (a ⊗ₜ[ℚ] x) :=
      (R.extendDivisorClass_tmul a x).symm

/-- Scalar extension of a numerical realization preserves the complete real
intersection form, not only its values on rational classes. -/
theorem pair_extendDivisorClass (x y : RealDivisorClass S) :
    R.divisorSpace.pair (R.extendDivisorClass x) (R.extendDivisorClass y) =
      (RealDivisorClass.divisorSpace S).pair x y := by
  let realizedForm : LinearMap.BilinForm ℝ (RealDivisorClass S) :=
    R.divisorSpace.intersection.compl₁₂ R.extendDivisorClass R.extendDivisorClass
  have hform : realizedForm = RealDivisorClass.intersection S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    apply TensorProduct.AlgebraTensorModule.ext
    intro b y
    simp only [realizedForm, LinearMap.compl₁₂_apply,
      extendDivisorClass_tmul, RealDivisorClass.intersection,
      LinearMap.BilinForm.baseChange_tmul]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    change b * (a * R.divisorSpace.pair (R.divisorClass x) (R.divisorClass y)) =
      (RationalDivisorClass.intersection S x y) • (a * b)
    rw [R.intersection_eq]
    simp only [RationalDivisorClass.intersection, LinearMap.mk₂_apply]
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    simp only [smul_eq_mul]
    ring
  change realizedForm x y = RealDivisorClass.intersection S x y
  rw [hform]

/-- Transport arbitrary real `B` and `omega` from the scalar-extended ring
presentation to a concrete divisor realization. -/
def realizeParameters (P : StabilityParameters (RealDivisorClass S)) :
    StabilityParameters D where
  B := R.extendDivisorClass P.B
  omega := R.extendDivisorClass P.omega

end NumericalRealization

/-- The rational ring has a canonical numerical realization in its own real
scalar extension. -/
def scalarExtensionRealization (S : NumericalRingData 2 A) :
    NumericalRealization S (D := RealDivisorClass S) where
  divisorSpace := RealDivisorClass.divisorSpace S
  divisorClass :=
    { toFun := RealDivisorClass.ofRational S
      map_zero' := by simp [RealDivisorClass.ofRational]
      map_add' := by
        intro x y
        rw [show RealDivisorClass.ofRational S (x + y) =
            (1 : ℝ) ⊗ₜ[ℚ] (x + y) from rfl]
        rw [TensorProduct.tmul_add]
        rfl }
  map_rat_smul := by
    intro q x
    change (1 : ℝ) ⊗ₜ[ℚ] (q • x) = (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] x)
    rw [TensorProduct.tmul_smul]
    exact (Rat.cast_smul_eq_qsmul ℝ q ((1 : ℝ) ⊗ₜ[ℚ] x)).symm
  intersection_eq := RealDivisorClass.pair_ofRational S

namespace ScalarExtension

variable {V : NumericalVarietyData 2 A N}

/-- The full Chern character valued in the canonical real scalar extension of
the rational codimension-one piece. -/
def chernCharacter : ChernCharacter N (RealDivisorClass V.ring) :=
  (scalarExtensionRealization V.ring).chernCharacter

@[simp]
theorem chernCharacter_rank (E : N) :
    (chernCharacter (V := V)).rank E = (V.rank E : ℝ) := rfl

@[simp]
theorem chernCharacter_chOne (E : N) :
    (chernCharacter (V := V)).chOne E =
      RealDivisorClass.ofRational V.ring
        ⟨V.chComp E 1, V.chComp_mem E 1⟩ := rfl

@[simp]
theorem chernCharacter_chTwo (E : N) :
    (chernCharacter (V := V)).chTwo E =
      ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := rfl

variable (R : NumericalRealization V.ring (D := D))

/-- The concrete first Chern class is the image of the canonical
scalar-extended first Chern class. -/
theorem map_chernCharacter_chOne (E : N) :
    R.extendDivisorClass ((chernCharacter (V := V)).chOne E) =
      R.chernCharacter.chOne E := by
  simp only [chernCharacter_chOne, NumericalRealization.chernCharacter_chOne,
    NumericalRealization.extendDivisorClass_ofRational]

/-- Arbitrary real scalar-extended `B`-fields and polarizations give the same
central charge after transport to any concrete numerical divisor
realization. -/
theorem centralCharge_eq_realization
    (P : StabilityParameters (RealDivisorClass V.ring)) (E : N) :
    (chernCharacter (V := V)).centralCharge
        (RealDivisorClass.divisorSpace V.ring) P E =
      R.chernCharacter.centralCharge R.divisorSpace
        (R.realizeParameters P) E := by
  rw [ChernCharacter.centralCharge_apply, ChernCharacter.centralCharge_apply]
  simp only [chernCharacter_rank, chernCharacter_chTwo,
    NumericalRealization.chernCharacter_rank,
    NumericalRealization.chernCharacter_chTwo,
    NumericalRealization.realizeParameters]
  rw [← map_chernCharacter_chOne R E]
  rw [R.pair_extendDivisorClass P.B
      ((chernCharacter (V := V)).chOne E)]
  rw [R.pair_extendDivisorClass P.B P.B]
  rw [R.pair_extendDivisorClass P.omega P.omega]
  rw [R.pair_extendDivisorClass P.omega
      ((chernCharacter (V := V)).chOne E)]
  rw [R.pair_extendDivisorClass P.omega P.B]

end ScalarExtension

end

end AlgebraicGeometry.Numerical.Surface
