/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.AssociatedSheaf.Construction

/-!
# From Cartier divisors to the Picard group

This file owns the specialized consequences of the associated-sheaf
construction: the associated sheaf of the zero divisor is the structure sheaf,
a principal divisor gives the structure sheaf, the associated sheaf of a sum is
the tensor product, and the resulting map to the Picard group is an additive
homomorphism that factors through the divisor class group.

## Main definitions

* `Scheme.CartierDivisor.associatedSheafZeroIso` and
  `Scheme.CartierDivisor.associatedSheafPrincipalIso`: `O_X(0)` and `O_X(div f)`
  are the structure sheaf.
* `Scheme.CartierDivisor.associatedTensorInverseIso`: `O_X(-D)` is a tensor
  inverse of `O_X(D)`.
* `Scheme.CartierDivisor.toPic`: the Picard-group element represented by
  `O_X(D)`.
* `Scheme.CartierDivisor.divisorToPicAdd`: `D ↦ O_X(D)` as an additive map to
  the Picard group.
* `Scheme.CartierDivisor.classToPicAdd` and `Scheme.CartierDivisor.classToPic`:
  the induced additive and multiplicative maps from the divisor class group.

## Main results

* `Scheme.CartierDivisor.divisorToPicAdd_principal`: principal divisors map to
  zero in the Picard group.
* `Scheme.CartierDivisor.coe_toPic` and
  `Scheme.CartierDivisor.classToPic_toClass`: the Picard class of `D` is the
  class of `O_X(D)`, and the class-group map agrees with `toPic` on classes.

## Implementation notes

The Picard element `toPic D` records `O_X(-D)` as its inverse through
`Modules.Pic.mkOfTensorInverse`; additivity of `divisorToPicAdd` is the tensor
comparison `associatedTensorAddIso`, and principal divisors vanish by the
canonical global-equation trivialization.

No unconditional pullback theorem is stated.  `CartierPullbackHypotheses`
supplies a function-field pullback for divisors as an explicit input, but a
comparison with pullback of module sheaves would also need compatibility
between that input, rational sections, and module sheafification.  That extra
compatibility is not part of the current Mathlib API.

## References

This file builds on `Scheme.CartierDivisor.associatedSheaf`,
`Scheme.CartierDivisor.associatedTensorAddIso` and
`Scheme.CartierDivisor.globalEquationIso`, and on this library's
`AlgebraicGeometry.Scheme.Modules.Pic`.

## Tags

Cartier divisor, associated sheaf, Picard group, divisor class group, principal divisor
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

namespace CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- The associated sheaf of the zero divisor is the structure sheaf. -/
noncomputable def associatedSheafZeroIso :
    associatedSheaf (0 : CartierDivisor X) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  refine (globalEquationIso (0 : CartierDivisor X) 0 ?_).symm
  intro x hx
  simp

/-- A principal divisor has trivial associated sheaf. -/
noncomputable def associatedSheafPrincipalIso
    (f : Additive X.functionFieldˣ) :
    associatedSheaf (principal X f) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  refine (globalEquationIso (principal X f) f ?_).symm
  intro x hx
  rfl

/-- `O_X(-D)` is an explicit tensor inverse of `O_X(D)`. -/
noncomputable def associatedTensorInverseIso (D : CartierDivisor X) :
    Modules.tensorObj (associatedSheaf D) (associatedSheaf (-D)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  associatedTensorAddIso D (-D) ≪≫
    eqToIso (by simp) ≪≫ associatedSheafZeroIso

/-! ### From Cartier divisors to the Picard group -/

/-- The Picard-group class represented by `O_X(D)`, with `O_X(-D)` as its recorded inverse. -/
noncomputable def toPic (D : CartierDivisor X) : Modules.Pic X :=
  Modules.Pic.mkOfTensorInverse (associatedSheaf D) (associatedSheaf (-D))
    (associatedTensorInverseIso D)

@[simp]
theorem coe_toPic (D : CartierDivisor X) :
    (toPic D : Modules.PicardClass X) =
      Modules.PicardClass.mk (associatedSheaf D) :=
  rfl

/-- Before quotienting by principal divisors, `D ↦ O_X(D)` is additive after writing the
Picard group additively. -/
noncomputable def divisorToPicAdd :
    CartierDivisor X →+ Additive (Modules.Pic X) where
  toFun D := Additive.ofMul (toPic D)
  map_zero' := by
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (SheafOfModules.unit X.ringCatSheaf) :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    apply Additive.toMul.injective
    apply Units.ext
    change (toPic (0 : CartierDivisor X) : Modules.PicardClass X) =
      ((1 : Modules.Pic X) : Modules.PicardClass X)
    rw [coe_toPic, Modules.Pic.coe_one]
    exact (Modules.PicardClass.mk_eq_mk_iff _ _).2
      ⟨associatedSheafZeroIso⟩
  map_add' D E := by
    apply Additive.toMul.injective
    apply Units.ext
    change (toPic (D + E) : Modules.PicardClass X) =
      (toPic D : Modules.PicardClass X) *
        (toPic E : Modules.PicardClass X)
    rw [coe_toPic, coe_toPic, coe_toPic,
      Modules.PicardClass.mk_mul_mk]
    exact (Modules.PicardClass.mk_eq_mk_iff _ _).2
      ⟨(associatedTensorAddIso D E).symm⟩

@[simp]
theorem divisorToPicAdd_apply (D : CartierDivisor X) :
    divisorToPicAdd D = Additive.ofMul (toPic D) :=
  rfl

@[simp]
theorem divisorToPicAdd_principal (f : Additive X.functionFieldˣ) :
    divisorToPicAdd (principal X f) = 0 := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  apply Additive.toMul.injective
  apply Units.ext
  change (toPic (principal X f) : Modules.PicardClass X) =
    ((1 : Modules.Pic X) : Modules.PicardClass X)
  rw [coe_toPic, Modules.Pic.coe_one]
  exact (Modules.PicardClass.mk_eq_mk_iff _ _).2
    ⟨associatedSheafPrincipalIso f⟩

/-- Cartier divisor classes map additively to the Picard group. Principal divisors vanish by
the canonical global-equation trivialization. -/
noncomputable def classToPicAdd :
    ClassGroup X →+ Additive (Modules.Pic X) :=
  QuotientAddGroup.lift (principalDivisors X) (divisorToPicAdd (X := X))
    (fun D hD ↦ by
      obtain ⟨f, rfl⟩ := hD
      exact divisorToPicAdd_principal f)

/-- Multiplicative form of the Cartier-class-to-Picard homomorphism. -/
noncomputable def classToPic :
    Multiplicative (ClassGroup X) →* Modules.Pic X :=
  (classToPicAdd (X := X)).toMultiplicativeLeft

@[simp]
theorem classToPic_toClass (D : CartierDivisor X) :
    classToPic (Multiplicative.ofAdd (toClass X D)) = toPic D :=
  rfl

end CartierDivisor

end AlgebraicGeometry.Scheme
