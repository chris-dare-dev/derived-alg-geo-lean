/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.EulerPairing

/-!
# The numerical Grothendieck lattice

The numerical Grothendieck group is the quotient by the radical of the Euler pairing.  This
file makes that construction explicit from `NumericalVarietyData.chi₂` and records the precise
finiteness input needed before the quotient is a lattice.

The Euler pairing supplied by `NumericalVarietyData` is `ℚ`-valued.  Consequently the descended
pairing below is also `ℚ`-valued; no integrality statement is silently assumed.  The integral
object is its underlying finite free `ℤ`-module.

## Main results

* `NumericalVarietyData.leftRadical` and `NumericalVarietyData.rightRadical` are the two
  Euler radicals.
* `NumericalVarietyData.leftRadical_eq_rightRadical` identifies them when the Euler form
  is symmetric.
* `NumericalVarietyData.NumericalQuotient` is the quotient by the radical.
* `NumericalVarietyData.numericalPairing` is the descended, nondegenerate pairing.
* `NumericalQuotient` is finitely generated over `ℤ` whenever `N` is
  (`instFiniteNumericalQuotient`, from `Module.Finite.quotient`), and free
  whenever it is also torsion-free, by Mathlib's instance
  `Module.free_of_finite_type_torsion_free'`. The lattice structure is
  therefore Mathlib's `[Module.Finite ℤ _] [Module.Free ℤ _]`; the repository
  no longer carries a class for it.
* `K3.numericalPairing_mk_eq_neg_mukaiPairing` fixes the K3 sign convention.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace NumericalVarietyData

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData n A N)

/-- The Euler pairing with its second argument packaged as an additive homomorphism. -/
noncomputable def eulerPairingRow (E : N) : N →+ ℚ :=
  AddMonoidHom.mk' (V.chi₂ E) (V.chi₂_add_right E)

/-- The Euler pairing as a biadditive homomorphism `N →+ (N →+ ℚ)`. -/
noncomputable def eulerPairing : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (V.eulerPairingRow) fun E F => by
    ext G
    exact V.chi₂_add_left E F G

/-- The transposed Euler pairing as a biadditive homomorphism. -/
noncomputable def eulerPairingFlip : N →+ (N →+ ℚ) :=
  AddMonoidHom.mk' (fun F => AddMonoidHom.mk' (fun E => V.chi₂ E F)
    (fun E G => V.chi₂_add_left E G F)) fun E F => by
      ext G
      exact V.chi₂_add_right G E F

/-- Unbundling `eulerPairing` recovers the original numerical Euler form `chi₂`. -/
@[simp]
theorem eulerPairing_apply (E F : N) : V.eulerPairing E F = V.chi₂ E F :=
  rfl

@[simp]
theorem eulerPairingFlip_apply (E F : N) :
    V.eulerPairingFlip E F = V.chi₂ F E :=
  rfl

/-- The left radical: classes pairing to zero against every class on the right. -/
noncomputable def leftRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (V.eulerPairing).ker

/-- The right radical: classes pairing to zero against every class on the left. -/
noncomputable def rightRadical : Submodule ℤ N :=
  AddSubgroup.toIntSubmodule (V.eulerPairingFlip).ker

/-- Membership in the left radical is pointwise vanishing of the Euler pairing in the
second argument. -/
theorem mem_leftRadical_iff (E : N) :
    E ∈ V.leftRadical ↔ ∀ F : N, V.chi₂ E F = 0 := by
  rw [leftRadical]
  change E ∈ (V.eulerPairing).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h F
    simpa using DFunLike.congr_fun h F
  · intro h
    ext F
    simpa using h F

/-- Membership in the right radical is pointwise vanishing of the Euler pairing in the
first argument. -/
theorem mem_rightRadical_iff (F : N) :
    F ∈ V.rightRadical ↔ ∀ E : N, V.chi₂ E F = 0 := by
  rw [rightRadical]
  change F ∈ (V.eulerPairingFlip).ker ↔ _
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h E
    simpa using DFunLike.congr_fun h E
  · intro h
    ext E
    simpa using h E

/-- The symmetry hypothesis under which the project uses a single Euler radical. -/
def IsEulerPairingSymmetric : Prop :=
  ∀ E F : N, V.chi₂ E F = V.chi₂ F E

/-- Symmetry turns vanishing against every right argument into vanishing against every left
argument, so the two kernels used to define the numerical quotient coincide. -/
theorem leftRadical_eq_rightRadical (hSymm : IsEulerPairingSymmetric V) :
    V.leftRadical (N := N) = V.rightRadical (N := N) := by
  ext E
  rw [mem_leftRadical_iff, mem_rightRadical_iff]
  constructor
  · intro h F
    rw [hSymm F E]
    exact h F
  · intro h F
    rw [hSymm E F]
    exact h F

/-- The numerical Grothendieck quotient by the left Euler radical.

Under `IsEulerPairingSymmetric`, `leftRadical_eq_rightRadical` shows that this is equivalently
the quotient by the right radical. -/
abbrev NumericalQuotient := N ⧸ V.leftRadical

/-- Descend the right argument of the Euler pairing to the numerical quotient. -/
noncomputable def eulerPairingDescendRight
    (hSymm : IsEulerPairingSymmetric V) (E : N) :
    NumericalQuotient V →+ ℚ :=
  QuotientAddGroup.lift V.leftRadical.toAddSubgroup
    (V.eulerPairingRow E) <| by
    intro F hF
    rw [AddMonoidHom.mem_ker]
    change V.chi₂ E F = 0
    rw [hSymm E F]
    exact (V.mem_leftRadical_iff F).mp hF E

/-- Evaluating the one-sided descent on a quotient representative recovers `chi₂`. -/
@[simp]
theorem eulerPairingDescendRight_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.eulerPairingDescendRight hSymm E (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The Euler pairing with its right argument descended, still additive in the left argument. -/
noncomputable def eulerPairingToQuotient
    (hSymm : IsEulerPairingSymmetric V) :
    N →+ (NumericalQuotient V →+ ℚ) :=
  AddMonoidHom.mk' (V.eulerPairingDescendRight hSymm) fun E F => by
    ext q
    refine Submodule.Quotient.induction_on _ q ?_
    intro G
    exact V.chi₂_add_left E F G

/-- The left-additive one-sided descent still evaluates to `chi₂` on representatives. -/
@[simp]
theorem eulerPairingToQuotient_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.eulerPairingToQuotient hSymm E (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The Euler pairing descended to the numerical quotient in both arguments. -/
noncomputable def numericalPairing
    (hSymm : IsEulerPairingSymmetric V) :
    NumericalQuotient V →+ (NumericalQuotient V →+ ℚ) :=
  QuotientAddGroup.lift V.leftRadical.toAddSubgroup
    (V.eulerPairingToQuotient hSymm) <| by
      intro E hE
      rw [AddMonoidHom.mem_ker]
      ext q
      refine Submodule.Quotient.induction_on _ q ?_
      intro F
      exact (V.mem_leftRadical_iff E).mp hE F

/-- The fully descended numerical pairing is computed by `chi₂` on representatives. -/
@[simp]
theorem numericalPairing_mk
    (hSymm : IsEulerPairingSymmetric V) (E F : N) :
    V.numericalPairing hSymm (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      V.chi₂ E F :=
  rfl

/-- The descended pairing remains symmetric. -/
theorem numericalPairing_symm
    (hSymm : IsEulerPairingSymmetric V)
    (x y : NumericalQuotient V) :
    V.numericalPairing hSymm x y = V.numericalPairing hSymm y x := by
  refine Submodule.Quotient.induction_on _ x fun E => ?_
  refine Submodule.Quotient.induction_on _ y fun F => ?_
  exact hSymm E F

/-- The descended pairing has zero left radical, by construction. -/
theorem numericalPairing_left_nondegenerate
    (hSymm : IsEulerPairingSymmetric V)
    (x : NumericalQuotient V)
    (hx : ∀ y : NumericalQuotient V, V.numericalPairing hSymm x y = 0) :
    x = 0 := by
  revert hx
  refine Submodule.Quotient.induction_on _ x fun E hx => ?_
  rw [Submodule.Quotient.mk_eq_zero, mem_leftRadical_iff]
  intro F
  simpa using hx (Submodule.Quotient.mk F)

/-- The descended pairing has zero right radical as well. -/
theorem numericalPairing_right_nondegenerate
    (hSymm : IsEulerPairingSymmetric V)
    (y : NumericalQuotient V)
    (hy : ∀ x : NumericalQuotient V, V.numericalPairing hSymm x y = 0) :
    y = 0 := by
  apply V.numericalPairing_left_nondegenerate hSymm y
  intro x
  rw [V.numericalPairing_symm hSymm]
  exact hy x

/-- The kernel of the descended pairing is zero. -/
theorem numericalPairing_ker_eq_bot
    (hSymm : IsEulerPairingSymmetric V) :
    (V.numericalPairing hSymm).ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [AddSubgroup.mem_bot]
    apply V.numericalPairing_left_nondegenerate hSymm x
    intro y
    have hzero := AddMonoidHom.mem_ker.mp hx
    simpa using DFunLike.congr_fun hzero y
  · exact bot_le

/-- Finite generation passes to the numerical quotient. Stated as an instance
so that consumers do not repeat the explicit `letI` the former
`numericalZLattice` theorem needed to reach `Module.Finite.quotient`.

Torsion-freeness does not pass to an arbitrary quotient, so a consumer that
needs the quotient to be free supplies `[Module.IsTorsionFree ℤ (NumericalQuotient V)]`
and obtains `Module.Free ℤ (NumericalQuotient V)` from Mathlib's instance
`Module.free_of_finite_type_torsion_free'`; a finite free `ℤ`-module is the
lattice, and no repository class stands in for that pair of hypotheses. -/
instance instFiniteNumericalQuotient [Module.Finite ℤ N] :
    Module.Finite ℤ (NumericalQuotient V) :=
  Module.Finite.quotient ℤ V.leftRadical

end NumericalVarietyData

namespace K3

open NumericalVarietyData

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- A K3 Euler pairing satisfies the symmetry hypothesis used by the numerical quotient. -/
theorem isEulerPairingSymmetric (hK3 : IsK3 V) : IsEulerPairingSymmetric V :=
  fun E F => chi₂_comm V hK3 E F

/-- On a K3, the two Euler radicals agree. -/
theorem leftRadical_eq_rightRadical (hK3 : IsK3 V) :
    V.leftRadical = V.rightRadical :=
  NumericalVarietyData.leftRadical_eq_rightRadical V (isEulerPairingSymmetric V hK3)

/-- On representatives, the numerical quotient pairing is minus the Mukai pairing.

Thus quotienting and descending preserve exactly the sign convention fixed by
`chi₂_eq_neg_mukaiPairing`. -/
theorem numericalPairing_mk_eq_neg_mukaiPairing (hK3 : IsK3 V) (E F : N) :
    V.numericalPairing (isEulerPairingSymmetric V hK3)
        (Submodule.Quotient.mk E) (Submodule.Quotient.mk F) =
      -mukaiPairing V E F := by
  rw [NumericalVarietyData.numericalPairing_mk, chi₂_eq_neg_mukaiPairing V hK3]

end K3

end AlgebraicGeometry.Numerical
