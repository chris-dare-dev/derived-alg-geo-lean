/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Slope
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.ChargePositivity
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian

/-!
# The exponential charge `Z(β,ω)` carried by a Mukai class map

Bridgeland's Lemma 6.2 (`math/0307164`, §6) says that `Z(β,ω)` is a stability
function on the tilted heart `𝒜(β,ω)`.  `ChargePositivity.lean` (#742) proved
the numerical core of the one hard case, with no category in sight.  This file
is the bridge: it carries a Mukai class map from an abelian category into the
real Mukai extension, so that `Z(β,ω)` becomes a charge on objects.

## What this file is, and what it is deliberately not

It is the mechanical half of #740 step 2 — `map_zero`, `map_iso` and
`additive`, all of which follow from additivity of the charge in the class
together with the corresponding property of the class map.

It is **not** the case analysis.  `MukaiChargeData` carries *only* the class map
and its three formal properties; it has no field asserting anything about
torsion, rank, slope, or the Mukai square.  That is deliberate.  Bundling the
case discriminants as hypotheses would make `nonzero_mem` a one-line case split
over invented assumptions — it would compile, pass every gate, and prove
nothing.  The four cases of Lemma 6.2 have to be *proved* from the tilted
heart's own description (`hnTilt_heart_iff`, `mem_hnTors_of_rank_zero`,
`degree_pos_of_rank_zero`), and that work is not in this file.

So there is no `toStabilityFunction` here.  `SlopeData.toStabilityFunction`
exists because `SlopeData`'s geometric fields genuinely discharge
`nonzero_mem`; the analogous step for `Z(β,ω)` is the open part of #740.

## The sign convention, which no gate catches

Bridgeland's §6 states every sign for the **sheaf**, not for the object of the
heart.  In the boundary case `E` is torsion-free with `μ_ω(E) = β·ω`, so
`E ∈ F(β)` and the object of the tilted heart is `E⟦1⟧`, with
`Z(E⟦1⟧) = -Z(E)`.  `ChargePositivity.lean` concludes `Re Z(E) > 0` for the
sheaf; the heart object therefore has `Im = 0` and `Re < 0`, which is the
`{z | z.im = 0 ∧ z.re < 0}` half of `semiClosedUpperHalfPlane`.  The two
apparent sign reversals cancel, and getting this backwards yields a false
statement that compiles.

## Additivity of the charge

`expCharge_add` and `expCharge_zero` are stated here rather than in
`LinearAlgebra/Lattice/Mukai/CentralCharge.lean`, where they arguably belong:
they are consequences of `polar` being additive in its second argument, and are
the only two facts about `expCharge` this bridge needs.  Moving them upstream is
a reasonable follow-up.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex QuadraticMap

universe u v

namespace CategoryTheory.Triangulated

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-- The exponential charge kills the zero class. -/
@[simp]
theorem expCharge_zero : Mukai.expCharge b β ω 0 = 0 := by
  simp [Mukai.expCharge, PeriodDomain.centralCharge]

/-- The exponential charge is additive in the Mukai class, because `polar` is
additive in its second argument. -/
theorem expCharge_add (v w : Mukai.RealExtension V) :
    Mukai.expCharge b β ω (v + w)
      = Mukai.expCharge b β ω v + Mukai.expCharge b β ω w := by
  simp only [Mukai.expCharge, PeriodDomain.centralCharge, polar_add_right]
  push_cast
  ring

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **A Mukai class map**, as a single hom out of the Grothendieck group.

This was three fields — `mukai_zero`, `mukai_iso`, `mukai_additive` — carried as
data.  They are the universal property of `K₀Ab`, so they are gone: one field
remains, and the three formal properties come from `AddMonoidHom` and
`K₀Ab.of_isZero` / `of_iso` / `of_shortExact`.

**Still not connected to the numerical lane.**  `mukai` here is an arbitrary hom
into the real Mukai extension; nothing forces it to be the Mukai vector of an
object's numerical class.  Making it factor through `N` and the numerical
quotient — and proving `charge` agrees with `numericalCharge` — is the next step,
and until it lands the support-property theorems proved on the numerical side are
unreachable from an object of a heart. -/
structure MukaiChargeData (A : Type u) [Category.{v} A] [Abelian A]
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The Mukai class, as a hom out of the Grothendieck group. -/
  mukai : K₀Ab A →+ Mukai.RealExtension V

namespace MukaiChargeData

variable (D : MukaiChargeData A V)

/-- `Z(β,ω)` as a charge on objects. -/
def charge (E : A) : ℂ := Mukai.expCharge b β ω (D.mukai (K₀Ab.of E))

@[simp]
theorem charge_apply (E : A) :
    D.charge b β ω E = Mukai.expCharge b β ω (D.mukai (K₀Ab.of E)) := rfl

theorem charge_zero {E : A} (hE : IsZero E) : D.charge b β ω E = 0 := by
  rw [charge_apply, K₀Ab.of_isZero hE, map_zero, expCharge_zero]

theorem charge_iso {E F : A} (e : E ≅ F) : D.charge b β ω E = D.charge b β ω F := by
  rw [charge_apply, charge_apply, K₀Ab.of_iso e]

theorem charge_additive (S : ShortComplex A) (hS : S.ShortExact) :
    D.charge b β ω S.X₂ = D.charge b β ω S.X₁ + D.charge b β ω S.X₃ := by
  rw [charge_apply, charge_apply, charge_apply, K₀Ab.of_shortExact S hS, map_add,
    expCharge_add]

end MukaiChargeData

end CategoryTheory.Triangulated
