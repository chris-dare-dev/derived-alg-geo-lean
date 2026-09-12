/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Exp.Kernel
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.ChargeFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Basic

/-!
# The surface and threefold charges are one kernel

`Walls/Exp/Kernel.lean` states the exponential charge once, indexed by
truncation degree. This file proves that the two charges already in the tree
are that kernel at `m = 2` and `m = 3`, so neither is a root any more.

The separation is the point. The kernel imports `Walls/ChargeFamily.lean` and
Mathlib and nothing else, so it imports no leaf; this file may import both
leaves because it is the comparison and not the root. Putting the comparisons
in the kernel would have made the root depend on the things it parents.

## What is proved

* `stCharge_eq_exp` — the surface charge (`Walls/Numerical/ChargeFamily.lean`)
  is the kernel at `m = 2`, `w = s + tI`.
* `threefold_charge_eq_exp` — the Bayer--Macrì--Toda charge
  (`Walls/Threefold/Basic.lean`) is the same kernel at `m = 3`, `w = β + αI`.
* the two family-level statements, which is the form a consumer needs: each
  existing `ChargeFamily` is a `reindex` of `Exp.chargeFamily` along its chart,
  pulled back along the coordinate identification.

## The coordinate identifications are equivalences, not projections

`surfaceVec` and `threefoldVec` are `≃+`, not one-way maps. The compressed
degree vectors and the tuple carriers hold the same data in the same order, so
nothing is lost passing between them, and stating them as equivalences is what
lets a later slice push wall theory in either direction. This is in contrast to
the divisorial lane, where the `H`-compression genuinely loses information once
the Picard rank exceeds one.

## What this does not claim

That the two families have the same walls, or that either is a stability
condition. A charge is one datum of a stability condition; the heart, the
slicing and the support property are elsewhere and are untouched.
-/

open Complex

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

/-- The surface lane's tuple carrier and the kernel's compressed degrees hold
the same three reals, in the same order. -/
def surfaceVec : NumClass ≃+ Exp.HDeg 2 where
  toFun v := ![v.1, v.2.1, v.2.2]
  invFun d := (d 0, d 1, d 2)
  left_inv := by intro v; simp
  right_inv := by intro d; funext k; fin_cases k <;> simp
  map_add' := by intro v w; funext k; fin_cases k <;> simp [Prod.fst_add, Prod.snd_add]

/-- The threefold lane's tuple carrier and the kernel's compressed degrees hold
the same four reals, in the same order. Slot `0` is `∫H³·ch₀` on both sides. -/
def threefoldVec : Threefold.NumClass ≃+ Exp.HDeg 3 where
  toFun v := ![v.1, v.2.1, v.2.2.1, v.2.2.2]
  invFun d := (d 0, d 1, d 2, d 3)
  left_inv := by intro v; simp
  right_inv := by intro d; funext k; fin_cases k <;> simp
  map_add' := by intro v w; funext k; fin_cases k <;> simp [Prod.fst_add, Prod.snd_add]

/-- The surface charge is the kernel at `m = 2`, `w = s + tI`. -/
theorem stCharge_eq_exp (s t : ℝ) (v : NumClass) :
    stCharge s t v = Exp.charge 2 (Exp.stChart (s, t)) ![v.rk, v.deg, v.ch2] := by
  simp only [Exp.charge, AddMonoidHom.mk'_apply, Exp.ofMoments, Exp.moments, Exp.coeff,
    Exp.stChart, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  apply Complex.ext <;>
    simp [stCharge, reZ, imZ, pow_two, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The Bayer--Macrì--Toda threefold charge is the same kernel at `m = 3`,
`w = β + αI`. Note the chart transposition against the surface case. -/
theorem threefold_charge_eq_exp (a b : ℝ) (v : Threefold.NumClass) :
    Threefold.charge a b v
      = Exp.charge 3 (Exp.alphaBetaChart (a, b)) ![v.deg0, v.deg1, v.deg2, v.deg3] := by
  simp only [Exp.charge, AddMonoidHom.mk'_apply, Exp.ofMoments, Exp.moments, Exp.coeff,
    Exp.alphaBetaChart, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  apply Complex.ext <;>
    simp [Threefold.charge, Threefold.reZ, Threefold.imZ, pow_two, pow_three,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring

/-- The surface charge family is the kernel's family, reindexed by its chart and
pulled back along the coordinate identification. -/
theorem stChargeFamily_eq :
    stChargeFamily
      = ((Exp.chargeFamily 2).reindex Exp.stChart).pullback surfaceVec.toAddMonoidHom := by
  apply ChargeFamily.ext
  intro p
  ext v
  exact stCharge_eq_exp p.1 p.2 v

/-- The threefold charge family, likewise. -/
theorem threefold_chargeFamily_eq :
    Threefold.chargeFamily
      = ((Exp.chargeFamily 3).reindex Exp.alphaBetaChart).pullback
          threefoldVec.toAddMonoidHom := by
  apply ChargeFamily.ext
  intro p
  ext v
  exact threefold_charge_eq_exp p.1 p.2 v

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
