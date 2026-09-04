/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

/-!
# The Mukai data of the rank-one K3 model

`GrothendieckGroup/MukaiVector.lean` says in its own "What this file does not
assert" section that nothing constructs an `IntegralMukaiData` and nothing
constructs an `AdditiveMukaiData`. This file meets that hypothesis, on the
degree-`2d` rank-one model `k3NumericalVariety d`, with

```
Λ = ℤ        c₁(E) = E 1        b x y = 2d·x·y
```

## What an inhabitant buys, without a line changing anywhere else

Every consumer of `IntegralMukaiData` on `main` takes one as a hypothesis, so
each is a statement about a structure nothing was known to satisfy. Supplying
one de-vacuates all of them at once: `GrothendieckGroup/CentralCharge.lean`,
`CategoricalCharge.lean`, `RadicalKernel.lean`, `Realization.lean` (the
`preservesEuler` family and the two isometry constructions), `EulerTransfer.lean`
and `Walls/Spherical/Basic.lean`.

## The three coordinates

`mukaiVector` is `(rank, c₁, mukaiSInt)` and `mukaiSInt = χ − rank`. On this
model `χ(E) = 2·E 0 + 2d·E 2` and `rank E = E 0`, so

```
v(E) = (E 0, E 1, E 0 + 2d·E 2)
```

which `mukaiVector_k3` records. Two classes are worth naming: the structure
sheaf `![1,0,0]` has `v = (1,0,1)` and is **spherical**, and the point class
`![0,0,1]` has `v = (0,0,2d)` and is **isotropic**. Those are the two
distinguished classes of `Mukai/Basic.lean`, inhabited here for the first time.

## `d ≠ 0` is needed less often than expected

The Mukai-vector computations below are evaluations on the model, not
consequences of Riemann–Roch, so they hold for every `d` — including `d = 0`,
where the "K3" is degenerate. Only `mukaiPairing_k3`, which crosses to
`mukaiPairing` through `pairing_mukaiVector`, needs `SatisfiesHRR` and `IsK3`
and hence `d ≠ 0`. Carrying `hd` on the others would be a hypothesis nothing
uses.

## Main results

* `k3MukaiForm`, `k3IntegralMukaiData`, `k3AdditiveMukaiData` — the witnesses.
* `mukaiVector_k3` and `pairing_mukaiVector_k3` — the coordinates and the
  pairing, evaluated.
* `mukaiPairing_k3` — the bridge to `mukaiPairing`, where `d ≠ 0` is spent.
* `isSpherical_structureSheaf_k3`, `isIsotropic_point_k3`.
-/

namespace AlgebraicGeometry.Numerical.Examples

open AlgebraicGeometry.Numerical

/-! ### The form and the data -/

/-- The Mukai form of the degree-`2d` model on `Λ = ℤ`: `⟪x, y⟫ = 2d·x·y`.

This is the intersection form of the rank-one Néron–Severi lattice `ℤ·H` with
`∫H² = 2d`, which is what `b_spec` has to reproduce. -/
def k3MukaiForm (d : ℕ) : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => 2 * (d : ℤ) * x * y)
    (fun _ _ _ => by ring) (fun _ _ _ => by ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by ring)

@[simp]
theorem k3MukaiForm_apply (d : ℕ) (x y : ℤ) :
    k3MukaiForm d x y = 2 * (d : ℤ) * x * y := rfl

/-- **The first `IntegralMukaiData` in the repository.**

`b_spec` is the whole content: the integral form must compute the intersection
number of first Chern classes. On this model `ch₁(E) = (E 1)·H`, so the product
is `(E 1)(F 1)·H²` and its degree is `2d·(E 1)(F 1)`. -/
noncomputable def k3IntegralMukaiData (d : ℕ) :
    K3.IntegralMukaiData (k3NumericalVariety d) ℤ where
  c₁ E := E 1
  b := k3MukaiForm d
  b_spec E F := by
    show ((2 * (d : ℤ) * (E 1) * (F 1) : ℤ) : ℚ)
      = surfaceDegree (2 * (d : ℚ))
        (algebraMap ℚ SurfaceRing (k3ChCoeff E 1) * H
          * (algebraMap ℚ SurfaceRing (k3ChCoeff F 1) * H))
    rw [mul_mul_mul_comm, ← map_mul, ← pow_two,
      surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
    simp only [k3ChCoeff]
    push_cast
    ring

/-- The same data with additivity of `c₁`, which on `SurfaceNum = Fin 3 → ℤ` is
pointwise addition and therefore `rfl`. -/
noncomputable def k3AdditiveMukaiData (d : ℕ) :
    K3.AdditiveMukaiData (k3NumericalVariety d) ℤ where
  __ := k3IntegralMukaiData d
  c₁_add _ _ := rfl

/-! ### The coordinates, evaluated -/

/-- The Mukai vector on the model: `v(E) = (E 0, E 1, E 0 + 2d·E 2)`.

The third coordinate is `χ − rank`, and `χ(E) = 2·E 0 + 2d·E 2` on this
presentation. -/
@[simp]
theorem mukaiVector_k3 (d : ℕ) (E : SurfaceNum) :
    (k3IntegralMukaiData d).mukaiVector E = (E 0, E 1, E 0 + 2 * (d : ℤ) * E 2) := by
  show (_, _, K3.mukaiSInt (k3NumericalVariety d) E) = _
  have : K3.mukaiSInt (k3NumericalVariety d) E = E 0 + 2 * (d : ℤ) * E 2 := by
    show (2 * E 0 + 2 * (d : ℤ) * E 2) - E 0 = _
    ring
  rw [this]
  rfl

/-- The Mukai pairing on the model, written out:
`⟪v(E), v(F)⟫ = 2d·(E 1)(F 1) − (E 0)·s(F) − (F 0)·s(E)` with
`s(E) = E 0 + 2d·E 2`.

An evaluation, not a consequence of Riemann–Roch — hence no `d ≠ 0`. -/
theorem pairing_mukaiVector_k3 (d : ℕ) (E F : SurfaceNum) :
    Mukai.pairing (k3MukaiForm d)
        ((k3IntegralMukaiData d).mukaiVector E) ((k3IntegralMukaiData d).mukaiVector F)
      = 2 * (d : ℤ) * (E 1) * (F 1)
        - (E 0) * (F 0 + 2 * (d : ℤ) * F 2)
        - (F 0) * (E 0 + 2 * (d : ℤ) * E 2) := by
  rw [mukaiVector_k3, mukaiVector_k3, Mukai.pairing_mk, k3MukaiForm_apply]

/-- **The bridge to `mukaiPairing`.** This is the one statement here that
crosses from the lattice to the numerical pairing, so it is the one that spends
`SatisfiesHRR` and `IsK3` — and hence `d ≠ 0`. -/
theorem mukaiPairing_k3 (d : ℕ) (hd : d ≠ 0) (E F : SurfaceNum) :
    ((2 * (d : ℤ) * (E 1) * (F 1)
        - (E 0) * (F 0 + 2 * (d : ℤ) * F 2)
        - (F 0) * (E 0 + 2 * (d : ℤ) * E 2) : ℤ) : ℚ)
      = K3.mukaiPairing (k3NumericalVariety d) E F := by
  rw [← pairing_mukaiVector_k3 d E F]
  exact (k3IntegralMukaiData d).pairing_mukaiVector
    (k3NumericalVariety_satisfiesHRR d hd) (k3_isK3 d hd) E F

/-! ### The two distinguished classes -/

/-- **The structure-sheaf class is spherical.** `v(![1,0,0]) = (1,0,1)`, so
`⟪v,v⟫ = 0 − 1 − 1 = −2`.

This is the first inhabitant of `Mukai.IsSpherical` coming from a variety
rather than from a hand-built lattice vector. -/
theorem isSpherical_structureSheaf_k3 (d : ℕ) :
    Mukai.IsSpherical (k3MukaiForm d)
      ((k3IntegralMukaiData d).mukaiVector ![1, 0, 0]) := by
  rw [Mukai.IsSpherical, Mukai.selfPairing, pairing_mukaiVector_k3]
  simp

/-- **The point class is isotropic.** `v(![0,0,1]) = (0,0,2d)`, so
`⟪v,v⟫ = 0`. -/
theorem isIsotropic_point_k3 (d : ℕ) :
    Mukai.IsIsotropic (k3MukaiForm d)
      ((k3IntegralMukaiData d).mukaiVector ![0, 0, 1]) := by
  rw [Mukai.IsIsotropic, Mukai.selfPairing, pairing_mukaiVector_k3]
  simp

end AlgebraicGeometry.Numerical.Examples
