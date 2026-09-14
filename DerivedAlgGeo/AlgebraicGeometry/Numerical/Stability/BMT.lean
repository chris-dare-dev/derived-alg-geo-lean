/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.TwistedChern
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-!
# The tilt slope and the Bayer–Macrì–Toda quantity on a threefold

At `n = 3` the twisted Chern character gives the three twisted degrees
`∫H²·ch₁^β`, `∫H·ch₂^β` and `∫ch₃^β`, and with them the tilt slope `ν_{α,β}`
and the quantity

```
Q_{α,β}(E) = α²·Δ_H(E) + 4(H·ch₂^β(E))² − 6(H²·ch₁^β(E))·(ch₃^β(E))
```

whose nonnegativity on tilt-semistable objects is the Bayer–Macrì–Toda
conjecture.

## This is a conjecture, and it is false in general

**Read this before consuming `BMTData` for anything.**

The inequality is Conjecture 1.3.1 of Bayer–Macrì–Toda, *Bridgeland stability
conditions on threefolds I: Bogomolov–Gieseker type inequalities*, J. Algebraic
Geom. 23 (2014) 117–163. It appears as Conjecture 4.1 of Bayer–Macrì–Stellari,
*The space of stability conditions on abelian threefolds, and on some
Calabi–Yau threefolds*, Invent. Math. 206 (2016) 869–933 — the numbering used
by the papers that assume it per-threefold.

It is known for:

| case | reference |
|---|---|
| `ℙ³` | Macrì, Algebra Number Theory 8 (2014) 173–190 |
| the smooth quadric hypersurface in `ℙ⁴` | Schmidt |
| all Fano threefolds of Picard rank one | Li |
| abelian threefolds | Maciocia–Piyaratne; Bayer–Macrì–Stellari |

**And it is false on the blow-up of `ℙ³` at a point** — Schmidt,
*Counterexample to the Generalized Bogomolov–Gieseker Inequality for
Threefolds*, Int. Math. Res. Not. IMRN 2017, no. 8, 2562–2566.

So `BMTData` is not merely unproved here. It is **unprovable as stated for all
threefolds**, and nothing in this repository will ever inhabit it in general. A
consumer must take it as a hypothesis about one specific threefold and must
never treat it as a fact.

**Contrast this with `BogomolovGiesekerData`.** That structure is also supplied
rather than proved, but what it supplies is *true* — the obstruction there is
that the proof runs through restriction theorems this repository does not have.
Here the obstruction is that the statement is false. The two look alike in Lean
and are entirely different in status, and that difference is the reason this
section exists.

## `TiltSemistable` is opaque

For the same reason `Semistable` is in `BogomolovGieseker.lean`, and one step
further out: tilt-semistability is a property of an object of a *tilted heart*,
and the numerical layer has neither hearts nor objects. It is a field.

## Main results

* `degH1Beta`, `degH2Beta`, `deg3Beta` — the three twisted degrees.
* `discrHBeta` — the `H`-twisted discriminant at `n = 3`.
* `nu` — the tilt slope, junk where the denominator vanishes.
* `Q` — the BMT quantity.
* `BMTData` — the conjecture, supplied and uninhabited.
* The `β = 0` and `α = 0` specialisations.
-/

universe u v

namespace AlgebraicGeometry.Numerical

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

namespace Threefold

variable (V : NumericalVarietyData 3 A N) (P : Polarization V.ring)

/-! ### The three twisted degrees -/

/-- `∫_X H²·ch₁^β(E)`. -/
noncomputable def degH1Beta (β : ℚ) (E : N) : ℚ :=
  V.ring.degree (chBetaComp V P β E 1 * P.cls ^ 2)

/-- `∫_X H·ch₂^β(E)`. -/
noncomputable def degH2Beta (β : ℚ) (E : N) : ℚ :=
  V.ring.degree (chBetaComp V P β E 2 * P.cls)

/-- `∫_X ch₃^β(E)`. -/
noncomputable def deg3Beta (β : ℚ) (E : N) : ℚ :=
  V.ring.degree (chBetaComp V P β E 3)

/-- The `H`-twisted discriminant on a threefold,
`Δ_H = (H²·ch₁^β)² − 2(H³·ch₀)(H·ch₂^β)`.

`ch₀` carries no `β`: the twist sums over `j ≤ 0` in degree zero, so
`ch₀^β = ch₀ = rank`. -/
noncomputable def discrHBeta (E : N) : ℚ :=
  (degH1Beta V P 0 E) ^ 2
    - 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) * (degH2Beta V P 0 E)

/-- **The threefold tilt discriminant is the Mukai self-pairing**, at
coefficient ring `ℚ` with the multiplication of `ℚ` as the bilinear form.

The rank slot carries `∫H³`, the codimension-three analogue of the `∫H²` in
`Surface.discrH_eq_selfPairing`.  The triple is the three twisted degrees at
`β`, and `discrHBeta_beta_inert` below says the value does not depend on which
`β` that is. -/
theorem discrHBeta_eq_selfPairing (E : N) :
    discrHBeta V P E
      = Mukai.selfPairing (LinearMap.mul ℚ ℚ)
          (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ), degH1Beta V P 0 E,
            degH2Beta V P 0 E) := by
  rw [Mukai.selfPairing_mk, discrHBeta]
  show _ = degH1Beta V P 0 E * degH1Beta V P 0 E
    - 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) * degH2Beta V P 0 E)
  ring

/-- **The tilt slope** `ν_{α,β}(E) = (H·ch₂^β − (α²/2)·H³·ch₀) / (H²·ch₁^β)`.

Junk where `H²·ch₁^β` vanishes, the same convention `slopeH` uses at rank
zero. -/
noncomputable def nu (α β : ℚ) (E : N) : ℚ :=
  (degH2Beta V P β E - (α ^ 2 / 2) * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)))
    / (degH1Beta V P β E)

/-- **The Bayer–Macrì–Toda quantity**
`Q_{α,β} = α²·Δ_H + 4(H·ch₂^β)² − 6(H²·ch₁^β)(ch₃^β)`.

Defining it is all this does. Whether it is nonnegative is `BMTData`, and see
the module docstring before assuming so. -/
noncomputable def Q (α β : ℚ) (E : N) : ℚ :=
  α ^ 2 * discrHBeta V P E + 4 * (degH2Beta V P β E) ^ 2
    - 6 * (degH1Beta V P β E) * (deg3Beta V P β E)

/-! ### The `β = 0` and `α = 0` specialisations -/

@[simp]
theorem degH1Beta_zero_beta (E : N) :
    degH1Beta V P 0 E = V.ring.degree (V.chComp E 1 * P.cls ^ 2) := by
  rw [degH1Beta, chBetaComp_zero_beta]

@[simp]
theorem degH2Beta_zero_beta (E : N) :
    degH2Beta V P 0 E = V.ring.degree (V.chComp E 2 * P.cls) := by
  rw [degH2Beta, chBetaComp_zero_beta]

@[simp]
theorem deg3Beta_zero_beta (E : N) :
    deg3Beta V P 0 E = V.ring.degree (V.chComp E 3) := by
  rw [deg3Beta, chBetaComp_zero_beta]

/-! ### `β` is inert in the discriminant

The two twisted degrees each move with `β`, and the discriminant is the one
combination of them that does not. `degH1Beta_eq_sub` and `degH2Beta_eq_sub`
are the two expansions; `discrHBeta_beta_inert` is the cancellation. -/

/-- `∫H²·ch₁^β = ∫H²·ch₁ − β·∫H³·ch₀`. -/
theorem degH1Beta_eq_sub (β : ℚ) (E : N) :
    degH1Beta V P β E
      = degH1Beta V P 0 E - β * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) := by
  have key : chBetaComp V P β E 1 * P.cls ^ 2
      = algebraMap ℚ A (-(β * (V.rank E : ℚ))) * P.cls ^ 3
        + V.chComp E 1 * P.cls ^ 2 := by
    rw [chBetaComp_eq, Finset.sum_range_succ, Finset.sum_range_one, V.chComp_zero]
    norm_num [twistCoeff, Nat.factorial, map_neg, map_mul]
    ring
  rw [degH1Beta, key, map_add, NumericalRingData.degree_algebraMap_mul,
    degH1Beta_zero_beta]
  ring

/-- `∫H·ch₂^β = ∫H·ch₂ − β·∫H²·ch₁ + (β²/2)·∫H³·ch₀`. -/
theorem degH2Beta_eq_sub (β : ℚ) (E : N) :
    degH2Beta V P β E
      = degH2Beta V P 0 E - β * degH1Beta V P 0 E
        + β ^ 2 / 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) := by
  have key : chBetaComp V P β E 2 * P.cls
      = algebraMap ℚ A (β ^ 2 / 2 * (V.rank E : ℚ)) * P.cls ^ 3
        + algebraMap ℚ A (-β) * (V.chComp E 1 * P.cls ^ 2)
        + V.chComp E 2 * P.cls := by
    rw [chBetaComp_eq, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, V.chComp_zero]
    norm_num [twistCoeff, Nat.factorial, map_neg, map_mul]
    ring
  rw [degH2Beta, key, map_add, map_add, NumericalRingData.degree_algebraMap_mul,
    NumericalRingData.degree_algebraMap_mul, degH2Beta_zero_beta, degH1Beta_zero_beta]
  ring

/-- **`β` is inert in the tilt discriminant.**

Each twisted degree moves with `β` — see the two expansions above — and the
combination `(∫H²ch₁^β)² − 2(∫H³ch₀)(∫H·ch₂^β)` is the one in which every `β`
term cancels: the linear terms cancel against each other and the quadratic ones
against the `β²/2` in `ch₂^β`.

This is the threefold instance of the `B`-twist invariance
`ChernCharacter.discriminant_twist` already records on the divisorial side. -/
theorem discrHBeta_beta_inert (β : ℚ) (E : N) :
    (degH1Beta V P β E) ^ 2
        - 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) * (degH2Beta V P β E)
      = discrHBeta V P E := by
  rw [discrHBeta, degH1Beta_eq_sub V P β E, degH2Beta_eq_sub V P β E]
  ring

theorem discrHBeta_zero_beta (E : N) :
    discrHBeta V P E
      = (V.ring.degree (V.chComp E 1 * P.cls ^ 2)) ^ 2
        - 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ))
          * V.ring.degree (V.chComp E 2 * P.cls) := by
  rw [discrHBeta, degH1Beta_zero_beta, degH2Beta_zero_beta]

/-- `Q` written out in untwisted components. -/
theorem Q_zero_beta (α : ℚ) (E : N) :
    Q V P α 0 E
      = α ^ 2 * ((V.ring.degree (V.chComp E 1 * P.cls ^ 2)) ^ 2
          - 2 * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ))
            * V.ring.degree (V.chComp E 2 * P.cls))
        + 4 * (V.ring.degree (V.chComp E 2 * P.cls)) ^ 2
        - 6 * (V.ring.degree (V.chComp E 1 * P.cls ^ 2))
          * V.ring.degree (V.chComp E 3) := by
  rw [Q, discrHBeta_zero_beta, degH1Beta_zero_beta, degH2Beta_zero_beta, deg3Beta_zero_beta]

/-- At `α = 0` the tilt slope is the plain ratio of the two twisted degrees. -/
theorem nu_zero_alpha (β : ℚ) (E : N) :
    nu V P 0 β E = degH2Beta V P β E / degH1Beta V P β E := by
  rw [nu]
  norm_num

/-- At `α = 0`, `Q` loses its discriminant term. -/
theorem Q_zero_alpha (β : ℚ) (E : N) :
    Q V P 0 β E
      = 4 * (degH2Beta V P β E) ^ 2 - 6 * (degH1Beta V P β E) * (deg3Beta V P β E) := by
  rw [Q]
  ring

/-! ### The conjecture, supplied and uninhabited -/

/-- **The Bayer–Macrì–Toda inequality, as supplied data.**

Carries a choice of tilt-semistability predicate as well as a proposition, so
`…Data` rather than `…Statement`, matching `BogomolovGiesekerData`.

**It is false in general.** See the module docstring: the conjecture fails on
the blow-up of `ℙ³` at a point (Schmidt, IMRN 2017). This structure is therefore
not merely unproved here but unprovable as stated for all threefolds, and
nothing in this repository inhabits it. Any consumer must hypothesise it for one
specific threefold.

That is the difference from `BogomolovGiesekerData`, which is unproved here but
**true**. -/
structure BMTData (V : NumericalVarietyData 3 A N) (P : Polarization V.ring) where
  /-- Tilt-semistability at parameters `(α, β)`, supplied.

  Opaque for the same reason `Semistable` is, and one step further out: this is
  a property of an object of a *tilted heart*, and the numerical layer has
  neither hearts nor objects. -/
  TiltSemistable : ℚ → ℚ → N → Prop
  /-- **The conjectural inequality.** Supplied, not proved, and **false for some
  threefolds** — see the structure's docstring. -/
  nonneg : ∀ (α β : ℚ) (E : N), 0 < α → TiltSemistable α β E → 0 ≤ Q V P α β E

end Threefold

end AlgebraicGeometry.Numerical
