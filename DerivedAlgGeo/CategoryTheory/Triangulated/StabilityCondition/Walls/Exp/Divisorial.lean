/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Charge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Exp.Kernel
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.CentralCharge

/-!
# The divisorial charge is the exponential kernel

`Walls/Exp/Kernel.lean` states the exponential charge once, indexed by
truncation degree, and `Walls/Exp/Comparison.lean` proves the two compressed
`H`-degree families are it. Those families are Picard rank one. This file does
the case that actually decides whether the kernel is worth having: the
divisorial charge of `Walls/Divisorial/Charge.lean`, which takes two
independent classes `B` and `omega` in the full real divisor space.

## Why this is the keystone

The compressed families reach the kernel through a vector of `H`-degrees. The
divisorial charge cannot: the `H`-compression is not injective once the Picard
rank exceeds one, so there is no degree vector to hand it. If the kernel could
only be reached that way it would cover the rank-one slice and nothing else,
and the unification would be cosmetic.

It is reached instead by keeping the same polynomial and replacing the degree
functional with the intersection form. The moments become

```text
mu 0 = ch2(E),   mu 1 = <w, ch1(E)>,   mu 2 = <w, w> * rk(E)
```

with `w = B + i*omega`, and `Exp.ofMoments 2` of those is the divisorial charge
on the nose. That is why `ofMoments` takes a moment sequence rather than a
vector of degrees: the two sources of moments are siblings under it, and
neither is a specialization of the other.

Two of the three independent designs of this tree concluded the multi-divisor
charge was a sibling that is not a child. They were wrong, and this file is the
proof.

## Stated on the triple

The keystone is proved on a bare `Mukai.RealExtension D`, not on a
`ChernCharacter`. That is load-bearing rather than stylistic: `mukaiCharge`
(`Walls/Divisorial/Mukai.lean`) is the same `expCharge` on a *different* triple,
so a `ChernCharacter`-level statement could not reach it, and the correction
class the next slice inhabits is exactly that difference. The
`ChernCharacter` forms below follow by `toRealExtension`.

`centralCharge_eq_expCharge` is the other half and was not previously recorded:
the divisorial charge and Bridgeland's `Z(beta, omega)` are the same function,
not two functions that agree in the cases anyone checked.

## What is not here

No correction class, no walls, no tilting. `kappa` arrives with the polarised
transport, where it belongs, because it is a pullback and not a coefficient.
-/

open Complex

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Divisorial

variable {D : Type*} [AddCommGroup D] [Module ℝ D]
variable {N : Type*} [AddCommGroup N]

/-- `<w, x>` for `w = B + i*omega`, as a complex number. -/
def cPair (S : DivisorSpace D) (P : StabilityParameters D) (x : D) : ℂ :=
  ((S.pair P.B x : ℝ) : ℂ) + ((S.pair P.omega x : ℝ) : ℂ) * I

/-- `<w, w>` for `w = B + i*omega`. The imaginary part carries the factor of
two from the cross term. -/
def cSelf (S : DivisorSpace D) (P : StabilityParameters D) : ℂ :=
  ((S.pair P.B P.B - S.pair P.omega P.omega : ℝ) : ℂ)
    + ((2 * S.pair P.omega P.B : ℝ) : ℂ) * I

/-- The divisorial moments of an arbitrary Mukai triple `(r, c, s)`:
`mu 0 = s`, `mu 1 = <w, c>`, `mu 2 = <w, w> * r`, and zero above.

These are the moments of `Exp.ofMoments` with the intersection form in place of
the degree functional, which is the whole content of the unification. -/
def tripleMoments (S : DivisorSpace D) (P : StabilityParameters D)
    (v : Mukai.RealExtension D) : ℕ → ℂ
  | 0 => ((v.2.2 : ℝ) : ℂ)
  | 1 => cPair S P v.2.1
  | 2 => cSelf S P * ((v.1 : ℝ) : ℂ)
  | _ + 3 => 0

/-- **The keystone.** Bridgeland's `Z(beta, omega)` on a Mukai triple is the
exponential kernel at truncation degree two. -/
theorem expCharge_eq_ofMoments (S : DivisorSpace D) (P : StabilityParameters D)
    (v : Mukai.RealExtension D) :
    Mukai.expCharge S.intersection P.B P.omega v
      = Exp.ofMoments 2 (tripleMoments S P v) := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  obtain ⟨r, c, s⟩ := v
  rw [Mukai.expCharge_apply _ _ _ hb]
  simp only [Exp.ofMoments, Finset.sum_range_succ, Finset.sum_range_zero, Exp.coeff,
    tripleMoments, cPair, cSelf]
  norm_num [Nat.factorial]
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      DivisorSpace.pair, hb P.omega P.B] <;> ring

/-- The rank-one collapse. On `B = b*H`, `omega = a*H` the intersection-form
charge of any triple is the scalar kernel on the compressed degrees
`(H^2 * r, H * c, s)`, which is how the divisorial branch and the compressed
branch meet. -/
theorem expCharge_rankOne_eq_charge (S : DivisorSpace D) (H : D) (a b : ℝ)
    (v : Mukai.RealExtension D) :
    Mukai.expCharge S.intersection (StabilityParameters.rankOne H a b).B
        (StabilityParameters.rankOne H a b).omega v
      = Exp.charge 2 (Exp.alphaBetaChart (a, b))
          ![S.pair H H * v.1, S.pair H v.2.1, v.2.2] := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  obtain ⟨r, c, s⟩ := v
  rw [Mukai.expCharge_apply _ _ _ hb]
  simp only [Exp.charge, AddMonoidHom.mk'_apply, Exp.ofMoments, Exp.moments, Exp.coeff,
    Exp.alphaBetaChart, Finset.sum_range_succ, Finset.sum_range_zero,
    StabilityParameters.rankOne]
  norm_num [Nat.factorial, DivisorSpace.pair]
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      pow_two, hb H c] <;> ring

/-- The divisorial charge **is** `Z(beta, omega)` on the Mukai triple of the
Chern character. Both sides were already in the tree; that they are one
function was not recorded. -/
theorem centralCharge_eq_expCharge (ch : ChernCharacter N D) (S : DivisorSpace D)
    (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E
      = Mukai.expCharge S.intersection P.B P.omega (ch.toRealExtension E) := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  rw [ChernCharacter.centralCharge_apply, Mukai.expCharge_apply _ _ _ hb]
  simp only [ChernCharacter.toRealExtension_apply, DivisorSpace.pair]
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      hb P.omega P.B] <;> ring

/-- The keystone in `ChernCharacter` form, by `toRealExtension`. -/
theorem centralCharge_eq_ofMoments (ch : ChernCharacter N D) (S : DivisorSpace D)
    (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E = Exp.ofMoments 2 (tripleMoments S P (ch.toRealExtension E)) := by
  rw [centralCharge_eq_expCharge, expCharge_eq_ofMoments]

/-- The divisorial moments of a Chern character: the triple moments of its
Mukai triple. -/
def moments (ch : ChernCharacter N D) (S : DivisorSpace D)
    (P : StabilityParameters D) (E : N) : ℕ → ℂ :=
  tripleMoments S P (ch.toRealExtension E)

theorem moments_apply (ch : ChernCharacter N D) (S : DivisorSpace D)
    (P : StabilityParameters D) (E : N) :
    moments ch S P E = tripleMoments S P (ch.toRealExtension E) := rfl

theorem moments_rankOne (ch : ChernCharacter N D) (S : DivisorSpace D) (H : D)
    (a b : ℝ) (E : N) :
    moments ch S (StabilityParameters.rankOne H a b) E
      = Exp.moments 2 (Exp.alphaBetaChart (a, b))
          ![S.pair H H * ch.rank E, S.pair H (ch.chOne E), ch.chTwo E] := by
  funext j
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  match j with
  | 0 => simp [moments, tripleMoments, Exp.moments]
  | 1 =>
    simp only [moments, tripleMoments, Exp.moments, cPair, StabilityParameters.rankOne,
      Exp.alphaBetaChart, DivisorSpace.pair, ChernCharacter.toRealExtension_apply,
      map_smul, smul_eq_mul, LinearMap.smul_apply, dif_pos (by omega : (1:ℕ) ≤ 2), pow_one]
    norm_num
    apply Complex.ext <;> simp
  | 2 =>
    simp only [moments, tripleMoments, Exp.moments, cSelf, StabilityParameters.rankOne,
      Exp.alphaBetaChart, DivisorSpace.pair, ChernCharacter.toRealExtension_apply,
      map_smul, smul_eq_mul, LinearMap.smul_apply, dif_pos (by omega : (2:ℕ) ≤ 2)]
    norm_num
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        pow_two] <;> ring
  | (k+3) => simp [moments, tripleMoments, Exp.moments]

/-- The rank-one collapse in `ChernCharacter` form. -/
theorem centralCharge_rankOne_eq_charge (ch : ChernCharacter N D) (S : DivisorSpace D)
    (H : D) (a b : ℝ) (E : N) :
    ch.centralCharge S (StabilityParameters.rankOne H a b) E
      = Exp.charge 2 (Exp.alphaBetaChart (a, b))
          ![S.pair H H * ch.rank E, S.pair H (ch.chOne E), ch.chTwo E] := by
  rw [centralCharge_eq_expCharge, expCharge_rankOne_eq_charge]
  simp [ChernCharacter.toRealExtension_apply]

end Divisorial

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
