/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Complex.Basic

/-!
# Additive central charges on numerical surfaces

The surface charge polynomial is independent of a particular surface model.
For a polarised numerical surface and an already chosen `B`-field twist it
only needs the three additive quantities

* `rank`,
* `∫ ch₁^B · H`, and
* `∫ ch₂^B`,

together with `∫ H²`.  This file packages those quantities and builds the
single charge polynomial shared by the projective-space and surface
presentations.

The package is deliberately a derived view rather than another
`NumericalVarietyData` subtype.  The numerical carrier may support several
presentations, and a charge is obtained by composing additive coordinate maps
with the charge polynomial.  No geometry, heart, support property, or
projective-family realization is asserted here.
-/

open Complex
namespace AlgebraicGeometry.Numerical

namespace Surface

noncomputable section

universe u

variable {N : Type u} [AddCommGroup N]

/-- The additive `B`-twisted coordinates consumed by a surface central charge.

`degree` is `∫ ch₁^B(E) · H`, `chTwo` is `∫ ch₂^B(E)`, and
`hyperplaneSquare` is `∫ H²`.  These are real because stability conditions
allow real `B`-fields even though the current intersection-ring presentation
is rational. -/
structure ChargeCoordinates (N : Type u) [AddCommGroup N] where
  /-- The rank, cast to `ℝ`. -/
  rank : N →+ ℝ
  /-- The twisted degree `∫ ch₁^B(E) · H`. -/
  degree : N →+ ℝ
  /-- The twisted top Chern-character number `∫ ch₂^B(E)`. -/
  chTwo : N →+ ℝ
  /-- The polarisation square `∫ H²`. -/
  hyperplaneSquare : ℝ

namespace ChargeCoordinates

variable (D : ChargeCoordinates N)

/-- Twist rank-one coordinates by the real `B`-field `B = bH`.

This is the component expansion of `ch^(bH) = exp(-bH) ch`.  It is useful for
Picard-rank-one surfaces, but the general numerical adapter accepts an
arbitrary `BField` instead. -/
noncomputable def twistByScalar (b : ℝ) : ChargeCoordinates N where
  rank := D.rank
  degree := AddMonoidHom.mk'
    (fun E => D.degree E - b * D.hyperplaneSquare * D.rank E)
    (by
      intro E F
      simp only [map_add]
      ring)
  chTwo := AddMonoidHom.mk'
    (fun E => D.chTwo E - b * D.degree E
      + b ^ 2 * D.hyperplaneSquare * D.rank E / 2)
    (by
      intro E F
      simp only [map_add]
      ring)
  hyperplaneSquare := D.hyperplaneSquare

/-- A scalar `B`-twist does not alter rank. -/
@[simp]
theorem twistByScalar_rank (b : ℝ) (E : N) :
    (D.twistByScalar b).rank E = D.rank E := rfl

/-- Evaluation of `∫H ch₁^(bH)`. -/
@[simp]
theorem twistByScalar_degree (b : ℝ) (E : N) :
    (D.twistByScalar b).degree E =
      D.degree E - b * D.hyperplaneSquare * D.rank E := rfl

/-- Evaluation of `∫ch₂^(bH)`. -/
@[simp]
theorem twistByScalar_chTwo (b : ℝ) (E : N) :
    (D.twistByScalar b).chTwo E =
      D.chTwo E - b * D.degree E
        + b ^ 2 * D.hyperplaneSquare * D.rank E / 2 := rfl

/-- Twisting does not alter the chosen polarisation. -/
@[simp]
theorem twistByScalar_hyperplaneSquare (b : ℝ) :
    (D.twistByScalar b).hyperplaneSquare = D.hyperplaneSquare := rfl

/-- The canonical surface central charge on `B`-twisted coordinates:

`-∫ ch₂^B + (a²/2)∫H² ch₀^B + i a∫H ch₁^B`, where `ω = aH`.
This definition is only the arithmetic polynomial, not a claim that a given
carrier comes from a geometric surface. -/
noncomputable def centralCharge (a : ℝ) : N →+ ℂ :=
  AddMonoidHom.mk'
    (fun E =>
      -Complex.ofReal (D.chTwo E)
        + Complex.ofReal (a ^ 2 * D.hyperplaneSquare * D.rank E / 2)
        + (a * Complex.I) * Complex.ofReal (D.degree E))
    (by
      intro E F
      simp only [map_add]
      push_cast
      ring)

/-- Pointwise expansion of the additive central charge. -/
@[simp]
theorem centralCharge_apply (a : ℝ) (E : N) :
    D.centralCharge a E =
      -Complex.ofReal (D.chTwo E)
        + Complex.ofReal (a ^ 2 * D.hyperplaneSquare * D.rank E / 2)
        + (a * Complex.I) * Complex.ofReal (D.degree E) := rfl

/-- Additivity gives the neutral-element law needed by charge consumers. -/
theorem centralCharge_zero (a : ℝ) : D.centralCharge a 0 = 0 :=
  (D.centralCharge a).map_zero

/-- The real part isolates the twisted `ch₂` term and the positive quadratic
polarisation term used in the surface stability function. -/
theorem centralCharge_re (a : ℝ) (E : N) :
    (D.centralCharge a E).re =
      -D.chTwo E + a ^ 2 * D.hyperplaneSquare * D.rank E / 2 := by
  simp only [centralCharge, AddMonoidHom.mk'_apply, Complex.add_re, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part is the positive multiple of the twisted `H`-degree
that determines the tilted-heart slope cutoff. -/
theorem centralCharge_im (a : ℝ) (E : N) :
    (D.centralCharge a E).im = a * D.degree E := by
  simp only [centralCharge, AddMonoidHom.mk'_apply, Complex.add_im, Complex.neg_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Expanding `ch^(bH)` recovers Li's projective-space notation exactly. -/
theorem centralCharge_twistByScalar_apply (a b : ℝ) (E : N) :
    (D.twistByScalar b).centralCharge a E =
      -Complex.ofReal (D.chTwo E)
        + (b + a * Complex.I) * Complex.ofReal (D.degree E)
        - (b + a * Complex.I) ^ 2
            * Complex.ofReal (D.hyperplaneSquare * D.rank E / 2) := by
  apply Complex.ext <;>
    simp only [centralCharge, twistByScalar, AddMonoidHom.mk'_apply,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_two] <;>
    ring

/-! ### Coordinate maps between two charge presentations -/

/-- A charge-coordinate map preserving the four quantities used by the charge polynomial.

This is the arithmetic shape needed before a geometric C1 comparison can be
attached.  In particular, the source and target carriers remain distinct. -/
structure Pullback {L M : Type*} [AddCommGroup L] [AddCommGroup M]
    (source : ChargeCoordinates L) (target : ChargeCoordinates M) where
  /-- The source-to-target additive class map. -/
  map : L →+ M
  /-- Preservation of the rank coordinate. -/
  rank_eq : ∀ E, source.rank E = target.rank (map E)
  /-- Preservation of the degree coordinate. -/
  degree_eq : ∀ E, source.degree E = target.degree (map E)
  /-- Preservation of the `ch₂` coordinate. -/
  chTwo_eq : ∀ E, source.chTwo E = target.chTwo (map E)
  /-- Preservation of the polarisation square. -/
  hyperplaneSquare_eq : source.hyperplaneSquare = target.hyperplaneSquare

namespace Pullback

variable {L M : Type*} [AddCommGroup L] [AddCommGroup M]
variable {source : ChargeCoordinates L} {target : ChargeCoordinates M}

/-- A coordinate-preserving map intertwines the canonical central charges. -/
theorem centralCharge_eq
    (h : Pullback source target) (a : ℝ) (E : L) :
    source.centralCharge a E = target.centralCharge a (h.map E) := by
  simp only [ChargeCoordinates.centralCharge, AddMonoidHom.mk'_apply]
  rw [h.rank_eq E, h.degree_eq E, h.chTwo_eq E, h.hyperplaneSquare_eq]

/-- A coordinate map preserving untwisted Chern data also preserves the
scalar `B = bH` twist. -/
noncomputable def twistByScalar (h : Pullback source target) (b : ℝ) :
    Pullback (source.twistByScalar b) (target.twistByScalar b) where
  map := h.map
  rank_eq := h.rank_eq
  degree_eq := by
    intro E
    simp only [ChargeCoordinates.twistByScalar_degree]
    rw [h.rank_eq E, h.degree_eq E, h.hyperplaneSquare_eq]
  chTwo_eq := by
    intro E
    simp only [ChargeCoordinates.twistByScalar_chTwo]
    rw [h.rank_eq E, h.degree_eq E, h.chTwo_eq E, h.hyperplaneSquare_eq]
  hyperplaneSquare_eq := by
    simp only [ChargeCoordinates.twistByScalar_hyperplaneSquare]
    exact h.hyperplaneSquare_eq

/-- This is the reusable comparison theorem for rank-one examples: coordinate
preservation before twisting suffices to identify the two resulting charges. -/
theorem centralCharge_twistByScalar_eq
    (h : Pullback source target) (a b : ℝ) (E : L) :
    (source.twistByScalar b).centralCharge a E =
      (target.twistByScalar b).centralCharge a (h.map E) :=
  centralCharge_eq (h.twistByScalar b) a E

end Pullback

end ChargeCoordinates

end

end Surface

end AlgebraicGeometry.Numerical
