/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialDiscriminant

/-!
# Every fixed-`u` slice of a divisorial wall family is an `(s, t)` half plane

`Walls/Numerical/Basic.lean` proves that a numerical wall in the `(s, t)` plane
is a circle centred on the `s`-axis or a vertical line, that two walls of a
fixed class are disjoint, and that they are nested.  Those are theorems about
the three-coordinate polynomial and, until this file, were available only to
the compressed Picard-rank-one transport of `WallTransport.lean`.

The divisorial family of `DivisorialWallSlice.lean` is indexed by
`B = s H + G(u)`, `omega = t H` with `u` in an arbitrary real transverse space.
Fixing `u` and letting `(s, t)` vary gives a half plane, and the theorem below
says that half plane **is** the `(s, t)` model, pulled back along the
degree-weighted triple of the `G(u)`-twisted character:

```text
(T.chargeFamily ch).reindex (fun (s,t) => ⟨s, u, t⟩)
  = stChargeFamily.pullback ((ch.twist S (G u)).coordinatesAt S H).toNumClassHom
```

Consequently the circle, line, disjointness, and nesting results hold on every
`u`-slice of a surface of arbitrary Picard rank.  This is the wall picture used
by Maciocia (arXiv:1202.4587, Prop. 2.6 and Thm 3.1), Arcara--Miles
(arXiv:1401.6149, §4) and Mizuno--Yoshida (arXiv:2502.18894, Thm 2.1), and it is
the reason those papers fix a transverse direction before drawing circles.

## The `u`-dependence is real

Twisting by `G(u)` does not change the compressed degree, because `H · G(u) = 0`,
but it does change the compressed `ch₂` and hence the discriminant:
`discr` of the slice class exceeds the untwisted one by
`2 H² r (G(u) · ch₁) - H² r² G(u)²` (`discr_sliceCoordinates`).  So the walls
genuinely move as `u` varies, which is what makes the transverse parameter worth
carrying; only within one `u`-plane are they nested.

## Nesting needs a nonnegative discriminant, and now has one

`barDiscriminant_parameters` computes the `\bar Δ^B_ω` of
`DivisorialDiscriminant.lean` at a slice point: it is `t²` times the slice
discriminant, with the `s`-dependence cancelling exactly.  Bogomolov--Gieseker
and a Hodge index at `omega` therefore discharge the `0 ≤ discr` hypothesis of
the disjointness and nesting theorems on every `u`-plane, not only on the
rank-one one.

Nothing here proves a Bogomolov inequality or a Hodge index theorem; both remain
the supplied data of `BogomolovGieseker.lean` and `DivisorialDiscriminant.lean`.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v w x

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-! ### Compressed coordinates as a point of the `(s, t)` wall plane -/

namespace ChargeCoordinates

variable (Dc : ChargeCoordinates N)

/-- The degree-weighted numerical triple of compressed charge coordinates.

The rank slot carries `∫H²`, which is what the `(s,t)` charge polynomial
requires; see the module docstring of `WallTransport.lean` for the term-by-term
derivation. -/
def toNumClass (E : N) : Wall.NumClass :=
  (Dc.hyperplaneSquare * Dc.rank E, Dc.degree E, Dc.chTwo E)

@[simp]
theorem toNumClass_rk (E : N) :
    (Dc.toNumClass E).rk = Dc.hyperplaneSquare * Dc.rank E := rfl

@[simp]
theorem toNumClass_deg (E : N) : (Dc.toNumClass E).deg = Dc.degree E := rfl

@[simp]
theorem toNumClass_ch2 (E : N) : (Dc.toNumClass E).ch2 = Dc.chTwo E := rfl

/-- The triple is additive, because each of its three coordinates is. -/
def toNumClassHom : N →+ Wall.NumClass :=
  AddMonoidHom.mk' Dc.toNumClass (by
    intro E F
    simp only [toNumClass, map_add, Prod.mk_add_mk, mul_add])

@[simp]
theorem toNumClassHom_apply (E : N) : Dc.toNumClassHom E = Dc.toNumClass E := rfl

/-- The wall-plane discriminant of the transported triple is the compressed
discriminant. -/
@[simp]
theorem discr_toNumClass (E : N) :
    Wall.NumClass.discr (Dc.toNumClass E) = Dc.discr E := by
  simp only [Wall.NumClass.discr_eq, toNumClass_rk, toNumClass_deg, toNumClass_ch2,
    ChargeCoordinates.discr]
  ring

/-- **The `(s,t)` charge of the transported triple is the scalar-twisted
charge.**  This is the identity that makes the whole `(s,t)` development
available to any compressed coordinates. -/
theorem stCharge_toNumClass (b a : ℝ) (E : N) :
    Wall.stCharge b a (Dc.toNumClass E) = (Dc.twistByScalar b).centralCharge a E := by
  apply Complex.ext
  · rw [Wall.stCharge_re, ChargeCoordinates.centralCharge_re]
    simp only [Wall.reZ, toNumClass_rk, toNumClass_deg, toNumClass_ch2,
      twistByScalar_chTwo, twistByScalar_rank, twistByScalar_hyperplaneSquare]
    ring
  · rw [Wall.stCharge_im, ChargeCoordinates.centralCharge_im]
    simp only [Wall.imZ, toNumClass_rk, toNumClass_deg, twistByScalar_degree]
    ring

/-- The `(s,t)` wall family of compressed coordinates: the generic `(s,t)` child
pulled back along the degree-weighted triple. -/
def stWallFamily : Wall.ChargeFamily (ℝ × ℝ) N :=
  Wall.stChargeFamily.pullback Dc.toNumClassHom

@[simp]
theorem stWallFamily_charge (p : ℝ × ℝ) (E : N) :
    Dc.stWallFamily.charge p E = Wall.stCharge p.1 p.2 (Dc.toNumClass E) := rfl

@[simp]
theorem stWallFamily_wallValue (p : ℝ × ℝ) (E F : N) :
    Dc.stWallFamily.wallValue p E F =
      Wall.wallExpr p.1 p.2 (Dc.toNumClass E) (Dc.toNumClass F) := by
  simp [stWallFamily]

end ChargeCoordinates

/-- The polarised-surface transport of `WallTransport.lean` is the compressed
transport of the coordinates it reads off.  The two differ only by where the
rational-to-real cast of the product `∫H² · rank` is taken. -/
theorem toNumClass_eq_ofNumericalData (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    Surface.toNumClass V P E =
      (ChargeCoordinates.ofNumericalData V P).toNumClass E := by
  have h : ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ)
      = ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) * ((V.rank E : ℤ) : ℝ) := by
    push_cast
    ring
  simp only [Surface.toNumClass, ChargeCoordinates.toNumClass,
    ChargeCoordinates.ofNumericalData_rank, ChargeCoordinates.ofNumericalData_degree,
    ChargeCoordinates.ofNumericalData_chTwo,
    ChargeCoordinates.ofNumericalData_hyperplaneSquare]
  rw [h]

/-! ### Twisting the character moves the `B`-field -/

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- **Twisting the character adds to the `B`-field.**  This is
`exp(-B₀) exp(-B) = exp(-(B₀+B))` read on the central charge, and it is what
lets a slice absorb its transverse direction into the character. -/
theorem centralCharge_twist (B : D) (P : StabilityParameters D) (E : N) :
    (ch.twist S B).centralCharge S P E =
      ch.centralCharge S ⟨P.B + B, P.omega⟩ E := by
  have hcomm : S.pair P.B B = S.pair B P.B := S.pair_comm P.B B
  rw [centralCharge_apply, centralCharge_apply]
  simp only [twist_rank, twist_chOne, twist_chTwo, DivisorSpace.pair, map_add, map_sub,
    map_smul, LinearMap.add_apply, smul_eq_mul] at hcomm ⊢
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero]
  · linear_combination (-(ch.rank E) / 2) * hcomm
  · ring

end ChernCharacter

/-! ### A fixed transverse parameter gives an `(s, t)` half plane -/

namespace OrthogonalSlice

variable {U : Type x} [AddCommGroup U] [Module ℝ U]

namespace Point

/-- The slice point at a fixed transverse parameter, as a function of `(s, t)`. -/
def ofST (uu : U) (p : ℝ × ℝ) : Point U := ⟨p.1, uu, p.2⟩

end Point

variable {S : DivisorSpace D} (T : OrthogonalSlice S U)

/-- The compressed coordinates a fixed `u`-slice sees: the `G(u)`-twisted
character, read at `H`. -/
def sliceCoordinates (ch : ChernCharacter N D) (uu : U) : ChargeCoordinates N :=
  (ch.twist S (T.transverse uu)).coordinatesAt S T.H

@[simp]
theorem sliceCoordinates_rank (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).rank E = ch.rank E := rfl

/-- The compressed degree does not see the transverse direction, because
`G(u)` is orthogonal to `H`. -/
@[simp]
theorem sliceCoordinates_degree (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).degree E = S.pair T.H (ch.chOne E) := by
  show S.pair T.H (ch.chOne E - ch.rank E • T.transverse uu) = _
  simp only [DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
  rw [show S.intersection T.H (T.transverse uu) = 0 from T.orthogonal uu]
  ring

@[simp]
theorem sliceCoordinates_chTwo (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).chTwo E =
      ch.chTwo E - S.pair (T.transverse uu) (ch.chOne E)
        + S.pair (T.transverse uu) (T.transverse uu) * ch.rank E / 2 := rfl

@[simp]
theorem sliceCoordinates_hyperplaneSquare (ch : ChernCharacter N D) (uu : U) :
    (T.sliceCoordinates ch uu).hyperplaneSquare = S.pair T.H T.H := rfl


@[simp]
theorem parameters_ofST (uu : U) (p : ℝ × ℝ) :
    T.parameters (Point.ofST uu p) =
      ⟨p.1 • T.H + T.transverse uu, p.2 • T.H⟩ := rfl

/-- **The fixed-`u` slice of a divisorial wall family is the `(s,t)` model.**

Reindexing the divisorial family to a fixed transverse parameter gives exactly
the generic `(s,t)` charge family, pulled back along the degree-weighted triple
of the `G(u)`-twisted character.  Every circle, line, disjointness and nesting
theorem of `Walls/Numerical/` therefore applies on that half plane. -/
theorem chargeFamily_reindex_ofST (ch : ChernCharacter N D) (uu : U) :
    (T.chargeFamily ch).reindex (Point.ofST uu) =
      (T.sliceCoordinates ch uu).stWallFamily := by
  ext p E
  rw [Wall.ChargeFamily.reindex_charge, ChargeCoordinates.stWallFamily_charge,
    ChargeCoordinates.stCharge_toNumClass]
  show ch.centralCharge S (T.parameters (Point.ofST uu p)) E
      = ((((ch.twist S (T.transverse uu)).coordinatesAt S T.H).twistByScalar
          p.1).centralCharge p.2) E
  rw [← ChernCharacter.centralCharge_rankOne_eq (ch.twist S (T.transverse uu)) S T.H p.2 p.1 E,
    ChernCharacter.centralCharge_twist]
  rfl

/-- The wall of two classes on a fixed `u`-slice is the `(s,t)` wall of their
transported triples. -/
theorem wallValue_ofST (ch : ChernCharacter N D) (uu : U) (p : ℝ × ℝ) (v w : N) :
    (T.chargeFamily ch).wallValue (Point.ofST uu p) v w =
      Wall.wallExpr p.1 p.2 ((T.sliceCoordinates ch uu).toNumClass v)
        ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [show (T.chargeFamily ch).wallValue (Point.ofST uu p) v w
        = ((T.chargeFamily ch).reindex (Point.ofST uu)).wallValue p v w from rfl,
    T.chargeFamily_reindex_ofST ch uu, ChargeCoordinates.stWallFamily_wallValue]

/-! ### The circle, on every slice -/

/-- **A numerical wall on a fixed `u`-slice is cut out by a circle equation.**
Maciocia Prop. 2.6; Mizuno--Yoshida Thm 2.1(1). -/
theorem wall_ofST_iff_circle (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) (v w : N) :
    Point.ofST uu p ∈ T.wall ch v w ↔
      Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) * (p.1 ^ 2 + p.2 ^ 2)
          + 2 * Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) * p.1
          + 2 * Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) = 0 := by
  rw [OrthogonalSlice.wall, Wall.ChargeFamily.mem_wall, T.wallValue_ofST]
  exact Wall.wall_iff_circle ht _ _

/-- Centre `(-minB/minA, 0)` and radius squared `(minB² - 2 minA minC)/minA²`,
on a fixed `u`-slice, in cleared form. -/
theorem wall_ofST_circle_eq (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) {v w : N}
    (hA : Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) ≠ 0) :
    Point.ofST uu p ∈ T.wall ch v w ↔
      (Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) * p.1
            + Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w)) ^ 2
          + (Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) * p.2) ^ 2
        = Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) ^ 2
          - 2 * Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w)
            * Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [OrthogonalSlice.wall, Wall.ChargeFamily.mem_wall, T.wallValue_ofST]
  exact Wall.wall_circle_eq ht hA

/-- The vertical-line case, on a fixed `u`-slice. -/
theorem wall_ofST_line_eq (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) {v w : N}
    (hA : Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) = 0)
    (hB : Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) ≠ 0) :
    Point.ofST uu p ∈ T.wall ch v w ↔
      p.1 = -(Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
          ((T.sliceCoordinates ch uu).toNumClass w))
        / Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
          ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [OrthogonalSlice.wall, Wall.ChargeFamily.mem_wall, T.wallValue_ofST]
  exact Wall.wall_line_eq ht hA hB

/-! ### The discriminant on a slice -/

/-- The slice discriminant, expanded.  The transverse direction contributes
`2 H² r (G(u) · ch₁) - H² r² G(u)²`, so the walls of one class genuinely move
with `u`. -/
theorem discr_sliceCoordinates (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).discr E =
      S.pair T.H (ch.chOne E) ^ 2
        - 2 * S.pair T.H T.H * ch.rank E * ch.chTwo E
        + 2 * S.pair T.H T.H * ch.rank E * S.pair (T.transverse uu) (ch.chOne E)
        - S.pair T.H T.H * ch.rank E ^ 2
          * S.pair (T.transverse uu) (T.transverse uu) := by
  simp only [ChargeCoordinates.discr, T.sliceCoordinates_degree,
    T.sliceCoordinates_rank, T.sliceCoordinates_chTwo,
    T.sliceCoordinates_hyperplaneSquare]
  ring

/-- **The bar discriminant at a slice point is `t²` times the slice
discriminant.**  The `s`-dependence cancels exactly, which is why
`\bar Δ^B_ω` is constant along each vertical line of the half plane. -/
theorem barDiscriminant_parameters (ch : ChernCharacter N D) (p : Point U) (E : N) :
    ch.barDiscriminant S (T.parameters p) E =
      p.t ^ 2 * (T.sliceCoordinates ch p.u).discr E := by
  have hHG : S.pair T.H (T.transverse p.u) = 0 := T.orthogonal p.u
  have hGH : S.pair (T.transverse p.u) T.H = 0 := by
    rw [S.pair_comm]; exact hHG
  simp only [DivisorSpace.pair] at hHG hGH
  simp only [ChernCharacter.barDiscriminant, ChernCharacter.twist_chOne,
    ChernCharacter.twist_chTwo, parameters_B, parameters_omega,
    T.discr_sliceCoordinates, DivisorSpace.pair, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hHG, hGH]
  ring

/-- **Bogomolov--Gieseker and a Hodge index discharge the discriminant
hypothesis on every `u`-slice.**  This is what the disjointness and nesting
theorems of `Walls/Numerical/` need, and until now it was available only on the
rank-one transport. -/
theorem discr_sliceCoordinates_nonneg (ch : ChernCharacter N D) (p : Point U)
    (ht : p.t ≠ 0) (h : S.HodgeIndex (T.parameters p).omega) {E : N}
    (hΔ : 0 ≤ ch.discriminant S E) :
    0 ≤ (T.sliceCoordinates ch p.u).discr E := by
  have hbar : 0 ≤ ch.barDiscriminant S (T.parameters p) E :=
    ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg ch S _ h E hΔ
  rw [T.barDiscriminant_parameters ch p E] at hbar
  have hts : 0 < p.t ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hts
  rw [mul_zero]
  exact hbar

/-- The same, against the wall-plane discriminant the `(s,t)` theorems consume. -/
theorem discr_toNumClass_sliceCoordinates_nonneg (ch : ChernCharacter N D)
    (p : Point U) (ht : p.t ≠ 0) (h : S.HodgeIndex (T.parameters p).omega) {E : N}
    (hΔ : 0 ≤ ch.discriminant S E) :
    0 ≤ Wall.NumClass.discr ((T.sliceCoordinates ch p.u).toNumClass E) := by
  rw [ChargeCoordinates.discr_toNumClass]
  exact T.discr_sliceCoordinates_nonneg ch p ht h hΔ

end OrthogonalSlice

end

end AlgebraicGeometry.Numerical.Surface
