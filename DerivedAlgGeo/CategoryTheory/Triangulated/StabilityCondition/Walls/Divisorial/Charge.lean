/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Coordinates
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm

/-!
# Divisorial surface charges over a real Neron--Severi space

The intrinsic parameters of a divisorial stability condition on a surface are
two independent real divisor classes: a `B`-field and an ample class `omega`.
They are not, in general, scalar multiples of one chosen generator.  This file
therefore keeps the following data in separate, composable layers:

* `DivisorSpace` supplies the real divisor space and its symmetric intersection
  form;
* `ChernCharacter` supplies additive maps `rank`, `chOne`, and `chTwo`;
* `StabilityParameters` supplies independent classes `B` and `omega`;
* `DivisorialParameters` optionally records membership of `omega` in a
  geometry-specific ample cone.

The charge is

`Z_(omega,B)(E) = -chTwo^B(E) + omega^2 rank(E) / 2
  + i (omega . chOne^B(E))`.

Equivalently, it is the Mukai pairing of `ch(E)` with the real and imaginary
parts of `exp(B + i omega)`.  The implementation reuses the repository's real
Mukai extension for this comparison, but does not assume that the numerical
class is a Mukai vector.  Here its third component is genuinely `chTwo`.  A
K3-specific charge uses the Todd-corrected third Mukai component and therefore
requires a separate, explicitly named adapter rather than overloading this
structure.

Rank-one families such as `B = beta H`, `omega = alpha H`, and orthogonal
slices such as `B = s H + u G`, `omega = t H` are constructors downstream of
the intrinsic definition.  They are deliberately not fields of the core data.

This file contains only numerical arithmetic.  It does not construct the
tilted heart, prove ampleness, or establish the support property.
-/

open Complex

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

universe u v

variable {D : Type u} [AddCommGroup D] [Module ℝ D]
variable {N : Type v} [AddCommGroup N]

/-- A real numerical divisor space with its symmetric intersection form.

For a smooth projective surface the intended model is `N^1(X)_R`, with the
usual intersection product.  No basis and no Picard-rank assumption is part of
the structure. -/
structure DivisorSpace (D : Type u) [AddCommGroup D] [Module ℝ D] where
  /-- The real intersection pairing. -/
  intersection : LinearMap.BilinForm ℝ D
  /-- Intersection of divisors on a surface is symmetric. -/
  intersection_symm : intersection.IsSymm

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- Dot notation for the intersection pairing. -/
def pair (x y : D) : ℝ := S.intersection x y

theorem pair_apply (x y : D) : S.pair x y = S.intersection x y := rfl

/-- Symmetry of the numerical intersection product. -/
theorem pair_comm (x y : D) : S.pair x y = S.pair y x :=
  S.intersection_symm.eq x y

@[simp]
theorem pair_zero_left (x : D) : S.pair 0 x = 0 := by
  simp [pair]

@[simp]
theorem pair_zero_right (x : D) : S.pair x 0 = 0 := by
  simp [pair]

end DivisorSpace

/-- Additive Chern-character coordinates with an uncompressed first Chern
class in the full real divisor space. -/
structure ChernCharacter (N : Type v) (D : Type u)
    [AddCommGroup N] [AddCommGroup D] [Module ℝ D] where
  /-- The rank coordinate. -/
  rank : N →+ ℝ
  /-- The full first Chern-character coordinate in `N^1(X)_R`. -/
  chOne : N →+ D
  /-- The integrated second Chern-character coordinate. -/
  chTwo : N →+ ℝ

namespace ChernCharacter

variable (ch : ChernCharacter N D)

/-- The Chern-character triple as an element of the real Mukai extension.

This is an additive packaging device; it does not assert that `ch` is the
Todd-corrected Mukai vector. -/
def toRealExtension : N →+ Mukai.RealExtension D where
  toFun E := (ch.rank E, ch.chOne E, ch.chTwo E)
  map_zero' := by simp
  map_add' E F := by simp

@[simp]
theorem toRealExtension_apply (E : N) :
    ch.toRealExtension E = (ch.rank E, ch.chOne E, ch.chTwo E) := rfl

/-- Twist by an arbitrary real divisor class `B`.

On a surface this is the degree-at-most-two expansion of
`ch^B = exp(-B) ch`. -/
def twist (S : DivisorSpace D) (B : D) : ChernCharacter N D where
  rank := ch.rank
  chOne := AddMonoidHom.mk'
    (fun E => ch.chOne E - ch.rank E • B)
    (by
      intro E F
      simp only [map_add, add_smul]
      abel)
  chTwo := AddMonoidHom.mk'
    (fun E => ch.chTwo E - S.pair B (ch.chOne E)
      + S.pair B B * ch.rank E / 2)
    (by
      intro E F
      simp only [map_add, DivisorSpace.pair]
      ring)

@[simp]
theorem twist_rank (S : DivisorSpace D) (B : D) (E : N) :
    (ch.twist S B).rank E = ch.rank E := rfl

@[simp]
theorem twist_chOne (S : DivisorSpace D) (B : D) (E : N) :
    (ch.twist S B).chOne E = ch.chOne E - ch.rank E • B := rfl

@[simp]
theorem twist_chTwo (S : DivisorSpace D) (B : D) (E : N) :
    (ch.twist S B).chTwo E =
      ch.chTwo E - S.pair B (ch.chOne E) + S.pair B B * ch.rank E / 2 := rfl

/-! ### Maps between presentations of the same surface character -/

/-- An additive map preserving the full Chern-character coordinates.

Unlike `ChargeCoordinates.Pullback`, this comparison happens before choosing
`B` and `omega`, so one witness transports every divisorial central charge on
the fixed divisor space. -/
structure Pullback {L M : Type*} [AddCommGroup L] [AddCommGroup M]
    (source : ChernCharacter L D) (target : ChernCharacter M D) where
  /-- The map between numerical class carriers. -/
  map : L →+ M
  /-- Preservation of rank. -/
  rank_eq : ∀ E, source.rank E = target.rank (map E)
  /-- Preservation of the full first Chern class. -/
  chOne_eq : ∀ E, source.chOne E = target.chOne (map E)
  /-- Preservation of the integrated second Chern character. -/
  chTwo_eq : ∀ E, source.chTwo E = target.chTwo (map E)

namespace Pullback

variable {L M : Type*} [AddCommGroup L] [AddCommGroup M]
variable {source : ChernCharacter L D} {target : ChernCharacter M D}

/-- A full-character comparison remains valid after twisting by any real
`B`-field. -/
def twist (h : Pullback source target) (S : DivisorSpace D) (B : D) :
    Pullback (source.twist S B) (target.twist S B) where
  map := h.map
  rank_eq := h.rank_eq
  chOne_eq := by
    intro E
    simp only [twist_chOne]
    rw [h.rank_eq E, h.chOne_eq E]
  chTwo_eq := by
    intro E
    simp only [twist_chTwo]
    rw [h.rank_eq E, h.chOne_eq E, h.chTwo_eq E]

end Pullback

end ChernCharacter

/-- The two independent divisor-class parameters used by the central charge.

The arithmetic definition does not need a positivity proof.  Consumers that
construct geometric stability conditions should use `DivisorialParameters` to
attach their chosen ample-cone predicate. -/
structure StabilityParameters (D : Type u) where
  /-- The real `B`-field. -/
  B : D
  /-- The real ample class, including any desired volume scaling. -/
  omega : D

namespace StabilityParameters

/-- The familiar Picard-rank-one slice `B = beta H`, `omega = alpha H`.

This constructor remains meaningful in higher Picard rank, but describes only
the two-dimensional slice along the chosen ray `H`. -/
def rankOne (H : D) (alpha beta : ℝ) : StabilityParameters D where
  B := beta • H
  omega := alpha • H

/-- The three-parameter slice used in higher-Picard-rank wall calculations:
`B = s H + u G` and `omega = t H`.

Orthogonality `H.G = 0` and positivity `t > 0` are geometric hypotheses on a
particular use of this constructor, not data needed to form the charge. -/
def orthogonalSlice (H G : D) (s u t : ℝ) : StabilityParameters D where
  B := s • H + u • G
  omega := t • H

end StabilityParameters

/-- Stability parameters together with a proof that `omega` lies in a supplied
ample cone.  The ample cone stays geometry-specific rather than being confused
with the weaker numerical condition `omega^2 > 0`. -/
structure DivisorialParameters (ample : Set D) extends StabilityParameters D where
  /-- The chosen `omega` is ample in the supplied geometric model. -/
  omega_ample : omega ∈ ample

namespace ChernCharacter

variable (ch : ChernCharacter N D)

/-- Untwisted charge coordinates measured against one divisor class `H`.

This is the lossy rank-one view used by the pre-existing surface charge API:
it retains `H.chOne` and `H^2`, but not the full first Chern class. -/
def coordinatesAt (S : DivisorSpace D) (H : D) : ChargeCoordinates N where
  rank := ch.rank
  degree := (S.intersection H).toAddMonoidHom.comp ch.chOne
  chTwo := ch.chTwo
  hyperplaneSquare := S.pair H H

@[simp]
theorem coordinatesAt_rank (S : DivisorSpace D) (H : D) (E : N) :
    (ch.coordinatesAt S H).rank E = ch.rank E := rfl

@[simp]
theorem coordinatesAt_degree (S : DivisorSpace D) (H : D) (E : N) :
    (ch.coordinatesAt S H).degree E = S.pair H (ch.chOne E) := rfl

@[simp]
theorem coordinatesAt_chTwo (S : DivisorSpace D) (H : D) (E : N) :
    (ch.coordinatesAt S H).chTwo E = ch.chTwo E := rfl

@[simp]
theorem coordinatesAt_hyperplaneSquare (S : DivisorSpace D) (H : D) :
    (ch.coordinatesAt S H).hyperplaneSquare = S.pair H H := rfl

/-- The terminal charge coordinates obtained after twisting in the full
divisor space.  This is the bridge to the surface charge polynomial already
used by rank-one examples. -/
def chargeCoordinates (S : DivisorSpace D) (P : StabilityParameters D) :
    ChargeCoordinates N :=
  let chB := ch.twist S P.B
  { rank := chB.rank
    degree := (S.intersection P.omega).toAddMonoidHom.comp chB.chOne
    chTwo := chB.chTwo
    hyperplaneSquare := S.pair P.omega P.omega }

@[simp]
theorem chargeCoordinates_rank (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    (ch.chargeCoordinates S P).rank E = ch.rank E := rfl

@[simp]
theorem chargeCoordinates_degree (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    (ch.chargeCoordinates S P).degree E =
      S.pair P.omega (ch.chOne E - ch.rank E • P.B) := rfl

@[simp]
theorem chargeCoordinates_chTwo (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    (ch.chargeCoordinates S P).chTwo E =
      ch.chTwo E - S.pair P.B (ch.chOne E)
        + S.pair P.B P.B * ch.rank E / 2 := rfl

@[simp]
theorem chargeCoordinates_hyperplaneSquare
    (S : DivisorSpace D) (P : StabilityParameters D) :
    (ch.chargeCoordinates S P).hyperplaneSquare = S.pair P.omega P.omega := rfl

namespace Pullback

variable {L M : Type*} [AddCommGroup L] [AddCommGroup M]
variable {source : ChernCharacter L D} {target : ChernCharacter M D}

/-- A full-character comparison induces the old rank-one coordinate comparison
at every chosen divisor class `H`. -/
def coordinatesAt (h : Pullback source target)
    (S : DivisorSpace D) (H : D) :
    ChargeCoordinates.Pullback
      (source.coordinatesAt S H) (target.coordinatesAt S H) where
  map := h.map
  rank_eq := h.rank_eq
  degree_eq := by
    intro E
    simp only [ChernCharacter.coordinatesAt_degree]
    rw [h.chOne_eq E]
  chTwo_eq := h.chTwo_eq
  hyperplaneSquare_eq := rfl

/-- A full-character comparison induces a comparison of every derived charge
view. -/
def chargeCoordinates (h : Pullback source target)
    (S : DivisorSpace D) (P : StabilityParameters D) :
    ChargeCoordinates.Pullback
      (source.chargeCoordinates S P) (target.chargeCoordinates S P) where
  map := h.map
  rank_eq := h.rank_eq
  degree_eq := by
    intro E
    simp only [ChernCharacter.chargeCoordinates_degree]
    rw [h.rank_eq E, h.chOne_eq E]
  chTwo_eq := by
    intro E
    simp only [ChernCharacter.chargeCoordinates_chTwo]
    rw [h.rank_eq E, h.chOne_eq E, h.chTwo_eq E]
  hyperplaneSquare_eq := rfl

end Pullback

/-- The intrinsic divisorial surface central charge. -/
def centralCharge (S : DivisorSpace D) (P : StabilityParameters D) : N →+ ℂ :=
  (ch.chargeCoordinates S P).centralCharge 1

namespace Pullback

variable {L M : Type*} [AddCommGroup L] [AddCommGroup M]
variable {source : ChernCharacter L D} {target : ChernCharacter M D}

/-- A full-character comparison intertwines the intrinsic central charge for
every choice of `B` and `omega`. -/
theorem centralCharge_eq (h : Pullback source target)
    (S : DivisorSpace D) (P : StabilityParameters D) (E : L) :
    source.centralCharge S P E = target.centralCharge S P (h.map E) :=
  ChargeCoordinates.Pullback.centralCharge_eq (h.chargeCoordinates S P) 1 E

end Pullback

/-- Expansion in twisted Chern-character notation. -/
theorem centralCharge_apply_twisted
    (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E =
      -Complex.ofReal ((ch.twist S P.B).chTwo E)
        + Complex.ofReal (S.pair P.omega P.omega * ch.rank E / 2)
        + Complex.I * Complex.ofReal
            (S.pair P.omega ((ch.twist S P.B).chOne E)) := by
  simp [centralCharge, ChargeCoordinates.centralCharge_apply, chargeCoordinates,
    DivisorSpace.pair]

/-- Expansion in untwisted Chern-character coordinates.

This is the formula used for divisorial stability conditions in arbitrary
Picard rank. -/
theorem centralCharge_apply
    (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E =
      Complex.ofReal
          (-ch.chTwo E + S.pair P.B (ch.chOne E)
            - (S.pair P.B P.B - S.pair P.omega P.omega) * ch.rank E / 2)
        + Complex.I * Complex.ofReal
            (S.pair P.omega (ch.chOne E) - S.pair P.omega P.B * ch.rank E) := by
  rw [centralCharge_apply_twisted]
  simp only [twist_chOne, twist_chTwo, DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
  push_cast
  ring

/-- The intrinsic charge restricts to the existing scalar-twist formula on
the rank-one slice `B = beta H`, `omega = alpha H`.

Thus the old compressed coordinates remain a valid downstream interface; they
are no longer asked to represent an arbitrary `B`-field. -/
theorem centralCharge_rankOne_eq
    (S : DivisorSpace D) (H : D) (alpha beta : ℝ) (E : N) :
    ch.centralCharge S (StabilityParameters.rankOne H alpha beta) E =
      ((ch.coordinatesAt S H).twistByScalar beta).centralCharge alpha E := by
  apply Complex.ext
  · simp only [centralCharge, ChargeCoordinates.centralCharge_re]
    simp [StabilityParameters.rankOne, chargeCoordinates, coordinatesAt,
      DivisorSpace.pair]
    ring
  · simp only [centralCharge, ChargeCoordinates.centralCharge_im]
    simp [StabilityParameters.rankOne, chargeCoordinates, coordinatesAt,
      DivisorSpace.pair]
    ring_nf
    simp

/-- The same charge written as the Mukai pairing with
`exp(B + i omega)`.  This makes the relation with the period-domain layer
explicit without baking Mukai-specific geometry into `ChernCharacter`. -/
theorem centralCharge_eq_realPairing
    (S : DivisorSpace D) (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E =
      Complex.ofReal
          (Mukai.realPairing S.intersection
            (Mukai.expRe S.intersection P.B P.omega) (ch.toRealExtension E))
        + Complex.I * Complex.ofReal
          (Mukai.realPairing S.intersection
            (Mukai.expIm S.intersection P.B P.omega) (ch.toRealExtension E)) := by
  rw [centralCharge_apply]
  simp only [Mukai.realPairing_apply, Mukai.expRe, Mukai.expIm,
    toRealExtension_apply, DivisorSpace.pair]
  push_cast
  rw [S.intersection_symm.eq P.B P.omega]
  congr 1 <;> ring

end ChernCharacter

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
