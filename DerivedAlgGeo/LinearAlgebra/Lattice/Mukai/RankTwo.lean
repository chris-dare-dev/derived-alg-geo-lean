/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.RankTwo
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-!
# Rank-two subpairs of a Mukai extension

The wall-classification literature for K3 surfaces (Bayer–Macrì) organises
walls by the **rank-two sublattice** `⟨v, w⟩` they determine, and the first
condition asked of that sublattice is that it be *hyperbolic* — signature
`(1, 1)`, equivalently negative Gram determinant.

Everything here is arithmetic of a pair of vectors in a symmetric bilinear
`ℤ`-lattice. As in `Lattice/Mukai/Basic.lean`, **no geometric statement is made or
used.** In particular:

* the correspondence between these rank-two data and actual walls in a space of
  stability conditions is Bayer–Macrì Theorem 5.7, which is geometry and is
  **not** asserted anywhere below;
* `IsHyperbolicPair` is a numerical condition on two lattice vectors, not a
  claim that a wall exists.

Every identity below is arithmetic of two vectors under a bilinear form and
none of it is about this carrier, so it is proved once over an arbitrary
`(R, M, B)` in `BilinearForm/RankTwo.lean` and specialised here at
`pairingBilin b`. What stays is the part that is about the Mukai extension:
`HasSphericalClass` and `HasIsotropicClass`, which are phrased in the
application's vocabulary for `-2` and `0`.

## Main results

* `gram_lincomb` — the Gram determinant transforms by the square of the
  change-of-basis determinant. This is what makes `IsHyperbolicPair`
  basis-independent, and it is proved for an arbitrary `2 × 2` integer matrix,
  not only unimodular ones.
* `selfPairing_orthWitness` — the explicit class
  `⟪v,w⟫ • v - ⟪v,v⟫ • w` is orthogonal to `v` and has self-pairing
  `⟪v,v⟫ * gram`. So a hyperbolic pair with `⟪v,v⟫ > 0` carries an explicit
  negative direction orthogonal to `v`: the signature-`(1,1)` witness, with no
  appeal to real coefficients or diagonalisation.
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-- The Gram determinant of the pair `(v, w)`. -/
def gram (v w : MukaiLattice N) : ℤ := BilinearForm.gram (pairingBilin b) v w

theorem gram_apply (v w : MukaiLattice N) :
    gram b v w = selfPairing b v * selfPairing b w - pairing b v w ^ 2 := rfl

theorem gram_comm (hb : ∀ x y : N, b x y = b y x) (v w : MukaiLattice N) :
    gram b v w = gram b w v :=
  BilinearForm.gram_comm (pairingBilin b) (fun x y => pairing_comm b hb x y) v w

@[simp]
theorem gram_zero_left (w : MukaiLattice N) : gram b (0 : MukaiLattice N) w = 0 :=
  BilinearForm.gram_zero_left (pairingBilin b) w

@[simp]
theorem gram_zero_right (v : MukaiLattice N) : gram b v (0 : MukaiLattice N) = 0 :=
  BilinearForm.gram_zero_right (pairingBilin b) v

/-! ### Expansion along a pair -/

/-- The pairing of two integer combinations of `v` and `w`. -/
theorem pairing_lincomb (hb : ∀ x y : N, b x y = b y x) (a₁ a₂ a₃ a₄ : ℤ)
    (v w : MukaiLattice N) :
    pairing b (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = a₁ * a₃ * selfPairing b v + (a₁ * a₄ + a₂ * a₃) * pairing b v w
        + a₂ * a₄ * selfPairing b w :=
  BilinearForm.apply_lincomb (pairingBilin b)
    (fun x y => pairing_comm b hb x y) a₁ a₂ a₃ a₄ v w

/-- The self-pairing of an integer combination: the binary quadratic form
attached to the pair `(v, w)`. -/
theorem selfPairing_lincomb (hb : ∀ x y : N, b x y = b y x) (a₁ a₂ : ℤ)
    (v w : MukaiLattice N) :
    selfPairing b (a₁ • v + a₂ • w)
      = a₁ ^ 2 * selfPairing b v + 2 * (a₁ * a₂) * pairing b v w
        + a₂ ^ 2 * selfPairing b w :=
  BilinearForm.self_lincomb (pairingBilin b)
    (fun x y => pairing_comm b hb x y) a₁ a₂ v w

/-- **Change of basis multiplies the Gram determinant by the square of the
determinant.**

Stated for an arbitrary integer matrix `!![a₁, a₃; a₂, a₄]`, so it covers
degenerate substitutions as well as unimodular ones. -/
theorem gram_lincomb (hb : ∀ x y : N, b x y = b y x) (a₁ a₂ a₃ a₄ : ℤ)
    (v w : MukaiLattice N) :
    gram b (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = (a₁ * a₄ - a₂ * a₃) ^ 2 * gram b v w :=
  BilinearForm.gram_lincomb (pairingBilin b)
    (fun x y => pairing_comm b hb x y) a₁ a₂ a₃ a₄ v w

/-! ### Hyperbolic pairs -/

/-- Negative Gram determinant: the rank-two form spanned by `v` and `w` is
indefinite. For a rank-two lattice this is signature `(1, 1)`.

A numerical condition on two vectors. It is **not** a claim that a wall exists
in any space of stability conditions. -/
def IsHyperbolicPair (v w : MukaiLattice N) : Prop :=
  BilinearForm.IsHyperbolicPair (pairingBilin b) v w

theorem isHyperbolicPair_iff (v w : MukaiLattice N) :
    IsHyperbolicPair b v w ↔ selfPairing b v * selfPairing b w < pairing b v w ^ 2 :=
  BilinearForm.isHyperbolicPair_iff (pairingBilin b) v w

/-- The binary quadratic form attached to a hyperbolic pair has positive
discriminant, i.e. it is indefinite. -/
theorem discr_pos_of_isHyperbolicPair {v w : MukaiLattice N}
    (h : IsHyperbolicPair b v w) :
    0 < 4 * (pairing b v w ^ 2 - selfPairing b v * selfPairing b w) :=
  BilinearForm.discr_pos_of_isHyperbolicPair (pairingBilin b) h

theorem gram_ne_zero_of_isHyperbolicPair {v w : MukaiLattice N}
    (h : IsHyperbolicPair b v w) : gram b v w ≠ 0 :=
  BilinearForm.gram_ne_zero_of_isHyperbolicPair (pairingBilin b) h

/-- A hyperbolic pair has nonzero first entry. -/
theorem ne_zero_left_of_isHyperbolicPair {v w : MukaiLattice N}
    (h : IsHyperbolicPair b v w) : v ≠ 0 :=
  BilinearForm.ne_zero_left_of_isHyperbolicPair (pairingBilin b) h

/-- A hyperbolic pair has nonzero second entry. -/
theorem ne_zero_right_of_isHyperbolicPair {v w : MukaiLattice N}
    (h : IsHyperbolicPair b v w) : w ≠ 0 :=
  BilinearForm.ne_zero_right_of_isHyperbolicPair (pairingBilin b) h

theorem isHyperbolicPair_comm (hb : ∀ x y : N, b x y = b y x) (v w : MukaiLattice N) :
    IsHyperbolicPair b v w ↔ IsHyperbolicPair b w v :=
  BilinearForm.isHyperbolicPair_comm (pairingBilin b)
    (fun x y => pairing_comm b hb x y) v w

/-- Being hyperbolic survives any change of basis of determinant `±1`. -/
theorem isHyperbolicPair_lincomb (hb : ∀ x y : N, b x y = b y x) {a₁ a₂ a₃ a₄ : ℤ}
    (hd : (a₁ * a₄ - a₂ * a₃) ^ 2 = 1) {v w : MukaiLattice N}
    (h : IsHyperbolicPair b v w) :
    IsHyperbolicPair b (a₁ • v + a₂ • w) (a₃ • v + a₄ • w) :=
  BilinearForm.isHyperbolicPair_lincomb (pairingBilin b)
    (fun x y => pairing_comm b hb x y) hd h

/-! ### The orthogonal negative direction

For a hyperbolic pair with `⟪v, v⟫ > 0`, the class below is an explicit
integral vector orthogonal to `v` with negative self-pairing. This is the
signature-`(1, 1)` witness in integral form: no real coefficients, no
diagonalisation, no appeal to Sylvester's law. -/

/-- `⟪v, w⟫ • v - ⟪v, v⟫ • w`, the projection of `w` off `v` cleared of
denominators. -/
def orthWitness (v w : MukaiLattice N) : MukaiLattice N :=
  BilinearForm.orthWitness (pairingBilin b) v w

theorem orthWitness_apply (v w : MukaiLattice N) :
    orthWitness b v w = pairing b v w • v - selfPairing b v • w := rfl

/-- The witness is orthogonal to `v`. Needs no symmetry hypothesis. -/
theorem pairing_orthWitness (v w : MukaiLattice N) :
    pairing b v (orthWitness b v w) = 0 :=
  BilinearForm.apply_orthWitness (pairingBilin b) v w

theorem selfPairing_orthWitness (hb : ∀ x y : N, b x y = b y x) (v w : MukaiLattice N) :
    selfPairing b (orthWitness b v w) = selfPairing b v * gram b v w :=
  BilinearForm.self_orthWitness (pairingBilin b)
    (fun x y => pairing_comm b hb x y) v w

/-- **The signature witness.** If the pair is hyperbolic and `v` has positive
square, the explicit class `orthWitness b v w` is orthogonal to `v` and has
strictly negative square. -/
theorem selfPairing_orthWitness_neg (hb : ∀ x y : N, b x y = b y x)
    {v w : MukaiLattice N} (hv : 0 < selfPairing b v)
    (h : IsHyperbolicPair b v w) :
    selfPairing b (orthWitness b v w) < 0 :=
  BilinearForm.self_orthWitness_neg (pairingBilin b)
    (fun x y => pairing_comm b hb x y) hv h

/-- The witness is nonzero whenever it has nonzero square. -/
theorem orthWitness_ne_zero (hb : ∀ x y : N, b x y = b y x)
    {v w : MukaiLattice N} (hv : 0 < selfPairing b v)
    (h : IsHyperbolicPair b v w) :
    orthWitness b v w ≠ 0 :=
  BilinearForm.orthWitness_ne_zero (pairingBilin b)
    (fun x y => pairing_comm b hb x y) hv h

/-! ### Numerical wall data

The predicates the Bayer–Macrì classification is phrased in terms of, as
conditions on the rank-two datum alone. Which geometric wall type each
corresponds to is Theorem 5.7 of that paper and is **not** formalised: it needs
moduli of stable objects.

`HasSphericalClass` and `HasIsotropicClass` stay here rather than moving to the
neutral owner: they are phrased in `IsSpherical` and `IsIsotropic`, which are
this application's vocabulary for `-2` and `0`. -/

/-- The set of integer combinations of `v` and `w`. -/
def pairSpan (v w : MukaiLattice N) : Set (MukaiLattice N) :=
  BilinearForm.pairSpan (R := ℤ) v w

theorem mem_pairSpan_left (v w : MukaiLattice N) : v ∈ pairSpan v w :=
  BilinearForm.mem_pairSpan_left (R := ℤ) v w

theorem mem_pairSpan_right (v w : MukaiLattice N) : w ∈ pairSpan v w :=
  BilinearForm.mem_pairSpan_right (R := ℤ) v w

theorem orthWitness_mem_pairSpan (v w : MukaiLattice N) :
    orthWitness b v w ∈ pairSpan v w :=
  BilinearForm.orthWitness_mem_pairSpan (pairingBilin b) v w

/-- The rank-two datum carries a spherical class. -/
def HasSphericalClass (v w : MukaiLattice N) : Prop :=
  ∃ x ∈ pairSpan v w, IsSpherical b x

/-- The rank-two datum carries a nonzero isotropic class. -/
def HasIsotropicClass (v w : MukaiLattice N) : Prop :=
  ∃ x ∈ pairSpan v w, x ≠ 0 ∧ IsIsotropic b x

/-- A hyperbolic pair with `⟪v, v⟫ > 0` carries an explicit nonzero class of
negative square. -/
theorem exists_neg_selfPairing_of_isHyperbolicPair (hb : ∀ x y : N, b x y = b y x)
    {v w : MukaiLattice N} (hv : 0 < selfPairing b v)
    (h : IsHyperbolicPair b v w) :
    ∃ x ∈ pairSpan v w, x ≠ 0 ∧ selfPairing b x < 0 :=
  BilinearForm.exists_neg_self_of_isHyperbolicPair (pairingBilin b)
    (fun x y => pairing_comm b hb x y) hv h

end Mukai
