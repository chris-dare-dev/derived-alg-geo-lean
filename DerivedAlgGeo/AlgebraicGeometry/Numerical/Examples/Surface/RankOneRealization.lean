/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialMukai
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialSupport

/-!
# The real divisor realization of a Picard-rank-one surface, and the K3 model

`Examples/Surface/RankOne.lean` builds the rational intersection ring
`ℚ[H]/(H³)` with `∫_X H² = h2`, and `K3.lean`, `ProjectivePlane.lean` and
`Abelian.lean` are three variety presentations over it.  What none of them had
was a `Surface.NumericalRealization`: a map of the rational codimension-one
piece into a real divisor space carrying the intersection form.  Without one,
every divisorial statement — the charge, the discriminants, the walls, the
support property — was conditional on a realization existing at all.

This file supplies it once, for every `h2`, and then instantiates the K3 case.

## The realization

The rational piece `N¹` is the line `ℚ·H`, so the real divisor space is `ℝ`
with `H` as the unit vector and the intersection form

```text
(x, y) ↦ h2 · x · y.
```

`surfaceRealization` packages that, and `surfaceChernCharacter_*` reads off the
induced real Chern character in the coordinates `(r, c, s)` of `SurfaceNum`:
rank `r`, first Chern class `c`, and `∫ch₂ = h2 · s`.  The last one is worth
stating explicitly, because `SurfaceNum` records the *coefficient* of `H²` and
the divisorial layer wants its *integral*.

## Hodge definiteness is free in Picard rank one

`DivisorSpace.HodgeDefinite` asks for `ω² > 0` together with negative
definiteness on `ω^⊥`.  On a line with a nondegenerate form the orthogonal
complement of a nonzero vector is zero, so the second condition holds with no
content and the first is `h2 · t² > 0`.  `surfaceHodgeDefinite` is therefore a
theorem, not a supplied certificate, and it is what makes the support property
of `Stability/DivisorialSupport.lean` fire on a model rather than on a
hypothesis.

That is the whole point of doing rank one first: it separates "the support
property argument is correct" from "the Hodge input is available", and only the
second is hard.  A Picard rank three example, where `ω^⊥` is a genuine negative
definite plane, is the next step and lives in `BlowUpPlane.lean`.

## What is not claimed

The carrier is not identified with `K_num(X)` for a geometric K3, and no
Chern-character map from coherent sheaves is constructed.  The
Bogomolov--Gieseker input is `k3BogomolovSanity`, whose `Semistable` predicate
is defined to be the conclusion; the support property below is therefore a
statement about the locus of classes of nonnegative discriminant, which is
exactly what it says, and it is **not** a theorem about semistable sheaves.
-/

open Submodule Set
open DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The real divisor line -/

/-- The real numerical divisor space of a Picard-rank-one surface: the line
spanned by `H`. -/
abbrev SurfaceDivisor : Type := ℝ

/-- The intersection form `(x, y) ↦ h2 · x · y` in the basis `H`. -/
def surfaceIntersectionForm (h2 : ℝ) : LinearMap.BilinForm ℝ SurfaceDivisor :=
  LinearMap.mk₂ ℝ (fun x y => h2 * x * y)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)

@[simp]
theorem surfaceIntersectionForm_apply (h2 x y : ℝ) :
    surfaceIntersectionForm h2 x y = h2 * x * y := rfl

/-- The real divisor space of a Picard-rank-one surface with `∫_X H² = h2`. -/
def surfaceDivisorSpace (h2 : ℝ) : DivisorSpace SurfaceDivisor where
  intersection := surfaceIntersectionForm h2
  intersection_symm := ⟨by intro x y; simp; ring⟩

@[simp]
theorem surfaceDivisorSpace_pair (h2 x y : ℝ) :
    (surfaceDivisorSpace h2).pair x y = h2 * x * y := rfl

/-! ### The rational divisor piece is the line `ℚ·H` -/

theorem one_lt_dim : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num

/-- The index of `H` in the power basis. -/
def idx1 : Fin surfacePB.dim := ⟨1, one_lt_dim⟩

@[simp]
theorem surfacePB_basis_idx1 : surfacePB.basis idx1 = H := by
  rw [surfacePB_basis_apply]
  simp [idx1]

theorem surfaceW_preimage_one : surfaceW ⁻¹' ({1} : Set ℕ) = ({idx1} : Set (Fin surfacePB.dim)) := by
  ext i
  constructor
  · intro hi
    have : (i : ℕ) = 1 := hi
    exact Set.mem_singleton_iff.mpr (Fin.ext this)
  · intro hi
    have : i = idx1 := hi
    show surfaceW i = 1
    rw [this]
    rfl

/-- The codimension-one piece is the rational line spanned by `H`. -/
theorem surfacePieceOne_eq_span :
    gradedPiece (⇑surfacePB.basis) surfaceW 1 = Submodule.span ℚ ({H} : Set SurfaceRing) := by
  rw [gradedPiece, surfaceW_preimage_one, Set.image_singleton, surfacePB_basis_idx1]

/-! ### The realization -/

/-- The `H`-coordinate of a rational divisor class, as a real number. -/
def surfaceDivisorClass (h2 : ℚ) :
    (surfaceNumericalRing h2).piece 1 →+ SurfaceDivisor :=
  AddMonoidHom.mk'
    (fun x => ((surfacePB.basis.coord idx1 x.1 : ℚ) : ℝ))
    (by
      intro x y
      change ((surfacePB.basis.coord idx1 (x.1 + y.1) : ℚ) : ℝ) = _
      rw [map_add]
      push_cast
      ring)

@[simp]
theorem surfaceDivisorClass_apply (h2 : ℚ) (x : (surfaceNumericalRing h2).piece 1) :
    surfaceDivisorClass h2 x = ((surfacePB.basis.coord idx1 x.1 : ℚ) : ℝ) := rfl

theorem surfaceDivisorClass_map_rat_smul (h2 : ℚ) (q : ℚ)
    (x : (surfaceNumericalRing h2).piece 1) :
    surfaceDivisorClass h2 (q • x) = (q : ℝ) • surfaceDivisorClass h2 x := by
  change ((surfacePB.basis.coord idx1 (q • x.1) : ℚ) : ℝ)
      = (q : ℝ) • ((surfacePB.basis.coord idx1 x.1 : ℚ) : ℝ)
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The `H`-coordinate of `a • H` is `a`. -/
theorem coord_idx1_smul_H (a : ℚ) : surfacePB.basis.coord idx1 (a • H) = a := by
  rw [← surfacePB_basis_idx1, Module.Basis.coord_apply, map_smul,
    Module.Basis.repr_self]
  simp

/-- A member of the codimension-one piece is a rational multiple of `H`, and its
coordinate is that multiple. -/
theorem exists_smul_H (h2 : ℚ) (x : (surfaceNumericalRing h2).piece 1) :
    x.1 = (surfacePB.basis.coord idx1 x.1) • H := by
  have hx : x.1 ∈ Submodule.span ℚ ({H} : Set SurfaceRing) := by
    rw [← surfacePieceOne_eq_span]
    exact x.2
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  rw [← ha, coord_idx1_smul_H]

/-- Multiplication in the rational ring realizes to the intersection form
`h2 · x · y`. -/
theorem surfaceDivisorClass_intersection (h2 : ℚ) (x y : (surfaceNumericalRing h2).piece 1) :
    (surfaceDivisorSpace (h2 : ℝ)).pair (surfaceDivisorClass h2 x) (surfaceDivisorClass h2 y) =
      (((surfaceNumericalRing h2).degree (x.1 * y.1) : ℚ) : ℝ) := by
  set a : ℚ := surfacePB.basis.coord idx1 x.1 with ha
  set b : ℚ := surfacePB.basis.coord idx1 y.1 with hb
  have hxy : x.1 * y.1 = (a * b) • H ^ 2 := by
    conv_lhs => rw [exists_smul_H h2 x, exists_smul_H h2 y]
    rw [smul_mul_smul_comm, ← pow_two]
  show (h2 : ℝ) * (a : ℝ) * (b : ℝ) = _
  rw [hxy]
  show _ = ((surfaceDegree h2 ((a * b) • H ^ 2) : ℚ) : ℝ)
  rw [map_smul, surfaceDegree_Hsq, smul_eq_mul]
  push_cast
  ring

/-- **The real divisor realization of a Picard-rank-one surface.** -/
def surfaceRealization (h2 : ℚ) :
    Surface.NumericalRealization (surfaceNumericalRing h2) (D := SurfaceDivisor) where
  divisorSpace := surfaceDivisorSpace (h2 : ℝ)
  divisorClass := surfaceDivisorClass h2
  map_rat_smul := surfaceDivisorClass_map_rat_smul h2
  intersection_eq := surfaceDivisorClass_intersection h2

@[simp]
theorem surfaceRealization_divisorSpace (h2 : ℚ) :
    (surfaceRealization h2).divisorSpace = surfaceDivisorSpace (h2 : ℝ) := rfl

/-- The realization sends `H` to the unit vector. -/
@[simp]
theorem surfaceDivisorClass_H (h2 : ℚ) :
    surfaceDivisorClass h2 ⟨H, H_mem_piece_one⟩ = 1 := by
  show ((surfacePB.basis.coord idx1 H : ℚ) : ℝ) = 1
  rw [← surfacePB_basis_idx1, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp

/-! ### Hodge definiteness in Picard rank one -/

/-- **Negative definiteness on `ω^⊥` is free on a line.**

The orthogonal complement of a nonzero vector for a nondegenerate form on `ℝ`
is `0`, so the definiteness clause is vacuous and only positivity of `ω²`
carries content. -/
theorem surfaceHodgeDefinite {h2 t : ℝ} (hh2 : 0 < h2) (ht : t ≠ 0) :
    (surfaceDivisorSpace h2).HodgeDefinite t where
  H_square_pos := by
    show 0 < h2 * t * t
    rw [mul_assoc]
    exact mul_pos hh2 (mul_self_pos.mpr ht)
  neg_definite x hx hxne := by
    exfalso
    apply hxne
    have hx' : h2 * t * x = 0 := hx
    have hne : h2 * t ≠ 0 := by
      have := ne_of_gt hh2
      exact mul_ne_zero this ht
    exact (mul_eq_zero.mp hx').resolve_left hne

/-! ### The K3 model -/

variable {d : ℕ}

/-- The realization of the degree-`2d` K3 model. -/
def k3Realization (d : ℕ) :
    Surface.NumericalRealization (k3NumericalVariety d).ring (D := SurfaceDivisor) :=
  surfaceRealization (2 * (d : ℚ))

@[simp]
theorem k3Realization_divisorSpace (d : ℕ) :
    (k3Realization d).divisorSpace = surfaceDivisorSpace (2 * (d : ℝ)) := by
  show surfaceDivisorSpace (((2 * (d : ℚ) : ℚ) : ℝ)) = _
  congr 1
  push_cast
  ring

/-- The realized polarization of the K3 model is the unit vector `H`. -/
@[simp]
theorem k3Realization_polarization (d : ℕ) (hd : d ≠ 0) :
    (k3Realization d).realizePolarization (k3Polarization d hd) = 1 :=
  surfaceDivisorClass_H _

/-- The real Chern character of the K3 model: rank `E 0`, first Chern class
`E 1`, and `∫ch₂ = 2d · E 2`. -/
@[simp]
theorem k3Realization_chernCharacter_rank (d : ℕ) (E : SurfaceNum) :
    (k3Realization d).chernCharacter.rank E = ((E 0 : ℤ) : ℝ) := rfl

/-- Not a `simp` lemma: the generic `NumericalRealization.chernCharacter_*`
lemmas are already `simp` and rewrite the left-hand side first, so the
normal-form linter rejects the attribute. -/
theorem k3Realization_chernCharacter_chOne (d : ℕ) (E : SurfaceNum) :
    (k3Realization d).chernCharacter.chOne E = ((E 1 : ℤ) : ℝ) := by
  show ((surfacePB.basis.coord idx1 ((k3NumericalVariety d).chComp E 1) : ℚ) : ℝ) = _
  show ((surfacePB.basis.coord idx1
    (algebraMap ℚ SurfaceRing (k3ChCoeff E 1) * H) : ℚ) : ℝ) = _
  rw [← Algebra.smul_def, coord_idx1_smul_H]
  simp [k3ChCoeff]

/-- Not a `simp` lemma: the generic `NumericalRealization.chernCharacter_*`
lemmas are already `simp` and rewrite the left-hand side first, so the
normal-form linter rejects the attribute. -/
theorem k3Realization_chernCharacter_chTwo (d : ℕ) (E : SurfaceNum) :
    (k3Realization d).chernCharacter.chTwo E = 2 * (d : ℝ) * ((E 2 : ℤ) : ℝ) := by
  show (((surfaceNumericalRing (2 * (d : ℚ))).degree
    ((k3NumericalVariety d).chComp E 2) : ℚ) : ℝ) = _
  show ((surfaceDegree (2 * (d : ℚ))
    (algebraMap ℚ SurfaceRing (k3ChCoeff E 2) * H ^ 2) : ℚ) : ℝ) = _
  rw [surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  show ((k3ChCoeff E 2 * (2 * (d : ℚ)) : ℚ) : ℝ) = _
  simp only [k3ChCoeff]
  push_cast
  ring

/-- **Hodge definiteness holds on the K3 model** at every nonzero real multiple
of `H`, with `d > 0`. -/
theorem k3HodgeDefinite {d : ℕ} (hd : d ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    (k3Realization d).divisorSpace.HodgeDefinite t := by
  rw [k3Realization_divisorSpace]
  refine surfaceHodgeDefinite ?_ ht
  have : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  linarith

/-! ### The support property, on a model rather than on hypotheses -/

/-- **The divisorial charge of the degree-`2d` K3 model has the quadratic
support property** on the locus of classes of nonnegative discriminant, at every
`(B, ω)` with `ω` a nonzero real multiple of `H`.

Both inputs of `hasQuadraticSupportProperty_semistable` are discharged here.
The Hodge input is `k3HodgeDefinite`, which is proved.  The Bogomolov input is
`k3BogomolovSanity`, whose `Semistable` predicate is *defined* to be
`0 ≤ discDegH`, so the locus below is exactly the nonnegative-discriminant
locus and **no claim is made about semistable sheaves**.

What is not tautologous is the conclusion: negative definiteness of the
`C`-discriminant on the kernel of the charge is genuine content, and it is what
the support property needs. -/
theorem k3HasQuadraticSupportProperty (d : ℕ) (hd : d ≠ 0)
    (Q : StabilityParameters SurfaceDivisor) (hQ : Q.omega ≠ 0) {C : ℝ} (hC : 0 ≤ C) :
    Support.HasQuadraticSupportProperty
      ((k3Realization d).divisorSpace.realCentralCharge Q)
      ((k3Realization d).chernCharacter.toRealExtension ''
        {E : SurfaceNum | (k3BogomolovSanity d hd).Semistable E}) :=
  (k3Realization d).hasQuadraticSupportProperty_semistable (k3Polarization d hd)
    (k3BogomolovSanity d hd) Q (k3HodgeDefinite hd hQ) hC

/-- The same conclusion in the norm-bound formulation. -/
theorem k3HasSupportProperty (d : ℕ) (hd : d ≠ 0)
    (Q : StabilityParameters SurfaceDivisor) (hQ : Q.omega ≠ 0) {C : ℝ} (hC : 0 ≤ C) :
    Support.HasSupportProperty
      ((k3Realization d).divisorSpace.realCentralCharge Q)
      ((k3Realization d).chernCharacter.toRealExtension ''
        {E : SurfaceNum | (k3BogomolovSanity d hd).Semistable E}) :=
  (k3Realization d).hasSupportProperty_semistable (k3Polarization d hd)
    (k3BogomolovSanity d hd) Q (k3HodgeDefinite hd hQ) hC

/-! ### The Mukai vector of the model -/

/-- **The realized square root of the Todd class of the model is `1 + [pt]`.**
This is `sqrtTodd_eq_k3` fired on a presentation that exists. -/
theorem k3Realization_sqrtTodd (d : ℕ) (hd : d ≠ 0) :
    (k3Realization d).sqrtTodd (V := k3NumericalVariety d) = SqrtTodd.k3 :=
  Surface.NumericalRealization.sqrtTodd_eq_k3 _ (k3_isK3 d hd)

/-- **Bridgeland's K3 charge on the model is the divisorial charge minus the
rank.** -/
theorem k3Realization_mukaiCharge (d : ℕ) (hd : d ≠ 0)
    (P : StabilityParameters SurfaceDivisor) (E : SurfaceNum) :
    (k3Realization d).chernCharacter.mukaiCharge (k3Realization d).divisorSpace
        ((k3Realization d).sqrtTodd (V := k3NumericalVariety d)) P E =
      (k3Realization d).chernCharacter.centralCharge (k3Realization d).divisorSpace P E
        - Complex.ofReal ((E 0 : ℤ) : ℝ) :=
  Surface.NumericalRealization.mukaiCharge_of_isK3 _ (k3_isK3 d hd) P E

end

end Examples

end AlgebraicGeometry.Numerical
