/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Cone

/-!
# Homogeneous maps of dg cones

The degree-zero cone lift in `Pretriangulated.Lift` is sufficient for the
ordinary homotopy category, but not for constructing a dg functor objectwise
by cones.  A dg functor must map every homogeneous morphism, not only closed
degree-zero ones.

For vertical maps `a` and `b` of degree `p`, a homogeneous square carries a
degree-`p-1` homotopy with boundary

`d k = (-1)^p (f₁ ≫ b - a ≫ f₂)`.

The induced cone map has degree `p`.  Its source-component term is multiplied
by `(-1)^p`; this sign is forced by the diagrammatic Leibniz convention.  With
it, differentiating the lift of a homogeneous square gives the strict lift of
`d a` and `d b` (`homogeneousLift_d`); the homotopy contributes exactly the
term that cancels the failure of the square to commute.

This file is the single owner of the cone lift.  The degree-zero
`IsConeOf.lift` of `Pretriangulated.Lift` is `homogeneousLift 0`, and
`HomotopySquare` there is a `HomogeneousSquare` of degree zero whose vertical
maps are closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace DGCategory

/-- A homogeneous homotopy-commutative square between closed degree-zero
arrows.  No closedness is imposed on the vertical maps: their differentials
are needed when the square is used as the value of a dg functor on an
arbitrary homogeneous morphism. -/
structure HomogeneousSquare
    {X₁ Y₁ X₂ Y₂ : C}
    (f₁ : (dgHom X₁ Y₁).X 0) (f₂ : (dgHom X₂ Y₂).X 0)
    (p : ℤ) (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p) where
  /-- The chosen homotopy has degree one below the vertical maps. -/
  homotopy : (dgHom X₁ Y₂).X (p - 1)
  /-- The signed boundary equation. -/
  homotopy_boundary :
    ((dgHom X₁ Y₂).d (p - 1) p).hom homotopy =
      p.negOnePow •
        (dgComp 0 p p (by omega) f₁ b -
          dgComp p 0 p (by omega) a f₂)

namespace HomogeneousSquare

/-- A strictly commuting homogeneous square, with zero homotopy. -/
def strict
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {p : ℤ} {a : (dgHom X₁ X₂).X p} {b : (dgHom Y₁ Y₂).X p}
    (h : dgComp 0 p p (by omega) f₁ b =
      dgComp p 0 p (by omega) a f₂) :
    HomogeneousSquare f₁ f₂ p a b where
  homotopy := 0
  homotopy_boundary := by
    rw [map_zero, h, sub_self, smul_zero]

@[simp]
theorem strict_homotopy
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {p : ℤ} {a : (dgHom X₁ X₂).X p} {b : (dgHom Y₁ Y₂).X p}
    (h : dgComp 0 p p (by omega) f₁ b =
      dgComp p 0 p (by omega) a f₂) :
    (strict h).homotopy = 0 :=
  rfl

end HomogeneousSquare

end DGCategory

namespace IsConeOf

variable {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
  {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
  (hc₁ : IsConeOf f₁ Z₁) (hc₂ : IsConeOf f₂ Z₂)

private lemma hom_units_smul {M N : AddCommGrpCat.{v}}
    (φ : M ⟶ N) (c : ℤˣ) (x : M) :
    φ.hom (c • x) = c • φ.hom x := by
  simp [Units.smul_def, map_zsmul]

private lemma dgComp_units_smul_left {W X Y : C}
    (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom W X).X p) (g : (dgHom X Y).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

private lemma dgComp_units_smul_right {W X Y : C}
    (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom W X).X p) (g : (dgHom X Y).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- Leibniz with the two successor degrees named independently.

The primitive axiom writes them as `p + 1` and `q + 1`.  Naming equal degrees
before eliminating the equalities lets cone calculations use the fibres
`p - 1 ⟶ p` without dependent casts. -/
private lemma dgComp_leibniz_general {W X Y : C}
    (p q p' q' r r' : ℤ) (hp : p + 1 = p') (hq : q + 1 = q')
    (h : p + q = r) (hr : r + 1 = r')
    (f : (dgHom W X).X p) (g : (dgHom X Y).X q) :
    ((dgHom W Y).d r r').hom (dgComp p q r h f g) =
      dgComp p q' r' (by omega) f (((dgHom X Y).d q q').hom g) +
        q.negOnePow • dgComp p' q r' (by omega)
          (((dgHom W X).d p p').hom f) g := by
  cases hp
  cases hq
  exact DGCategory.dgComp_leibniz p q r r' h hr f g

/-- The homogeneous lift of a homotopy-commutative square to its chosen cone
objects.  The first term has the Koszul sign forced by differentiation. -/
noncomputable def homogeneousLift (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (k : (dgHom X₁ Y₂).X (p - 1)) :
    (dgHom Z₁ Z₂).X p :=
  p.negOnePow •
      dgComp 1 (p - 1) p (by omega) hc₁.fst
        (dgComp p (-1) (p - 1) (by omega) a hc₂.inl) +
    dgComp 0 p p (by omega) hc₁.snd
      (dgComp p 0 p (by omega) b hc₂.inr) +
    dgComp 1 (p - 1) p (by omega) hc₁.fst
      (dgComp (p - 1) 0 (p - 1) (by omega) k hc₂.inr)

/-- A homogeneous cone lift restricts to `b` on the target inclusion. -/
lemma inr_comp_homogeneousLift (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (k : (dgHom X₁ Y₂).X (p - 1)) :
    dgComp 0 p p (by omega) hc₁.inr (hc₁.homogeneousLift hc₂ p a b k) =
      dgComp p 0 p (by omega) b hc₂.inr := by
  rw [homogeneousLift, map_add, map_add]
  simp only [Units.smul_def, map_zsmul]
  rw [← dgComp_assoc 0 1 (p - 1) 1 p p (by omega) (by omega) (by omega),
    hc₁.inr_comp_fst,
    ← dgComp_assoc 0 0 p 0 p p (by omega) (by omega) (by omega),
    hc₁.inr_comp_snd, dgId_comp,
    ← dgComp_assoc 0 1 (p - 1) 1 p p (by omega) (by omega) (by omega),
    hc₁.inr_comp_fst]
  simp

/-- `inr_comp_homogeneousLift` with an arbitrary common result-degree name.
This form is convenient in graded naturality statements, whose composition
witnesses need not normalize their result index syntactically. -/
lemma inr_comp_homogeneousLift_general (p r : ℤ)
    (h0p : 0 + p = r) (hp0 : p + 0 = r)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (k : (dgHom X₁ Y₂).X (p - 1)) :
    dgComp 0 p r h0p hc₁.inr (hc₁.homogeneousLift hc₂ p a b k) =
      dgComp p 0 r hp0 b hc₂.inr := by
  have hr : r = p := by omega
  cases hr
  exact hc₁.inr_comp_homogeneousLift hc₂ p a b k

/-- The shifted source inclusion is graded-natural for strict homogeneous
cone lifts.  The factor `(-1)^p` is exactly the Koszul sign later required by
the degree-`-1` natural transformation from the source functor to its cone. -/
lemma inl_comp_homogeneousLift_strict (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p) :
    dgComp (-1) p (p - 1) (by omega) hc₁.inl
        (hc₁.homogeneousLift hc₂ p a b 0) =
      p.negOnePow • dgComp p (-1) (p - 1) (by omega) a hc₂.inl := by
  rw [homogeneousLift, map_add, map_add]
  simp only [map_zero, AddMonoidHom.zero_apply,
    add_zero, dgComp_units_smul_right]
  rw [← DGCategory.dgComp_assoc (-1) 1 (p - 1) 0 p (p - 1)
      (by omega) (by omega) (by omega),
    hc₁.inl_comp_fst, DGCategory.dgId_comp,
    ← DGCategory.dgComp_assoc (-1) 0 p (-1) p (p - 1)
      (by omega) (by omega) (by omega),
    hc₁.inl_comp_snd]
  simp

/-- `inl_comp_homogeneousLift_strict` with an arbitrary common result-degree
name, for direct use in degree-`-1` graded naturality. -/
lemma inl_comp_homogeneousLift_strict_general (p r : ℤ)
    (hm1p : -1 + p = r) (hpm1 : p + -1 = r)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p) :
    dgComp (-1) p r hm1p hc₁.inl
        (hc₁.homogeneousLift hc₂ p a b 0) =
      p.negOnePow • dgComp p (-1) r hpm1 a hc₂.inl := by
  have hr : r = p - 1 := by omega
  cases hr
  exact hc₁.inl_comp_homogeneousLift_strict hc₂ p a b

/-- At degree zero with zero homotopy, the homogeneous lift of the identity
square is the identity of the cone. -/
private lemma homogeneousLift_id_aux (t : ℤ) (ht : t = -1)
    (h₁ : 1 + t = 0) (h₂ : 0 + (-1) = t) (h₃ : t + 0 = t) :
    dgComp 1 t 0 h₁ hc₁.fst
          (dgComp 0 (-1) t h₂ (dgId X₁) hc₁.inl) +
        dgComp 0 0 0 (by omega) hc₁.snd
          (dgComp 0 0 0 (by omega) (dgId Y₁) hc₁.inr) +
      dgComp 1 t 0 h₁ hc₁.fst
        (dgComp t 0 t h₃ 0 hc₁.inr) = dgId Z₁ := by
  cases ht
  rw [DGCategory.dgId_comp (-1) hc₁.inl,
    DGCategory.dgId_comp 0 hc₁.inr]
  simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
  exact hc₁.fst_inl_add_snd_inr

lemma homogeneousLift_id :
    hc₁.homogeneousLift hc₁ 0 (dgId X₁) (dgId Y₁) 0 = dgId Z₁ := by
  rw [homogeneousLift, Int.negOnePow_zero, one_smul]
  exact homogeneousLift_id_aux hc₁ (0 - 1) (by omega)
    (by omega) (by omega) (by omega)

/-- The homogeneous lift of the zero square is zero. -/
@[simp]
lemma homogeneousLift_zero (p : ℤ) :
    hc₁.homogeneousLift hc₂ p 0 0 0 = 0 := by
  simp [homogeneousLift]

/-- The strict homogeneous lift is additive in the vertical maps. -/
lemma homogeneousLift_strict_add (p : ℤ)
    (a a' : (dgHom X₁ X₂).X p) (b b' : (dgHom Y₁ Y₂).X p) :
    hc₁.homogeneousLift hc₂ p (a + a') (b + b') 0 =
      hc₁.homogeneousLift hc₂ p a b 0 +
        hc₁.homogeneousLift hc₂ p a' b' 0 := by
  simp [homogeneousLift, map_add, smul_add]
  abel

/-- The source projection reads the signed source component of a homogeneous
cone lift.  The homotopy term dies against `inr ≫ fst = 0`, so no strictness
is needed. -/
lemma homogeneousLift_comp_fst (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (k : (dgHom X₁ Y₂).X (p - 1)) :
    dgComp p 1 (p + 1) (by omega)
        (hc₁.homogeneousLift hc₂ p a b k) hc₂.fst =
      p.negOnePow • dgComp 1 p (p + 1) (by omega) hc₁.fst a := by
  rw [homogeneousLift, map_add, map_add]
  simp only [AddMonoidHom.add_apply]
  rw [dgComp_units_smul_left]
  rw [DGCategory.dgComp_assoc 1 (p - 1) 1 p p (p + 1)
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc p (-1) 1 (p - 1) 0 p
      (by omega) (by omega) (by omega),
    hc₂.inl_comp_fst, DGCategory.dgComp_id,
    DGCategory.dgComp_assoc 0 p 1 p (p + 1) (p + 1)
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc p 0 1 p 1 (p + 1)
      (by omega) (by omega) (by omega),
    hc₂.inr_comp_fst,
    DGCategory.dgComp_assoc 1 (p - 1) 1 p p (p + 1)
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc (p - 1) 0 1 (p - 1) 1 p
      (by omega) (by omega) (by omega),
    hc₂.inr_comp_fst]
  simp

/-- The target projection reads the target component of a strict homogeneous
cone lift. -/
lemma homogeneousLift_comp_snd (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p) :
    dgComp p 0 p (by omega)
        (hc₁.homogeneousLift hc₂ p a b 0) hc₂.snd =
      dgComp 0 p p (by omega) hc₁.snd b := by
  rw [homogeneousLift, map_add, map_add]
  simp only [AddMonoidHom.add_apply]
  rw [dgComp_units_smul_left]
  simp only [map_zero, AddMonoidHom.zero_apply]
  rw [DGCategory.dgComp_assoc 1 (p - 1) 0 p (p - 1) p
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc p (-1) 0 (p - 1) (-1) (p - 1)
      (by omega) (by omega) (by omega),
    hc₂.inl_comp_snd,
    DGCategory.dgComp_assoc 0 p 0 p p p
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc p 0 0 p 0 p
      (by omega) (by omega) (by omega),
    hc₂.inr_comp_snd, DGCategory.dgComp_id]
  simp

/-- Two homogeneous maps into a cone are equal when their two cone
projections agree.  This is the all-degree analogue of extensionality for a
binary direct sum, derived from the cone's splitting of the identity. -/
lemma homogeneous_ext (p : ℤ) {u v : (dgHom Z₁ Z₂).X p}
    (hfst : dgComp p 1 (p + 1) (by omega) u hc₂.fst =
      dgComp p 1 (p + 1) (by omega) v hc₂.fst)
    (hsnd : dgComp p 0 p (by omega) u hc₂.snd =
      dgComp p 0 p (by omega) v hc₂.snd) :
    u = v := by
  rw [← DGCategory.dgComp_id p u, ← DGCategory.dgComp_id p v,
    ← hc₂.fst_inl_add_snd_inr, map_add, map_add]
  rw [← DGCategory.dgComp_assoc p 1 (-1) (p + 1) 0 p
      (by omega) (by omega) (by omega),
    ← DGCategory.dgComp_assoc p 0 0 p 0 p
      (by omega) (by omega) (by omega),
    hfst, hsnd,
    DGCategory.dgComp_assoc p 1 (-1) (p + 1) 0 p
      (by omega) (by omega) (by omega),
    DGCategory.dgComp_assoc p 0 0 p 0 p
      (by omega) (by omega) (by omega)]

section Composition

variable {X₃ Y₃ Z₃ : C} {f₃ : (dgHom X₃ Y₃).X 0}
  (hc₃ : IsConeOf f₃ Z₃)

/-- Strict homogeneous cone lifts preserve graded composition.

This theorem is the multiplicativity law required by the objectwise-cone dg
functor.  Its proof uses the two projection identities, so the sign is checked
once at the canonical cone boundary rather than by re-expanding three cone
formulas. -/
lemma homogeneousLift_strict_comp (p q : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (c : (dgHom X₂ X₃).X q) (d : (dgHom Y₂ Y₃).X q) :
    dgComp p q (p + q) (by omega)
        (hc₁.homogeneousLift hc₂ p a b 0)
        (hc₂.homogeneousLift hc₃ q c d 0) =
      hc₁.homogeneousLift hc₃ (p + q)
        (dgComp p q (p + q) (by omega) a c)
        (dgComp p q (p + q) (by omega) b d) 0 := by
  apply hc₃.homogeneous_ext (p + q)
  · rw [DGCategory.dgComp_assoc p q 1 (p + q) (q + 1) (p + q + 1)
        (by omega) (by omega) (by omega),
      hc₂.homogeneousLift_comp_fst hc₃ q c d,
      dgComp_units_smul_right,
      ← DGCategory.dgComp_assoc p 1 q (p + 1) (q + 1) (p + q + 1)
        (by omega) (by omega) (by omega),
      hc₁.homogeneousLift_comp_fst hc₂ p a b,
      dgComp_units_smul_left, smul_smul,
      DGCategory.dgComp_assoc 1 p q (p + 1) (p + q) (p + q + 1)
        (by omega) (by omega) (by omega),
      hc₁.homogeneousLift_comp_fst hc₃ (p + q)
        (dgComp p q (p + q) (by omega) a c)
        (dgComp p q (p + q) (by omega) b d),
      Int.negOnePow_add]
    simp [mul_comm]
  · rw [DGCategory.dgComp_assoc p q 0 (p + q) q (p + q)
        (by omega) (by omega) (by omega),
      hc₂.homogeneousLift_comp_snd hc₃ q c d,
      ← DGCategory.dgComp_assoc p 0 q p q (p + q)
        (by omega) (by omega) (by omega),
      hc₁.homogeneousLift_comp_snd hc₂ p a b,
      DGCategory.dgComp_assoc 0 p q p (p + q) (p + q)
        (by omega) (by omega) (by omega),
      hc₁.homogeneousLift_comp_snd hc₃ (p + q)
        (dgComp p q (p + q) (by omega) a c)
        (dgComp p q (p + q) (by omega) b d)]

end Composition

private lemma homogeneousLift_succ_aux (p t : ℤ) (ht : t = p)
    (h₁ : 1 + t = p + 1) (h₂ : p + 1 + -1 = t)
    (a : (dgHom X₁ X₂).X (p + 1)) (b : (dgHom Y₁ Y₂).X (p + 1)) :
    (p + 1).negOnePow •
          dgComp 1 t (p + 1) h₁ hc₁.fst
            (dgComp (p + 1) (-1) t h₂ a hc₂.inl) +
        dgComp 0 (p + 1) (p + 1) (by omega) hc₁.snd
          (dgComp (p + 1) 0 (p + 1) (by omega) b hc₂.inr) =
      (p + 1).negOnePow •
          dgComp 1 p (p + 1) (by omega) hc₁.fst
            (dgComp (p + 1) (-1) p (by omega) a hc₂.inl) +
        dgComp 0 (p + 1) (p + 1) (by omega) hc₁.snd
          (dgComp (p + 1) 0 (p + 1) (by omega) b hc₂.inr) := by
  cases ht
  rfl

/-- The degree-`p+1` strict lift written with predecessor degree `p`.

This isolates the only dependent normalization between `(p + 1) - 1` and
`p`; consumers can calculate entirely in the latter fibre. -/
private lemma homogeneousLift_succ (p : ℤ)
    (a : (dgHom X₁ X₂).X (p + 1)) (b : (dgHom Y₁ Y₂).X (p + 1)) :
    hc₁.homogeneousLift hc₂ (p + 1) a b 0 =
      (p + 1).negOnePow •
          dgComp 1 p (p + 1) (by omega) hc₁.fst
            (dgComp (p + 1) (-1) p (by omega) a hc₂.inl) +
        dgComp 0 (p + 1) (p + 1) (by omega) hc₁.snd
          (dgComp (p + 1) 0 (p + 1) (by omega) b hc₂.inr) := by
  rw [homogeneousLift]
  simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
  exact homogeneousLift_succ_aux hc₁ hc₂ p (p + 1 - 1)
    (by omega) (by omega) (by omega) a b

/-- **The homogeneous lift of a homotopy-commutative square commutes with the
differential.**  The differential of the degree-`p` lift is the strict
degree-`p+1` lift of the differentials of its two vertical maps: the
`a`-term's differential is `fst ≫ a ≫ f₂ ≫ inr`, the `b`-term's is
`-(fst ≫ f₁) ≫ b ≫ inr` -- the cone's own correction -- and the boundary of
the homotopy is exactly their difference, so the three cancel and only the
`d a` and `d b` components survive.

This is the chain-map identity behind every cone functor in the repository;
the strict case `homogeneousLift_strict_d` and the degree-zero
`IsConeOf.lift_closed` are both instances of it. -/
lemma homogeneousLift_d (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (s : DGCategory.HomogeneousSquare f₁ f₂ p a b) :
    ((dgHom Z₁ Z₂).d p (p + 1)).hom
        (hc₁.homogeneousLift hc₂ p a b s.homotopy) =
      hc₁.homogeneousLift hc₂ (p + 1)
        (((dgHom X₁ X₂).d p (p + 1)).hom a)
        (((dgHom Y₁ Y₂).d p (p + 1)).hom b) 0 := by
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  have hA : ((dgHom X₁ Z₂).d (p - 1) p).hom
        (dgComp p (-1) (p - 1) (by omega) a hc₂.inl) =
      dgComp p 0 p (by omega) a
          (dgComp 0 0 0 (by omega) f₂ hc₂.inr) -
        dgComp (p + 1) (-1) p (by omega)
          (((dgHom X₁ X₂).d p (p + 1)).hom a) hc₂.inl := by
    have h := dgComp_leibniz_general p (-1) (p + 1) 0 (p - 1) p
      (by omega) (by omega) (by omega) (by omega) a hc₂.inl
    rw [hc₂.δ_inl] at h
    simpa only [hneg, Units.neg_smul, one_smul, sub_eq_add_neg] using h
  have hB : ((dgHom Y₁ Z₂).d p (p + 1)).hom
        (dgComp p 0 p (by omega) b hc₂.inr) =
      dgComp (p + 1) 0 (p + 1) (by omega)
        (((dgHom Y₁ Y₂).d p (p + 1)).hom b) hc₂.inr := by
    have h := dgComp_leibniz_general p 0 (p + 1) 1 p (p + 1)
      (by omega) (by omega) (by omega) (by omega) b hc₂.inr
    rw [hc₂.inr_closed] at h
    simpa using h
  have hK : ((dgHom X₁ Z₂).d (p - 1) p).hom
        (dgComp (p - 1) 0 (p - 1) (by omega) s.homotopy hc₂.inr) =
      dgComp p 0 p (by omega)
        (((dgHom X₁ Y₂).d (p - 1) p).hom s.homotopy) hc₂.inr := by
    have h := dgComp_leibniz_general (p - 1) 0 p 1 (p - 1) p
      (by omega) (by omega) (by omega) (by omega) s.homotopy hc₂.inr
    rw [hc₂.inr_closed] at h
    simpa using h
  have hT₁ : ((dgHom Z₁ Z₂).d p (p + 1)).hom
        (p.negOnePow •
          dgComp 1 (p - 1) p (by omega) hc₁.fst
            (dgComp p (-1) (p - 1) (by omega) a hc₂.inl)) =
      p.negOnePow •
        dgComp 1 p (p + 1) (by omega) hc₁.fst
          (dgComp p 0 p (by omega) a
              (dgComp 0 0 0 (by omega) f₂ hc₂.inr) -
            dgComp (p + 1) (-1) p (by omega)
              (((dgHom X₁ X₂).d p (p + 1)).hom a) hc₂.inl) := by
    rw [hom_units_smul]
    have h := dgComp_leibniz_general 1 (p - 1) 2 p p (p + 1)
      (by omega) (by omega) (by omega) (by omega) hc₁.fst
        (dgComp p (-1) (p - 1) (by omega) a hc₂.inl)
    rw [h, hA, hc₁.delta_fst]
    simp
  have hT₂ : ((dgHom Z₁ Z₂).d p (p + 1)).hom
        (dgComp 0 p p (by omega) hc₁.snd
          (dgComp p 0 p (by omega) b hc₂.inr)) =
      dgComp 0 (p + 1) (p + 1) (by omega) hc₁.snd
          (dgComp (p + 1) 0 (p + 1) (by omega)
            (((dgHom Y₁ Y₂).d p (p + 1)).hom b) hc₂.inr) +
        p.negOnePow •
          dgComp 1 p (p + 1) (by omega)
            (-dgComp 1 0 1 (by omega) hc₁.fst f₁)
            (dgComp p 0 p (by omega) b hc₂.inr) := by
    have h := dgComp_leibniz_general 0 p 1 (p + 1) p (p + 1)
      (by omega) (by omega) (by omega) (by omega) hc₁.snd
        (dgComp p 0 p (by omega) b hc₂.inr)
    rw [h, hB, hc₁.delta_snd]
  have hT₃ : ((dgHom Z₁ Z₂).d p (p + 1)).hom
        (dgComp 1 (p - 1) p (by omega) hc₁.fst
          (dgComp (p - 1) 0 (p - 1) (by omega) s.homotopy hc₂.inr)) =
      p.negOnePow •
        dgComp 1 p (p + 1) (by omega) hc₁.fst
          (dgComp p 0 p (by omega)
            (dgComp 0 p p (by omega) f₁ b - dgComp p 0 p (by omega) a f₂)
            hc₂.inr) := by
    have h := dgComp_leibniz_general 1 (p - 1) 2 p p (p + 1)
      (by omega) (by omega) (by omega) (by omega) hc₁.fst
        (dgComp (p - 1) 0 (p - 1) (by omega) s.homotopy hc₂.inr)
    rw [h, hK, s.homotopy_boundary, hc₁.delta_fst,
      dgComp_units_smul_left, dgComp_units_smul_right]
    simp
  have hfb :
      dgComp 1 p (p + 1) (by omega)
          (-dgComp 1 0 1 (by omega) hc₁.fst f₁)
          (dgComp p 0 p (by omega) b hc₂.inr) =
        -dgComp 1 p (p + 1) (by omega) hc₁.fst
          (dgComp p 0 p (by omega)
            (dgComp 0 p p (by omega) f₁ b) hc₂.inr) := by
    rw [map_neg, AddMonoidHom.neg_apply,
      DGCategory.dgComp_assoc 1 0 p 1 p (p + 1)
        (by omega) (by omega) (by omega),
      ← DGCategory.dgComp_assoc 0 p 0 p p p
        (by omega) (by omega) (by omega)]
  have hfa :
      dgComp 1 p (p + 1) (by omega) hc₁.fst
          (dgComp p 0 p (by omega) a
            (dgComp 0 0 0 (by omega) f₂ hc₂.inr)) =
        dgComp 1 p (p + 1) (by omega) hc₁.fst
          (dgComp p 0 p (by omega)
            (dgComp p 0 p (by omega) a f₂) hc₂.inr) := by
    rw [← DGCategory.dgComp_assoc p 0 0 p 0 p
      (by omega) (by omega) (by omega)]
  rw [homogeneousLift, map_add, map_add, hT₁, hT₂, hT₃, hfb,
    homogeneousLift_succ]
  simp only [smul_sub, map_sub, AddMonoidHom.sub_apply, Int.negOnePow_succ,
    Units.neg_smul, smul_neg, hfa]
  abel

/-- The strict case of `homogeneousLift_d`: with a zero homotopy the square
commutes on the nose and the lift is a chain map. -/
lemma homogeneousLift_strict_d (p : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (hsquare : dgComp 0 p p (by omega) f₁ b =
      dgComp p 0 p (by omega) a f₂) :
    ((dgHom Z₁ Z₂).d p (p + 1)).hom
        (hc₁.homogeneousLift hc₂ p a b 0) =
      hc₁.homogeneousLift hc₂ (p + 1)
        (((dgHom X₁ X₂).d p (p + 1)).hom a)
        (((dgHom Y₁ Y₂).d p (p + 1)).hom b) 0 :=
  hc₁.homogeneousLift_d hc₂ p a b (DGCategory.HomogeneousSquare.strict hsquare)

/-- The differential law for a strict homogeneous lift in arbitrary source
and target degrees.  Off the cochain-complex successor diagonal all three
differentials vanish by shape; on the diagonal this is
`homogeneousLift_strict_d`. -/
lemma homogeneousLift_strict_map_d (p q : ℤ)
    (a : (dgHom X₁ X₂).X p) (b : (dgHom Y₁ Y₂).X p)
    (hsquare : dgComp 0 p p (by omega) f₁ b =
      dgComp p 0 p (by omega) a f₂) :
    ((dgHom Z₁ Z₂).d p q).hom
        (hc₁.homogeneousLift hc₂ p a b 0) =
      hc₁.homogeneousLift hc₂ q
        (((dgHom X₁ X₂).d p q).hom a)
        (((dgHom Y₁ Y₂).d p q).hom b) 0 := by
  by_cases hpq : p + 1 = q
  · subst q
    exact hc₁.homogeneousLift_strict_d hc₂ p a b hsquare
  · have hshape : ¬(ComplexShape.up ℤ).Rel p q := by
      simpa [ComplexShape.up, ComplexShape.up'] using hpq
    rw [(dgHom Z₁ Z₂).shape p q hshape,
      (dgHom X₁ X₂).shape p q hshape,
      (dgHom Y₁ Y₂).shape p q hshape]
    simp [homogeneousLift]

end IsConeOf

end CategoryTheory
