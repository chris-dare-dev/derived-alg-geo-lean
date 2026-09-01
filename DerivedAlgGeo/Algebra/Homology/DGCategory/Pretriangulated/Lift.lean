/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Cone

/-!
# Lifting a square to a map of cones

`dg-enhancements-e6`. `complete_distinguished_triangle_morphism` asks that a
commuting square between the first two vertices of two distinguished triangles
extend to the third. For cone triangles the extension is written down against the
splitting, and this file writes it down.

## The homotopy is the whole difficulty

If the square commuted *on the nose* the obvious candidate
`fst₁ ≫ (a ≫ inl₂) + snd₁ ≫ (b ≫ inr₂)` would already be closed. It does not:
the square commutes in `H⁰`, which means only that `f₁ ≫ b - a ≫ f₂` is a
coboundary, and the candidate's differential is exactly that difference pushed
into the cone. So the homotopy `k` witnessing it is *added to the map*, as a
third term `fst₁ ≫ (k ≫ inr₂)`, and the two contributions cancel.

That is the axiom's actual content, and it is why the lift is not unique: a
different `k` gives a different `c`, homotopic but not equal.

## Both squares are strict

Once `c` exists, neither square needs a homotopy. `inr₁ ≫ c = b ≫ inr₂` because
`inr₁` is orthogonal to `fst₁` and a section of `snd₁`, so the `k`-term and the
`a`-term both vanish. And `c ≫ toShift₂ = toShift₁ ≫ a⟦1⟧` because `inl₂ ≫ fst₂`
is the identity while `inr₂ ≫ fst₂` is zero, which kills the `b`- and `k`-terms
and leaves `mapShift`'s definition on both sides.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace IsConeOf

variable {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
  (hc₁ : IsConeOf f₁ Z₁) (hc₂ : IsConeOf f₂ Z₂)
  (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) (k : (dgHom X₁ Y₂).X (-1))

/-- The lift of a square to the cones, with the homotopy folded in. -/
noncomputable def lift : (dgHom Z₁ Z₂).X 0 :=
  dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp 0 (-1) (-1) (by omega) a hc₂.inl) +
    dgComp 0 0 0 (by omega) hc₁.snd (dgComp 0 0 0 (by omega) b hc₂.inr) +
    dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp (-1) 0 (-1) (by omega) k hc₂.inr)

/-- **The first square, strictly.** `inr₁ ≫ fst₁ = 0` kills the first and third
terms, and `inr₁ ≫ snd₁ = dgId` leaves the second. -/
lemma inr_comp_lift :
    dgComp 0 0 0 (by omega) hc₁.inr (hc₁.lift hc₂ a b k) =
      dgComp 0 0 0 (by omega) b hc₂.inr := by
  rw [lift, map_add, map_add,
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) hc₁.inr hc₁.fst
      (dgComp 0 (-1) (-1) (by omega) a hc₂.inl),
    ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hc₁.inr hc₁.snd
      (dgComp 0 0 0 (by omega) b hc₂.inr),
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) hc₁.inr hc₁.fst
      (dgComp (-1) 0 (-1) (by omega) k hc₂.inr),
    hc₁.inr_comp_fst, hc₁.inr_comp_snd, dgId_comp]
  simp

/-- **The lift is closed.** The `a`-term's differential is `fst₁ ≫ a ≫ f₂ ≫ inr₂`,
the `b`-term's is `-(fst₁ ≫ f₁) ≫ b ≫ inr₂` — the cone's own correction — and the
homotopy's term contributes their difference. Nothing else cancels them: this is
where `k` is used, and the only place it is. -/
lemma lift_closed (ha : ((dgHom X₁ X₂).d 0 1).hom a = 0)
    (hb : ((dgHom Y₁ Y₂).d 0 1).hom b = 0)
    (hk : ((dgHom X₁ Y₂).d (-1) 0).hom k =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) :
    ((dgHom Z₁ Z₂).d 0 1).hom (hc₁.lift hc₂ a b k) = 0 := by
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  have hA : ((dgHom X₁ Z₂).d (-1) 0).hom (dgComp 0 (-1) (-1) (by omega) a hc₂.inl) =
      dgComp 0 0 0 (by omega) a (dgComp 0 0 0 (by omega) f₂ hc₂.inr) := by
    have h : ((dgHom X₁ Z₂).d (-1) 0).hom (dgComp 0 (-1) (-1) (by omega) a hc₂.inl) =
        dgComp 0 0 0 (by omega) a (((dgHom X₂ Z₂).d (-1) 0).hom hc₂.inl) +
          (-1 : ℤ).negOnePow •
            dgComp 1 (-1) 0 (by omega) (((dgHom X₁ X₂).d 0 1).hom a) hc₂.inl :=
      dgComp_leibniz (X := X₁) (Y := X₂) (Z := Z₂) 0 (-1) (-1) 0 (by omega) (by omega)
        a hc₂.inl
    rw [h, hc₂.δ_inl, ha]
    simp
  have hB : ((dgHom Y₁ Z₂).d 0 1).hom (dgComp 0 0 0 (by omega) b hc₂.inr) = 0 := by
    have h : ((dgHom Y₁ Z₂).d 0 1).hom (dgComp 0 0 0 (by omega) b hc₂.inr) =
        dgComp 0 1 1 (by omega) b (((dgHom Y₂ Z₂).d 0 1).hom hc₂.inr) +
          (0 : ℤ).negOnePow •
            dgComp 1 0 1 (by omega) (((dgHom Y₁ Y₂).d 0 1).hom b) hc₂.inr :=
      dgComp_leibniz (X := Y₁) (Y := Y₂) (Z := Z₂) 0 0 0 1 (by omega) (by omega) b hc₂.inr
    rw [h, hc₂.inr_closed, hb]
    simp
  have hK : ((dgHom X₁ Z₂).d (-1) 0).hom (dgComp (-1) 0 (-1) (by omega) k hc₂.inr) =
      dgComp 0 0 0 (by omega)
        (dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) hc₂.inr := by
    have h : ((dgHom X₁ Z₂).d (-1) 0).hom (dgComp (-1) 0 (-1) (by omega) k hc₂.inr) =
        dgComp (-1) 1 0 (by omega) k (((dgHom Y₂ Z₂).d 0 1).hom hc₂.inr) +
          (0 : ℤ).negOnePow •
            dgComp 0 0 0 (by omega) (((dgHom X₁ Y₂).d (-1) 0).hom k) hc₂.inr :=
      dgComp_leibniz (X := X₁) (Y := Y₂) (Z := Z₂) (-1) 0 (-1) 0 (by omega) (by omega)
        k hc₂.inr
    rw [h, hc₂.inr_closed, hk]
    simp
  have hT1 : ((dgHom Z₁ Z₂).d 0 1).hom
        (dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp 0 (-1) (-1) (by omega) a hc₂.inl)) =
      dgComp 1 0 1 (by omega) hc₁.fst
        (dgComp 0 0 0 (by omega) a (dgComp 0 0 0 (by omega) f₂ hc₂.inr)) := by
    have h : ((dgHom Z₁ Z₂).d 0 1).hom
          (dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp 0 (-1) (-1) (by omega) a hc₂.inl)) =
        dgComp 1 0 1 (by omega) hc₁.fst
            (((dgHom X₁ Z₂).d (-1) 0).hom (dgComp 0 (-1) (-1) (by omega) a hc₂.inl)) +
          (-1 : ℤ).negOnePow • dgComp 2 (-1) 1 (by omega)
            (((dgHom Z₁ X₁).d 1 2).hom hc₁.fst) (dgComp 0 (-1) (-1) (by omega) a hc₂.inl) :=
      dgComp_leibniz (X := Z₁) (Y := X₁) (Z := Z₂) 1 (-1) 0 1 (by omega) (by omega) _ _
    rw [h, hA, hc₁.delta_fst]
    simp
  have hT2 : ((dgHom Z₁ Z₂).d 0 1).hom
        (dgComp 0 0 0 (by omega) hc₁.snd (dgComp 0 0 0 (by omega) b hc₂.inr)) =
      dgComp 1 0 1 (by omega) (-dgComp 1 0 1 (by omega) hc₁.fst f₁)
        (dgComp 0 0 0 (by omega) b hc₂.inr) := by
    have h : ((dgHom Z₁ Z₂).d 0 1).hom
          (dgComp 0 0 0 (by omega) hc₁.snd (dgComp 0 0 0 (by omega) b hc₂.inr)) =
        dgComp 0 1 1 (by omega) hc₁.snd
            (((dgHom Y₁ Z₂).d 0 1).hom (dgComp 0 0 0 (by omega) b hc₂.inr)) +
          (0 : ℤ).negOnePow • dgComp 1 0 1 (by omega)
            (((dgHom Z₁ Y₁).d 0 1).hom hc₁.snd) (dgComp 0 0 0 (by omega) b hc₂.inr) :=
      dgComp_leibniz (X := Z₁) (Y := Y₁) (Z := Z₂) 0 0 0 1 (by omega) (by omega) _ _
    rw [h, hB, hc₁.delta_snd]
    simp
  have hT3 : ((dgHom Z₁ Z₂).d 0 1).hom
        (dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp (-1) 0 (-1) (by omega) k hc₂.inr)) =
      dgComp 1 0 1 (by omega) hc₁.fst
        (dgComp 0 0 0 (by omega)
          (dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) hc₂.inr) := by
    have h : ((dgHom Z₁ Z₂).d 0 1).hom
          (dgComp 1 (-1) 0 (by omega) hc₁.fst (dgComp (-1) 0 (-1) (by omega) k hc₂.inr)) =
        dgComp 1 0 1 (by omega) hc₁.fst
            (((dgHom X₁ Z₂).d (-1) 0).hom (dgComp (-1) 0 (-1) (by omega) k hc₂.inr)) +
          (-1 : ℤ).negOnePow • dgComp 2 (-1) 1 (by omega)
            (((dgHom Z₁ X₁).d 1 2).hom hc₁.fst) (dgComp (-1) 0 (-1) (by omega) k hc₂.inr) :=
      dgComp_leibniz (X := Z₁) (Y := X₁) (Z := Z₂) 1 (-1) 0 1 (by omega) (by omega) _ _
    rw [h, hK, hc₁.delta_fst]
    simp
  rw [lift, map_add, map_add, hT1, hT2, hT3]
  simp only [map_sub, AddMonoidHom.sub_apply, map_neg, AddMonoidHom.neg_apply]
  rw [← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hc₁.fst a
      (dgComp 0 0 0 (by omega) f₂ hc₂.inr),
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)
      (dgComp 1 0 1 (by omega) hc₁.fst a) f₂ hc₂.inr,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)
      (dgComp 1 0 1 (by omega) hc₁.fst f₁) b hc₂.inr,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hc₁.fst
      (dgComp 0 0 0 (by omega) f₁ b) hc₂.inr,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hc₁.fst
      (dgComp 0 0 0 (by omega) a f₂) hc₂.inr,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hc₁.fst f₁ b,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) hc₁.fst a f₂]
  abel

section Shift

variable {X₁' X₂' : C} (s₁ : IsShiftBy X₁ 1 X₁') (s₂ : IsShiftBy X₂ 1 X₂')

/-- **The second square, strictly.** `inr₂ ≫ fst₂ = 0` kills the `b`- and
`k`-terms, `inl₂ ≫ fst₂ = dgId` collapses the `a`-term, and both sides become
`fst₁ ≫ (a ≫ s₂.hom)` — which is `mapShift`'s definition read backwards through
`s₁.hom ≫ s₁.inv = dgId`. -/
lemma lift_comp_toShift :
    dgComp 0 0 0 (by omega) (hc₁.lift hc₂ a b k) (hc₂.toShift s₂) =
      dgComp 0 0 0 (by omega) (hc₁.toShift s₁) (IsShiftBy.mapShift s₁ s₂ a) := by
  rw [lift, toShift, toShift, IsShiftBy.mapShift, map_add, AddMonoidHom.add_apply,
    map_add, AddMonoidHom.add_apply]
  -- the `a`-term
  rw [dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst
      (dgComp 0 (-1) (-1) (by omega) a hc₂.inl) (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    dgComp_assoc 0 (-1) 0 (-1) (-1) (-1) (by omega) (by omega) (by omega) a hc₂.inl
      (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) hc₂.inl hc₂.fst s₂.hom,
    hc₂.inl_comp_fst, dgId_comp]
  -- the `b`- and `k`-terms
  rw [dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) hc₁.snd
      (dgComp 0 0 0 (by omega) b hc₂.inr) (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) b hc₂.inr
      (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) hc₂.inr hc₂.fst s₂.hom,
    hc₂.inr_comp_fst,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst
      (dgComp (-1) 0 (-1) (by omega) k hc₂.inr) (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    dgComp_assoc (-1) 0 0 (-1) 0 (-1) (by omega) (by omega) (by omega) k hc₂.inr
      (dgComp 1 (-1) 0 (by omega) hc₂.fst s₂.hom),
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) hc₂.inr hc₂.fst s₂.hom,
    hc₂.inr_comp_fst]
  simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
  -- the right-hand side
  rw [dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst s₁.hom
      (dgComp 1 (-1) 0 (by omega) (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) s₁.hom
      (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom,
    ← dgComp_assoc (-1) 1 0 0 1 0 (by omega) (by omega) (by omega) s₁.hom s₁.inv a,
    s₁.hom_inv, dgId_comp]

end Shift

end IsConeOf

end CategoryTheory
