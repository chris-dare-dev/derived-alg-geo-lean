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

namespace DGCategory

/-- A degree-zero square between dg morphisms together with a chosen
degree-minus-one homotopy witnessing its commutativity in `H⁰`.

This is the canonical input to cone functoriality.  In particular, the
homotopy is stored as data rather than merely asserted to exist, so cone maps
can be constructed and composed without making a fresh choice. -/
structure HomotopySquare
    {X₁ Y₁ X₂ Y₂ : C}
    (f₁ : (dgHom X₁ Y₁).X 0) (f₂ : (dgHom X₂ Y₂).X 0)
    (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) where
  /-- The first vertical morphism is closed. -/
  a_closed : ((dgHom X₁ X₂).d 0 1).hom a = 0
  /-- The second vertical morphism is closed. -/
  b_closed : ((dgHom Y₁ Y₂).d 0 1).hom b = 0
  /-- The chosen homotopy from `f₁ ≫ b` to `a ≫ f₂`. -/
  homotopy : (dgHom X₁ Y₂).X (-1)
  /-- The boundary equation satisfied by the chosen homotopy. -/
  homotopy_boundary :
    ((dgHom X₁ Y₂).d (-1) 0).hom homotopy =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂

namespace HomotopySquare

/-- Two homotopy squares with the same chosen homotopy are equal.  Closedness
and the boundary equation are propositions, so the degree-minus-one element is
the only additional data once the four boundary morphisms are fixed. -/
@[ext]
lemma ext
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}
    {s t : HomotopySquare f₁ f₂ a b}
    (h : s.homotopy = t.homotopy) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- The identity homotopy square. -/
def id {X Y : C} (f : (dgHom X Y).X 0) :
    HomotopySquare f f (dgId X) (dgId Y) where
  a_closed := dgId_cocycle X
  b_closed := dgId_cocycle Y
  homotopy := 0
  homotopy_boundary := by
    rw [map_zero, dgComp_id, dgId_comp]
    simp

/-- Composition of chosen homotopy squares.  The composite homotopy is the
standard sum `k₁ ≫ b₂ + a₁ ≫ k₂`; unlike an existential commutativity proof,
this operation retains the witness needed by the induced cone map. -/
def comp
    {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {f₃ : (dgHom X₃ Y₃).X 0}
    {a₁ : (dgHom X₁ X₂).X 0} {b₁ : (dgHom Y₁ Y₂).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (s₁ : HomotopySquare f₁ f₂ a₁ b₁)
    (s₂ : HomotopySquare f₂ f₃ a₂ b₂) :
    HomotopySquare f₁ f₃
      (dgComp 0 0 0 (by omega) a₁ a₂)
      (dgComp 0 0 0 (by omega) b₁ b₂) where
  a_closed := dgComp_closed (by omega) (by omega) s₁.a_closed s₂.a_closed
  b_closed := dgComp_closed (by omega) (by omega) s₁.b_closed s₂.b_closed
  homotopy :=
    dgComp (-1) 0 (-1) (by omega) s₁.homotopy b₂ +
      dgComp 0 (-1) (-1) (by omega) a₁ s₂.homotopy
  homotopy_boundary := by
    have h₁ : ((dgHom X₁ Y₃).d (-1) 0).hom
          (dgComp (-1) 0 (-1) (by omega) s₁.homotopy b₂) =
        dgComp 0 0 0 (by omega)
          (((dgHom X₁ Y₂).d (-1) 0).hom s₁.homotopy) b₂ := by
      have h : ((dgHom X₁ Y₃).d (-1) 0).hom
            (dgComp (-1) 0 (-1) (by omega) s₁.homotopy b₂) =
          dgComp (-1) 1 0 (by omega) s₁.homotopy
              (((dgHom Y₂ Y₃).d 0 1).hom b₂) +
            (0 : ℤ).negOnePow •
              dgComp 0 0 0 (by omega)
                (((dgHom X₁ Y₂).d (-1) 0).hom s₁.homotopy) b₂ :=
        dgComp_leibniz (X := X₁) (Y := Y₂) (Z := Y₃)
          (-1) 0 (-1) 0 (by omega) (by omega) s₁.homotopy b₂
      rw [h, s₂.b_closed]
      simp
    have h₂ : ((dgHom X₁ Y₃).d (-1) 0).hom
          (dgComp 0 (-1) (-1) (by omega) a₁ s₂.homotopy) =
        dgComp 0 0 0 (by omega) a₁
          (((dgHom X₂ Y₃).d (-1) 0).hom s₂.homotopy) := by
      have h : ((dgHom X₁ Y₃).d (-1) 0).hom
            (dgComp 0 (-1) (-1) (by omega) a₁ s₂.homotopy) =
          dgComp 0 0 0 (by omega) a₁
              (((dgHom X₂ Y₃).d (-1) 0).hom s₂.homotopy) +
            (-1 : ℤ).negOnePow •
              dgComp 1 (-1) 0 (by omega)
                (((dgHom X₁ X₂).d 0 1).hom a₁) s₂.homotopy :=
        dgComp_leibniz (X := X₁) (Y := X₂) (Z := Y₃)
          0 (-1) (-1) 0 (by omega) (by omega) a₁ s₂.homotopy
      rw [h, s₁.a_closed]
      simp
    rw [map_add, h₁, h₂, s₁.homotopy_boundary, s₂.homotopy_boundary]
    simp only [map_sub, AddMonoidHom.sub_apply]
    rw [← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) a₁ f₂ b₂,
      ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) a₁ a₂ f₃,
      ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) f₁ b₁ b₂]
    abel

end HomotopySquare

end DGCategory

namespace IsConeOf

variable {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
  (hc₁ : IsConeOf f₁ Z₁) (hc₂ : IsConeOf f₂ Z₂)
  (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) (k : (dgHom X₁ Y₂).X (-1))

/-- A cone morphism keeps the dg representative and the strict identities
  that make it useful downstream. In particular, this is stronger data than
  a morphism between the corresponding triangles in `H⁰`: the representative
  is closed before passing to the quotient, and both cone squares are retained
  on the nose. -/
structure Morphism where
  /-- The chosen homotopy-commutative square on the first two objects. -/
  square : DGCategory.HomotopySquare f₁ f₂ a b
  /-- The closed degree-zero dg morphism between the cone objects. -/
  hom : cocycles Z₁ Z₂
  /-- The square on the cone inclusions. -/
  inr_comm :
    dgComp 0 0 0 (by omega) hc₁.inr hom.1 =
      dgComp 0 0 0 (by omega) b hc₂.inr
  /-- The square on the connecting maps, for arbitrary chosen shifts. -/
  toShift_comm : ∀ {X₁' X₂' : C}
    (s₁ : IsShiftBy X₁ 1 X₁') (s₂ : IsShiftBy X₂ 1 X₂'),
    dgComp 0 0 0 (by omega) hom.1 (hc₂.toShift s₂) =
      dgComp 0 0 0 (by omega) (hc₁.toShift s₁)
        (IsShiftBy.mapShift s₁ s₂ a)

namespace Morphism

variable {hc₁ : IsConeOf f₁ Z₁} {hc₂ : IsConeOf f₂ Z₂}
  {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}

/-- The closedness of the first component, projected from the canonical
homotopy-square input. -/
lemma a_closed (m : Morphism hc₁ hc₂ a b) :
    ((dgHom X₁ X₂).d 0 1).hom a = 0 :=
  m.square.a_closed

/-- The closedness of the second component, projected from the canonical
homotopy-square input. -/
lemma b_closed (m : Morphism hc₁ hc₂ a b) :
    ((dgHom Y₁ Y₂).d 0 1).hom b = 0 :=
  m.square.b_closed

/-- The chosen degree-minus-one homotopy underlying a cone morphism. -/
def homotopy (m : Morphism hc₁ hc₂ a b) : (dgHom X₁ Y₂).X (-1) :=
  m.square.homotopy

/-- The boundary equation for the chosen homotopy underlying a cone
morphism. -/
lemma homotopy_boundary (m : Morphism hc₁ hc₂ a b) :
    ((dgHom X₁ Y₂).d (-1) 0).hom m.homotopy =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂ :=
  m.square.homotopy_boundary

/-- A cone morphism is determined by its chosen homotopy square and its
closed map between cone objects.  The two strict compatibility fields are
propositions. -/
@[ext]
lemma ext {m n : Morphism hc₁ hc₂ a b}
    (hs : m.square = n.square) (hc : m.hom = n.hom) : m = n := by
  cases m
  cases n
  cases hs
  cases hc
  rfl

end Morphism

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

/-- The standard dg lift of a chosen homotopy square, packaged as a cone
morphism. `lift_closed` consumes the square's boundary equation, while the two
strict square lemmas retain the resulting naturality before passage to `H⁰`. -/
noncomputable def liftMorphism
    (s : DGCategory.HomotopySquare f₁ f₂ a b) :
  Morphism hc₁ hc₂ a b :=
  { square := s
    hom := ⟨hc₁.lift hc₂ a b s.homotopy,
      hc₁.lift_closed hc₂ _ _ _ s.a_closed s.b_closed s.homotopy_boundary⟩
    inr_comm := hc₁.inr_comp_lift hc₂ a b s.homotopy
    toShift_comm := fun s₁ s₂ =>
      hc₁.lift_comp_toShift hc₂ a b s.homotopy s₁ s₂ }

end Shift

section Composition

variable {X₃ Y₃ Z₃ : C} {f₃ : (dgHom X₃ Y₃).X 0}
  (hc₃ : IsConeOf f₃ Z₃)

/-- The identity cone morphism. Its connecting square is the naturality of
`IsConeOf.toShift` with respect to the comparison between two shifts. -/
def Morphism.id {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    Morphism hc hc (dgId X) (dgId Y) where
  square := DGCategory.HomotopySquare.id f
  hom := ⟨dgId Z, by simpa only [mem_cocycles_iff] using dgId_cocycle Z⟩
  inr_comm := by
    change dgComp 0 0 0 (by omega) hc.inr (dgId Z) =
      dgComp 0 0 0 (by omega) (dgId Y) hc.inr
    rw [dgComp_id, dgId_comp]
  toShift_comm s₁ s₂ := by
    change dgComp 0 0 0 (by omega) (dgId Z) (hc.toShift s₂) =
      dgComp 0 0 0 (by omega) (hc.toShift s₁)
        (IsShiftBy.mapShift s₁ s₂ (dgId X))
    rw [dgId_comp, ← IsShiftBy.compare_eq_mapShift s₁ s₂, hc.toShift_comp_compare]

/-- Compose cone morphisms using a chosen shift of the middle source.

The underlying degree-zero maps compose strictly. The intermediate shift is
only needed to splice the two `toShift_comm` fields; in a pretriangulated dg
category it can be supplied by the witness from `IsPretriangulated.exists_shift`. -/
def Morphism.compAt
    {a₁ : (dgHom X₁ X₂).X 0} {b₁ : (dgHom Y₁ Y₂).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (m₁ : Morphism hc₁ hc₂ a₁ b₁)
    (m₂ : Morphism hc₂ hc₃ a₂ b₂)
    {X₂' : C} (s₂ : IsShiftBy X₂ 1 X₂') :
    Morphism hc₁ hc₃
      (dgComp 0 0 0 (by omega) a₁ a₂)
      (dgComp 0 0 0 (by omega) b₁ b₂) where
  square := m₁.square.comp m₂.square
  hom := ⟨dgComp 0 0 0 (by omega) m₁.hom.1 m₂.hom.1,
    dgComp_closed (by omega) (by omega) m₁.hom.2 m₂.hom.2⟩
  inr_comm := by
    calc
      dgComp 0 0 0 (by omega) hc₁.inr
          (dgComp 0 0 0 (by omega) m₁.hom.1 m₂.hom.1) =
          dgComp 0 0 0 (by omega)
            (dgComp 0 0 0 (by omega) hc₁.inr m₁.hom.1) m₂.hom.1 := by
              exact (dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                hc₁.inr m₁.hom.1 m₂.hom.1).symm
      _ = dgComp 0 0 0 (by omega)
            (dgComp 0 0 0 (by omega) b₁ hc₂.inr) m₂.hom.1 := by rw [m₁.inr_comm]
      _ = dgComp 0 0 0 (by omega) b₁
            (dgComp 0 0 0 (by omega) hc₂.inr m₂.hom.1) := by
              exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                b₁ hc₂.inr m₂.hom.1
      _ = dgComp 0 0 0 (by omega) b₁
            (dgComp 0 0 0 (by omega) b₂ hc₃.inr) := by rw [m₂.inr_comm]
      _ = dgComp 0 0 0 (by omega)
            (dgComp 0 0 0 (by omega) b₁ b₂) hc₃.inr := by
              exact (dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                b₁ b₂ hc₃.inr).symm
  toShift_comm s₁ s₃ := by
    calc
      dgComp 0 0 0 (by omega)
          (dgComp 0 0 0 (by omega) m₁.hom.1 m₂.hom.1) (hc₃.toShift s₃) =
          dgComp 0 0 0 (by omega) m₁.hom.1
            (dgComp 0 0 0 (by omega) m₂.hom.1 (hc₃.toShift s₃)) := by
              exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                m₁.hom.1 m₂.hom.1 (hc₃.toShift s₃)
      _ = dgComp 0 0 0 (by omega) m₁.hom.1
            (dgComp 0 0 0 (by omega) (hc₂.toShift s₂)
              (IsShiftBy.mapShift s₂ s₃ a₂)) := by
              rw [m₂.toShift_comm s₂ s₃]
      _ = dgComp 0 0 0 (by omega)
            (dgComp 0 0 0 (by omega) m₁.hom.1 (hc₂.toShift s₂))
            (IsShiftBy.mapShift s₂ s₃ a₂) := by
              exact (dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                m₁.hom.1 (hc₂.toShift s₂) (IsShiftBy.mapShift s₂ s₃ a₂)).symm
      _ = dgComp 0 0 0 (by omega)
            (dgComp 0 0 0 (by omega) (hc₁.toShift s₁)
              (IsShiftBy.mapShift s₁ s₂ a₁))
            (IsShiftBy.mapShift s₂ s₃ a₂) := by
              rw [m₁.toShift_comm s₁ s₂]
      _ = dgComp 0 0 0 (by omega) (hc₁.toShift s₁)
            (dgComp 0 0 0 (by omega)
              (IsShiftBy.mapShift s₁ s₂ a₁) (IsShiftBy.mapShift s₂ s₃ a₂)) := by
              exact dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega)
                (hc₁.toShift s₁) (IsShiftBy.mapShift s₁ s₂ a₁)
                (IsShiftBy.mapShift s₂ s₃ a₂)
      _ = dgComp 0 0 0 (by omega) (hc₁.toShift s₁)
            (IsShiftBy.mapShift s₁ s₃
              (dgComp 0 0 0 (by omega) a₁ a₂)) := by
              rw [IsShiftBy.mapShift_comp]

/-- The canonical composition in a pretriangulated dg category. The chosen
middle shift is hidden behind the pretriangulated existence witness; use
`Morphism.compAt` when working without that instance or when a specific witness
is already available. -/
noncomputable def Morphism.comp
    [IsPretriangulated C]
    {a₁ : (dgHom X₁ X₂).X 0} {b₁ : (dgHom Y₁ Y₂).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (m₁ : Morphism hc₁ hc₂ a₁ b₁)
    (m₂ : Morphism hc₂ hc₃ a₂ b₂) :
  Morphism hc₁ hc₃
      (dgComp 0 0 0 (by omega) a₁ a₂)
      (dgComp 0 0 0 (by omega) b₁ b₂) :=
  Morphism.compAt (hc₁ := hc₁) (hc₂ := hc₂) (hc₃ := hc₃) m₁ m₂
    ((IsPretriangulated.exists_shift X₂ 1).choose_spec.some)

end Composition

end IsConeOf

end CategoryTheory
