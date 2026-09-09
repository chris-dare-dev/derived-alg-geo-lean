/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousLift

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

## One owner for the lift

Everything here is the degree-zero case of `Pretriangulated.HomogeneousLift`.
`HomotopySquare` is a `HomogeneousSquare` of degree zero whose vertical maps
are closed, `lift` is `homogeneousLift 0`, and closedness of the lift is
`homogeneousLift_d` read at degree zero. No sign is computed twice.

## Both squares are strict

Once `c` exists, neither square needs a homotopy. `inr₁ ≫ c = b ≫ inr₂` because
`inr₁` is orthogonal to `fst₁` and a section of `snd₁`, so the `k`-term and the
`a`-term both vanish. And `c ≫ fst₂ = fst₁ ≫ a` because `inl₂ ≫ fst₂` is the
identity while `inr₂ ≫ fst₂` is zero, which kills the `b`- and `k`-terms.

The second square is stated on the cone projection `fst`, not on the
connecting morphism into a chosen shift: it needs no shift witness, so cone
morphisms compose without choosing one, and the connecting-morphism form
`Morphism.toShift_comm` is a consequence for every witness at once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace DGCategory

/-- A degree-zero square between closed dg morphisms together with a chosen
degree-minus-one homotopy witnessing its commutativity in `H⁰`: a
`HomogeneousSquare` of degree zero whose vertical maps are closed.

This is the canonical input to cone functoriality.  In particular, the
homotopy is stored as data rather than merely asserted to exist, so cone maps
can be constructed and composed without making a fresh choice. -/
structure HomotopySquare
    {X₁ Y₁ X₂ Y₂ : C}
    (f₁ : (dgHom X₁ Y₁).X 0) (f₂ : (dgHom X₂ Y₂).X 0)
    (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0)
    extends HomogeneousSquare f₁ f₂ 0 a b where
  /-- The first vertical morphism is closed. -/
  a_closed : ((dgHom X₁ X₂).d 0 1).hom a = 0
  /-- The second vertical morphism is closed. -/
  b_closed : ((dgHom Y₁ Y₂).d 0 1).hom b = 0

namespace HomotopySquare

variable {X₁ Y₁ X₂ Y₂ : C}
  {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
  {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}

/-- The boundary equation of a degree-zero homotopy, with the trivial Koszul
sign `(-1)^0` removed: `δ k = f₁ ≫ b - a ≫ f₂`. -/
lemma boundary (s : HomotopySquare f₁ f₂ a b) :
    ((dgHom X₁ Y₂).d (-1) 0).hom s.homotopy =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂ := by
  -- The homogeneous boundary is stated at index `0 - 1` with the sign
  -- `(-1)^0`; both are definitionally what the statement says, so `exact`
  -- closes the gap that `rw` cannot cross inside a dependent index.
  have h := s.homotopy_boundary
  rw [Int.negOnePow_zero, one_smul] at h
  exact h

/-- Build a homotopy square from closed vertical maps and the unsigned
boundary equation. -/
def ofBoundary (ha : ((dgHom X₁ X₂).d 0 1).hom a = 0)
    (hb : ((dgHom Y₁ Y₂).d 0 1).hom b = 0)
    (k : (dgHom X₁ Y₂).X (-1))
    (hk : ((dgHom X₁ Y₂).d (-1) 0).hom k =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) :
    HomotopySquare f₁ f₂ a b where
  homotopy := k
  homotopy_boundary := by
    rw [Int.negOnePow_zero, one_smul]
    exact hk
  a_closed := ha
  b_closed := hb

@[simp]
lemma ofBoundary_homotopy (ha : ((dgHom X₁ X₂).d 0 1).hom a = 0)
    (hb : ((dgHom Y₁ Y₂).d 0 1).hom b = 0)
    (k : (dgHom X₁ Y₂).X (-1))
    (hk : ((dgHom X₁ Y₂).d (-1) 0).hom k =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) :
    (ofBoundary ha hb k hk).homotopy = k :=
  rfl

/-- Two homotopy squares with the same chosen homotopy are equal.  Closedness
and the boundary equation are propositions, so the degree-minus-one element is
the only additional data once the four boundary morphisms are fixed. -/
@[ext]
lemma ext {s t : HomotopySquare f₁ f₂ a b}
    (h : s.homotopy = t.homotopy) : s = t := by
  rcases s with ⟨⟨ks, hks⟩, has, hbs⟩
  rcases t with ⟨⟨kt, hkt⟩, hat, hbt⟩
  have hk : ks = kt := h
  subst hk
  rfl

/-- The identity homotopy square. -/
def id {X Y : C} (f : (dgHom X Y).X 0) :
    HomotopySquare f f (dgId X) (dgId Y) :=
  ofBoundary (dgId_cocycle X) (dgId_cocycle Y) 0 (by
    rw [map_zero, dgComp_id, dgId_comp]
    simp)

@[simp]
lemma id_homotopy {X Y : C} (f : (dgHom X Y).X 0) : (id f).homotopy = 0 :=
  rfl

/-- Composition of chosen homotopy squares.  The composite homotopy is the
standard sum `k₁ ≫ b₂ + a₁ ≫ k₂`; unlike an existential commutativity proof,
this operation retains the witness needed by the induced cone map. -/
def comp
    {X₃ Y₃ : C} {f₃ : (dgHom X₃ Y₃).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (s₁ : HomotopySquare f₁ f₂ a b)
    (s₂ : HomotopySquare f₂ f₃ a₂ b₂) :
    HomotopySquare f₁ f₃
      (dgComp 0 0 0 (by omega) a a₂)
      (dgComp 0 0 0 (by omega) b b₂) :=
  ofBoundary
    (dgComp_closed (by omega) (by omega) s₁.a_closed s₂.a_closed)
    (dgComp_closed (by omega) (by omega) s₁.b_closed s₂.b_closed)
    (dgComp (-1) 0 (-1) (by omega) s₁.homotopy b₂ +
      dgComp 0 (-1) (-1) (by omega) a s₂.homotopy)
    (by
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
            (dgComp 0 (-1) (-1) (by omega) a s₂.homotopy) =
          dgComp 0 0 0 (by omega) a
            (((dgHom X₂ Y₃).d (-1) 0).hom s₂.homotopy) := by
        have h : ((dgHom X₁ Y₃).d (-1) 0).hom
              (dgComp 0 (-1) (-1) (by omega) a s₂.homotopy) =
            dgComp 0 0 0 (by omega) a
                (((dgHom X₂ Y₃).d (-1) 0).hom s₂.homotopy) +
              (-1 : ℤ).negOnePow •
                dgComp 1 (-1) 0 (by omega)
                  (((dgHom X₁ X₂).d 0 1).hom a) s₂.homotopy :=
          dgComp_leibniz (X := X₁) (Y := X₂) (Z := Y₃)
            0 (-1) (-1) 0 (by omega) (by omega) a s₂.homotopy
        rw [h, s₁.a_closed]
        simp
      rw [map_add, h₁, h₂, s₁.boundary, s₂.boundary]
      simp only [map_sub, AddMonoidHom.sub_apply]
      rw [← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) a f₂ b₂,
        ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) a a₂ f₃,
        ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega) f₁ b b₂]
      abel)

@[simp]
lemma comp_homotopy
    {X₃ Y₃ : C} {f₃ : (dgHom X₃ Y₃).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (s₁ : HomotopySquare f₁ f₂ a b)
    (s₂ : HomotopySquare f₂ f₃ a₂ b₂) :
    (s₁.comp s₂).homotopy =
      dgComp (-1) 0 (-1) (by omega) s₁.homotopy b₂ +
        dgComp 0 (-1) (-1) (by omega) a s₂.homotopy :=
  rfl

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
  /-- The square on the cone projections to the sources.  Stated on `fst`,
  so no shift witness is involved; see `Morphism.toShift_comm` for the
  connecting-morphism form at any chosen shift. -/
  fst_comm :
    dgComp 0 1 1 (by omega) hom.1 hc₂.fst =
      dgComp 1 0 1 (by omega) hc₁.fst a

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
  m.square.boundary

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

/-- **The connecting-morphism square, at every chosen shift.**  `toShift` is
`fst` followed by the shift's element and `mapShift` is conjugation by the
two shift witnesses, so the `fst` square gives the connecting square once
`s₁.hom ≫ s₁.inv` cancels. -/
lemma toShift_comm (m : Morphism hc₁ hc₂ a b) {X₁' X₂' : C}
    (s₁ : IsShiftBy X₁ 1 X₁') (s₂ : IsShiftBy X₂ 1 X₂') :
    dgComp 0 0 0 (by omega) m.hom.1 (hc₂.toShift s₂) =
      dgComp 0 0 0 (by omega) (hc₁.toShift s₁)
        (IsShiftBy.mapShift s₁ s₂ a) := by
  rw [IsConeOf.toShift, IsConeOf.toShift, IsShiftBy.mapShift,
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega) m.hom.1 hc₂.fst s₂.hom,
    m.fst_comm,
    dgComp_assoc 1 0 (-1) 1 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst a s₂.hom,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst s₁.hom
      (dgComp 1 (-1) 0 (by omega) (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) s₁.hom
      (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom,
    ← dgComp_assoc (-1) 1 0 0 1 0 (by omega) (by omega) (by omega) s₁.hom s₁.inv a,
    s₁.hom_inv, dgId_comp]

end Morphism

/-- The lift of a square to the cones, with the homotopy folded in: the
degree-zero case of `homogeneousLift`. -/
noncomputable def lift : (dgHom Z₁ Z₂).X 0 :=
  hc₁.homogeneousLift hc₂ 0 a b k

/-- **The first square, strictly.** `inr₁ ≫ fst₁ = 0` kills the first and third
terms, and `inr₁ ≫ snd₁ = dgId` leaves the second. -/
lemma inr_comp_lift :
    dgComp 0 0 0 (by omega) hc₁.inr (hc₁.lift hc₂ a b k) =
      dgComp 0 0 0 (by omega) b hc₂.inr :=
  hc₁.inr_comp_homogeneousLift hc₂ 0 a b k

/-- **The second square, strictly.** `inr₂ ≫ fst₂ = 0` kills the `b`- and
`k`-terms and `inl₂ ≫ fst₂ = dgId` collapses the `a`-term. -/
lemma lift_comp_fst :
    dgComp 0 1 1 (by omega) (hc₁.lift hc₂ a b k) hc₂.fst =
      dgComp 1 0 1 (by omega) hc₁.fst a := by
  have h := hc₁.homogeneousLift_comp_fst hc₂ 0 a b k
  rw [Int.negOnePow_zero, one_smul] at h
  exact h

/-- **The lift is closed.** `homogeneousLift_d` at degree zero: the
differential of the lift is the lift of `δ a` and `δ b`, which vanish. -/
lemma lift_closed (ha : ((dgHom X₁ X₂).d 0 1).hom a = 0)
    (hb : ((dgHom Y₁ Y₂).d 0 1).hom b = 0)
    (hk : ((dgHom X₁ Y₂).d (-1) 0).hom k =
      dgComp 0 0 0 (by omega) f₁ b - dgComp 0 0 0 (by omega) a f₂) :
    ((dgHom Z₁ Z₂).d 0 1).hom (hc₁.lift hc₂ a b k) = 0 := by
  have h := hc₁.homogeneousLift_d hc₂ 0 a b
    (DGCategory.HomotopySquare.ofBoundary ha hb k hk).toHomogeneousSquare
  have ha' : ((dgHom X₁ X₂).d 0 (0 + 1)).hom a = 0 := ha
  have hb' : ((dgHom Y₁ Y₂).d 0 (0 + 1)).hom b = 0 := hb
  rw [ha', hb', homogeneousLift_zero] at h
  exact h

section Shift

variable {X₁' X₂' : C} (s₁ : IsShiftBy X₁ 1 X₁') (s₂ : IsShiftBy X₂ 1 X₂')

/-- The standard dg lift of a chosen homotopy square, packaged as a cone
morphism. `lift_closed` consumes the square's boundary equation, while the two
strict square lemmas retain the resulting naturality before passage to `H⁰`. -/
noncomputable def liftMorphism
    (s : DGCategory.HomotopySquare f₁ f₂ a b) :
  Morphism hc₁ hc₂ a b :=
  { square := s
    hom := ⟨hc₁.lift hc₂ a b s.homotopy,
      hc₁.lift_closed hc₂ _ _ _ s.a_closed s.b_closed s.boundary⟩
    inr_comm := hc₁.inr_comp_lift hc₂ a b s.homotopy
    fst_comm := hc₁.lift_comp_fst hc₂ a b s.homotopy }

/-- The connecting-morphism square of the lift, for any two shift witnesses.
`lift_comp_fst` supplies the `fst` square; the rest is `s₁.hom ≫ s₁.inv = 1`. -/
lemma lift_comp_toShift :
    dgComp 0 0 0 (by omega) (hc₁.lift hc₂ a b k) (hc₂.toShift s₂) =
      dgComp 0 0 0 (by omega) (hc₁.toShift s₁) (IsShiftBy.mapShift s₁ s₂ a) := by
  rw [IsConeOf.toShift, IsConeOf.toShift, IsShiftBy.mapShift,
    ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega)
      (hc₁.lift hc₂ a b k) hc₂.fst s₂.hom,
    hc₁.lift_comp_fst hc₂ a b k,
    dgComp_assoc 1 0 (-1) 1 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst a s₂.hom,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega) hc₁.fst s₁.hom
      (dgComp 1 (-1) 0 (by omega) (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega) s₁.hom
      (dgComp 1 0 1 (by omega) s₁.inv a) s₂.hom,
    ← dgComp_assoc (-1) 1 0 0 1 0 (by omega) (by omega) (by omega) s₁.hom s₁.inv a,
    s₁.hom_inv, dgId_comp]

end Shift

section Composition

variable {X₃ Y₃ Z₃ : C} {f₃ : (dgHom X₃ Y₃).X 0}
  (hc₃ : IsConeOf f₃ Z₃)

/-- The identity cone morphism. -/
def Morphism.id {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    Morphism hc hc (dgId X) (dgId Y) where
  square := DGCategory.HomotopySquare.id f
  hom := ⟨dgId Z, by simpa only [mem_cocycles_iff] using dgId_cocycle Z⟩
  inr_comm := by
    change dgComp 0 0 0 (by omega) hc.inr (dgId Z) =
      dgComp 0 0 0 (by omega) (dgId Y) hc.inr
    rw [dgComp_id, dgId_comp]
  fst_comm := by
    change dgComp 0 1 1 (by omega) (dgId Z) hc.fst =
      dgComp 1 0 1 (by omega) hc.fst (dgId X)
    rw [dgId_comp, dgComp_id]

/-- Composition of cone morphisms.  The underlying degree-zero maps and the
homotopies compose strictly, and both cone squares are chased through the
middle cone; no shift witness is needed. -/
def Morphism.comp
    {a₁ : (dgHom X₁ X₂).X 0} {b₁ : (dgHom Y₁ Y₂).X 0}
    {a₂ : (dgHom X₂ X₃).X 0} {b₂ : (dgHom Y₂ Y₃).X 0}
    (m₁ : Morphism hc₁ hc₂ a₁ b₁)
    (m₂ : Morphism hc₂ hc₃ a₂ b₂) :
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
  fst_comm := by
    calc
      dgComp 0 1 1 (by omega)
          (dgComp 0 0 0 (by omega) m₁.hom.1 m₂.hom.1) hc₃.fst =
          dgComp 0 1 1 (by omega) m₁.hom.1
            (dgComp 0 1 1 (by omega) m₂.hom.1 hc₃.fst) := by
              exact dgComp_assoc 0 0 1 0 1 1 (by omega) (by omega) (by omega)
                m₁.hom.1 m₂.hom.1 hc₃.fst
      _ = dgComp 0 1 1 (by omega) m₁.hom.1
            (dgComp 1 0 1 (by omega) hc₂.fst a₂) := by rw [m₂.fst_comm]
      _ = dgComp 1 0 1 (by omega)
            (dgComp 0 1 1 (by omega) m₁.hom.1 hc₂.fst) a₂ := by
              exact (dgComp_assoc 0 1 0 1 1 1 (by omega) (by omega) (by omega)
                m₁.hom.1 hc₂.fst a₂).symm
      _ = dgComp 1 0 1 (by omega)
            (dgComp 1 0 1 (by omega) hc₁.fst a₁) a₂ := by rw [m₁.fst_comm]
      _ = dgComp 1 0 1 (by omega) hc₁.fst
            (dgComp 0 0 0 (by omega) a₁ a₂) := by
              exact dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)
                hc₁.fst a₁ a₂

end Composition

end IsConeOf

end CategoryTheory
