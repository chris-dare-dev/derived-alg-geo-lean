/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.HeartDatum
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.Tactic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak stability: the definitions of §14

Definitions 14.1–14.3 of arXiv:1902.08184v4, on the abstract layer, together
with the embedding of ordinary stability into the weak structure.

**What "weak" changes and nothing else**: at integer phases the central
charge of a nonzero semistable object may lie on the *closed* ray
`ℝ_{≥0}·e^{iπφ}` — in particular it may vanish — while at non-integer phases
the open-ray condition of an ordinary prestability condition is kept. On a
heart, the values land in `ℍ ⊔ ℝ_{≤0}` rather than `ℍ ⊔ ℝ_{<0}`. The objects
of charge zero form the subcategory `A⁰` of Definition 14.3, whose closure
properties under subobjects, quotients and extensions are proved here from
`K₀` additivity and elementary half-plane arithmetic.

## Phrasing choices, stated for the reviewer

* The heart is carried inside `C` as `t.heart`, following
  `WeakStabilityCondition/Tilting/TorsionPair/Heart.lean`.  The pinned Mathlib does supply
  `t.heartFullSubcategoryAbelian`; triangle-form subobject data is retained
  here because it stays in the ambient category where the charge and slicing
  live.  `TStructure.heartFullSubcategory_shortExact_of_distTriang` identifies
  those heart triangles with short exact sequences in the abelian heart.
* The paper's `K(A)` is replaced by the ambient `K₀ C`, on which this
  library's charges already live; the positivity conditions quantify over heart
  objects
  only. The comparison `K(A) ≅ K(D)` for a bounded t-structure is **not**
  available at the pin and is **not** assumed — nothing here needs it.
* Slopes take values in `WithTop ℝ`, with `μ = +∞` exactly when the charge
  has vanishing imaginary part, as in Definition 14.2.
* **No binding to any statement of the paper is claimed.** These declarations
  are candidates for the §14 coordinates of the coverage map; promotion past
  `target` is a separate, evidence-gated act (#111).
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable {Λ : Type*} [AddCommGroup Λ]

/-! ### Definition 14.1: weak prestability conditions

The weak parent data has the compatibility ray closed at integer phases and
open elsewhere. Ordinary prestability extends this structure downstream, so
the weak layer does not import its stronger child. -/

/-- A weak prestability condition with respect to a class map `v : K₀ C →+ Λ`
(Definition 14.1): a slicing and a central charge on `Λ` such that a nonzero
semistable object of phase `φ` has charge on the ray `ℝ_{>0}·e^{iπφ}` when
`φ ∉ ℤ`, and on the closed ray `ℝ_{≥0}·e^{iπφ}` — so possibly zero — when
`φ ∈ ℤ`. -/
structure WeakPreStabilityCondition (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility: nonnegative radius always, positive off the integers. -/
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ m : ℝ, 0 ≤ m ∧ ((∀ n : ℤ, φ ≠ (n : ℝ)) → 0 < m) ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

/-! ### Definition 14.2: weak stability functions on a heart -/

variable (t : TStructure C)

/-- A weak stability function on the heart of `t` (Definition 14.2): an
additive charge whose value on every nonzero heart object lies in
`ℍ ⊔ ℝ_{≤0} = {z : 0 < Im z} ∪ {z : Im z = 0 ∧ Re z ≤ 0}`.

This is `WeakStabilityFunctionOn` at `heartDatum t` — the ambient
instantiation of the one charge-positivity structure — **not** a structure of
its own. The half-plane it used to write out by hand is
`closedUpperHalfPlane`, and the two agree definitionally. `Z` keeps its name
as a field and `upper` keeps its name and argument shape as a theorem below,
so consumers are unaffected. -/
abbrev WeakStabilityFunction := WeakStabilityFunctionOn (heartDatum t)

/-- An ordinary stability function on the heart of `t`: values on nonzero
heart objects lie in `ℍ ⊔ ℝ_{<0}`, the *strict* form. Carried here so the
embedding into the weak structure is a theorem rather than prose.

This is `StabilityFunctionOn` at `heartDatum t`, at
`semiClosedUpperHalfPlane`. The strict-implies-weak embedding is
`StabilityFunctionOn.toWeak`, proved once for every class datum rather than
once here. -/
abbrev StabilityFunction := StabilityFunctionOn (heartDatum t)

variable {t}

/-- **Values on nonzero heart objects lie in `ℍ ⊔ ℝ_{≤0}`** — the defining
positivity, in the curried argument shape consumers use. Formerly a structure
field; now the datum's positivity condition, unfolded. -/
theorem WeakStabilityFunction.upper (W : WeakStabilityFunction t) (E : C)
    (hE : t.heart E) (hne : ¬IsZero E) :
    0 < (W.Z (K₀.of C E)).im ∨
      ((W.Z (K₀.of C E)).im = 0 ∧ (W.Z (K₀.of C E)).re ≤ 0) :=
  W.nonzero_mem E ⟨hE, hne⟩

/-- **Values on nonzero heart objects lie in `ℍ ⊔ ℝ_{<0}`** — the strict form,
in the curried argument shape consumers use. -/
theorem StabilityFunction.upper (Z : StabilityFunction t) (E : C)
    (hE : t.heart E) (hne : ¬IsZero E) :
    0 < (Z.Z (K₀.of C E)).im ∨
      ((Z.Z (K₀.of C E)).im = 0 ∧ (Z.Z (K₀.of C E)).re < 0) :=
  Z.nonzero_mem E ⟨hE, hne⟩

variable (t)

namespace StabilityFunction

variable {t}

/-- **Ordinary stability functions are weak stability functions**:
`ℝ_{<0} ⊆ ℝ_{≤0}`, same charge.

The inclusion is `StabilityFunctionOn.toWeak`, proved once for every class
datum. This wrapper preserves the name and signature the §14 lane uses. -/
def toWeak (Z : StabilityFunction t) : WeakStabilityFunction t :=
  StabilityFunctionOn.toWeak Z

@[simp]
theorem toWeak_Z (Z : StabilityFunction t) : Z.toWeak.Z = Z.Z := rfl

end StabilityFunction

namespace WeakStabilityFunction

variable {t}
variable (W : WeakStabilityFunction t)

/-- The charge of an object: `Z` evaluated at its `K₀` class. -/
noncomputable abbrev charge (E : C) : ℂ := W.Z (K₀.of C E)

/-- Charges are additive on distinguished triangles, by the defining relation
of `K₀`. -/
theorem charge_triangle {T : Triangle C} (hT : T ∈ distTriang C) :
    W.charge T.obj₂ = W.charge T.obj₁ + W.charge T.obj₃ := by
  simp only [charge, K₀.of_triangle C T hT, map_add]

/-- `charge_triangle`, specialised to an explicit `Triangle.mk` so the
projections are already reduced. -/
theorem charge_triangle' {A E B : C} {f : A ⟶ E} {g : E ⟶ B}
    {h : B ⟶ A⟦(1 : ℤ)⟧} (hdist : Triangle.mk f g h ∈ distTriang C) :
    W.charge E = W.charge A + W.charge B :=
  W.charge_triangle hdist

/-- The charge of a zero object vanishes. -/
theorem charge_isZero {E : C} (hE : IsZero E) : W.charge E = 0 := by
  simp [charge, K₀.of_isZero C hE]

/-- The slope of Definition 14.2: `-Re Z(E)/Im Z(E)` when `Im Z(E) > 0`, and
`+∞` otherwise. -/
noncomputable def slope (E : C) : WithTop ℝ :=
  if 0 < (W.charge E).im then ((-(W.charge E).re / (W.charge E).im : ℝ) : WithTop ℝ)
  else ⊤

theorem slope_of_im_pos {E : C} (h : 0 < (W.charge E).im) :
    W.slope E = ((-(W.charge E).re / (W.charge E).im : ℝ) : WithTop ℝ) :=
  if_pos h

theorem slope_of_im_nonpos {E : C} (h : ¬0 < (W.charge E).im) :
    W.slope E = ⊤ :=
  if_neg h

/-- The charge is invariant under isomorphism of ambient objects. -/
theorem charge_eq_of_iso {E E' : C} (e : E ≅ E') :
    W.charge E = W.charge E' := by
  simp only [charge, K₀.of_iso C e]

/-- The weak slope is invariant under isomorphism of ambient objects. -/
theorem slope_eq_of_iso {E E' : C} (e : E ≅ E') :
    W.slope E = W.slope E' := by
  unfold slope
  rw [W.charge_eq_of_iso e]

/-- `Z`-semistability (Definition 14.2): every subobject has slope at most
the slope of the corresponding quotient. Subobject data is a distinguished
triangle with all three vertices in the heart — for heart objects that is a
short exact sequence — and both ends are required nonzero, matching the
paper's quantification over proper nonzero subobjects. -/
def IsSemistable (E : C) : Prop :=
  t.heart E ∧ ∀ ⦃A B : C⦄, t.heart A → t.heart B → ¬IsZero A → ¬IsZero B →
    ∀ (f : A ⟶ E) (g : E ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C → W.slope A ≤ W.slope B

/-- `Z`-stability: every proper nonzero subobject has slope strictly smaller
than the corresponding nonzero quotient.  This is the strict counterpart of
`IsSemistable`, expressed using the same ambient distinguished triangles. -/
def IsStable (E : C) : Prop :=
  t.heart E ∧ ∀ ⦃A B : C⦄, t.heart A → t.heart B → ¬IsZero A → ¬IsZero B →
    ∀ (f : A ⟶ E) (g : E ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C → W.slope A < W.slope B

/-- A weak-stable object is weak-semistable. -/
theorem IsStable.isSemistable {E : C} (hE : W.IsStable E) : W.IsSemistable E := by
  refine ⟨hE.1, ?_⟩
  intro A B hA hB hA0 hB0 f g d hdist
  exact (hE.2 hA hB hA0 hB0 f g d hdist).le

/-- Weak semistability is invariant under isomorphism of ambient heart
objects. -/
theorem isSemistable_of_iso {E E' : C} (e : E ≅ E')
    (hE : W.IsSemistable E) : W.IsSemistable E' := by
  refine ⟨ObjectProperty.prop_of_iso t.heart e hE.1, ?_⟩
  intro A B hA hB hA0 hB0 f g d hdist
  let f' : A ⟶ E := f ≫ e.inv
  let g' : E ⟶ B := e.hom ≫ g
  have hdist' : Triangle.mk f' g' d ∈ distTriang C := by
    refine isomorphic_distinguished _ hdist _ ?_
    exact Triangle.isoMk _ _ (Iso.refl A) e (Iso.refl B)
      (by simp [f']) (by simp [g']) (by simp)
  exact hE.2 hA hB hA0 hB0 f' g' d hdist'

/-- Isomorphism-invariant reformulation of weak semistability. -/
theorem isSemistable_iff_of_iso {E E' : C} (e : E ≅ E') :
    W.IsSemistable E ↔ W.IsSemistable E' :=
  ⟨W.isSemistable_of_iso e, W.isSemistable_of_iso e.symm⟩

/-- Weak stability is invariant under isomorphism of ambient heart objects. -/
theorem isStable_of_iso {E E' : C} (e : E ≅ E')
    (hE : W.IsStable E) : W.IsStable E' := by
  refine ⟨ObjectProperty.prop_of_iso t.heart e hE.1, ?_⟩
  intro A B hA hB hA0 hB0 f g d hdist
  let f' : A ⟶ E := f ≫ e.inv
  let g' : E ⟶ B := e.hom ≫ g
  have hdist' : Triangle.mk f' g' d ∈ distTriang C := by
    refine isomorphic_distinguished _ hdist _ ?_
    exact Triangle.isoMk _ _ (Iso.refl A) e (Iso.refl B)
      (by simp [f']) (by simp [g']) (by simp)
  exact hE.2 hA hB hA0 hB0 f' g' d hdist'

/-- Isomorphism-invariant reformulation of weak stability. -/
theorem isStable_iff_of_iso {E E' : C} (e : E ≅ E') :
    W.IsStable E ↔ W.IsStable E' :=
  ⟨W.isStable_of_iso e, W.isStable_of_iso e.symm⟩

/-! ### Definition 14.3: the zero-charge subcategory -/

/-- The zero-charge subcategory `A⁰` (Definition 14.3): heart objects of
vanishing charge. -/
def zeroCharge : ObjectProperty C := fun E => t.heart E ∧ W.charge E = 0

theorem zeroCharge_def (E : C) :
    W.zeroCharge E ↔ t.heart E ∧ W.charge E = 0 := Iff.rfl

instance zeroCharge_isClosedUnderIsomorphisms :
    W.zeroCharge.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hheart, hcharge⟩ := hX
    refine ⟨ObjectProperty.prop_of_iso t.heart e hheart, ?_⟩
    simpa [charge, K₀.of_iso C e] using hcharge

/-- The half-plane splitting behind every closure property of `A⁰`: two
values in `ℍ ⊔ ℝ_{≤0}` summing to zero are each zero. Stated on a pair of
heart objects, zero objects allowed. -/
theorem charge_eq_zero_pair {A B : C} (hA : t.heart A) (hB : t.heart B)
    (hsum : W.charge A + W.charge B = 0) :
    W.charge A = 0 ∧ W.charge B = 0 := by
  by_cases hzA : IsZero A
  · have h0 : W.charge A = 0 := W.charge_isZero hzA
    exact ⟨h0, by rwa [h0, zero_add] at hsum⟩
  by_cases hzB : IsZero B
  · have h0 : W.charge B = 0 := W.charge_isZero hzB
    exact ⟨by rwa [h0, add_zero] at hsum, h0⟩
  have hA' := W.upper A hA hzA
  have hB' := W.upper B hB hzB
  have hIm : (W.charge A).im + (W.charge B).im = 0 := by
    have := congrArg Complex.im hsum
    simpa using this
  have hImA : 0 ≤ (W.charge A).im := by
    rcases hA' with h | h
    · exact h.le
    · exact h.1.ge
  have hImB : 0 ≤ (W.charge B).im := by
    rcases hB' with h | h
    · exact h.le
    · exact h.1.ge
  have hImA0 : (W.charge A).im = 0 := by linarith
  have hImB0 : (W.charge B).im = 0 := by linarith
  have hReA : (W.charge A).re ≤ 0 := by
    rcases hA' with h | h
    · rw [hImA0] at h
      exact absurd h (lt_irrefl 0)
    · exact h.2
  have hReB : (W.charge B).re ≤ 0 := by
    rcases hB' with h | h
    · rw [hImB0] at h
      exact absurd h (lt_irrefl 0)
    · exact h.2
  have hRe : (W.charge A).re + (W.charge B).re = 0 := by
    have := congrArg Complex.re hsum
    simpa using this
  have hReA0 : (W.charge A).re = 0 := by linarith
  have hReB0 : (W.charge B).re = 0 := by linarith
  constructor <;> [skip; skip] <;>
    exact Complex.ext (by assumption) (by assumption)

/-- **`A⁰` is closed under subobjects** (in the triangle phrasing): the left
vertex of a heart short exact sequence with zero-charge middle has zero
charge. -/
theorem zeroCharge_left {A E B : C} (hA : t.heart A) (hB : t.heart B)
    (hE : W.zeroCharge E)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : W.zeroCharge A := by
  have hsum := W.charge_triangle' hdist
  rw [hE.2] at hsum
  exact ⟨hA, (W.charge_eq_zero_pair hA hB hsum.symm).1⟩

/-- **`A⁰` is closed under quotients**: the right vertex, dually. -/
theorem zeroCharge_right {A E B : C} (hA : t.heart A) (hB : t.heart B)
    (hE : W.zeroCharge E)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : W.zeroCharge B := by
  have hsum := W.charge_triangle' hdist
  rw [hE.2] at hsum
  exact ⟨hB, (W.charge_eq_zero_pair hA hB hsum.symm).2⟩

/-- **`A⁰` is closed under extensions**: charges add on triangles. -/
theorem zeroCharge_extension {A E B : C} (hA : W.zeroCharge A)
    (hB : W.zeroCharge B) (hE : t.heart E)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : W.zeroCharge E := by
  have hsum := W.charge_triangle' hdist
  rw [hA.2, hB.2, add_zero] at hsum
  exact ⟨hE, hsum⟩

end WeakStabilityFunction

end CategoryTheory.Triangulated.WeakStabilityCondition
