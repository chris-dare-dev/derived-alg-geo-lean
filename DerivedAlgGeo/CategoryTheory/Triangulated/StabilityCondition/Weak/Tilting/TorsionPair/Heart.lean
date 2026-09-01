/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Tactic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Torsion pairs on a heart, and the tilted aisles

The Happel–Reiten–Smalø tilt: from a torsion pair on the heart of a
t-structure, a second t-structure whose heart is the extension of the torsion
class by the shifted torsion-free class.

**The tilt is constructed here**, as `HeartTorsionPair.tilt`, with every field
proved and nothing declared with `sorry`.

## The one design decision worth explaining

The tilted aisles are normally written with cohomology functors:

```
D^{≤0}_† = {X ∈ D^{≤0} : H⁰(X) ∈ T},   D^{≥0}_† = {X ∈ D^{≥-1} : H^{-1}(X) ∈ F}.
```

**Mathlib has no `Hⁿ` for a t-structure at the pin** — `TStructure/` carries
`truncLE`, `truncGE` and the truncation triangle, but no cohomology functor
into the heart. This project now constructs that functor and proves it
homological in `WeakStabilityCondition/Tilting/Cohomology/Homological.lean`;
`WeakStabilityCondition/StabilityCondition/Metric/Mass/Subadditivity/CohomologyExactness.lean`
transports the result to the stability-condition API. The aisle construction
here predates that bridge and does not depend on it.

So the aisles here are defined by **Hom-orthogonality instead**, which needs no
cohomology functor at all. For `X ∈ D^{≤0}` and `F` in the heart the counit
gives `Hom(X, F) ≅ Hom(H⁰X, F)`, and `T` is exactly the left orthogonal of `F`
in the heart, so

```
H⁰(X) ∈ T   ⟺   Hom(X, F) = 0 for every F ∈ F.
```

The right-hand side is what `tiltLE` says. It is equivalent to the usual
definition wherever the usual definition can be stated, and it is available
here, where the usual one is not. That equivalence is not only prose: with
`τ^{≥0}` (resp. `τ^{≤0}`) in the role of `H⁰`, it is the theorems
`tiltLE_iff_tors_truncGE` and `tiltGE_iff_free_truncLE` at the end of this
file.

## Status

Established here: the datum, the aisles at every integer level with their
isomorphism-closure, both factorisation lemmas standing in for the two counit
isomorphisms, the orthogonality characterisations of both classes, the
agreement of both aisles with the textbook `H⁰` formulation, and the
identification of the tilted heart with the extensions of `T` by `F⟦1⟧`.

All six non-trivial `TStructure` fields are proved, and `tilt` assembles them.
`exists_triangle_zero_one` — the last and hardest — is `exists_tilt_triangle`,
built from two octahedra and no cohomology functor.

`tilt` requires `[IsTriangulated C]`. That is not incidental: the octahedral
axiom is what makes `τ^{≥0}` preserve `D^{≤0}`, which is what puts `H⁰` in the
heart, and it is also what supplies the two octahedra. It is carried
explicitly rather than assumed globally.
-/

namespace CategoryTheory.Triangulated.Tilting

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (t : TStructure C)

/-- A torsion pair on the heart of `t`, phrased inside `C` rather than inside
the heart as a category.

Stating it in `C` avoids the full-subcategory plumbing that carrying an
`Abelian` instance on the heart would require, and the decomposition axiom
becomes a distinguished triangle — which for objects of the heart is the same
thing as a short exact sequence there. `WeakStabilityCondition/Tilting/TorsionPair/Basic.lean` is the
abelian-category version of the same notion; neither is derived from the other
here. -/
structure HeartTorsionPair where
  /-- the torsion class -/
  tors : ObjectProperty C
  /-- the torsion-free class -/
  free : ObjectProperty C
  tors_isLE : ∀ X, tors X → t.IsLE X 0
  tors_isGE : ∀ X, tors X → t.IsGE X 0
  free_isLE : ∀ X, free X → t.IsLE X 0
  free_isGE : ∀ X, free X → t.IsGE X 0
  tors_isClosedUnderIsomorphisms : tors.IsClosedUnderIsomorphisms := by infer_instance
  free_isClosedUnderIsomorphisms : free.IsClosedUnderIsomorphisms := by infer_instance
  /-- no nonzero map from a torsion object to a torsion-free one -/
  hom_eq_zero : ∀ ⦃X Y : C⦄, tors X → free Y → ∀ f : X ⟶ Y, f = 0
  /-- every object of the heart is an extension of a torsion-free object by a
  torsion one -/
  exists_triangle : ∀ X : C, t.IsLE X 0 → t.IsGE X 0 →
    ∃ (T F : C) (_ : tors T) (_ : free F) (f : T ⟶ X) (g : X ⟶ F) (h : F ⟶ T⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C

namespace HeartTorsionPair

attribute [instance] tors_isClosedUnderIsomorphisms free_isClosedUnderIsomorphisms

variable {t}
variable (P : HeartTorsionPair t)

/-! ### The tilted aisles

Stated first at the level the tilt is defined at; `tiltLEAt` / `tiltGEAt` below
extend them to every integer, which is what a `TStructure` needs. -/

/-- The tilted co-aisle `D^{≤0}_†`: objects of `D^{≤0}` with no nonzero map to
a torsion-free object. Under the counit isomorphism this says `H⁰(X) ∈ T`. -/
def tiltLE : ObjectProperty C :=
  fun X => t.IsLE X 0 ∧ ∀ F : C, P.free F → ∀ f : X ⟶ F, f = 0

/-- The tilted aisle `D^{≥1}_†`: objects of `D^{≥0}` with no nonzero map from a
torsion object. Under the counit isomorphism this says `H⁰(X) ∈ F`. -/
def tiltGE : ObjectProperty C :=
  fun X => t.IsGE X 0 ∧ ∀ T : C, P.tors T → ∀ f : T ⟶ X, f = 0

instance tiltLE_isClosedUnderIsomorphisms : P.tiltLE.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hle, horth⟩ := hX
    refine ⟨t.isLE_of_iso e 0, fun F hF f => ?_⟩
    have := horth F hF (e.hom ≫ f)
    calc f = e.inv ≫ (e.hom ≫ f) := by simp
    _ = 0 := by rw [this, comp_zero]

instance tiltGE_isClosedUnderIsomorphisms : P.tiltGE.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hge, horth⟩ := hX
    refine ⟨t.isGE_of_iso e 0, fun T hT f => ?_⟩
    have := horth T hT (f ≫ e.inv)
    calc f = (f ≫ e.inv) ≫ e.hom := by simp
    _ = 0 := by rw [this, zero_comp]

/-! ### The factorisation lemmas

Everything the Hom-vanishing axiom needs, and the substitute for the counit
isomorphism `Hom(X, F) ≅ Hom(H⁰X, F)` that a cohomology functor would supply.
The dual pair below it is the substitute for the other adjunction's
`Hom(T, X) ≅ Hom(T, H⁰X)`, and is what the aisle-side textbook agreement
(`freeOrth_iff_free_truncLE`) runs on. -/

/-- **Every map into `D^{≥0}` factors through the truncation `τ^{≥0}`.**

This is the half of the counit isomorphism the tilt actually uses. When
additionally `X ∈ D^{≤0}` the target `τ^{≥0}X` lies in the heart and plays the
role of `H⁰(X)`, so this is what lets an orthogonality hypothesis on `X` be
transported to one on `H⁰(X)`.

No hypothesis on `X` is needed: the truncation triangle exists for every
object, and `Hom(τ^{<0}X, F)` vanishes for degree reasons alone. -/
theorem exists_factor_truncGE {X F : C} (hF : t.IsGE F 0) (f : X ⟶ F) :
    ∃ g : ((t.triangleLTGE 0).obj X).obj₃ ⟶ F,
      f = ((t.triangleLTGE 0).obj X).mor₂ ≫ g := by
  refine Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished 0 X) f ?_
  exact t.zero_of_isLE_of_isGE _ (0 - 1) 0 (by lia) inferInstance hF

/-- The factorisation is unique: `τ^{≥0}X` really does corepresent maps out of
`X` into `D^{≥0}`, not merely dominate them. -/
theorem factor_truncGE_unique {X F : C} (hF : t.IsGE F 0)
    {g₁ g₂ : ((t.triangleLTGE 0).obj X).obj₃ ⟶ F}
    (h : ((t.triangleLTGE 0).obj X).mor₂ ≫ g₁
       = ((t.triangleLTGE 0).obj X).mor₂ ≫ g₂) :
    g₁ = g₂ := by
  rw [← sub_eq_zero]
  obtain ⟨h', hh'⟩ :=
    Triangle.yoneda_exact₃ _ (t.triangleLTGE_distinguished 0 X) (g₁ - g₂)
      (by rw [Preadditive.comp_sub, h, sub_self])
  have hzero : h' = 0 :=
    t.zero_of_isLE_of_isGE h' (0 - 1 - 1) 0 (by lia)
      (t.isLE_shift _ (0 - 1) 1 (0 - 1 - 1) (by lia)) hF
  rw [hh', hzero, comp_zero]

/-- **Every map from `D^{≤0}` factors through the truncation `τ^{≤0}`.**

The dual of `exists_factor_truncGE`. When additionally `X ∈ D^{≥0}` the source
`τ^{≤0}X` lies in the heart and plays the role of `H⁰(X)`, so this is what
lets an orthogonality hypothesis on `X` be transported to one on `H⁰(X)` from
the torsion side.

As with its dual, no hypothesis on `X` is needed: the truncation triangle
exists for every object, and `Hom(A, τ^{≥1}X)` vanishes for degree reasons
alone. -/
theorem exists_factor_truncLE {A X : C} (hA : t.IsLE A 0) (f : A ⟶ X) :
    ∃ g : A ⟶ ((t.triangleLTGE 1).obj X).obj₁,
      f = g ≫ ((t.triangleLTGE 1).obj X).mor₁ := by
  refine Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished 1 X) f ?_
  exact t.zero_of_isLE_of_isGE _ 0 1 (by lia) hA inferInstance

/-- The factorisation is unique: `τ^{≤0}X` really does represent maps from
`D^{≤0}` into `X`, not merely dominate them. The inverse rotation replaces
the rotation of the dual proof, and no rotation sign is ever inspected. -/
theorem factor_truncLE_unique {A X : C} (hA : t.IsLE A 0)
    {g₁ g₂ : A ⟶ ((t.triangleLTGE 1).obj X).obj₁}
    (h : g₁ ≫ ((t.triangleLTGE 1).obj X).mor₁
       = g₂ ≫ ((t.triangleLTGE 1).obj X).mor₁) :
    g₁ = g₂ := by
  rw [← sub_eq_zero]
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _
    (inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 1 X)) (g₁ - g₂)
    (by
      show (g₁ - g₂) ≫ ((t.triangleLTGE 1).obj X).mor₁ = 0
      rw [Preadditive.sub_comp, h, sub_self])
  have hk0 : k = 0 :=
    t.zero_of_isLE_of_isGE k 0 2 (by lia) hA
      (t.isGE_shift _ 1 (-1) 2 (by lia))
  rw [hk, hk0]
  exact zero_comp

/-! ### Orthogonality characterisations

Each class is the orthogonal of the other *inside the heart*. The forward
direction is the `hom_eq_zero` axiom; the converse is where the decomposition
axiom earns its place, and it needs no cohomology functor — only that a
distinguished triangle whose second map vanishes has a zero third object, which
here follows from a degree count. -/

/-- An object of the heart with no nonzero map to a torsion-free object is
torsion. -/
theorem tors_of_orthogonal {A : C} (hle : t.IsLE A 0) (hge : t.IsGE A 0)
    (h : ∀ Y : C, P.free Y → ∀ u : A ⟶ Y, u = 0) : P.tors A := by
  obtain ⟨T, Y, hT, hY, i, p, d, hdist⟩ := P.exists_triangle A hle hge
  haveI := P.tors_isLE T hT
  have hYzero : IsZero Y := by
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ hdist (𝟙 Y) (by show p ≫ 𝟙 Y = 0; simpa using h Y hY p)
    have hk0 : k = 0 :=
      t.zero_of_isLE_of_isGE k (-1) 0 (by lia)
        (t.isLE_shift T 0 1 (-1) (by lia)) (P.free_isGE Y hY)
    rw [IsZero.iff_id_eq_zero, hk, hk0]
    exact comp_zero
  haveI : IsIso i := (Triangle.isZero₃_iff_isIso₁ _ hdist).mp hYzero
  exact ObjectProperty.prop_of_iso P.tors (asIso i) hT

/-- An object of the heart with no nonzero map from a torsion object is
torsion-free. The dual of `tors_of_orthogonal`: the inverse rotation replaces
the rotation, and no rotation sign is ever inspected. -/
theorem free_of_orthogonal {A : C} (hle : t.IsLE A 0) (hge : t.IsGE A 0)
    (h : ∀ T : C, P.tors T → ∀ u : T ⟶ A, u = 0) : P.free A := by
  obtain ⟨T, F, hT, hF, i, p, d, hdist⟩ := P.exists_triangle A hle hge
  haveI := P.free_isGE F hF
  have hTzero : IsZero T := by
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hdist) (𝟙 T)
      (by
        show 𝟙 T ≫ i = 0
        rw [Category.id_comp]
        exact h T hT i)
    have hk0 : k = 0 :=
      t.zero_of_isLE_of_isGE k 0 1 (by lia) (P.tors_isLE T hT)
        (t.isGE_shift F 0 (-1) 1 (by lia))
    rw [IsZero.iff_id_eq_zero, hk, hk0]
    exact zero_comp
  haveI : IsIso p := (Triangle.isZero₁_iff_isIso₂ _ hdist).mp hTzero
  exact ObjectProperty.prop_of_iso P.free (asIso p).symm hF

/-! ### The Hom-vanishing axiom

`zero'` for the tilted t-structure, proved without any cohomology functor: the
factorisation lemma moves the orthogonality hypothesis from `X` onto
`τ^{≥0}X`, and `tors_of_orthogonal` then puts that truncation in the torsion
class, where the second aisle's hypothesis kills it. -/

/-- **No nonzero map from the tilted co-aisle to the tilted aisle.** -/
theorem hom_eq_zero_of_tiltLE_of_tiltGE [IsTriangulated C] {X Y : C}
    (hX : P.tiltLE X) (hY : P.tiltGE Y) (f : X ⟶ Y) : f = 0 := by
  obtain ⟨hXle, hXorth⟩ := hX
  obtain ⟨hYge, hYorth⟩ := hY
  haveI := hXle
  obtain ⟨g, hg⟩ := exists_factor_truncGE hYge f
  -- `τ^{≥0}X` lies in the heart: `IsGE` by construction, `IsLE` because `X` is.
  have hobj : ((t.triangleLTGE 0).obj X).obj₃ = (t.truncGE 0).obj X := rfl
  have hle3 : t.IsLE (((t.triangleLTGE 0).obj X).obj₃) 0 := by
    rw [hobj]; infer_instance
  have hge3 : t.IsGE (((t.triangleLTGE 0).obj X).obj₃) 0 := inferInstance
  have hTorth : ∀ Z : C, P.free Z →
      ∀ u : ((t.triangleLTGE 0).obj X).obj₃ ⟶ Z, u = 0 := by
    intro Z hZ u
    refine factor_truncGE_unique (P.free_isGE Z hZ) ?_
    rw [comp_zero]
    exact hXorth Z hZ _
  have htors : P.tors (((t.triangleLTGE 0).obj X).obj₃) :=
    P.tors_of_orthogonal hle3 hge3 hTorth
  rw [hg, hYorth _ htors g]
  exact comp_zero

/-! ### The indexed families

A `Triangulated.TStructure` needs an aisle at every integer, not just at the
level the tilt is defined. Splitting the orthogonality condition off as its own
isomorphism-closed predicate is what keeps the shift axioms to a single
application of `shiftFunctorAdd'` each. -/

/-- Objects with no nonzero map to a torsion-free object. -/
def torsOrth : ObjectProperty C := fun Y => ∀ F : C, P.free F → ∀ f : Y ⟶ F, f = 0

/-- Objects with no nonzero map from a torsion object. -/
def freeOrth : ObjectProperty C := fun Y => ∀ T : C, P.tors T → ∀ f : T ⟶ Y, f = 0

instance torsOrth_isClosedUnderIsomorphisms : P.torsOrth.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX F hF f := by
    have hz := hX F hF (e.hom ≫ f)
    calc f = e.inv ≫ (e.hom ≫ f) := by simp
    _ = 0 := by rw [hz, comp_zero]

instance freeOrth_isClosedUnderIsomorphisms : P.freeOrth.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX T hT f := by
    have hz := hX T hT (f ≫ e.inv)
    calc f = (f ≫ e.inv) ≫ e.hom := by simp
    _ = 0 := by rw [hz, zero_comp]

/-- The tilted co-aisle at level `n`: `X ∈ D^{≤n}_†` iff `X⟦n⟧ ∈ D^{≤0}_†`. -/
def tiltLEAt (n : ℤ) : ObjectProperty C :=
  fun X => t.IsLE X n ∧ P.torsOrth (X⟦n⟧)

/-- The tilted aisle at level `n`: `X ∈ D^{≥n}_†` iff `X⟦n-1⟧ ∈ D^{≥1}_†`,
and `tiltGE` is the level-one member. -/
def tiltGEAt (n : ℤ) : ObjectProperty C :=
  fun X => t.IsGE X (n - 1) ∧ P.freeOrth (X⟦n - 1⟧)

/-! #### Agreement with the level at which the tilt was defined -/

theorem tiltLEAt_zero_iff (X : C) : P.tiltLEAt 0 X ↔ P.tiltLE X := by
  constructor
  · rintro ⟨hle, horth⟩
    exact ⟨hle, ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X) horth⟩
  · rintro ⟨hle, horth⟩
    exact ⟨hle, ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X).symm horth⟩

theorem tiltGEAt_one_iff (X : C) : P.tiltGEAt 1 X ↔ P.tiltGE X := by
  have h : (1 : ℤ) - 1 = 0 := by ring
  rw [tiltGEAt, tiltGE, h]
  constructor
  · rintro ⟨hge, horth⟩
    exact ⟨hge, ObjectProperty.prop_of_iso P.freeOrth ((shiftFunctorZero C ℤ).app X) horth⟩
  · rintro ⟨hge, horth⟩
    exact ⟨hge, ObjectProperty.prop_of_iso P.freeOrth ((shiftFunctorZero C ℤ).app X).symm horth⟩

/-! #### The shift axioms

Each is one application of `shiftFunctorAdd'` against the orthogonality
predicate's isomorphism-closure, plus the corresponding `IsLE`/`IsGE` shift. -/

/-- The `le_shift` field for the tilted co-aisle. -/
theorem tiltLEAt_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : P.tiltLEAt n X) :
    P.tiltLEAt n' (X⟦a⟧) := by
  obtain ⟨hle, horth⟩ := hX
  haveI := hle
  exact ⟨t.isLE_shift X n a n' h,
    ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorAdd' C a n' n h).app X) horth⟩

/-- The `ge_shift` field for the tilted aisle. -/
theorem tiltGEAt_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : P.tiltGEAt n X) :
    P.tiltGEAt n' (X⟦a⟧) := by
  obtain ⟨hge, horth⟩ := hX
  haveI := hge
  exact ⟨t.isGE_shift X (n - 1) a (n' - 1) (by lia),
    ObjectProperty.prop_of_iso P.freeOrth
      ((shiftFunctorAdd' C a (n' - 1) (n - 1) (by lia)).app X) horth⟩

/-! #### The two inclusions

Both are pure degree counts: neither uses the orthogonality hypothesis it is
handed, because the shifted object is already separated from the heart by
`t.zero`. -/

/-- The `le_zero_le` field. -/
theorem tiltLEAt_zero_le : P.tiltLEAt 0 ≤ P.tiltLEAt 1 := by
  rintro X ⟨hle, -⟩
  haveI := hle
  refine ⟨t.isLE_of_le X 0 1 (by lia), ?_⟩
  intro F hF f
  exact t.zero_of_isLE_of_isGE f (-1) 0 (by lia)
    (t.isLE_shift X 0 1 (-1) (by lia)) (P.free_isGE F hF)

/-- The `ge_one_le` field. -/
theorem tiltGEAt_one_le : P.tiltGEAt 1 ≤ P.tiltGEAt 0 := by
  rintro X ⟨hge, -⟩
  haveI := hge
  refine ⟨t.isGE_of_ge X (0 - 1) (1 - 1) (by lia), ?_⟩
  intro T hT f
  exact t.zero_of_isLE_of_isGE f 0 1 (by lia) (P.tors_isLE T hT)
    (t.isGE_shift X (1 - 1) (0 - 1) 1 (by lia))

/-- The `zero'` field, transported to the indexed families. -/
theorem tiltAt_zero' [IsTriangulated C] {X Y : C}
    (hX : P.tiltLEAt 0 X) (hY : P.tiltGEAt 1 Y) (f : X ⟶ Y) : f = 0 :=
  P.hom_eq_zero_of_tiltLE_of_tiltGE ((P.tiltLEAt_zero_iff X).mp hX)
    ((P.tiltGEAt_one_iff Y).mp hY) f

/-! ### Recognising the two aisles from a triangle

These are the shapes the two halves of a tilted truncation take, and they are
the reason the tilt does **not** need a cohomology functor after all.

The textbook construction of `exists_triangle_zero_one` says: cut `H⁰(A)` by
the torsion pair as `0 → T₀ → H⁰(A) → F₀ → 0`, then take

```
X = extension of T₀ by τ^{≤-1}A,      Y = extension of τ^{≥1}A by F₀.
```

Membership of `X` and `Y` in the two aisles is then usually read off a long
exact cohomology sequence. The two lemmas below get it instead from
`isLE₂`/`isGE₂` plus a single factorisation through the triangle — no `Hⁿ`
anywhere.

A first attempt built `X` as the fibre of `τ^{≤0}A → F₀` instead. That shape
does **not** work formally: `IsLE X 0` then sits between `0` and
`Hom(F₀⟦-1⟧, Z)`, which does not vanish for degree reasons, and recovering it
genuinely needs that `H⁰(A) → F₀` is epi. The extension shape below avoids that
entirely, because both of its ends are already in `D^{≤0}`. -/

/-- **An extension of a torsion object by an object of `D^{≤-1}` lies in the
tilted co-aisle.** -/
theorem tiltLE_of_triangle {Z X T₀ : C} (hZ : t.IsLE Z (-1)) (hT : P.tors T₀)
    {f : Z ⟶ X} {g : X ⟶ T₀} {h : T₀ ⟶ Z⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : P.tiltLE X := by
  haveI := hZ
  haveI := P.tors_isLE T₀ hT
  refine ⟨t.isLE₂ _ hdist 0 (t.isLE_of_le Z (-1) 0 (by lia)) (P.tors_isLE T₀ hT), ?_⟩
  intro F' hF' u
  obtain ⟨u', hu'⟩ := Triangle.yoneda_exact₂ _ hdist u
    (t.zero_of_isLE_of_isGE _ (-1) 0 (by lia) hZ (P.free_isGE F' hF'))
  rw [hu', P.hom_eq_zero hT hF' u']
  exact comp_zero

/-- **An extension of an object of `D^{≥1}` by a torsion-free object lies in
the tilted aisle.** -/
theorem tiltGE_of_triangle {F₀ Y W : C} (hF : P.free F₀) (hW : t.IsGE W 1)
    {f : F₀ ⟶ Y} {g : Y ⟶ W} {h : W ⟶ F₀⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : P.tiltGE Y := by
  haveI := hW
  haveI := P.free_isGE F₀ hF
  refine ⟨t.isGE₂ _ hdist 0 (P.free_isGE F₀ hF) (t.isGE_of_ge W 0 1 (by lia)), ?_⟩
  intro T hT u
  obtain ⟨u', hu'⟩ := Triangle.coyoneda_exact₂ _ hdist u
    (t.zero_of_isLE_of_isGE _ 0 1 (by lia) (P.tors_isLE T hT) hW)
  rw [hu', P.hom_eq_zero hT hF u']
  exact zero_comp

/-- The co-aisle recognition, in the indexed form a `TStructure` field wants. -/
theorem tiltLEAt_zero_of_triangle {Z X T₀ : C} (hZ : t.IsLE Z (-1)) (hT : P.tors T₀)
    {f : Z ⟶ X} {g : X ⟶ T₀} {h : T₀ ⟶ Z⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : P.tiltLEAt 0 X :=
  (P.tiltLEAt_zero_iff X).mpr (P.tiltLE_of_triangle hZ hT hdist)

/-- The aisle recognition, in the indexed form a `TStructure` field wants. -/
theorem tiltGEAt_one_of_triangle {F₀ Y W : C} (hF : P.free F₀) (hW : t.IsGE W 1)
    {f : F₀ ⟶ Y} {g : Y ⟶ W} {h : W ⟶ F₀⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : P.tiltGEAt 1 Y :=
  (P.tiltGEAt_one_iff Y).mpr (P.tiltGE_of_triangle hF hW hdist)

/-! ### The truncation triangle for the tilted aisles

The last field. Two octahedra do all the work, and the choice of *which*
octahedron is the whole trick:

* `Octahedron'` works with **fibres**, and applied to `B ⟶ H ⟶ F₀` its three
  fibres are `Z`, `X`, `T₀` — delivering `Z ⟶ X ⟶ T₀` with no desuspension.
  The cone-flavoured `Octahedron` would give the same triangle shifted once,
  and unshifting it costs sign bookkeeping for nothing.
* `Octahedron` works with **cones**, and applied to `X ⟶ B ⟶ A` its three
  cones are `F₀`, `Y`, `W` — delivering `F₀ ⟶ Y ⟶ W` directly.

Both outputs are exactly what `tiltLE_of_triangle` and `tiltGE_of_triangle`
consume. -/

/-- **The tilted truncation triangle, from abstract triangle data.**

Separated from the instantiation so that the octahedral content is visible on
its own: given the two t-structure truncation triangles and the torsion
decomposition of the heart object between them, this produces the tilted
truncation of `A`. -/
theorem exists_tilt_triangle_of_data [IsTriangulated C] {A B W Z H T₀ F₀ : C}
    {zb : Z ⟶ B} {bh : B ⟶ H} {hz : H ⟶ Z⟦(1 : ℤ)⟧}
    (hZBH : Triangle.mk zb bh hz ∈ distTriang C)
    {ba : B ⟶ A} {aw : A ⟶ W} {wb : W ⟶ B⟦(1 : ℤ)⟧}
    (hBAW : Triangle.mk ba aw wb ∈ distTriang C)
    {th : T₀ ⟶ H} {hf : H ⟶ F₀} {ft : F₀ ⟶ T₀⟦(1 : ℤ)⟧}
    (hTHF : Triangle.mk th hf ft ∈ distTriang C)
    (hZ : t.IsLE Z (-1)) (hT : P.tors T₀) (hF : P.free F₀) (hW : t.IsGE W 1) :
    ∃ (X Y : C) (_ : P.tiltLEAt 0 X) (_ : P.tiltGEAt 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- `X` is the fibre of `B ⟶ F₀`; the fibre octahedron makes it an extension
  -- of `T₀` by `Z`, which is the shape the co-aisle recognises.
  obtain ⟨X, xb, fx, hXBF⟩ := distinguished_cocone_triangle₁ (bh ≫ hf)
  have hX : P.tiltLEAt 0 X :=
    P.tiltLEAt_zero_of_triangle hZ hT
      (Triangulated.someOctahedron' rfl hZBH hTHF hXBF).mem
  -- `Y` is the cone of `X ⟶ A`; the cone octahedron makes it an extension of
  -- `W` by `F₀`, which is the shape the aisle recognises.
  obtain ⟨Y, ay, yx, hXAY⟩ := distinguished_cocone_triangle (xb ≫ ba)
  have hY : P.tiltGEAt 1 Y :=
    P.tiltGEAt_one_of_triangle hF hW
      (Triangulated.someOctahedron rfl hXBF hBAW hXAY).mem
  exact ⟨X, Y, hX, hY, xb ≫ ba, ay, yx, hXAY⟩

/-- **`exists_triangle_zero_one` for the tilted aisles.**

Every object has a tilted truncation. With the five fields already proved
above, this completes the Happel–Reiten–Smalø tilt as a `TStructure`. -/
theorem exists_tilt_triangle [IsTriangulated C] (A : C) :
    ∃ (X Y : C) (_ : P.tiltLEAt 0 X) (_ : P.tiltGEAt 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  -- `B = τ^{≤0}A`, `W = τ^{≥1}A`.
  have hBAW := t.triangleLTGE_distinguished 1 A
  set B := ((t.triangleLTGE 1).obj A).obj₁ with hBdef
  haveI : t.IsLE B 0 := t.isLE_of_le B (1 - 1) 0 (by lia)
  -- `Z = τ^{≤-1}B`, `H = τ^{≥0}B`, and `H` lies in the heart.
  have hZBH := t.triangleLTGE_distinguished 0 B
  -- `IsGE` is immediate; `IsLE` needs the octahedral axiom, via the same
  -- `truncGE`-preserves-`D^{≤0}` instance that `zero'` leans on.
  have hHle : t.IsLE ((t.triangleLTGE 0).obj B).obj₃ 0 := by
    have hobj : ((t.triangleLTGE 0).obj B).obj₃ = (t.truncGE 0).obj B := rfl
    rw [hobj]; infer_instance
  obtain ⟨T₀, F₀, hT, hF, th, hf, ft, hTHF⟩ :=
    P.exists_triangle ((t.triangleLTGE 0).obj B).obj₃ hHle inferInstance
  exact P.exists_tilt_triangle_of_data hZBH hBAW hTHF
    (t.isLE_of_le _ (0 - 1) (-1) (by lia)) hT hF inferInstance

/-! ### The tilt

All six non-trivial fields are proved, so the tilted aisles assemble into an
honest `Triangulated.TStructure`. -/

instance tiltLEAt_isClosedUnderIsomorphisms (n : ℤ) :
    (P.tiltLEAt n).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hle, horth⟩ := hX
    haveI := hle
    exact ⟨t.isLE_of_iso e n,
      ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctor C n).mapIso e) horth⟩

instance tiltGEAt_isClosedUnderIsomorphisms (n : ℤ) :
    (P.tiltGEAt n).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hge, horth⟩ := hX
    haveI := hge
    exact ⟨t.isGE_of_iso e (n - 1),
      ObjectProperty.prop_of_iso P.freeOrth ((shiftFunctor C (n - 1)).mapIso e) horth⟩

/-- **The Happel–Reiten–Smalø tilt of `t` at the torsion pair `P`.**

The aisles are `tiltLEAt` and `tiltGEAt`; every field is one of the theorems
above. No cohomology functor appears anywhere in the construction — see the
module docstring for why the usual one is unavailable here and what replaces
it. -/
def tilt [IsTriangulated C] : TStructure C where
  le := P.tiltLEAt
  ge := P.tiltGEAt
  le_isClosedUnderIsomorphisms n := P.tiltLEAt_isClosedUnderIsomorphisms n
  ge_isClosedUnderIsomorphisms n := P.tiltGEAt_isClosedUnderIsomorphisms n
  le_shift := P.tiltLEAt_shift
  ge_shift := P.tiltGEAt_shift
  zero' _ _ f hX hY := P.tiltAt_zero' hX hY f
  le_zero_le := P.tiltLEAt_zero_le
  ge_one_le := P.tiltGEAt_one_le
  exists_triangle_zero_one := P.exists_tilt_triangle

@[simp]
theorem tilt_le [IsTriangulated C] (n : ℤ) : (P.tilt).le n = P.tiltLEAt n := rfl

@[simp]
theorem tilt_ge [IsTriangulated C] (n : ℤ) : (P.tilt).ge n = P.tiltGEAt n := rfl

/-- The tilt of the degenerate torsion pair changes nothing at level zero on
the co-aisle side, in the sense that its membership is the original `IsLE`
condition together with a vacuous orthogonality clause. Recorded as a sanity
check on the indexing rather than as a result. -/
theorem tilt_le_zero_iff [IsTriangulated C] (X : C) :
    (P.tilt).le 0 X ↔ (t.IsLE X 0 ∧ P.torsOrth (X⟦(0 : ℤ)⟧)) := Iff.rfl

/-! ### Agreement with the textbook aisles

The module docstring claims the Hom-orthogonal aisles agree with the textbook
`H⁰` formulation wherever the latter can be stated. At this pin the textbook
side **is** statable, with `τ^{≥0}` (resp. `τ^{≤0}`) in the role of `H⁰` on
`D^{≤0}` (resp. `D^{≥0}`), and the four theorems below are that claim. Each
direction is the factorisation lemma on one side and the orthogonality
characterisation or the `hom_eq_zero` axiom on the other; `[IsTriangulated C]`
is what puts the truncation in the heart, exactly as in `zero'`. -/

/-- **The co-aisle orthogonality condition is the textbook `H⁰` condition**:
for `X ∈ D^{≤0}`, orthogonality to the torsion-free class is torsionness of
`τ^{≥0}X`. -/
theorem torsOrth_iff_tors_truncGE [IsTriangulated C] {X : C} (hX : t.IsLE X 0) :
    P.torsOrth X ↔ P.tors ((t.truncGE 0).obj X) := by
  haveI := hX
  have hobj : ((t.triangleLTGE 0).obj X).obj₃ = (t.truncGE 0).obj X := rfl
  rw [← hobj]
  constructor
  · intro horth
    have hle3 : t.IsLE (((t.triangleLTGE 0).obj X).obj₃) 0 := by
      rw [hobj]; infer_instance
    refine P.tors_of_orthogonal hle3 inferInstance ?_
    intro Z hZ u
    refine factor_truncGE_unique (P.free_isGE Z hZ) ?_
    rw [comp_zero]
    exact horth Z hZ _
  · intro htors F hF f
    obtain ⟨g, hg⟩ := exists_factor_truncGE (P.free_isGE F hF) f
    rw [hg, P.hom_eq_zero htors hF g]
    exact comp_zero

/-- **The aisle orthogonality condition is the textbook `H⁰` condition**: for
`X ∈ D^{≥0}`, orthogonality to the torsion class is torsion-freeness of
`τ^{≤0}X`. -/
theorem freeOrth_iff_free_truncLE [IsTriangulated C] {X : C} (hX : t.IsGE X 0) :
    P.freeOrth X ↔ P.free ((t.truncLE 0).obj X) := by
  haveI := hX
  have hobj : ((t.triangleLTGE 1).obj X).obj₁ = (t.truncLE 0).obj X := rfl
  rw [← hobj]
  constructor
  · intro horth
    have hge1 : t.IsGE (((t.triangleLTGE 1).obj X).obj₁) 0 := by
      rw [hobj]; infer_instance
    have hle1 : t.IsLE (((t.triangleLTGE 1).obj X).obj₁) 0 :=
      t.isLE_of_le _ (1 - 1) 0 (by lia)
    refine P.free_of_orthogonal hle1 hge1 ?_
    intro T hT u
    refine factor_truncLE_unique (P.tors_isLE T hT) ?_
    rw [zero_comp]
    exact horth T hT _
  · intro hfree T hT f
    obtain ⟨g, hg⟩ := exists_factor_truncLE (P.tors_isLE T hT) f
    rw [hg, P.hom_eq_zero hT hfree g]
    exact zero_comp

/-- **The tilted co-aisle is the textbook one**: `X ∈ D^{≤0}_†` iff
`X ∈ D^{≤0}` and `H⁰(X) ∈ T`, with `τ^{≥0}X` in the role of `H⁰(X)`. -/
theorem tiltLE_iff_tors_truncGE [IsTriangulated C] (X : C) :
    P.tiltLE X ↔ t.IsLE X 0 ∧ P.tors ((t.truncGE 0).obj X) := by
  constructor
  · rintro ⟨hle, horth⟩
    exact ⟨hle, (P.torsOrth_iff_tors_truncGE hle).mp horth⟩
  · rintro ⟨hle, htors⟩
    exact ⟨hle, (P.torsOrth_iff_tors_truncGE hle).mpr htors⟩

/-- **The tilted aisle is the textbook one**: `X ∈ D^{≥1}_†` iff `X ∈ D^{≥0}`
and `H⁰(X) ∈ F`, with `τ^{≤0}X` in the role of `H⁰(X)`. -/
theorem tiltGE_iff_free_truncLE [IsTriangulated C] (X : C) :
    P.tiltGE X ↔ t.IsGE X 0 ∧ P.free ((t.truncLE 0).obj X) := by
  constructor
  · rintro ⟨hge, horth⟩
    exact ⟨hge, (P.freeOrth_iff_free_truncLE hge).mp horth⟩
  · rintro ⟨hge, hfree⟩
    exact ⟨hge, (P.freeOrth_iff_free_truncLE hge).mpr hfree⟩

/-! ### The tilted heart

The textbook description `A† = ⟨F⟦1⟧, T⟩`. Because `(T, F)` is a torsion
pair the extension closure collapses to a single step, so the identification
is an iff: an object lies in the tilted heart exactly when it is an extension
of a torsion object by a shifted torsion-free one. No cohomology functor and
no truncation–shift commutation appears anywhere: the forward direction reads
both memberships off the truncation triangle of `X` and its `⟦-1⟧`-shift, and
the backward direction is the two recognition lemmas, once directly and once
through the `⟦-1⟧`-shift of the given triangle. -/

/-- **An extension of a torsion object by a shifted torsion-free object lies
in the tilted heart.** -/
theorem tilt_heart_of_triangle [IsTriangulated C] {F₀ X T₀ : C}
    (hF : P.free F₀) (hT : P.tors T₀)
    {f : F₀⟦(1 : ℤ)⟧ ⟶ X} {g : X ⟶ T₀} {h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g h ∈ distTriang C) : (P.tilt).heart X := by
  haveI := P.free_isLE F₀ hF
  haveI := P.free_isGE F₀ hF
  rw [TStructure.mem_heart_iff]
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · show P.tiltLEAt 0 X
    exact P.tiltLEAt_zero_of_triangle (t.isLE_shift F₀ 0 1 (-1) (by lia)) hT hdist
  · show P.tiltGEAt 0 X
    have hdist' := Triangle.shift_distinguished _ hdist (-1)
    have hF' : P.free ((F₀⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) :=
      ObjectProperty.prop_of_iso P.free
        (((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by lia)).app F₀).symm) hF
    have hW : t.IsGE (T₀⟦(-1 : ℤ)⟧) 1 := by
      haveI := P.tors_isGE T₀ hT
      exact t.isGE_shift T₀ 0 (-1) 1 (by lia)
    have h1 : P.tiltGEAt 1 (X⟦(-1 : ℤ)⟧) :=
      (P.tiltGEAt_one_iff _).mpr (P.tiltGE_of_triangle hF' hW hdist')
    exact ObjectProperty.prop_of_iso (P.tiltGEAt 0)
      ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X)
      (P.tiltGEAt_shift 1 1 0 (by lia) _ h1)

/-- **Every object of the tilted heart is an extension of a torsion object by
a shifted torsion-free one** — the truncation triangle of `X`, with `τ^{≥0}X`
torsion by `torsOrth_iff_tors_truncGE` and `(τ^{<0}X)⟦-1⟧` torsion-free by
`free_of_orthogonal` and one coyoneda factorisation. -/
theorem exists_triangle_of_tilt_heart [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) :
    ∃ (F₀ T₀ : C) (_ : P.free F₀) (_ : P.tors T₀) (f : F₀⟦(1 : ℤ)⟧ ⟶ X)
      (g : X ⟶ T₀) (h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  rw [TStructure.mem_heart_iff] at hX
  obtain ⟨⟨hle⟩, ⟨hge⟩⟩ := hX
  obtain ⟨hXle, horth⟩ := hle
  obtain ⟨hXge, hforth⟩ := hge
  haveI := hXle
  haveI := hXge
  have hdist := t.triangleLTGE_distinguished 0 X
  -- `τ^{≥0}X` is torsion.
  have htors : P.tors (((t.triangleLTGE 0).obj X).obj₃) :=
    (P.torsOrth_iff_tors_truncGE hXle).mp
      (ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X) horth)
  -- `(τ^{<0}X)⟦-1⟧` lies in the heart.
  have hobj₁ : ((t.triangleLTGE 0).obj X).obj₁ = (t.truncLT 0).obj X := rfl
  haveI : t.IsLE (((t.triangleLTGE 0).obj X).obj₁) (0 - 1) := inferInstance
  haveI : t.IsGE (((t.triangleLTGE 0).obj X).obj₁) (0 - 1) := by
    rw [hobj₁]; infer_instance
  have hle₀ : t.IsLE ((((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧) 0 :=
    t.isLE_shift _ (0 - 1) (-1) 0 (by lia)
  have hge₀ : t.IsGE ((((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧) 0 :=
    t.isGE_shift _ (0 - 1) (-1) 0 (by lia)
  -- `(τ^{<0}X)⟦-1⟧` is torsion-free: a torsion map into it composes to a map
  -- into `X⟦-1⟧`, which dies by the aisle membership, and the composition is
  -- injective for degree reasons via the shifted truncation triangle.
  have hfree : P.free ((((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧) := by
    refine P.free_of_orthogonal hle₀ hge₀ ?_
    intro T hT u
    have hdist' := Triangle.shift_distinguished _ hdist (-1)
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hdist') u
      (hforth T hT _)
    have hk0 : k = 0 := by
      have hobj₃ : ((shiftFunctor (Triangle C) (-1 : ℤ)).obj
            ((t.triangleLTGE 0).obj X)).obj₃
          = (((t.triangleLTGE 0).obj X).obj₃)⟦(-1 : ℤ)⟧ := rfl
      haveI : t.IsGE (((shiftFunctor (Triangle C) (-1 : ℤ)).obj
          ((t.triangleLTGE 0).obj X)).obj₃) 1 := by
        rw [hobj₃]; exact t.isGE_shift _ 0 (-1) 1 (by lia)
      exact t.zero_of_isLE_of_isGE k 0 2 (by lia) (P.tors_isLE T hT)
        (t.isGE_shift _ 1 (-1) 2 (by lia))
    rw [hk, hk0]
    exact zero_comp
  -- assemble the triangle along `(τ^{<0}X)⟦-1⟧⟦1⟧ ≅ τ^{<0}X`.
  have e := (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app
    (((t.triangleLTGE 0).obj X).obj₁)
  refine ⟨(((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧,
    ((t.triangleLTGE 0).obj X).obj₃, hfree, htors,
    e.hom ≫ ((t.triangleLTGE 0).obj X).mor₁, ((t.triangleLTGE 0).obj X).mor₂,
    ((t.triangleLTGE 0).obj X).mor₃ ≫ e.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ hdist _ ?_
  exact Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp [← Functor.map_comp])

/-- **The tilted heart is the textbook one**: extensions of `T` by `F⟦1⟧`.
The single-step form is exact because `(T, F)` is a torsion pair, so this is
the identification `A† = ⟨F⟦1⟧, T⟩` with no extension-closure operator
needed. -/
theorem tilt_heart_iff [IsTriangulated C] (X : C) :
    (P.tilt).heart X ↔
      ∃ (F₀ T₀ : C) (_ : P.free F₀) (_ : P.tors T₀) (f : F₀⟦(1 : ℤ)⟧ ⟶ X)
        (g : X ⟶ T₀) (h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C := by
  constructor
  · exact P.exists_triangle_of_tilt_heart
  · rintro ⟨F₀, T₀, hF, hT, f, g, h, hdist⟩
    exact P.tilt_heart_of_triangle hF hT hdist

/-! ### What is proved, and what is not

**Every field of `Triangulated.TStructure` is proved**, and `tilt` is the
resulting t-structure:

| field | theorem |
|---|---|
| `le_isClosedUnderIsomorphisms` / `ge_…` | `tiltLEAt_isClosedUnderIsomorphisms` / `tiltGEAt_…` |
| `le_shift` / `ge_shift` | `tiltLEAt_shift` / `tiltGEAt_shift` |
| `le_zero_le` / `ge_one_le` | `tiltLEAt_zero_le` / `tiltGEAt_one_le` |
| `zero'` | `tiltAt_zero'`, on `hom_eq_zero_of_tiltLE_of_tiltGE` |
| `exists_triangle_zero_one` | `exists_tilt_triangle` |

Neither inclusion uses the orthogonality hypothesis it is handed — both are
pure degree counts against `t.zero`.

### What is still not here

`free_of_orthogonal` is no longer on this list: the independent review of the
tilt (#86, finding F1) observed that the textbook-agreement claim above was
prose-only on the aisle side, and the dual pair — `exists_factor_truncLE` /
`factor_truncLE_unique` and `free_of_orthogonal` — now exists, together with
the four agreement theorems. Its inverse-rotation bookkeeping turned out to
cost nothing: `coyoneda_exact₂` on the inverse rotation never inspects a
rotated map, so no sign appears.

* **Any connection to a stability condition.** `tilt` is a t-structure on a
  triangulated category. That the tilted heart is the heart of a stability
  condition, or that tilting is how stability conditions on surfaces are
  built, is *motivation* for this file and is not formalised in it.

The identification of the tilted heart, formerly on this list, is
`tilt_heart_iff` (#106): the heart is exactly the extensions of `T` by
`F⟦1⟧`, the single-step form of the extension closure `⟨F⟦1⟧, T⟩`, exact
here because `(T, F)` is a torsion pair.

### The correction that made this possible

Kept because the wrong turn is what a reader would otherwise repeat. Earlier
revisions of this file asserted that `exists_triangle_zero_one` needs the long
exact cohomology sequence of `H⁰`, and treated it as blocked on machinery
Mathlib does not have.

That was inferred from the **textbook construction**, which cuts `X` as the
fibre of `τ^{≤0}A ⟶ F₀`. **That shape genuinely does need cohomology**:
`IsLE X 0` then depends on `H⁰(A) ⟶ F₀` being epi, and formally `Hom(X, Z)`
only injects into `Hom(F₀⟦-1⟧, Z)`, which does not vanish for degree reasons.

The shape used here builds `X` as an **extension of `T₀` by `τ^{≤-1}A`**, whose
two ends are already in `D^{≤0}`, so `isLE₂` closes the degree half and one
factorisation closes the orthogonality half. The obstruction was in the chosen
construction, not in the theorem.

The same substitution runs throughout: `τ^{≥0}X` plays the role of `H⁰(X)`,
`exists_factor_truncGE` plays the role of the counit isomorphism, and
Hom-orthogonality plays the role of membership in `T`. None of the three needs
a cohomology functor to exist.
-/

end HeartTorsionPair

end CategoryTheory.Triangulated.Tilting
