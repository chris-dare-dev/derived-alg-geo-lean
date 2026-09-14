/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# A t-structure is determined by its aisle, and restrictions along a functor

Section 4 of arXiv:1902.08184 calls a t-structure `τ` on `𝒟` **`S`-local** when
for every quasi-compact open `U ⊆ S` there is a t-structure `τ_U` on `𝒟_U`
making the restriction functor t-exact, and Remark 4.6(1) observes that `τ_U` is
then unique. Both halves of that sentence need vocabulary the repository did not
have: `Phase/Transfer/Inducing.lean` still records `S`-locality as lying outside
the categorical layer.

This file supplies the categorical half, for one functor at a time.

**Uniqueness is really a statement about aisles.** A t-structure carries two
object properties, but they determine each other: `t.ge (n + 1)` is the right
orthogonal of `t.le n` and conversely, by Mathlib's
`TStructure.isGE_iff_orthogonal` and `isLE_iff_orthogonal`. So two t-structures
with the same coconnective half are equal, and `ext_le` is the form Remark
4.6(1) consumes -- once one knows the aisle of `τ_U` is pinned, `τ_U` itself is.

**`Restriction` is the data, `RestrictsAlong` the proposition.** Quantifying
either over the quasi-compact opens of a base is what `S`-locality will be; that
quantifier is geometric and is not taken here, because the categories `𝒟_U`
vary with `U` and the base-change layer owns them.

Nothing here constructs a t-structure. `Restriction` is inhabited only by
someone who already has `τ_U`, and the uniqueness statement says which `τ_U`
that must be, not that one exists.
-/

universe v v' u u'

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A t-structure is its two object properties: every remaining field is a
proposition. -/
theorem ext {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) (hge : t₁.ge = t₂.ge) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  subst hle
  subst hge
  rfl

/-- The connective half is the right orthogonal of the coconnective half, so the
coconnective half determines it. -/
theorem ge_eq_of_le_eq {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) :
    t₁.ge = t₂.ge := by
  funext n
  funext X
  have key : ∀ (t : TStructure C) (m : ℤ) (Y : C),
      t.ge m Y ↔ ∀ (Z : C) (f : Z ⟶ Y), t.le (m - 1) Z → f = 0 := by
    intro t m Y
    constructor
    · intro hY Z f hZ
      letI : t.IsGE Y m := ⟨hY⟩
      letI : t.IsLE Z (m - 1) := ⟨hZ⟩
      exact t.zero f (m - 1) m (by lia)
    · intro hY
      have := (t.isGE_iff_orthogonal (m - 1) m (by lia) Y).2
        (fun Z f hf ↦ hY Z f hf.le)
      exact this.ge
  rw [key t₁ n X, key t₂ n X, hle]

/-- **A t-structure is determined by its aisle.** This is the engine behind the
uniqueness in Remark 4.6(1) of arXiv:1902.08184: pinning the coconnective half
of `τ_U` pins `τ_U`. -/
theorem ext_le {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) : t₁ = t₂ :=
  ext hle (ge_eq_of_le_eq hle)

end TStructure

end CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A t-structure on the target of `F` making `F` t-exact.

This is one clause of `S`-locality, at one functor. `S`-locality quantifies it
over the quasi-compact opens of the base; that quantifier is geometric, because
the target category varies with the open. -/
structure Restriction (t : TStructure C) (F : C ⥤ D) where
  /-- The t-structure on the target. -/
  tStructure : TStructure D
  /-- The functor is t-exact for the two. -/
  isTExact : F.IsTExact t tStructure

/-- The proposition that `t` restricts along `F`, forgetting which t-structure
witnesses it. -/
def RestrictsAlong (t : TStructure C) (F : C ⥤ D) : Prop :=
  Nonempty (t.Restriction F)

namespace Restriction

variable {t : TStructure C} {F : C ⥤ D}

theorem restrictsAlong (r : t.Restriction F) : t.RestrictsAlong F :=
  ⟨r⟩

/-- Two restrictions of `t` along `F` that agree on aisles are the same
t-structure. Remark 4.6(1) is this together with a proof that the aisle of the
restriction is pinned -- which is geometric, and is not claimed here. -/
theorem tStructure_eq_of_le_eq (r₁ r₂ : t.Restriction F)
    (hle : r₁.tStructure.le = r₂.tStructure.le) :
    r₁.tStructure = r₂.tStructure :=
  ext_le hle

/-- The identity functor restricts every t-structure to itself. -/
def id (t : TStructure C) : t.Restriction (𝟭 C) where
  tStructure := t
  isTExact :=
    letI : (𝟭 C).IsRightTExact t t := ⟨fun _ _ hX ↦ hX⟩
    letI : (𝟭 C).IsLeftTExact t t := ⟨fun _ _ hX ↦ hX⟩
    Functor.isTExact_of

end Restriction

end CategoryTheory.Triangulated.TStructure
