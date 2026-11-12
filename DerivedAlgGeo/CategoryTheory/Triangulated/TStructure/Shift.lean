/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Truncation functors commute with the shift

For a t-structure `t` on a pretriangulated category and `a n : ℤ`,

```
((t.truncLT (a + n)).obj X)⟦n⟧ ≅ (t.truncLT a).obj (X⟦n⟧)
((t.truncGE (a + n)).obj X)⟦n⟧ ≅ (t.truncGE a).obj (X⟦n⟧)
```

## Main definitions

* `CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGE` — the truncation
  triangle of `X` at `a + n`, shifted by `n`.
* `TStructure.shiftedTriangleLTGEIso` — its isomorphism with the truncation
  triangle of `X⟦n⟧` at `a`, over the identity of `X⟦n⟧`.
* `TStructure.truncLTShiftIso`, `TStructure.truncGEShiftIso` — the two displayed
  isomorphisms, as components of that triangle isomorphism.

## Main results

* `TStructure.exists_shiftedTriangleLTGE_iso` — the shifted truncation triangle
  is isomorphic to the truncation triangle of `X⟦n⟧` at `a`.
* `TStructure.truncLTShiftIso_hom_comp_truncLTι`,
  `TStructure.truncGEπ_comp_truncGEShiftIso_hom` — the isomorphisms sit over,
  respectively under, `X⟦n⟧` up to the sign `(-1)ⁿ`.

## Implementation notes

### Why this is not in Mathlib

Mathlib's truncation API (`TruncLTGE.lean`, `TruncLEGT.lean`) has **no shift
lemmas at all**. The functors, their natural transformations, the truncation
triangle and its uniqueness are all present; the interaction with
`shiftFunctor` is simply absent. This file is Mathlib-shaped and is written to
be upstreamed.

### The proof, in one paragraph

Shifting the truncation triangle `τ<ᵃ⁺ⁿX → X → τ≥ᵃ⁺ⁿX → [1]` by `n` gives a
distinguished triangle (`Triangle.shift_distinguished`) whose middle object is
`X⟦n⟧`, whose first object is `IsLE (a-1)` and whose third is `IsGE a`
(`t.isLE_shift`, `t.isGE_shift`). The truncation triangle of `X⟦n⟧` at `a` has
exactly the same three properties. Mathlib's `t.triangle_iso_exists` says a
distinguished triangle with an `IsLE (a-1)` first object and an `IsGE a` third
object is determined up to isomorphism by its middle object, so the two are
isomorphic over `𝟙 (X⟦n⟧)` — and both isomorphisms fall out of the single
triangle isomorphism at once.

That uniqueness lemma is the whole content. Everything else is bookkeeping.

### Downstream

This is what `originalHeartCohFunctor t n ≅ shiftFunctor C n ⋙ originalHeartCohFunctor t 0`
needs, and hence what upgrades heart cohomology from homological at `n = 0` to
homological in every degree.

## References

The file builds on Mathlib's `CategoryTheory.Triangulated.TStructure.triangle_iso_exists`,
`CategoryTheory.Triangulated.TStructure.triangleLTGE` and
`CategoryTheory.Pretriangulated.Triangle.shift_distinguished`.

## Tags

t-structure, truncation, shift functor, distinguished triangle
-/

universe v u

namespace CategoryTheory.Triangulated.TStructure

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : CategoryTheory.Triangulated.TStructure C) (a n : ℤ) (X : C)

/-- The truncation triangle of `X` at `a + n`, shifted by `n`.

Its middle object is `X⟦n⟧`, so it is a candidate for the truncation triangle of
`X⟦n⟧` at `a`; the point of this file is that it *is* one. -/
noncomputable def shiftedTriangleLTGE : Triangle C :=
  (CategoryTheory.shiftFunctor (Triangle C) n).obj ((t.triangleLTGE (a + n)).obj X)

theorem shiftedTriangleLTGE_distinguished :
    shiftedTriangleLTGE t a n X ∈ distTriang C :=
  Triangle.shift_distinguished _ (t.triangleLTGE_distinguished (a + n) X) n

instance isLE_shiftedTriangleLTGE_obj₁ :
    t.IsLE (shiftedTriangleLTGE t a n X).obj₁ (a - 1) := by
  have : t.IsLE ((t.truncLT (a + n)).obj X) (a + n - 1) := t.isLE_truncLT_obj ..
  exact t.isLE_shift ((t.truncLT (a + n)).obj X) (a + n - 1) n (a - 1) (by lia)

instance isGE_shiftedTriangleLTGE_obj₃ :
    t.IsGE (shiftedTriangleLTGE t a n X).obj₃ a :=
  t.isGE_shift ((t.truncGE (a + n)).obj X) (a + n) n a (by lia)

/-- **Uniqueness of the truncation decomposition**, applied to the shifted
truncation triangle: it is isomorphic to the truncation triangle of `X⟦n⟧` at
`a`, over the identity of `X⟦n⟧`. -/
theorem exists_shiftedTriangleLTGE_iso :
    ∃ e : shiftedTriangleLTGE t a n X ≅ (t.triangleLTGE a).obj (X⟦n⟧),
      e.hom.hom₂ = 𝟙 _ :=
  t.triangle_iso_exists (shiftedTriangleLTGE_distinguished t a n X)
    (t.triangleLTGE_distinguished a (X⟦n⟧)) (Iso.refl _) (a - 1) a
    (isLE_shiftedTriangleLTGE_obj₁ t a n X) (isGE_shiftedTriangleLTGE_obj₃ t a n X)
    (by infer_instance) (by infer_instance) (by lia)

/-- The chosen triangle isomorphism. Both truncation-shift isomorphisms below are
components of this one. -/
noncomputable def shiftedTriangleLTGEIso :
    shiftedTriangleLTGE t a n X ≅ (t.triangleLTGE a).obj (X⟦n⟧) :=
  (exists_shiftedTriangleLTGE_iso t a n X).choose

theorem shiftedTriangleLTGEIso_hom₂ :
    (shiftedTriangleLTGEIso t a n X).hom.hom₂ = 𝟙 (X⟦n⟧) :=
  (exists_shiftedTriangleLTGE_iso t a n X).choose_spec

/-- **`truncLT` commutes with the shift.** -/
noncomputable def truncLTShiftIso :
    ((t.truncLT (a + n)).obj X)⟦n⟧ ≅ (t.truncLT a).obj (X⟦n⟧) :=
  Triangle.π₁.mapIso (shiftedTriangleLTGEIso t a n X)

/-- **`truncGE` commutes with the shift.** -/
noncomputable def truncGEShiftIso :
    ((t.truncGE (a + n)).obj X)⟦n⟧ ≅ (t.truncGE a).obj (X⟦n⟧) :=
  Triangle.π₃.mapIso (shiftedTriangleLTGEIso t a n X)

/-- The `truncLT` isomorphism sits over `X⟦n⟧`, **up to the sign `(-1)ⁿ`**.

The sign is not an artefact of the proof: `Triangle.shiftFunctor` multiplies a
triangle's maps by `n.negOnePow`, which is exactly why `shiftFunctor C n` is not
a triangulated functor on the nose. Any downstream use of these isomorphisms
inherits the sign, so it is stated rather than absorbed. -/
@[reassoc]
theorem truncLTShiftIso_hom_comp_truncLTι :
    (truncLTShiftIso t a n X).hom ≫ (t.truncLTι a).app (X⟦n⟧) =
      n.negOnePow • ((t.truncLTι (a + n)).app X)⟦n⟧' := by
  change
    (shiftedTriangleLTGEIso t a n X).hom.hom₁ ≫
        ((t.triangleLTGE a).obj (X⟦n⟧)).mor₁ = _
  calc
    _ = (shiftedTriangleLTGE t a n X).mor₁ ≫
        (shiftedTriangleLTGEIso t a n X).hom.hom₂ :=
      ((shiftedTriangleLTGEIso t a n X).hom.comm₁).symm
    _ = _ := by
      rw [shiftedTriangleLTGEIso_hom₂]
      dsimp only [shiftedTriangleLTGE, Triangle.shiftFunctor_eq,
        Triangle.shiftFunctor_obj, TStructure.triangleLTGE,
        Triangle.functorMk_obj, Triangle.mk_mor₁, Functor.comp_obj]
      exact Category.comp_id _

/-- The `truncGE` isomorphism sits under `X⟦n⟧`, **up to the sign `(-1)ⁿ`**; see
the note on `truncLTShiftIso_hom_comp_truncLTι`. -/
@[reassoc]
theorem truncGEπ_comp_truncGEShiftIso_hom :
    (n.negOnePow • ((t.truncGEπ (a + n)).app X)⟦n⟧') ≫ (truncGEShiftIso t a n X).hom =
      (t.truncGEπ a).app (X⟦n⟧) := by
  change
    (shiftedTriangleLTGE t a n X).mor₂ ≫
        (shiftedTriangleLTGEIso t a n X).hom.hom₃ = _
  calc
    _ = (shiftedTriangleLTGEIso t a n X).hom.hom₂ ≫
        ((t.triangleLTGE a).obj (X⟦n⟧)).mor₂ :=
      (shiftedTriangleLTGEIso t a n X).hom.comm₂
    _ = _ := by
      rw [shiftedTriangleLTGEIso_hom₂]
      dsimp only [TStructure.triangleLTGE, Triangle.functorMk_obj,
        Triangle.mk_mor₂, Functor.comp_obj]
      exact Category.id_comp _

/-- Inverse form of `truncGEπ_comp_truncGEShiftIso_hom`, used to prove
naturality of the comparison. -/
@[reassoc]
theorem truncGEπ_comp_truncGEShiftIso_inv :
    (t.truncGEπ a).app (X⟦n⟧) ≫ (truncGEShiftIso t a n X).inv =
      n.negOnePow • ((t.truncGEπ (a + n)).app X)⟦n⟧' := by
  rw [← truncGEπ_comp_truncGEShiftIso_hom t a n X]
  simp

end CategoryTheory.Triangulated.TStructure
