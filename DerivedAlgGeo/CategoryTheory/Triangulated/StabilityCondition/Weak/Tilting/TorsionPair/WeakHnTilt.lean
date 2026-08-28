/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.HnTiltHeart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.WeakStabilityFunction

/-!
# The tilt of a weak stability function at a slope cutoff

`TorsionPair/WeakStabilityFunction.lean` produces `hnTorsionPair`, the torsion pair cut out of
an abelian category by a slope `μ₀ : WithTop ℝ`.  This file feeds it through the
Happel–Reiten–Smalø machinery that `HeartAdapter.lean` and `HnTiltHeart.lean` already set up for
the strict case, and describes the resulting heart.

**Nothing here is new mathematics.**  Every declaration is one composition, exactly as in the
strict `HeartAdapter.lean` / `HnTiltHeart.lean` pair.  The chain

```
TorsionPair t.heart.FullSubcategory → HeartTorsionPair t → (tilt) TStructure C
```

is generic in the torsion pair, so once the weak pair exists — which is what took the work, and
what needed the charge-free subobject correspondence behind it — the tilt is immediate.

## The one difference that matters

The strict `hnTilt` cuts by a **phase** `β : ℝ`.  This one cuts by a **slope** in `WithTop ℝ`,
and that is not cosmetic: on a surface a skyscraper has charge `0` and no phase at all, so no
phase cutoff can place it, while every finite slope cutoff puts it in `T μ₀`
(`WeakSlopeData.mem_hnTors_of_rank_zero`).  The tilted heart here therefore contains the objects
that the strict construction cannot even speak about, which is the entire reason the weak lane
exists.

Both are at `abelianDatum` of the heart, so they are strictly parallel: the strict
`StabilityFunction t.heart.FullSubcategory` is `StabilityFunctionOn (abelianDatum …)`, and this
is `WeakStabilityFunctionOn` at the same datum.  Neither is at `heartDatum t`, whose classes live
in the ambient `K₀ C`.

## What this is still not

It is not Bridgeland's Lemma 6.2.  This says *what the tilted heart is*; Lemma 6.2 says that
`Z(β,ω)` is a stability function **on** it, which is the four-case positivity argument and needs
the real part as well as the imaginary one.  `MukaiWeakCutoff.lean` supplies the imaginary half
against the untilted classes; nothing here closes the gap.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

namespace WeakStabilityFunctionOn

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {t : TStructure C}

open Tilting

/-- The weak cutoff pair, transported to the heart-torsion-pair form Happel–Reiten–Smalø
consumes. -/
def hnHeartTorsionPair
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) : HeartTorsionPair t :=
  HeartTorsionPair.ofTorsionPair (W.hnTorsionPair μ₀ hHN)

@[simp]
theorem hnHeartTorsionPair_tors
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) :
    (W.hnHeartTorsionPair μ₀ hHN).tors = ambientProperty t (W.hnTorsProperty μ₀) := rfl

@[simp]
theorem hnHeartTorsionPair_free
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) :
    (W.hnHeartTorsionPair μ₀ hHN).free = ambientProperty t (W.hnFreeProperty μ₀) := rfl

/-- **The tilt of a weak stability function at a slope cutoff**, as a t-structure on the ambient
category.  The whole chain in one declaration: weak HN filtrations cut at `μ₀`, the resulting
torsion pair, and Happel–Reiten–Smalø. -/
def hnTilt (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) : TStructure C :=
  (W.hnHeartTorsionPair μ₀ hHN).tilt

/-- **The tilted heart is the extensions of `T μ₀` by `F μ₀ ⟦1⟧`.** -/
theorem hnTilt_heart_iff
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) (X : C) :
    (W.hnTilt μ₀ hHN).heart X ↔
      ∃ (F₀ T₀ : C) (_ : ambientProperty t (W.hnFreeProperty μ₀) F₀)
        (_ : ambientProperty t (W.hnTorsProperty μ₀) T₀)
        (f : F₀⟦(1 : ℤ)⟧ ⟶ X) (g : X ⟶ T₀)
        (h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C :=
  (W.hnHeartTorsionPair μ₀ hHN).tilt_heart_iff X

/-- A torsion object stays in the tilted heart. -/
theorem mem_hnTilt_heart_of_hnTors
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) {T₀ : C}
    (hT : ambientProperty t (W.hnTorsProperty μ₀) T₀) :
    (W.hnTilt μ₀ hHN).heart T₀ :=
  (W.hnHeartTorsionPair μ₀ hHN).tors_mem_tilt_heart hT

/-- A torsion-free object enters the tilted heart after one shift. -/
theorem shift_mem_hnTilt_heart_of_hnFree
    (W : WeakStabilityFunctionOn (abelianDatum t.heart.FullSubcategory))
    (μ₀ : WithTop ℝ) (hHN : W.HasHNProperty) {F₀ : C}
    (hF : ambientProperty t (W.hnFreeProperty μ₀) F₀) :
    (W.hnTilt μ₀ hHN).heart (F₀⟦(1 : ℤ)⟧) :=
  (W.hnHeartTorsionPair μ₀ hHN).free_shift_mem_tilt_heart hF

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
