/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.TorsionPair.HeartAdapter
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Basic

/-!
# What the tilted heart of a stability function is

`HeartAdapter.lean` produces `hnTilt`, a t-structure on `C` from a stability
function on the heart and a cutoff `β`.  It does not say what its heart
contains.  This file does, by specialising the Happel–Reiten–Smalø description
already proved in `TorsionPair/Heart.lean` and `Cohomology/Basic.lean`:

```
A(β) = ⟨F β ⟦1⟧, T β⟩
```

* `hnTilt_heart_iff` — an object is in the tilted heart exactly when it sits in
  a distinguished triangle `F₀⟦1⟧ → X → T₀` with all Harder–Narasimhan phases
  of `F₀` at most `β` and all those of `T₀` above it.
* `mem_hnTilt_heart_of_hnTors`, `shift_mem_hnTilt_heart_of_hnFree` — the two
  generating families, which are the `T₀ = X` and `F₀⟦1⟧ = X` ends of that
  triangle.

Nothing here is new mathematics; all three are one composition each.  What they
buy is that the tilted heart can be described in the phase language of
`Cutoff.lean` rather than in terms of two abstract `ObjectProperty`s, which is
the form §6 states it in.

`Foundation/StabilityFunction/SlopeCutoff.lean` is the companion on the other
side: it says which objects are in `T β` to begin with, namely every nonzero
object of rank zero, at every `β < 1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

namespace StabilityFunction

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {t : TStructure C}

open Tilting

/-- **The tilted heart is the extensions of `T β` by `F β ⟦1⟧`.** -/
theorem hnTilt_heart_iff (Z : StabilityFunction t.heart.FullSubcategory) (β : ℝ)
    (hHN : Z.HasHNProperty) (X : C) :
    (Z.hnTilt β hHN).heart X ↔
      ∃ (F₀ T₀ : C) (_ : ambientProperty t (Z.hnFreeProperty β) F₀)
        (_ : ambientProperty t (Z.hnTorsProperty β) T₀)
        (f : F₀⟦(1 : ℤ)⟧ ⟶ X) (g : X ⟶ T₀)
        (h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C :=
  (Z.hnHeartTorsionPair β hHN).tilt_heart_iff X

/-- A torsion object stays in the tilted heart. -/
theorem mem_hnTilt_heart_of_hnTors (Z : StabilityFunction t.heart.FullSubcategory)
    (β : ℝ) (hHN : Z.HasHNProperty) {T₀ : C}
    (hT : ambientProperty t (Z.hnTorsProperty β) T₀) :
    (Z.hnTilt β hHN).heart T₀ :=
  (Z.hnHeartTorsionPair β hHN).tors_mem_tilt_heart hT

/-- A torsion-free object enters the tilted heart after one shift. -/
theorem shift_mem_hnTilt_heart_of_hnFree
    (Z : StabilityFunction t.heart.FullSubcategory) (β : ℝ)
    (hHN : Z.HasHNProperty) {F₀ : C}
    (hF : ambientProperty t (Z.hnFreeProperty β) F₀) :
    (Z.hnTilt β hHN).heart (F₀⟦(1 : ℤ)⟧) :=
  (Z.hnHeartTorsionPair β hHN).free_shift_mem_tilt_heart hF

end StabilityFunction

end CategoryTheory.Triangulated
