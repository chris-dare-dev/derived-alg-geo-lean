/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.Consequences
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakHNTransport

/-!
# The μ-slope and its Harder–Narasimhan property, read on the heart

The Gieseker lane builds the μ-slope on `Coh X` and proves the Harder–Narasimhan property there.
The abstract stability machinery is written against the heart of a t-structure. This file joins
the two, and it is the first time in the tree that a stability-theoretic hypothesis stated for a
heart is discharged from geometry.

## What makes it possible

Two things that did not exist before this lane:

* `Algebra/Homology/DerivedCategory/Heart.lean` identifies the heart of the canonical t-structure
  on `D(Coh X)` with `Coh X` itself;
* `Weak/Foundation/StabilityFunction/WeakHNTransport.lean` carries weak slope data, and the
  Harder–Narasimhan property, along an equivalence of abelian categories.

Composing them is all that happens here. Nothing is re-proved.

## What this does *not* discharge

`heart_hasHNProperty` still takes `MuHNInput`, exactly as `hasHNProperty` does. Neither of that
structure's two fields has ever been proved for a projective surface: one asks for `Coh X` to be a
Noetherian category, and the other **is Grothendieck's boundedness lemma**. Carrying the result to
the heart does not make either easier, and it must not be read as having discharged them.

## The local instances, and why they are local

`HasDerivedCategory` records a *chosen* localization, and the repository's convention is that
`HasDerivedCategory.standard` is a local instance in each consumer and never a global one, so that
the choice is literally the same term everywhere. The heart's abelian structure is local for the
same reason. Both follow the pattern already used across the derived-category files.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- The heart of the canonical t-structure on the derived category of coherent sheaves. -/
abbrev cohHeart : ObjectProperty (DerivedCategory (Coh X)) :=
  (DerivedCategory.TStructure.t (C := Coh X)).heart

/-- **The μ-slope, read on the heart.**

`Coh X` is the heart of the canonical t-structure, and weak slope data transports along that
identification. -/
noncomputable def heartWeakSlopeData (h : MuPositivityData P) :
    WeakSlopeData (cohHeart (X := X)).FullSubcategory :=
  (P.weakSlopeData h).congr (DerivedCategory.heartEquivalence (Coh X))

/-- **The Harder–Narasimhan property on the heart.**

The abstract stability machinery takes this as a hypothesis at every use site and no geometric
category had ever supplied it in the form the machinery asks for. `MuHNInput` is still a
hypothesis; see the module docstring on why that matters. -/
theorem heart_hasHNProperty (h : MuPositivityData P) (I : MuHNInput P h) :
    (P.heartWeakSlopeData h).toWeakStabilityFunction.HasHNProperty :=
  WeakSlopeData.congr_hasHNProperty _ _ (hasHNProperty h I)

/-- The rank on the heart is the multiplicity of the sheaf it comes from. -/
theorem heartWeakSlopeData_rank_functor (h : MuPositivityData P) (F : Coh X) :
    (P.heartWeakSlopeData h).rank
        ((DerivedCategory.heartEquivalence (Coh X)).functor.obj F) = P.multiplicity F :=
  (WeakSlopeData.congr_rank_functor _ _ F).trans (weakSlopeData_rank h F)

/-- The slope on the heart is the μ-slope of the sheaf it comes from. -/
theorem heartWeakSlopeData_topSlope_functor (h : MuPositivityData P) (F : Coh X) :
    (P.heartWeakSlopeData h).topSlope
        ((DerivedCategory.heartEquivalence (Coh X)).functor.obj F) =
      (P.weakSlopeData h).topSlope F :=
  WeakSlopeData.congr_topSlope_functor _ _ F

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
