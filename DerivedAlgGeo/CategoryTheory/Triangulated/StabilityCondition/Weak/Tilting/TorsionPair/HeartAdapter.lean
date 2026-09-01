/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.StabilityFunction

/-!
# From an abelian torsion pair on the heart to the HRS input

`TorsionPair/Basic.lean` states a torsion pair inside an abelian category;
`TorsionPair/Heart.lean` states one on the heart of a t-structure from inside
the ambient triangulated category, and tilts it.  Their docstrings say that
neither is derived from the other.  This file derives the second from the
first:

```
TorsionPair t.heart.FullSubcategory  →  HeartTorsionPair t  →  (tilt) TStructure C
```

Nothing here is new mathematics.  Both halves already exist and are proved
generically in `t`:

* `TStructure.heartFullSubcategoryAbelian` makes the heart abelian, so a
  `TorsionPair` on it can even be stated;
* `TStructure.heartFullSubcategory_shortExact_triangle` turns a short exact
  sequence in the heart into a distinguished triangle in `C`, which is exactly
  the difference between the two decomposition axioms.

What was missing is the transport of the two classes, which is
`ambientProperty`: a property of heart objects read as a property of ambient
objects that happen to lie in the heart.

## The payoff

`StabilityFunction.hnHeartTorsionPair` composes this with `hnTorsionPair` of
`TorsionPair/StabilityFunction.lean`.  A stability function on the heart with
the Harder–Narasimhan property and a number `β` therefore produce, with no
further input, a t-structure on `C` — its `tilt`.  That is the shape of
Bridgeland's `A(β,ω)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

namespace Tilting

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable (t : TStructure C)

/-- A property of heart objects, read as a property of ambient objects. -/
def ambientProperty (P : ObjectProperty t.heart.FullSubcategory) :
    ObjectProperty C :=
  fun X => ∃ h : t.heart X, P ⟨X, h⟩

variable {t}

omit [IsTriangulated C] in
theorem ambientProperty_of_obj {P : ObjectProperty t.heart.FullSubcategory}
    {X : t.heart.FullSubcategory} (hX : P X) : ambientProperty t P X.obj :=
  ⟨X.property, hX⟩

omit [IsTriangulated C] in
theorem heart_of_ambientProperty {P : ObjectProperty t.heart.FullSubcategory}
    {X : C} (hX : ambientProperty t P X) : t.heart X :=
  hX.choose

omit [IsTriangulated C] in
theorem isLE_of_ambientProperty {P : ObjectProperty t.heart.FullSubcategory}
    {X : C} (hX : ambientProperty t P X) : t.IsLE X 0 :=
  ((t.mem_heart_iff X).1 (heart_of_ambientProperty hX)).1

omit [IsTriangulated C] in
theorem isGE_of_ambientProperty {P : ObjectProperty t.heart.FullSubcategory}
    {X : C} (hX : ambientProperty t P X) : t.IsGE X 0 :=
  ((t.mem_heart_iff X).1 (heart_of_ambientProperty hX)).2

instance ambientProperty_isClosedUnderIsomorphisms
    (P : ObjectProperty t.heart.FullSubcategory)
    [P.IsClosedUnderIsomorphisms] :
    (ambientProperty t P).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hXheart, hXP⟩ := hX
    have hYheart : t.heart Y := t.heart.prop_of_iso e hXheart
    exact ⟨hYheart, P.prop_of_iso (X := ⟨X, hXheart⟩) (Y := ⟨Y, hYheart⟩)
      (ObjectProperty.isoMk t.heart e) hXP⟩

/-- **A torsion pair on the heart is a `HeartTorsionPair`.**  The classes are
carried out to `C` by `ambientProperty`, and the short exact sequence becomes a
distinguished triangle by `heartFullSubcategory_shortExact_triangle`. -/
def HeartTorsionPair.ofTorsionPair (P : TorsionPair t.heart.FullSubcategory) :
    HeartTorsionPair t where
  tors := ambientProperty t P.tors
  free := ambientProperty t P.free
  tors_isLE _ h := isLE_of_ambientProperty h
  tors_isGE _ h := isGE_of_ambientProperty h
  free_isLE _ h := isLE_of_ambientProperty h
  free_isGE _ h := isGE_of_ambientProperty h
  hom_eq_zero := by
    rintro X Y ⟨hX, hXP⟩ ⟨hY, hYP⟩ f
    have hzero := P.hom_eq_zero hXP hYP
      (ObjectProperty.homMk (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) f)
    simpa using congrArg (fun g => g.hom) hzero
  exists_triangle X hLE hGE := by
    have hX : t.heart X := (t.mem_heart_iff X).2 ⟨hLE, hGE⟩
    obtain ⟨T, F, i, p, w, hT, hF, hSE⟩ := P.exists_shortExact ⟨X, hX⟩
    letI := hSE.mono_f
    letI := hSE.epi_g
    obtain ⟨δ, hδ⟩ :=
      TStructure.heartFullSubcategory_shortExact_triangle (C := C) t i p w
        (fun {W} α hα => by
          have hker : IsLimit (KernelFork.ofι (ShortComplex.mk i p w).f
              (ShortComplex.mk i p w).zero) := hSE.fIsKernel
          exact ⟨hker.lift (KernelFork.ofι α hα),
            hker.fac _ WalkingParallelPair.zero⟩)
    exact ⟨T.obj, F.obj, ambientProperty_of_obj hT, ambientProperty_of_obj hF,
      i.hom, p.hom, δ, hδ⟩

@[simp]
theorem HeartTorsionPair.ofTorsionPair_tors
    (P : TorsionPair t.heart.FullSubcategory) :
    (HeartTorsionPair.ofTorsionPair P).tors = ambientProperty t P.tors :=
  rfl

@[simp]
theorem HeartTorsionPair.ofTorsionPair_free
    (P : TorsionPair t.heart.FullSubcategory) :
    (HeartTorsionPair.ofTorsionPair P).free = ambientProperty t P.free :=
  rfl

end Tilting

namespace StabilityFunction

open Tilting

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {t : TStructure C}

/-- **A stability function on the heart tilts.**  Its two classes at a phase
cutoff are a torsion pair, hence a `HeartTorsionPair`, hence — through
`HeartTorsionPair.tilt` — a t-structure on `C`. -/
def hnHeartTorsionPair (Z : StabilityFunction t.heart.FullSubcategory) (β : ℝ)
    (hHN : Z.HasHNProperty) : HeartTorsionPair t :=
  HeartTorsionPair.ofTorsionPair (Z.hnTorsionPair β hHN)

@[simp]
theorem hnHeartTorsionPair_tors (Z : StabilityFunction t.heart.FullSubcategory)
    (β : ℝ) (hHN : Z.HasHNProperty) :
    (hnHeartTorsionPair Z β hHN).tors = ambientProperty t (Z.hnTorsProperty β) :=
  rfl

@[simp]
theorem hnHeartTorsionPair_free (Z : StabilityFunction t.heart.FullSubcategory)
    (β : ℝ) (hHN : Z.HasHNProperty) :
    (hnHeartTorsionPair Z β hHN).free = ambientProperty t (Z.hnFreeProperty β) :=
  rfl

/-- **The tilt of a stability function at a cutoff**, as a t-structure on the
ambient category.  This is the whole chain in one declaration: HN filtrations
cut at `β`, the resulting torsion pair, and Happel–Reiten–Smalø. -/
def hnTilt (Z : StabilityFunction t.heart.FullSubcategory) (β : ℝ)
    (hHN : Z.HasHNProperty) : TStructure C :=
  (hnHeartTorsionPair Z β hHN).tilt

end StabilityFunction

end CategoryTheory.Triangulated
