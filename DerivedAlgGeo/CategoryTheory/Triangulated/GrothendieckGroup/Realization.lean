/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial

/-!
# Realizations of a triangulated Grothendieck group

A realization of `K₀ C` in an additive commutative group is simply an additive
homomorphism. This file gives that canonical hom type a semantic abbreviation
and records when a triangulated functor descends through two realizations.

Nothing here is numerical or geometric: a numerical Grothendieck group, a
cohomological realization, or any other additive target is a consumer of the
same root.
-/

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u₁ u₂ v₁ v₂ x₁ x₂

/-- A realization of the triangulated Grothendieck group in an additive
commutative group. This is an abbreviation, not a parallel one-field carrier. -/
abbrev K₀.Realization (C : Type u₁) [Category.{v₁} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (A : Type x₁) [AddCommGroup A] :=
  K₀ C →+ A

namespace K₀.Realization

variable {C : Type u₁} {D : Type u₂} {A : Type x₁} {B : Type x₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [AddCommGroup A] [AddCommGroup B]

/-- `F` descends to `f` along two realizations when the square formed by
`K₀.map F`, the realizations, and `f` commutes. -/
def Descends (R : K₀.Realization C A) (R' : K₀.Realization D B)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] (f : A →+ B) : Prop :=
  ∀ x : K₀ C, R' (K₀.map F x) = f (R x)

/-- A descent is determined on classes of objects. -/
theorem Descends.apply_of {R : K₀.Realization C A} {R' : K₀.Realization D B}
    {F : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated] {f : A →+ B}
    (h : R.Descends R' F f) (X : C) :
    R' (K₀.of D (F.obj X)) = f (R (K₀.of C X)) := by
  have := h (K₀.of C X)
  rwa [K₀.map_of] at this

/-- Naturally isomorphic triangulated functors have the same descents. -/
theorem Descends.of_natIso {R : K₀.Realization C A} {R' : K₀.Realization D B}
    {F G : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated]
    [G.CommShift ℤ] [G.IsTriangulated] {f : A →+ B}
    (h : R.Descends R' F f) (e : F ≅ G) : R.Descends R' G f := by
  intro x
  rw [← K₀.map_congr e]
  exact h x

end K₀.Realization

end CategoryTheory.Triangulated
