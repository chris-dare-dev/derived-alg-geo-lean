/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

/-!
# Constructing a t-structure from an aisle

This file isolates the formal, non-representability part of the compact-generator
existence theorem.  An object property is an aisle when it is closed under the
relevant shift and every object admits the required approximation triangle.  Its
right orthogonal is then the coaisle, and the two properties determine a
t-structure.

For Theorem A.13 of arXiv:2607.28411v1, Brown representability constructs
universal approximation maps. `AisleData.ofApproximationMaps` completes those
maps to distinguished triangles and proves their cones are right orthogonal.
This file then assembles the triangles into a t-structure, but does not
postulate that compact generators alone produce the universal maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- A universal map from an aisle candidate to an object.

The two Hom conditions are the exact amount of control needed to prove that
the cone of `hom` is right orthogonal to `U`: surjectivity kills maps through
the middle term, while injectivity after `[1]` kills their connecting maps.
Brown representability constructs maps with these properties in the
compact-generator application. -/
structure ApproximationMap (U : ObjectProperty C) (A : C) where
  /-- The approximating object. -/
  left : C
  /-- The approximating object belongs to the aisle candidate. -/
  left_mem : U left
  /-- The universal approximation morphism. -/
  hom : left ⟶ A
  /-- Every map from an object of `U` to `A` factors through `hom`. -/
  hom_surjective (Z : C) (hZ : U Z) :
    Function.Surjective (fun f : Z ⟶ left => f ≫ hom)
  /-- After shifting the approximation triangle, precomposition with `hom[1]`
  is injective on maps from objects of `U`. -/
  shift_hom_injective (Z : C) (hZ : U Z) :
    Function.Injective (fun f : Z ⟶ left⟦(1 : ℤ)⟧ => f ≫ hom⟦(1 : ℤ)⟧')

/-- The data that makes an object property an aisle.

The approximation triangle is the only genuinely existential part.  In the
compact-generator application it is supplied by Brown representability. -/
structure AisleData (U : ObjectProperty C) : Prop where
  /-- Aisles are closed under the shift occurring in the nonpositive half of a
  t-structure. -/
  shift : U ≤ U.shift (1 : ℤ)
  /-- Every object has an aisle/right-orthogonal approximation triangle. -/
  exists_triangle (A : C) :
    ∃ (X Y : C) (_ : U X) (_ : U.rightOrthogonal Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C

namespace AisleData

variable {U : ObjectProperty C}

/-- Complete universal approximation maps to triangles and prove that their
cones lie in the right orthogonal.

This is the exactness step between Brown representability's map-level output
and the aisle constructor.  In particular, callers do not supply a chosen
cone or assert its orthogonality: both are constructed here. -/
theorem ofApproximationMaps
    (hshift : U ≤ U.shift (1 : ℤ))
    (happrox : ∀ A : C, Nonempty (ApproximationMap U A)) :
    AisleData U where
  shift := hshift
  exists_triangle A := by
    obtain ⟨a⟩ := happrox A
    obtain ⟨Y, g, h, hT⟩ :=
      Pretriangulated.distinguished_cocone_triangle a.hom
    let T := Triangle.mk a.hom g h
    have hY : U.rightOrthogonal Y := by
      intro Z f hZ
      have hfh : f ≫ h = 0 := by
        apply a.shift_hom_injective Z hZ
        change (f ≫ h) ≫ a.hom⟦(1 : ℤ)⟧' =
          (0 : Z ⟶ a.left⟦(1 : ℤ)⟧) ≫ a.hom⟦(1 : ℤ)⟧'
        have hh : h ≫ a.hom⟦(1 : ℤ)⟧' = 0 := by
          have hh' := comp_distTriang_mor_zero₃₁ (Triangle.mk a.hom g h) hT
          dsimp only [Triangle.mk] at hh'
          exact hh'
        rw [Category.assoc, hh, comp_zero, zero_comp]
      obtain ⟨k, rfl⟩ := Triangle.coyoneda_exact₃ T hT f hfh
      obtain ⟨l, rfl⟩ := a.hom_surjective Z hZ k
      change (l ≫ a.hom) ≫ g = 0
      have hfg : a.hom ≫ g = 0 := by
        have hfg' := comp_distTriang_mor_zero₁₂ (Triangle.mk a.hom g h) hT
        dsimp only [Triangle.mk] at hfg'
        exact hfg'
      rw [Category.assoc, hfg, comp_zero]
    exact ⟨a.left, Y, a.left_mem, hY, a.hom, g, h, hT⟩

/-- The right orthogonal of an aisle is closed under the opposite shift. -/
lemma rightOrthogonal_le_shift (h : AisleData U) :
    U.rightOrthogonal ≤ U.rightOrthogonal.shift (-1 : ℤ) := by
  intro Y hY X f hX
  let e : (Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ Y := by
    simpa using shiftShiftNeg Y (-1 : ℤ)
  have hg : (shiftFunctor C (1 : ℤ)).map f ≫ e.hom = 0 :=
    hY _ (h.shift X hX)
  apply (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).1
  rw [← cancel_mono e.hom]
  simpa only [Limits.zero_comp] using hg

variable [U.IsClosedUnderIsomorphisms]

/-- An aisle and its right orthogonal determine a t-structure. -/
noncomputable def tStructure (h : AisleData U) : TStructure C where
  le n := U.shift n
  ge n := U.rightOrthogonal.shift (n - 1)
  le_shift n a n' ha X hX := by
    change ((U.shift n').shift a) X
    rw [U.shift_shift a n' n ha]
    exact hX
  ge_shift n a n' ha X hX := by
    change ((U.rightOrthogonal.shift (n' - 1)).shift a) X
    rw [U.rightOrthogonal.shift_shift a (n' - 1) (n - 1) (by omega)]
    exact hX
  zero' {X Y} f hX hY := by
    have hX' : U X := by simpa using hX
    have hY' : U.rightOrthogonal Y := by simpa using hY
    exact hY' f hX'
  le_zero_le X hX := by
    rw [U.shift_zero ℤ] at hX
    exact h.shift X hX
  ge_one_le X hX := by
    rw [sub_self, U.rightOrthogonal.shift_zero ℤ] at hX
    exact h.rightOrthogonal_le_shift X hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, k, hk⟩ := h.exists_triangle A
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, k, hk⟩

@[simp]
lemma tStructure_le_zero (h : AisleData U) : h.tStructure.le 0 = U := by
  simp [tStructure]

@[simp]
lemma tStructure_ge_one (h : AisleData U) :
    h.tStructure.ge 1 = U.rightOrthogonal := by
  simp [tStructure]

end AisleData

end CategoryTheory.Triangulated.TStructure
