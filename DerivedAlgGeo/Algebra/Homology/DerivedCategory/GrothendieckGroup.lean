/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.ExactSequence
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedHeart
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Grothendieck classes from bounded derived cohomology

For an abelian category `A`, the alternating sum of the cohomology classes of
an object of `Dᵇ(A)` is additive on distinguished triangles.  It therefore
descends to a canonical homomorphism

`K₀(Dᵇ(A)) →+ K₀Ab(A)`.

This file constructs that direction only.  Identifying it as the inverse of
the standard-heart comparison requires a separate dévissage theorem; no
equivalence of Grothendieck groups is assumed here.
-/

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Degree-`n` cohomology of a bounded-derived object. -/
noncomputable abbrev boundedHomologyFunctor (n : ℤ) : Bounded A ⥤ A :=
  Bounded.ι ⋙ homologyFunctor A n

/-- A bounded-derived object has only finitely many nonzero cohomology
objects. -/
theorem boundedHomology_hasFiniteNonzeroSupport (X : Bounded A) :
    K₀Ab.HasFiniteNonzeroSupport
      (fun n : ℤ => (boundedHomologyFunctor A n).obj X) := by
  obtain ⟨⟨lower, hGE⟩, ⟨upper, hLE⟩⟩ := X.property
  refine (Set.finite_Icc lower upper).subset ?_
  intro n hn
  constructor
  · by_contra hnlower
    have hnlt : n < lower := lt_of_not_ge hnlower
    apply hn
    letI : X.obj.IsGE lower := hGE
    exact isZero_of_isGE X.obj lower n hnlt
  · by_contra hnupper
    have hnlt : upper < n := lt_of_not_ge hnupper
    apply hn
    letI : X.obj.IsLE upper := hLE
    exact isZero_of_isLE X.obj upper n hnlt

/-- The alternating sum of the cohomology classes of a bounded-derived
object. -/
noncomputable def boundedEulerClass (X : Bounded A) : K₀Ab A :=
  K₀Ab.eulerClass (fun n : ℤ => (boundedHomologyFunctor A n).obj X)

/-- The bounded cohomology Euler class is additive on distinguished
triangles. -/
theorem boundedEulerClass_additive (T : Triangle (Bounded A))
    (hT : T ∈ distTriang (Bounded A)) :
    boundedEulerClass A T.obj₂ =
      boundedEulerClass A T.obj₁ + boundedEulerClass A T.obj₃ := by
  let T' : Triangle (DerivedCategory A) := Bounded.ι.mapTriangle.obj T
  have hT' : T' ∈ distTriang (DerivedCategory A) :=
    Bounded.ι.map_distinguished T hT
  let A₀ : ℤ → A := fun n => (boundedHomologyFunctor A n).obj T.obj₁
  let B : ℤ → A := fun n => (boundedHomologyFunctor A n).obj T.obj₂
  let C : ℤ → A := fun n => (boundedHomologyFunctor A n).obj T.obj₃
  let f : ∀ n, A₀ n ⟶ B n := fun n => (boundedHomologyFunctor A n).map T.mor₁
  let g : ∀ n, B n ⟶ C n := fun n => (boundedHomologyFunctor A n).map T.mor₂
  let δ : ∀ n, C n ⟶ A₀ (n + 1) := fun n =>
    HomologySequence.δ T' n (n + 1) rfl
  have hfg₀ : ∀ n, f n ≫ g n = 0 := by
    intro n
    dsimp only [f, g]
    rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
  have hgδ₀ : ∀ n, g n ≫ δ n = 0 := by
    intro n
    exact HomologySequence.comp_δ T' hT' n (n + 1) rfl
  have hδf₀ : ∀ n, δ n ≫ f (n + 1) = 0 := by
    intro n
    exact HomologySequence.δ_comp T' hT' n (n + 1) rfl
  have hfg : ∀ n, (ShortComplex.mk (f n) (g n) (hfg₀ n)).Exact := by
    intro n
    simpa only [f, g, boundedHomologyFunctor, Functor.comp_map, T',
      Functor.mapTriangle_obj, Triangle.mk] using HomologySequence.exact₂ T' hT' n
  have hgδ : ∀ n, (ShortComplex.mk (g n) (δ n) (hgδ₀ n)).Exact := by
    intro n
    simpa only [A₀, B, C, g, δ, boundedHomologyFunctor, Functor.comp_obj,
      Functor.comp_map, T', Functor.mapTriangle_obj, Triangle.mk] using
        HomologySequence.exact₃ T' hT' n (n + 1) rfl
  have hδf : ∀ n, (ShortComplex.mk (δ n) (f (n + 1)) (hδf₀ n)).Exact := by
    intro n
    simpa only [A₀, B, C, δ, f, boundedHomologyFunctor, Functor.comp_obj,
      Functor.comp_map, T', Functor.mapTriangle_obj, Triangle.mk] using
        HomologySequence.exact₁ T' hT' n (n + 1) rfl
  have hA : K₀Ab.HasFiniteNonzeroSupport A₀ := by
    exact boundedHomology_hasFiniteNonzeroSupport A T.obj₁
  have hB : K₀Ab.HasFiniteNonzeroSupport B := by
    exact boundedHomology_hasFiniteNonzeroSupport A T.obj₂
  have hC : K₀Ab.HasFiniteNonzeroSupport C := by
    exact boundedHomology_hasFiniteNonzeroSupport A T.obj₃
  simpa only [boundedEulerClass, K₀Ab.eulerClass, boundedHomologyFunctor,
    Functor.comp_obj, T', Functor.mapTriangle_obj, A₀, B, C] using
    K₀Ab.eulerClass_add_of_exact f g δ hfg₀ hgδ₀ hδf₀ hfg hgδ hδf hA hB hC

/-- Triangle additivity packaged for the universal property of `K₀`. -/
instance boundedEulerClass_isTriangleAdditive :
    IsTriangleAdditive (boundedEulerClass A) :=
  ⟨boundedEulerClass_additive A⟩

/-- The canonical cohomological Euler map `K₀(Dᵇ(A)) →+ K₀Ab(A)`. -/
noncomputable def boundedEulerClassHom : K₀ (Bounded A) →+ K₀Ab A :=
  K₀.lift (Bounded A) (boundedEulerClass A)

@[simp]
theorem boundedEulerClassHom_of (X : Bounded A) :
    boundedEulerClassHom A (K₀.of (Bounded A) X) = boundedEulerClass A X :=
  K₀.lift_of (Bounded A) (boundedEulerClass A) X

end DerivedCategory
