/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ModuleCat.LinearDual
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Serre functors on linear categories

A Serre functor on a `k`-linear category is an endofunctor `S` together with
natural linear equivalences

`Dual k (A ⟶ B) ≃ₗ[k] (B ⟶ S.obj A)`.

The pointwise equivalences and their two naturality equations are the fields of
`SerreFunctorData`.  This is data by the mathematical nature of a Serre
functor, not a `...Data` wrapper meaning that an unproved theorem has silently
been postulated.  Geometric consumers may later supply such data explicitly.

No shift or triangulation is needed for the definition.  Hom-finiteness is a
separate property and appears only where double-dual or dimension arguments
actually spend it.

The would-be functor-level packaging has variance `C × Cᵒᵖ`: dualising
reverses the contravariance/covariance of `Hom(A,B)`.  It is deliberately not
exported at these general universes.  If `k : Type w` and morphisms live in
`Type v`, then `Dual k Hom(A,B)` lives in `Type (max w v)` while
`Hom(B,S A)` remains in `Type v`; without an equality or a systematic `ULift`,
they are not objects of the same `ModuleCat`.  The pointwise `≃ₗ` has no such
artificial restriction and every downstream theorem uses it directly.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C]

/-- Every Hom-space of a linear category is finite-dimensional. -/
class HomFinite : Prop where
  /-- The finite-dimensionality witness for each Hom-space. -/
  finite : ∀ A B : C, Module.Finite k (A ⟶ B)

attribute [instance] HomFinite.finite

/-- A Serre functor with its natural duality equivalence.

The two equations are written pointwise to keep the variance explicit and to
avoid hiding the load-bearing content inside a large functor expression. -/
structure SerreFunctorData where
  /-- The underlying endofunctor. -/
  S : C ⥤ C
  /-- Serre duality, pointwise. -/
  eta : ∀ A B : C, Module.Dual k (A ⟶ B) ≃ₗ[k] (B ⟶ S.obj A)
  /-- Naturality in the first, covariant variable. -/
  naturality_left : ∀ {A A' B : C} (f : A ⟶ A') (phi : Module.Dual k (A ⟶ B)),
    eta A' B (phi.comp (Linear.leftComp k B f)) =
      eta A B phi ≫ S.map f
  /-- Naturality in the second, contravariant variable. -/
  naturality_right : ∀ {A B B' : C} (g : B' ⟶ B) (phi : Module.Dual k (A ⟶ B)),
    eta A B' (phi.comp (Linear.rightComp k A g)) =
      g ≫ eta A B phi

/-- The property that a category admits some Serre functor. -/
abbrev HasSerreFunctor : Prop := Nonempty (SerreFunctorData k C)

/-- A chosen Serre functor which is an autoequivalence.

This is the common categorical package used by geometric residual categories.
The stronger `EnriquesCategoryData` adds a specified relation between the
square of the Serre functor and a shift. -/
structure SerreCategoryData where
  /-- The chosen Serre functor and duality. -/
  serre : SerreFunctorData k C
  /-- The Serre functor is an autoequivalence. -/
  serreIsEquivalence : serre.S.IsEquivalence

namespace SerreCategoryData

variable {k C} (A : SerreCategoryData k C)

/-- The chosen Serre functor can be used as an equivalence by a consumer
without installing a global instance. -/
theorem hasSerreEquivalence : A.serre.S.IsEquivalence :=
  A.serreIsEquivalence

end SerreCategoryData

namespace SerreFunctorData

variable {k C} (D : SerreFunctorData k C)

/-- The Serre pairing `Hom(A,B) × Hom(B,S A) → k`. -/
noncomputable def pairing (A B : C) :
    (A ⟶ B) →ₗ[k] (B ⟶ D.S.obj A) →ₗ[k] k where
  toFun f :=
    { toFun := fun g ↦ (D.eta A B).symm g f
      map_add' := by
        intro g h
        rw [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c g
        simp }
  map_add' := by
    intro f g
    ext h
    exact map_add ((D.eta A B).symm h) f g
  map_smul' := by
    intro c f
    ext g
    simp

@[simp]
theorem pairing_apply (A B : C) (f : A ⟶ B) (g : B ⟶ D.S.obj A) :
    D.pairing A B f g = (D.eta A B).symm g f :=
  rfl

/-- The Serre pairing separates its first argument. -/
theorem pairing_separating_left (A B : C) (f : A ⟶ B)
    (hf : ∀ g : B ⟶ D.S.obj A, D.pairing A B f g = 0) : f = 0 := by
  apply Module.eval_apply_injective k
  ext phi
  simpa using hf (D.eta A B phi)

/-- The Serre pairing separates its second argument. -/
theorem pairing_separating_right (A B : C) (g : B ⟶ D.S.obj A)
    (hg : ∀ f : A ⟶ B, D.pairing A B f g = 0) : g = 0 := by
  apply (D.eta A B).symm.injective
  apply LinearMap.ext
  intro f
  simpa using hg f

/-- Serre duality identifies the dimensions of the two Hom-spaces. -/
theorem finrank_hom_eq [HomFinite k C] (A B : C) :
    Module.finrank k (A ⟶ B) = Module.finrank k (B ⟶ D.S.obj A) := by
  calc
    Module.finrank k (A ⟶ B) =
        Module.finrank k (Module.Dual k (Module.Dual k (A ⟶ B))) :=
      (Module.evalEquiv k (A ⟶ B)).finrank_eq
    _ = Module.finrank k (Module.Dual k (A ⟶ B)) :=
      Subspace.dual_finrank_eq
    _ = Module.finrank k (B ⟶ D.S.obj A) :=
      (D.eta A B).finrank_eq

/-- The Serre trace on maps `A ⟶ S A`. -/
noncomputable def trace (A : C) : (A ⟶ D.S.obj A) →ₗ[k] k where
  toFun f := (D.eta A A).symm f (𝟙 A)
  map_add' := by intro f g; rw [map_add, LinearMap.add_apply]
  map_smul' := by
    intro c f
    simp

@[simp]
theorem trace_apply (A : C) (f : A ⟶ D.S.obj A) :
    D.trace A f = (D.eta A A).symm f (𝟙 A) :=
  rfl

/-- Cyclicity of the Serre trace, obtained from both naturality fields. -/
theorem trace_comp {A B : C} (f : A ⟶ B) (g : B ⟶ D.S.obj A) :
    D.trace B (g ≫ D.S.map f) = D.trace A (f ≫ g) := by
  let phi : Module.Dual k (A ⟶ B) := (D.eta A B).symm g
  have hleft := D.naturality_left f phi
  have hright := D.naturality_right f phi
  simp only [phi, LinearEquiv.apply_symm_apply] at hleft hright
  change (D.eta B B).symm (g ≫ D.S.map f) (𝟙 B) =
    (D.eta A A).symm (f ≫ g) (𝟙 A)
  rw [← hleft, ← hright]
  simp [Linear.leftComp, Linear.rightComp]

end SerreFunctorData

end CategoryTheory.SerreFunctor
