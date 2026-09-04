/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Functor

/-!
# `k`-linear dg categories

`DGCategory` is stated over abelian groups so that its Hom-complexes are
exactly the complexes `CochainComplex.HomComplex` produces. Linearity over a
commutative ring is layered on top, the way `CategoryTheory.Linear` layers over
`Preadditive` in Mathlib.

`ADR-0011` records why this is a refinement rather than part of the definition:
a first draft that baked `ModuleCat k` into `dgHom` collided with the
`AddCommGrpCat`-valued `HomComplex` three separate times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u'' w

namespace CategoryTheory

open DGCategoryStruct

/-- A `k`-linear structure on a dg category: given `k`-module structures on the
graded pieces of the Hom-complexes, both the differential and the composition
are `k`-linear.

The module structures are a parameter rather than a field. A field cannot be
used as an instance inside the same class's later field types, and the version
that tried produced a stuck `HSMul` metavariable on the first axiom. -/
class DGLinear (k : Type w) [CommRing k] (C : Type u) [DGCategory.{v} C]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)] where
  /-- The differential is `k`-linear. -/
  d_smul {X Y : C} (p q : ℤ) (c : k) (f : (dgHom X Y).X p) :
    ((dgHom X Y).d p q).hom (c • f) = c • ((dgHom X Y).d p q).hom f
  /-- Composition is `k`-linear in its first argument. -/
  comp_smul_left {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : k)
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g
  /-- Composition is `k`-linear in its second argument. -/
  comp_smul_right {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : k)
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g

namespace DGFunctor

/-- A scalar-preserving dg functor between `k`-linear dg categories. This is a
refinement of `DGFunctor`, parallel to Mathlib's `Functor.Linear`; it records
only linearity of the maps on Hom-complexes. -/
class Linear (k : Type w) [CommRing k]
    {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
    [∀ (X Y : D) (p : ℤ), Module k ((dgHom X Y).X p)]
    [DGLinear k C] [DGLinear k D] (F : DGFunctor C D) : Prop where
  /-- A linear dg functor preserves scalar multiplication in every degree. -/
  map_smul {X Y : C} (p : ℤ) (c : k) (f : (dgHom X Y).X p) :
    F.map p (c • f) = c • F.map p f

variable {k : Type w} [CommRing k]
  {C : Type u} {D : Type u'} {E : Type u''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [∀ (X Y : D) (p : ℤ), Module k ((dgHom X Y).X p)]
  [∀ (X Y : E) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [DGLinear k D] [DGLinear k E]

variable {F : DGFunctor C D} {G : DGFunctor D E}

/-- A linear dg functor preserves scalar multiplication in every degree. -/
@[simp]
lemma map_smul [F.Linear k] {X Y : C} (p : ℤ) (c : k) (f : (dgHom X Y).X p) :
    F.map p (c • f) = c • F.map p f :=
  Linear.map_smul _ _ _

/-- The identity dg functor is linear. -/
instance idLinear : (DGFunctor.id C).Linear k where
  map_smul _ _ _ := rfl

/-- A composite of linear dg functors is linear. -/
instance compLinear [F.Linear k] [G.Linear k] : (F.comp G).Linear k where
  map_smul p c f := by
    change G.map p (F.map p (c • f)) = c • G.map p (F.map p f)
    rw [F.map_smul, G.map_smul]

end DGFunctor

end CategoryTheory
