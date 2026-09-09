/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.H0
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-!
# Closed degree-zero dg natural transformations in `H⁰`

A closed homogeneous dg natural transformation of degree zero has closed
components, so each of them represents a morphism of `H⁰`, and its graded
naturality at degree zero carries no sign.  What comes out is an ordinary
natural transformation `H⁰ F ⟶ H⁰ G`.

This is the adapter that lets dg-level data be compared with ordinary
categorical data at all: without it a `DGAdjunction` and a Mathlib
`Adjunction` on `H⁰` are two unrelated structures.

## Only degree zero, and only closed

Both hypotheses are used and neither can be dropped.  A transformation of
degree `n ≠ 0` has components in the wrong group to be a morphism of `H⁰`,
and an unclosed degree-zero one has components that are not cocycles.  The
sign in graded naturality is `(-1)^(n * p)`, which is `+1` exactly because
both `n` and the degree `p` of the morphism being transported are zero here;
a degree-`n` version would have to land in a shifted Hom, which is the
functorial-shift capability the roadmap still lists as open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  {F G : DGFunctor C D}

/-- A closed dg natural transformation has closed components. -/
lemma IsClosed.app_mem_cocycles {α : HomogeneousNatTrans F G 0}
    (hα : IsClosed α) (X : C) :
    app α X ∈ cocycles (F.obj X) (G.obj X) := by
  rw [mem_cocycles_iff]
  rw [← show (0 : ℤ) + 1 = 1 by omega]
  exact hα.app_d X

/-- **A closed degree-zero dg natural transformation descends to `H⁰`.**

The components are the classes of the dg components; naturality is graded
naturality at degree zero, where the Koszul sign is `+1`. -/
def h0 (α : HomogeneousNatTrans F G 0) (hα : IsClosed α) : F.h0 ⟶ G.h0 where
  app X := H0.homMk (C := D) ⟨app α (H0.of C X), hα.app_mem_cocycles _⟩
  naturality := by
    intro X Y f
    induction f using Quotient.ind with
    | _ f =>
      change H0.homMk _ ≫ H0.homMk _ = H0.homMk _ ≫ H0.homMk _
      rw [H0.homMk_comp, H0.homMk_comp]
      refine congrArg _ (Subtype.ext ?_)
      -- `exact` rather than `simpa`: the two sides differ only in whether the
      -- target is spelled through `G.h0` or through `G`, which is definitional.
      have h := naturality α 0 0 (by omega) (by omega) f.1
      rw [zero_mul, Int.negOnePow_zero, one_smul] at h
      exact h

@[simp]
theorem h0_app (α : HomogeneousNatTrans F G 0) (hα : IsClosed α) (X : H0 C) :
    (h0 α hα).app X =
      H0.homMk (C := D) ⟨app α (H0.of C X), hα.app_mem_cocycles _⟩ :=
  rfl

/-- The identity dg natural transformation descends to the identity. -/
@[simp]
theorem h0_id (F : DGFunctor C D) (hF : IsClosed (id F)) :
    h0 (id F) hF = 𝟙 F.h0 := by
  ext X
  exact H0.homMk_id (C := D) (F.obj (H0.of C X))

/-- The identity dg natural transformation is closed. -/
theorem isClosed_id (F : DGFunctor C D) : IsClosed (id F) := by
  ext X
  exact dgId_cocycle (F.obj X)

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
