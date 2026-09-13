/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory

/-!
# Regrading homogeneous dg natural transformations by a source shift

Shifting the source by `n` raises the degree of a homogeneous transformation
from `p` to `n + p`.  This file packages that operation as an additive
equivalence, using the generic `IsShiftBy.precompEquiv` in the dg category of
dg functors.  In particular, a degree-`p` transformation `F ⟶ G` becomes a
degree-zero transformation `F[-p] ⟶ G`.

The construction is one-sided on purpose.  It changes the source by composing
with the inverse shift element; it does not introduce another shift functor or
another `HasShift` instance.  The inverse composes with the selected shift
element, and closedness is preserved and reflected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D] [IsPretriangulated D]
  {F G : DGFunctor C D}

/-- The inverse selected by representability in the dg functor category is the
pointwise inverse already selected in the target.  This makes the abstract
source regrading below compute through the original objectwise witnesses. -/
@[simp]
theorem shiftedFunctorWitness_inv_app (F : DGFunctor C D) (n : ℤ) (X : C) :
    HomogeneousNatTrans.app (F.shiftedFunctorWitness n).inv X =
      (F.shiftWitness n X).inv := by
  apply ((F.shiftWitness n X).bijective (F.shiftObj n X) n 0 (by omega)).injective
  change dgComp n (-n) 0 (by omega)
      (HomogeneousNatTrans.app (F.shiftedFunctorWitness n).inv X)
        (F.shiftWitness n X).hom =
    dgComp n (-n) 0 (by omega)
      (F.shiftWitness n X).inv (F.shiftWitness n X).hom
  calc
    _ = HomogeneousNatTrans.app (dgComp n (-n) 0 (by omega)
        (F.shiftedFunctorWitness n).inv (F.shiftHom n)) X :=
      (HomogeneousNatTrans.composition_apply_app (F.shiftedFunctorWitness n).inv
        (F.shiftHom n) 0 (by omega) X).symm
    _ = HomogeneousNatTrans.app (dgId (F.shiftedFunctor n)) X :=
      congrArg (fun θ => HomogeneousNatTrans.app θ X)
        (F.shiftedFunctorWitness n).inv_hom
    _ = dgId (F.shiftObj n X) := rfl
    _ = _ := (F.shiftWitness n X).inv_hom.symm

namespace HomogeneousNatTrans

/-- Regrade a homogeneous dg natural transformation by shifting its source.
Forward transport is precomposition by the inverse shift element; inverse
transport is precomposition by the shift element. -/
noncomputable def sourceShiftEquiv (F G : DGFunctor C D)
    (n p q : ℤ) (h : n + p = q) :
    HomogeneousNatTrans F G p ≃+
      HomogeneousNatTrans (F.shiftedFunctor n) G q :=
  (F.shiftedFunctorWitness n).precompEquiv G p q h

/-- The forward source regrading, evaluated at an object. -/
@[simp]
theorem sourceShiftEquiv_apply_app (F G : DGFunctor C D)
    (n p q : ℤ) (h : n + p = q)
    (α : HomogeneousNatTrans F G p) (X : C) :
    app (sourceShiftEquiv F G n p q h α) X =
      dgComp n p q h (F.shiftWitness n X).inv (app α X) := by
  change app (HomogeneousNatTrans.composition
      (F.shiftedFunctor n) F G n p q h
        (F.shiftedFunctorWitness n).inv α) X = _
  rw [composition_apply_app, shiftedFunctorWitness_inv_app]
  rfl

/-- The inverse source regrading, evaluated at an object. -/
@[simp]
theorem sourceShiftEquiv_symm_apply_app (F G : DGFunctor C D)
    (n p q : ℤ) (h : n + p = q)
    (β : HomogeneousNatTrans (F.shiftedFunctor n) G q) (X : C) :
    app ((sourceShiftEquiv F G n p q h).symm β) X =
      dgComp (-n) q p (by omega) (F.shiftWitness n X).hom (app β X) := by
  change app (HomogeneousNatTrans.composition F (F.shiftedFunctor n) G
      (-n) q p (by omega) (F.shiftHom n) β) X = _
  rw [composition_apply_app, F.shiftHom_app]
  rfl

/-- Source-shift regrading commutes with the pointwise differential because
the inverse shift element is closed and occurs on the left of the transformed
component, where the surviving Leibniz term carries no sign. -/
theorem differential_sourceShiftEquiv (F G : DGFunctor C D)
    (n p q : ℤ) (h : n + p = q)
    (α : HomogeneousNatTrans F G p) :
    differential (sourceShiftEquiv F G n p q h α) =
      sourceShiftEquiv F G n (p + 1) (q + 1) (by omega)
        (differential α) := by
  rw [← complex_d_apply (sourceShiftEquiv F G n p q h α),
    ← complex_d_apply α]
  exact (F.shiftedFunctorWitness n).precompEquiv_d G p q h α

/-- Source-shift regrading preserves and reflects closedness. -/
theorem sourceShiftEquiv_isClosed_iff (F G : DGFunctor C D)
    (n p q : ℤ) (h : n + p = q)
    (α : HomogeneousNatTrans F G p) :
    IsClosed (sourceShiftEquiv F G n p q h α) ↔ IsClosed α := by
  rw [IsClosed, IsClosed, differential_sourceShiftEquiv]
  exact (sourceShiftEquiv F G n (p + 1) (q + 1) (by omega)).map_eq_zero_iff

end HomogeneousNatTrans

end DGFunctor

end CategoryTheory
