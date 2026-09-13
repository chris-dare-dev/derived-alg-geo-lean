/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Linear
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ShiftIso

/-!
# Scalar-linear Hom-complex comparison for dg shifts

The additive comparison `IsShiftBy.homIso` identifies the Hom-complex into a
chosen shift with a shifted Hom-complex.  In a `k`-linear dg category the same
right-composition map is linear in every degree, so it gives an isomorphism of
`ModuleCat k`-valued complexes.

This file supplies that scalar refinement.  It does not define another shift,
cohomology object, or quotient: the comparison is built from the existing
`IsShiftBy` witness and `DGLinear.homComplex`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace IsShiftBy

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

private def linearHomCocycle {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) :
    CochainComplex.HomComplex.Cocycle
      (DGLinear.homComplex k W X) (DGLinear.homComplex k W Y) (-n) :=
  CochainComplex.HomComplex.Cocycle.mk
    (DGLinear.postcompCochain k W (-n) h.hom) (-n + 1) rfl (by
      rw [DGLinear.postcompCochain_d, h.hom_closed, map_zero])

/-- Right composition with the shift element as a morphism of scalar-linear
Hom-complexes.  It is obtained from the standard Mathlib equivalence between
closed degree-`-n` cochains and maps into the `-n` shift. -/
noncomputable def linearHomMap {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) :
    DGLinear.homComplex k W X ⟶ (DGLinear.homComplex k W Y)⟦-n⟧ :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (linearHomCocycle (k := k) h W)

@[simp]
lemma linearHomMap_f_apply {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) (p : ℤ)
    (f : (dgHom W X).X p) :
    ((h.linearHomMap (k := k) W).f p).hom f =
      dgComp p (-n) (p + -n) rfl f h.hom :=
  rfl

/-- Every component of the scalar-linear Hom-complex comparison is bijective. -/
lemma bijective_linearHomMap {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) (p : ℤ) :
    Function.Bijective ((h.linearHomMap (k := k) W).f p).hom :=
  h.bijective W p (p + -n) rfl

/-- The scalar-linear Hom-complex isomorphism represented by a chosen dg
shift. -/
noncomputable def linearHomIso {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) :
    DGLinear.homComplex k W X ≅ (DGLinear.homComplex k W Y)⟦-n⟧ := by
  letI (p : ℤ) : IsIso ((h.linearHomMap (k := k) W).f p) :=
    (ConcreteCategory.isIso_iff_bijective ((h.linearHomMap (k := k) W).f p)).2
      (h.bijective_linearHomMap (k := k) W p)
  exact HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ asIso ((h.linearHomMap (k := k) W).f p))
    (fun p q _ ↦ (h.linearHomMap (k := k) W).comm p q)

@[simp]
lemma linearHomIso_hom_f_apply {X Y : C} {n : ℤ}
    (h : IsShiftBy X n Y) (W : C) (p : ℤ)
    (f : (dgHom W X).X p) :
    ((h.linearHomIso (k := k) W).hom.f p).hom f =
      dgComp p (-n) (p + -n) rfl f h.hom :=
  rfl

end IsShiftBy

end CategoryTheory
