/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentationOfSupport
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomology
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# Finite cohomology presentations for dg Hom-complexes

In a scalar-linear pretriangulated dg category with `HomFiniteBounded` H⁰,
the cohomology of every dg Hom-complex is finite-dimensional and supported in
finitely many degrees.  Over the coefficient field, the general formality
theorem therefore supplies a finite cohomology presentation automatically.

The selected degree set is the finite support already carried by
`HomFiniteBounded`.  This file does not assert naturality of the resulting
presentations or exactness of any evaluation functor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated Limits

namespace H0

variable (k : Type w) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]

/-- The finite set of shifts on which the H⁰ Hom-space can have nonzero
dimension. -/
noncomputable def homComplexCohomologyDegrees (X Y : C) : Finset ℤ :=
  (HomFiniteBounded.support_finite (k := k)
    (show H0 C from X) (show H0 C from Y)).toFinset

/-- The homology of a dg Hom-complex vanishes away from the finite support
selected by `HomFiniteBounded`. -/
lemma isZero_homComplex_homology_of_not_mem (X Y : C) (i : ℤ)
    (hi : i ∉ homComplexCohomologyDegrees k X Y) :
    IsZero ((DGLinear.homComplex k X Y).homology i) := by
  have hnot : i ∉ Function.support (fun n : ℤ =>
      (Module.finrank k
        ((show H0 C from X) ⟶ (show H0 C from Y)⟦n⟧) : ℤ)) := by
    intro hmem
    apply hi
    exact (HomFiniteBounded.support_finite (k := k)
      (show H0 C from X) (show H0 C from Y)).mem_toFinset.mpr hmem
  have hfinrankInt :
      (Module.finrank k
        ((show H0 C from X) ⟶ (show H0 C from Y)⟦i⟧) : ℤ) = 0 := by
    by_contra hne
    apply hnot
    exact hne
  have hfinrankNat :
      Module.finrank k
        ((show H0 C from X) ⟶ (show H0 C from Y)⟦i⟧) = 0 := by
    exact_mod_cast hfinrankInt
  letI : Subsingleton
      ((show H0 C from X) ⟶ (show H0 C from Y)⟦i⟧) :=
    Module.finrank_zero_iff.mp hfinrankNat
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (homologyShiftLinearEquiv (k := k) X Y i).toEquiv.subsingleton

/-- The canonical finite-support choice together with coefficient-side
formality gives a finite cohomology presentation of every dg Hom-complex. -/
noncomputable def homComplexFiniteCohomologyPresentation (X Y : C) :
    CochainComplex.FiniteCohomologyPresentation
      (DGLinear.homComplex k X Y) :=
  CochainComplex.FiniteCohomologyPresentation.ofFiniteSupport
    (DGLinear.homComplex k X Y) (homComplexCohomologyDegrees k X Y)
    (isZero_homComplex_homology_of_not_mem k X Y)

end H0

end CategoryTheory
