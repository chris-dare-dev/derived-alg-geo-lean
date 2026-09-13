/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentation
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.CommShift
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.LinearCopower
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor

/-!
# Finite cohomology presentations of scalar-linear copowers

An explicit finite cohomology presentation of a coefficient complex can be
transported through the selected scalar-linear copower dg functor. The result
is a finite biproduct of shifted degree-zero copowers in `H⁰ C`.

The construction reuses three existing categorical interfaces:

* homotopy invariance of `linearCopowerFunctor`;
* Mathlib's preservation of finite biproducts by additive functors;
* `SingleFunctors.postcomp` and the established coherent shift action on
  `H⁰` of a dg functor.

Thus this file introduces no copower-specific direct-sum preservation record
and no new shift comparison. It does not choose bases for the homology
objects, compute a Grothendieck class, or assert an Euler formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

/-- Degreewise scalar-linear copowers of single coefficient modules, with
their coherent shift comparison inherited by postcomposition. -/
noncomputable def linearCopowerSingleFunctors [IsPretriangulated C] (X : C) :
    SingleFunctors (ModuleCat.{v} k) (H0 C) ℤ := by
  letI : (linearCopowerFunctor k X).h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  exact (CochainComplex.singleFunctors (ModuleCat.{v} k)).postcomp
    (Cdg.toH0 (ModuleCat.{v} k) ⋙ (linearCopowerFunctor k X).h0)

@[simp]
lemma linearCopowerSingleFunctors_obj [IsPretriangulated C]
    (X : C) (i : ℤ) (V : ModuleCat.{v} k) :
    ((linearCopowerSingleFunctors (k := k) X).functor i).obj V =
      (show H0 C from linearCopowerObj (C := C)
        ((CochainComplex.singleFunctor (ModuleCat.{v} k) i).obj V) X) :=
  rfl

end CategoryTheory

namespace CochainComplex.FiniteCohomologyPresentation

open CategoryTheory CategoryTheory.DGCategoryStruct CategoryTheory.DGCategory
  CategoryTheory.Limits

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

variable {K : CochainComplex (ModuleCat.{v} k) ℤ}

/-- A finite cohomology presentation of the coefficient complex presents its
selected scalar-linear copower as a finite biproduct of shifted degree-zero
copowers.

The shift is `-i`, following Mathlib's cochain convention. No cone
preservation or exactness hypothesis is needed. -/
noncomputable def linearCopowerIso [IsPretriangulated C]
    (P : CochainComplex.FiniteCohomologyPresentation K) (X : C) :
    (show H0 C from linearCopowerObj (C := C) K X) ≅
      ⨁ fun i : {i // i ∈ P.degrees} =>
        (show H0 C from linearCopowerObj (C := C)
          ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
            (K.homology i.1)) X)⟦-i.1⟧ := by
  let F : CochainComplex (ModuleCat.{v} k) ℤ ⥤ H0 C :=
    Cdg.toH0 (ModuleCat.{v} k) ⋙ (linearCopowerFunctor k X).h0
  exact linearCopowerObjIsoOfHomotopyEquiv X P.homotopyEquiv ≪≫
    F.mapBiproduct (fun i : {i // i ∈ P.degrees} =>
      (CochainComplex.singleFunctor (ModuleCat.{v} k) i.1).obj
        (K.homology i.1)) ≪≫
    biproduct.mapIso fun i =>
      (((linearCopowerSingleFunctors (k := k) X).shiftIso
        (-i.1) i.1 0 (by omega)).app (K.homology i.1)).symm

end CochainComplex.FiniteCohomologyPresentation
