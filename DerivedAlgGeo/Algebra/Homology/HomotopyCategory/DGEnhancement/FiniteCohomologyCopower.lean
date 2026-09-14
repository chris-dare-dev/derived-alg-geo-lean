/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentation
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.LinearCopowerFiniteFree

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
and no new shift comparison. Its finite-free specialization consumes the
generic sibling interface, makes no basis-independence claim, computes no
Grothendieck class, and asserts no Euler formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

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

namespace CochainComplex.FiniteCohomologyPresentation

open CategoryTheory CategoryTheory.DGCategoryStruct CategoryTheory.DGCategory
  CategoryTheory.Limits

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {k : Type v} [CommRing k] [StrongRankCondition k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]
  {K : CochainComplex (ModuleCat.{v} k) ℤ}

/-- If the homology modules in a supplied finite presentation are finite free,
the selected scalar-linear copower is a finite biproduct of shifts of the
original object, with multiplicities given by their `finrank`s.

The nested biproduct records the cohomological degree and its multiplicity
separately. The isomorphism is noncanonical: each inner expansion uses
Mathlib's noncomputably selected finite basis. -/
noncomputable def linearCopowerFinrankIso [IsPretriangulated C]
    (P : CochainComplex.FiniteCohomologyPresentation K)
    [∀ i : {i // i ∈ P.degrees}, Module.Free k (K.homology i.1)]
    [∀ i : {i // i ∈ P.degrees}, Module.Finite k (K.homology i.1)]
    (X : C) :
    (show H0 C from linearCopowerObj (C := C) K X) ≅
      ⨁ fun i : {i // i ∈ P.degrees} =>
        ⨁ fun _ : Fin (Module.finrank k (K.homology i.1)) =>
          (show H0 C from X)⟦-i.1⟧ :=
  P.linearCopowerIso X ≪≫
    biproduct.mapIso (fun i =>
      (CategoryTheory.shiftFunctor (H0 C) (-i.1)).mapIso
        (CategoryTheory.linearCopowerSingleZeroFinrankIso
          (k := k) (V := K.homology i.1) X) ≪≫
      (CategoryTheory.shiftFunctor (H0 C) (-i.1)).mapBiproduct
        (fun _ : Fin (Module.finrank k (K.homology i.1)) =>
          (show H0 C from X)))

end CochainComplex.FiniteCohomologyPresentation
