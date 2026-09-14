/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopowerUnit
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.CommShift
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.LinearCopower
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite-free scalar-linear copowers

Degreewise scalar-linear copowers of single coefficient modules form a
coherent shifted family. A supplied finite basis expands the degree-zero member
as a finite biproduct of copies of the original object in `H⁰`; finite free
modules over rings with strong rank condition therefore have a `finrank`
expansion.

The public basis interface allows an arbitrary finite index universe. Its
implementation reindexes to `Fin n`, where Mathlib's concrete
`ModuleCat.biproductIsoPi` and additive-functor preservation apply, and then
uses Mathlib's categorical biproduct reindexing. No basis-independence,
Grothendieck-class, or Euler claim is made.
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

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits

section FiniteFree

variable {k : Type v} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

/-- A finite basis identifies its module with a finite biproduct of copies of
the scalar unit. This helper remains private until it has a second consumer
outside scalar-linear copowers. -/
private noncomputable def basisBiproductIso
    {ι : Type} [Finite ι] {V : ModuleCat.{v} k} (b : Module.Basis ι k V) :
    V ≅ ⨁ fun _ : ι => ModuleCat.of k k :=
  b.equivFun.toModuleIso ≪≫
    (ModuleCat.biproductIsoPi
      (fun _ : ι => ModuleCat.of k k)).symm

/-- The small-universe implementation of basis expansion. Arbitrary finite
index types are reduced to this case below by reindexing to `Fin n`. -/
private noncomputable def linearCopowerSingleZeroIsoOfSmallBasis
    [IsPretriangulated C] {ι : Type} [Finite ι]
    {V : ModuleCat.{v} k} (b : Module.Basis ι k V) (X : C) :
    (show H0 C from linearCopowerObj (C := C)
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj V) X) ≅
      ⨁ fun _ : ι => (show H0 C from X) := by
  let F := (CochainComplex.singleFunctor (ModuleCat.{v} k) 0) ⋙
    (Cdg.toH0 (ModuleCat.{v} k) ⋙ (linearCopowerFunctor k X).h0)
  letI : F.Additive := by
    dsimp [F]
    infer_instance
  exact F.mapIso (basisBiproductIso b) ≪≫
    F.mapBiproduct (fun _ : ι => ModuleCat.of k k) ≪≫
    biproduct.mapIso (fun _ : ι => linearCopowerUnitIso (k := k) X)

/-- A chosen finite basis expands the degree-zero single linear copower into
a finite biproduct of copies of the original object. The index universe is
independent of the coefficient-module universe. -/
noncomputable def linearCopowerSingleZeroIsoOfBasis
    [IsPretriangulated C] {ι : Type w} [Finite ι]
    {V : ModuleCat.{v} k} (b : Module.Basis ι k V) (X : C) :
    (show H0 C from linearCopowerObj (C := C)
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj V) X) ≅
      ⨁ fun _ : ι => (show H0 C from X) := by
  classical
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  exact linearCopowerSingleZeroIsoOfSmallBasis (b.reindex e) X ≪≫
    (biproduct.whiskerEquiv
      (f := fun _ : ι => (show H0 C from X))
      (g := fun _ : Fin (Fintype.card ι) => (show H0 C from X))
      e (fun _ => Iso.refl _)).symm

/-- A finite free degree-zero coefficient module over a ring with strong rank
condition expands its selected linear copower into `finrank` copies of the
original object. The isomorphism uses Mathlib's noncomputably selected finite
basis; fields are the main specialization. -/
noncomputable def linearCopowerSingleZeroFinrankIso
    [StrongRankCondition k] [IsPretriangulated C] {V : ModuleCat.{v} k}
    [Module.Free k V]
    [Module.Finite k V] (X : C) :
    (show H0 C from linearCopowerObj (C := C)
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj V) X) ≅
      ⨁ fun _ : Fin (Module.finrank k V) => (show H0 C from X) :=
  linearCopowerSingleZeroIsoOfBasis (Module.finBasis k V) X

end FiniteFree

end CategoryTheory
