/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.SingleHomology
import DerivedAlgGeo.Algebra.Homology.Homotopy.HomologyModel

/-!
# Finite cohomology presentations

This file packages the coefficient-side splitting input needed by finite
cohomological constructions. For a complex `K` and a finite set of degrees
`s`, `finiteCohomologyModel K s` is the finite biproduct of the homology
objects of `K`, each placed in its own degree. A
`FiniteCohomologyPresentation K` is an explicit homotopy equivalence from `K`
to one such model.

The finite set is called `degrees`, not `support`: it may contain degrees in
which homology vanishes. The presentation is data rather than a typeclass,
because its chain maps and homotopies are noncanonical choices which later
consumers use explicitly.

No formality theorem is asserted here. In particular, boundedness or finite
dimensionality alone is not silently converted into a homotopy equivalence,
and quasi-isomorphisms are not treated as homotopy equivalences. This file
also does not mention dg copowers, Euler characteristics, or Grothendieck
groups.

When homology vanishes away from the selected degrees,
`homologyModelIsoFiniteCohomologyModel` identifies the full zero-differential
homology model with this finite model.  This is a categorical comparison, not
a formality theorem for the original complex.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory Category Limits

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The finite zero-differential model formed from the homology objects of
`K` in the specified degrees.

It is assembled from Mathlib's `singleFunctor` and finite biproduct rather
than from a repository-owned shifted-sum construction. -/
noncomputable def finiteCohomologyModel
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) :
    CochainComplex A ℤ :=
  ⨁ fun i : {i // i ∈ degrees} =>
    (singleFunctor A i.1).obj (K.homology i.1)

/-- Homology of the finite model is the finite biproduct of the homologies of
its single summands. This is Mathlib's additive homology functor preserving a
finite biproduct. -/
noncomputable def finiteCohomologyModelHomologyIso
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) (i : ℤ) :
    (finiteCohomologyModel K degrees).homology i ≅
      ⨁ fun j : {j // j ∈ degrees} =>
        ((singleFunctor A j.1).obj (K.homology j.1)).homology i := by
  let F := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  change F.obj (⨁ fun j : {j // j ∈ degrees} =>
    (singleFunctor A j.1).obj (K.homology j.1)) ≅ _
  exact F.mapBiproduct _

/-- Away from the selected finite set, every degree of the finite cohomology
model is a biproduct of zero objects. -/
lemma isZero_finiteCohomologyModel_X_of_not_mem
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) (i : ℤ)
    (hi : i ∉ degrees) :
    IsZero ((finiteCohomologyModel K degrees).X i) := by
  let F := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  apply ((F.mapBiproduct fun j : {j // j ∈ degrees} =>
    (singleFunctor A j.1).obj (K.homology j.1))).isZero_iff.mpr
  apply (biproduct.isLimit _).isZero_pt
  exact Functor.isZero _ fun j =>
    HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) j.as.1 (K.homology j.as.1) i (by
        intro h
        apply hi
        rw [h]
        exact j.as.2)

set_option backward.isDefEq.respectTransparency false in
/-- The finite cohomology model has zero differential. -/
@[simp]
lemma finiteCohomologyModel_d
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) (i j : ℤ) :
    (finiteCohomologyModel K degrees).d i j = 0 := by
  change (⨁ fun n : {n // n ∈ degrees} =>
    (singleFunctor A n.1).obj (K.homology n.1)).d i j = 0
  apply (cancel_mono (((HomologicalComplex.eval A (ComplexShape.up ℤ) j).mapBiproduct
    fun n : {n // n ∈ degrees} =>
      (singleFunctor A n.1).obj (K.homology n.1))).hom).1
  apply biproduct.hom_ext
  intro n
  dsimp only [Function.comp_def]
  simp only [Category.assoc, Functor.mapBiproduct_hom,
    biproduct.lift_π, HomologicalComplex.eval_map]
  rw [zero_comp]
  simpa only [CochainComplex.singleFunctor_obj_d, comp_zero, zero_comp] using
    ((biproduct.π (fun n : {n // n ∈ degrees} =>
      (singleFunctor A n.1).obj (K.homology n.1)) n).comm i j).symm

/-- A biproduct whose summands other than `i` are zero is isomorphic to its
`i`-th summand. -/
private noncomputable def biproductIsoOfIsZeroCompl
    {J : Type*} [Fintype J] (f : J → A) (i : J)
    (h : ∀ j, j ≠ i → IsZero (f j)) :
    (⨁ f) ≅ f i where
  hom := biproduct.π f i
  inv := biproduct.ι f i
  hom_inv_id := by
    apply biproduct.hom_ext
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · exact (h j hj).eq_of_tgt _ _
  inv_hom_id := by simp

/-- In a retained degree, evaluation of the finite cohomology model is the
corresponding homology object. -/
private noncomputable def finiteCohomologyModelXIsoOfMem
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) (i : ℤ)
    (hi : i ∈ degrees) :
    (finiteCohomologyModel K degrees).X i ≅ K.homology i :=
  let F := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  F.mapBiproduct (fun j : {j // j ∈ degrees} =>
      (singleFunctor A j.1).obj (K.homology j.1)) ≪≫
    biproductIsoOfIsZeroCompl
      (fun j : {j // j ∈ degrees} =>
        ((singleFunctor A j.1).obj (K.homology j.1)).X i)
      ⟨i, hi⟩ (fun j hj =>
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) j.1 (K.homology j.1) i (by
            intro h
            apply hj
            apply Subtype.ext
            exact h.symm)) ≪≫
    HomologicalComplex.singleObjXSelf
      (ComplexShape.up ℤ) i (K.homology i)

/-- If the homology of `K` vanishes away from `degrees`, its full
zero-differential homology model is isomorphic to the existing finite
cohomology model on `degrees`.

This comparison is categorical and does not assert that `K` itself is formal.
-/
noncomputable def homologyModelIsoFiniteCohomologyModel
    (K : CochainComplex A ℤ) (degrees : Finset ℤ)
    (hSupport : ∀ i, i ∉ degrees → IsZero (K.homology i)) :
    homologyModel K ≅ finiteCohomologyModel K degrees :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if hi : i ∈ degrees then
      (finiteCohomologyModelXIsoOfMem K degrees i hi).symm
    else
      IsZero.iso (hSupport i hi)
        (isZero_finiteCohomologyModel_X_of_not_mem K degrees i hi))
    (fun i j _ => by
      simp only [homologyModel_d, finiteCohomologyModel_d,
        zero_comp, comp_zero])

/-- A chosen homotopy presentation of a complex by finitely many of its
homology objects. -/
structure FiniteCohomologyPresentation (K : CochainComplex A ℤ) where
  /-- Degrees retained by the finite model. This need not be minimal. -/
  degrees : Finset ℤ
  /-- The chosen homotopy equivalence to the finite homology model. -/
  homotopyEquiv : HomotopyEquiv K (finiteCohomologyModel K degrees)

/-- The finite homology model in its canonical shifted degree-zero form.

Mathlib's cochain convention is `(K⟦n⟧).X p = K.X (p + n)`, so the
single object in degree `i` is the degree-zero single shifted by `-i`. This
normalization belongs to the model itself and requires no formality data. -/
noncomputable def finiteCohomologyModelIsoShifted
    (K : CochainComplex A ℤ) (degrees : Finset ℤ) :
    finiteCohomologyModel K degrees ≅
      ⨁ fun i : {i // i ∈ degrees} =>
        ((singleFunctor A 0).obj (K.homology i.1))⟦-i.1⟧ :=
  biproduct.mapIso fun i =>
    (((singleFunctors A).shiftIso (-i.1) i.1 0 (by omega)).app
      (K.homology i.1)).symm

namespace FiniteCohomologyPresentation

variable {K L : CochainComplex A ℤ}

/-- Pull a finite cohomology presentation back along a homotopy
equivalence. -/
noncomputable def pullback
    (P : FiniteCohomologyPresentation L) (e : HomotopyEquiv K L) :
    FiniteCohomologyPresentation K where
  degrees := P.degrees
  homotopyEquiv := e.trans <|
    P.homotopyEquiv.trans <| HomotopyEquiv.ofIso <|
      biproduct.mapIso fun i =>
        (singleFunctor A i.1).mapIso (e.toHomologyIso i.1).symm

@[simp]
lemma pullback_degrees
    (P : FiniteCohomologyPresentation L) (e : HomotopyEquiv K L) :
    (P.pullback e).degrees = P.degrees :=
  rfl

/-- The presentation identifies the homology of `K` with that of its finite
model. -/
noncomputable def homologyIso (P : FiniteCohomologyPresentation K) (i : ℤ) :
    K.homology i ≅ (finiteCohomologyModel K P.degrees).homology i :=
  P.homotopyEquiv.toHomologyIso i

/-- A finite cohomology presentation forces homology to vanish outside its
recorded finite set of degrees. -/
lemma isZero_homology_of_not_mem
    (P : FiniteCohomologyPresentation K) (i : ℤ) (hi : i ∉ P.degrees) :
    IsZero (K.homology i) := by
  apply (P.homologyIso i).isZero_iff.mpr
  apply (finiteCohomologyModelHomologyIso K P.degrees i).isZero_iff.mpr
  apply (biproduct.isLimit _).isZero_pt
  exact Functor.isZero _ fun j =>
    HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) j.as.1 (K.homology j.as.1) i (by
        intro h
        apply hi
        rw [h]
        exact j.as.2)

/-- A presentation also gives a homotopy equivalence directly to the shifted
degree-zero normal form. -/
noncomputable def shiftedHomotopyEquiv
    (P : FiniteCohomologyPresentation K) :
    HomotopyEquiv K
      (⨁ fun i : {i // i ∈ P.degrees} =>
        ((singleFunctor A 0).obj (K.homology i.1))⟦-i.1⟧) :=
  P.homotopyEquiv.trans <|
    HomotopyEquiv.ofIso (finiteCohomologyModelIsoShifted K P.degrees)

end FiniteCohomologyPresentation

end CochainComplex
