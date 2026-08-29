/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.Seam
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.ShiftComparison

/-!
# The seam commutes with the shift

`dg-enhancements-e7`. `Cdg.seam : H⁰(C^dg A) ≌ K(A)` is an equivalence of
ordinary categories, and both sides carry a shift by `ℤ`: on the left the one
`H0Shift.lean` builds out of `IsPretriangulated.exists_shift`, on the right
Mathlib's, induced through the quotient. Nothing so far relates them.
`Functor.CommShift` does, and #378 calls it "the real content of this epic".

## The route: factor through cochain complexes

The two shifts are built by different routes out of the same shift on
`CochainComplex A ℤ`, so the comparison is cleanest with that common source kept
in the picture. The tautological functor

    Cdg.toH0 : CochainComplex A ℤ ⥤ H⁰(C^dg A)

is the identity on objects, sends a chain map to the class of its own cochain,
and is full; and it satisfies `Cdg.toH0 ⋙ Cdg.h0Functor = HomotopyCategory.quotient`
on morphisms as well as objects (`Cdg.h0Functor_map_toH0_map`). So a `CommShift`
structure on `Cdg.toH0`, together with Mathlib's on the quotient functor,
assembles into one on the seam -- and that assembly is formal, which is the point
of going this way round.

## Where the mathematics actually is

All of it is in `Cdg.toH0`'s two coherence identities, and both reduce to
`IsShiftBy.compare` bookkeeping over the model lemmas of
`HomotopyCategory/ShiftComparison.lean`. The chosen shift
`IsPretriangulated.shiftObj` is
`Classical.choice`, so it is never unfolded; what is used is that any two shifts
of the same object by the same degree are canonically isomorphic and that those
comparisons compose (`IsShiftBy.compare_trans`). The `add` coherence telescopes a
four-term composite into a single `compare` in exactly that way.

## `backward.isDefEq.respectTransparency`

`H0 C` is a type synonym for `C`, so goals about `H0 (Cdg A)` are routinely
ill-typed at `instances` transparency and no rewrite fires. Mathlib's own
`set_option backward.isDefEq.respectTransparency false` is the sanctioned way
through, and it is used here for exactly the declarations that need it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex Limits DGCategoryStruct DGCategory

namespace Cdg
variable (A : Type u) [Category.{v} A] [Preadditive A]

/-- Cochain complexes into `H⁰(C^dg A)`. -/
def toH0 : CochainComplex A ℤ ⥤ H0 (Cdg A) where
  obj K := (show H0 (Cdg A) from (K : Cdg A))
  map {K L} φ := H0.homMk (C := Cdg A) (X := (K : Cdg A)) (Y := (L : Cdg A))
    ⟨Cochain.ofHom φ, δ_ofHom φ⟩
  map_id K := rfl
  map_comp {K L M} φ ψ := by
    rw [H0.homMk_comp]
    exact congrArg _ (Subtype.ext (Cochain.ofHom_comp φ ψ))

variable {A}

lemma toH0_map {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (toH0 A).map φ = H0.homMk (C := Cdg A) (X := (K : Cdg A)) (Y := (L : Cdg A))
      ⟨Cochain.ofHom φ, δ_ofHom φ⟩ := rfl

instance : (toH0 A).Full where
  map_surjective {K L} f := by
    induction f using Quotient.ind with
    | _ z =>
      refine ⟨Cocycle.homOf (⟨z.1, z.2⟩ : Cocycle (of A K) (of A L) 0), ?_⟩
      exact congrArg _ (Subtype.ext (Cocycle.cochain_ofHom_homOf_eq_coe _))

lemma h0Functor_map_toH0_map {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    h0Functor.map ((toH0 A).map φ) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ :=
  congrArg (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    (Cocycle.homOf_ofHom_eq_self φ)

section CommShift
variable [HasBinaryBiproducts A] [HasZeroObject A]

/-- The comparison between the model shift and the chosen shift, in `H⁰`. -/
noncomputable def toH0ShiftIso (K : Cdg A) (n : ℤ) :
    (show H0 (Cdg A) from shiftObj K n) ≅
      (show H0 (Cdg A) from IsPretriangulated.shiftObj (Cdg A) K n) :=
  H0.compareIso (Cdg.isShiftBy K n) (IsPretriangulated.shiftWitness (Cdg A) K n)

omit [HasBinaryBiproducts A] [HasZeroObject A] in
lemma compare_isShiftBy_zero (K : Cdg A) :
    IsShiftBy.compare (Cdg.isShiftBy K 0) (IsShiftBy.self K) =
      Cochain.ofHom ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app (of A K)) := by
  refine IsShiftBy.compare_unique _ _ _ ?_
  show Cochain.comp (shiftCocycle K 0).1
      (Cochain.ofHom ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app (of A K)))
      (show -0 + 0 = -0 by omega) = Cochain.ofHom (𝟙 (of A K))
  rw [shiftCocycle_zero]
  exact (Cochain.ofHom_comp _ _).symm.trans (congrArg Cochain.ofHom
    ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv_hom_id_app (of A K)))

omit [HasBinaryBiproducts A] [HasZeroObject A] in
lemma compare_isShiftBy_add (K : Cdg A) (a b : ℤ) :
    IsShiftBy.compare (Cdg.isShiftBy K (a + b))
        (IsShiftBy.comp' (Cdg.isShiftBy K a) (Cdg.isShiftBy (shiftObj K a) b) (a + b) rfl) =
      Cochain.ofHom ((shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app (of A K)) := by
  refine IsShiftBy.compare_unique _ _ _ ?_
  exact (comp_shiftCocycle K a b).symm

/-- The `zero` coherence, componentwise. -/
lemma toH0ShiftIso_zero_hom (K : Cdg A) :
    (toH0ShiftIso K 0).hom =
      (toH0 A).map ((shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.app (of A K)) ≫
        (H0.shiftFunctorZeroIso (Cdg A)).inv.app K := by
  refine Eq.trans ?_ (H0.homMk_comp (C := Cdg A) _ _).symm
  refine congrArg _ (Subtype.ext ?_)
  exact (IsShiftBy.compare_trans (Cdg.isShiftBy K 0) (IsShiftBy.self K)
      (IsPretriangulated.shiftWitness (Cdg A) K 0)).symm.trans
    (congrArg (fun z => dgComp 0 0 0 (by omega) z
      (IsShiftBy.compare (IsShiftBy.self K)
        (IsPretriangulated.shiftWitness (Cdg A) K 0)))
      (compare_isShiftBy_zero K))

/-- The `add` coherence, componentwise. -/
lemma toH0ShiftIso_add_hom (K : Cdg A) (a b : ℤ) :
    (toH0ShiftIso K (a + b)).hom =
      (toH0 A).map ((shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app (of A K)) ≫
        (toH0ShiftIso (shiftObj K a) b).hom ≫
          (H0.shiftFunctor (Cdg A) b).map ((toH0ShiftIso K a).hom) ≫
            (H0.shiftFunctorAddIso (Cdg A) a b).inv.app K := by
  refine Eq.trans ?_ (H0.homMk_comp (C := Cdg A) _ _).symm
  refine congrArg _ (Subtype.ext ?_)
  symm
  show dgComp 0 0 0 (by omega)
      (Cochain.ofHom ((shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app (of A K)))
      (dgComp 0 0 0 (by omega)
        (IsShiftBy.compare (Cdg.isShiftBy (shiftObj K a) b)
          (IsPretriangulated.shiftWitness (Cdg A) (shiftObj K a) b))
        (dgComp 0 0 0 (by omega)
          (IsShiftBy.mapShift
            (IsPretriangulated.shiftWitness (Cdg A) (shiftObj K a) b)
            (IsPretriangulated.shiftWitness (Cdg A) (IsPretriangulated.shiftObj (Cdg A) K a) b)
            (IsShiftBy.compare (Cdg.isShiftBy K a)
              (IsPretriangulated.shiftWitness (Cdg A) K a)))
          (IsShiftBy.compare (H0.shiftCompWitness' (Cdg A) K a b (a + b) rfl)
            (IsPretriangulated.shiftWitness (Cdg A) K (a + b))))) =
    IsShiftBy.compare (Cdg.isShiftBy K (a + b))
      (IsPretriangulated.shiftWitness (Cdg A) K (a + b))
  rw [H0.shiftCompWitness', IsShiftBy.mapShift_compare_comp' _ _ _ _ (a + b) rfl,
    ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
    ← compare_isShiftBy_add K a b]
  exact (congrArg (fun z => dgComp 0 0 0 (by omega) (dgComp 0 0 0 (by omega) z
        (IsShiftBy.compare
          (IsShiftBy.comp' (Cdg.isShiftBy K a)
            (IsPretriangulated.shiftWitness (Cdg A) (shiftObj K a) b) (a + b) rfl)
          (IsShiftBy.comp' (IsPretriangulated.shiftWitness (Cdg A) K a)
            (IsPretriangulated.shiftWitness (Cdg A)
              (IsPretriangulated.shiftObj (Cdg A) K a) b) (a + b) rfl)))
        (IsShiftBy.compare
          (IsShiftBy.comp' (IsPretriangulated.shiftWitness (Cdg A) K a)
            (IsPretriangulated.shiftWitness (Cdg A)
              (IsPretriangulated.shiftObj (Cdg A) K a) b) (a + b) rfl)
          (IsPretriangulated.shiftWitness (Cdg A) K (a + b))))
      (IsShiftBy.compare_comp'_right _ _ _ _ rfl)).trans
    ((congrArg (fun z => dgComp 0 0 0 (by omega) z
        (IsShiftBy.compare
          (IsShiftBy.comp' (IsPretriangulated.shiftWitness (Cdg A) K a)
            (IsPretriangulated.shiftWitness (Cdg A)
              (IsPretriangulated.shiftObj (Cdg A) K a) b) (a + b) rfl)
          (IsPretriangulated.shiftWitness (Cdg A) K (a + b))))
      (IsShiftBy.compare_trans _ _ _)).trans (IsShiftBy.compare_trans _ _ _))

noncomputable instance toH0CommShift : (toH0 A).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun K => toH0ShiftIso K n) (by
    intro K L φ
    refine (H0.homMk_comp (C := Cdg A) _ _).trans
      (Eq.trans ?_ (H0.homMk_comp (C := Cdg A) _ _).symm)
    refine congrArg _ (Subtype.ext ?_)
    show dgComp 0 0 0 (by omega) (Cochain.ofHom (φ⟦n⟧'))
        (IsShiftBy.compare (Cdg.isShiftBy (L : Cdg A) n)
          (IsPretriangulated.shiftWitness (Cdg A) (L : Cdg A) n)) =
      dgComp 0 0 0 (by omega)
        (IsShiftBy.compare (Cdg.isShiftBy (K : Cdg A) n)
          (IsPretriangulated.shiftWitness (Cdg A) (K : Cdg A) n))
        (IsShiftBy.mapShift (IsPretriangulated.shiftWitness (Cdg A) (K : Cdg A) n)
          (IsPretriangulated.shiftWitness (Cdg A) (L : Cdg A) n) (Cochain.ofHom φ))
    exact (congrArg (fun z => dgComp 0 0 0 (by omega) z
        (IsShiftBy.compare (Cdg.isShiftBy (L : Cdg A) n)
          (IsPretriangulated.shiftWitness (Cdg A) (L : Cdg A) n)))
      (mapShift_isShiftBy n φ)).symm.trans (IsShiftBy.mapShift_compare _ _ _ _ _))
  commShiftIso_zero := by
    ext K
    rw [Functor.CommShift.isoZero_hom_app, H0.shiftFunctorZero_eq]
    exact toH0ShiftIso_zero_hom (K : Cdg A)
  commShiftIso_add a b := by
    ext K
    rw [Functor.CommShift.isoAdd_hom_app, H0.shiftFunctorAdd_eq]
    exact toH0ShiftIso_add_hom (K : Cdg A) a b

/-- The seam's commutation isomorphism with the shift, at one object: undo the
comparison of `Cdg.toH0`, then apply Mathlib's for the quotient functor. -/
noncomputable def seamShiftIso (n : ℤ) (X : H0 (Cdg A)) :
    h0Functor.obj ((CategoryTheory.shiftFunctor (H0 (Cdg A)) n).obj X) ≅
      (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).obj
        (h0Functor.obj X) :=
  h0Functor.mapIso (((toH0 A).commShiftIso n).app X).symm ≪≫
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).app
      X

lemma seamShiftIso_hom (n : ℤ) (X : H0 (Cdg A)) :
    (seamShiftIso n X).hom =
      h0Functor.map (((toH0 A).commShiftIso n).inv.app X) ≫
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).hom.app X := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The seam commutes with the shift.** -/
noncomputable def seamCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor (H0 (Cdg A)) n ⋙ h0Functor ≅
      h0Functor ⋙ CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n :=
  NatIso.ofComponents (fun X => seamShiftIso n X) (by
    intro X Y f
    obtain ⟨φ, rfl⟩ := (toH0 A).map_surjective f
    rw [seamShiftIso_hom, seamShiftIso_hom]
    show h0Functor.map ((CategoryTheory.shiftFunctor (H0 (Cdg A)) n).map ((toH0 A).map φ)) ≫ _ = _
    have e1 := ((toH0 A).commShiftIso n).inv.naturality φ
    have e2 : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) n).map φ) ≫
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).hom.app Y =
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).hom.app X ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map φ) :=
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).hom.naturality φ
    dsimp only [Functor.comp_map] at e1
    rw [← Functor.map_comp_assoc, e1, Functor.map_comp, Category.assoc,
      h0Functor_map_toH0_map, e2, ← Category.assoc, Functor.comp_map,
      h0Functor_map_toH0_map])

lemma seamCommShiftIso_hom_app (n : ℤ) (X : H0 (Cdg A)) :
    (seamCommShiftIso n).hom.app X = (seamShiftIso n X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`dg-enhancements-e7`, the shift half.** -/
noncomputable instance h0FunctorCommShift : (h0Functor (A := A)).CommShift ℤ where
  commShiftIso := seamCommShiftIso
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app]
    show (seamShiftIso 0 X).hom = _
    rw [seamShiftIso_hom, (toH0 A).commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.map_comp, Category.assoc,
      h0Functor_map_toH0_map, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
    rfl
  commShiftIso_add a b := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    show (seamShiftIso (a + b) X).hom = _
    rw [seamShiftIso_hom, (toH0 A).commShiftIso_add, Functor.CommShift.isoAdd_inv_app,
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app]
    have nat : h0Functor.map ((CategoryTheory.shiftFunctor (H0 (Cdg A)) b).map
          (((toH0 A).commShiftIso a).inv.app X)) ≫
        (h0Functor.map (((toH0 A).commShiftIso b).inv.app
            ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) a).obj X)) ≫
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso b).hom.app
            ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) a).obj X)) =
      (h0Functor.map (((toH0 A).commShiftIso b).inv.app
          ((CategoryTheory.shiftFunctor (H0 (Cdg A)) a).obj X)) ≫
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso b).hom.app
          ((CategoryTheory.shiftFunctor (H0 (Cdg A)) a).obj X)) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) b).map
          (h0Functor.map (((toH0 A).commShiftIso a).inv.app X)) :=
      (seamCommShiftIso b).hom.naturality (((toH0 A).commShiftIso a).inv.app X)
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, Category.assoc, h0Functor_map_toH0_map,
      ← Functor.map_comp_assoc (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        ((shiftFunctorAdd (CochainComplex A ℤ) a b).inv.app X)
        ((shiftFunctorAdd (CochainComplex A ℤ) a b).hom.app X),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simp only [seamCommShiftIso_hom_app, seamShiftIso_hom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% nat]
    rfl

end CommShift
end Cdg
end CategoryTheory
