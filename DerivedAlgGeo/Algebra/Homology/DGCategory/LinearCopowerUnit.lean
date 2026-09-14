/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopower
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The scalar unit linear copower

In a `k`-linear dg category, the degree-zero single complex on `k` has `X`
itself as its linear copower with `X`.  The universal chain map sends `1` to
the dg identity of `X`.

This is the unit computation for the existing `IsLinearCopowerOf` interface.
It does not choose a global `HasLinearCopowers` instance or assert anything
about finite-dimensional coefficient modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {k : Type v} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- The closed cochain which sends the scalar unit to the dg identity of
`X`. -/
noncomputable def linearCopowerUnitCocycle (X : C) :
    CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k)) (DGLinear.homComplex k X X) 0 :=
    CochainComplex.HomComplex.Cocycle.fromSingleMk (p := 0) (q := 0) (n := 0)
      (ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf k k ((dgHom X X).X 0)).symm (dgId X)))
      rfl 1 rfl (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change ((dgHom X X).d 0 1).hom (a • dgId X) = 0
        rw [DGLinear.d_smul, dgId_cocycle, smul_zero])

/-- The universal chain map for the scalar-unit linear copower of `X`. -/
noncomputable def linearCopowerUnitUniv (X : C) :
    (CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k) ⟶
      DGLinear.homComplex k X X :=
  (CochainComplex.HomComplex.Cocycle.equivHom _ _).symm
    (linearCopowerUnitCocycle X)

/-- The universal chain map, in the canonical cochain coordinate on the
degree-zero single, sends `a` to `a • dgId X`. -/
lemma cochain_ofHom_linearCopowerUnitUniv (X : C) :
    CochainComplex.HomComplex.Cochain.ofHom
        (linearCopowerUnitUniv (k := k) X) =
      CochainComplex.HomComplex.Cochain.fromSingleMk
        (ModuleCat.ofHom
          ((LinearMap.ringLmapEquivSelf k k ((dgHom X X).X 0)).symm
            (dgId X))) (by omega) := by
  simp [linearCopowerUnitUniv, linearCopowerUnitCocycle,
    CochainComplex.HomComplex.Cocycle.equivHom]

/-- The degree-zero single complex on the scalar ring has `X` itself as its
linear copower with `X`. -/
noncomputable def isLinearCopowerOfUnit (X : C) :
    IsLinearCopowerOf k
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k)) X X where
  univ := linearCopowerUnitUniv X
  bijective W p := by
    let e : (dgHom X W).X p ≃+
        CochainComplex.HomComplex.Cochain
          ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
            (ModuleCat.of k k))
          (DGLinear.homComplex k X W) p :=
      (LinearMap.ringLmapEquivSelf k ℕ ((dgHom X W).X p)).toAddEquiv.symm |>.trans
        (ModuleCat.homAddEquiv
          (M := ModuleCat.of k k)
          (N := ModuleCat.of k ((dgHom X W).X p))).symm |>.trans
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv
            (X := ModuleCat.of k k)
            (K := DGLinear.homComplex k X W)
            (p := 0) (q := p) (n := p) (by omega)).symm
    have he :
        (linearCopowerCochain k (linearCopowerUnitUniv X) p :
          (dgHom X W).X p → _) = e := by
      funext g
      apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv
        (X := ModuleCat.of k k)
        (K := DGLinear.homComplex k X W)
        (p := 0) (q := p) (n := p) (by omega)).injective
      change (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by omega))
          ((CochainComplex.HomComplex.Cochain.ofHom
            (linearCopowerUnitUniv (k := k) X)).comp
              (DGLinear.postcompCochain k X p g) (by omega)) = _
      rw [cochain_ofHom_linearCopowerUnitUniv]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      simp [e, CochainComplex.HomComplex.Cochain.fromSingleEquiv,
        DGLinear.postcompCochain, DGLinear.comp_smul_left, dgId_comp,
        ← Category.assoc]
      change a • g = (LinearMap.smulRight (1 : k →ₗ[k] k) g) a
      rfl
    rw [he]
    exact e.bijective

/-- The selected scalar-unit linear copower is isomorphic to the original
object in `H⁰ C`. -/
noncomputable def linearCopowerUnitIso (X : C)
    [HasLinearCopower k
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k)) X] :
    (show H0 C from linearCopowerObj (C := C)
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k)) X) ≅
      (show H0 C from X) :=
  (Z0.toH0 C).mapIso
    ((linearCopowerIsLinearCopower (C := C)
      ((CochainComplex.singleFunctor (ModuleCat.{v} k) 0).obj
        (ModuleCat.of k k)) X).compareIso
      (isLinearCopowerOfUnit X))

end CategoryTheory
