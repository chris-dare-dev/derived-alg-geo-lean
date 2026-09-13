/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Colimits
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopower
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Linear

/-!
# Scalar-linear copowers in the standard dg category of module complexes

For a commutative ring `k`, Mathlib's total tensor product of cochain
complexes represents the repository's scalar-linear copower interface in
`Cdg (ModuleCat k)`.  The core comparison curries a degree-`p` cochain

`K ⊗ X ⟶ W`

to a degree-`p` cochain

`K ⟶ DGLinear.homComplex k X W`.

The inverse is assembled with Mathlib's coproduct eliminator for the total
complex and `TensorProduct.lift`.  The universal cochain is the curry of the
identity on `K ⊗ X`; its chain-map law is the usual Koszul cancellation
between the vertical tensor differential `(-1)^i d_X` and the Hom-complex
term `(-1)^(i+1) d_X`.

Mathlib's current monoidal structure on `ModuleCat` requires the scalar ring
and module objects to live in the same universe.  Accordingly this first
concrete instance is intentionally stated for `k : Type v` and
`ModuleCat.{v} k`; no universe-lifting wrapper is introduced here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex DGCategoryStruct
  HomologicalComplex MonoidalCategory

namespace Cdg

variable (k : Type v) [CommRing k]

/-- Mathlib's total tensor product, regarded as an object of the standard dg
category of module complexes. -/
noncomputable abbrev linearTensorObj
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) : Cdg (ModuleCat.{v} k) :=
  HomologicalComplex.tensorObj K (Cdg.of _ X)

/-- The inclusion of the `(i,j)` summand in an arbitrarily equal total
degree. -/
noncomputable abbrev linearTensorιOfEq
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) (i j n : ℤ) (h : i + j = n) :
    ((curriedTensor (ModuleCat.{v} k)).obj (K.X i)).obj ((Cdg.of _ X).X j) ⟶
      (Cdg.of _ (linearTensorObj k K X)).X n :=
  HomologicalComplex.ιMapBifunctor K (Cdg.of _ X)
    (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℤ) i j n h

/-- The inclusion of the `(i,j)` summand in total degree `i + j`. -/
noncomputable abbrev linearTensorι
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) (i j : ℤ) :
    ((curriedTensor (ModuleCat.{v} k)).obj (K.X i)).obj ((Cdg.of _ X).X j) ⟶
      (Cdg.of _ (linearTensorObj k K X)).X (i + j) :=
  linearTensorιOfEq k K X i j (i + j) rfl

/-- Curry a homogeneous cochain out of a total tensor product into a
homogeneous cochain whose values are Hom-complex cochains. -/
noncomputable def tensorCurryCochain
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ) :
    (dgHom (linearTensorObj k K X) W).X p →ₗ[k]
      Cochain K (DGLinear.homComplex k X W) p where
  toFun g := Cochain.mk fun i ip hip => ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun j q hjq => ModuleCat.ofHom
        ((TensorProduct.curry
          ((linearTensorι k K X i j ≫
            g.v (i + j) q (by omega)).hom)) x)
      map_add' := by
        intro x x'
        apply Cochain.ext
        intro j q hjq
        apply ModuleCat.hom_ext
        exact (TensorProduct.curry
          ((linearTensorι k K X i j ≫
            g.v (i + j) q (by omega)).hom)).map_add x x'
      map_smul' := by
        intro a x
        apply Cochain.ext
        intro j q hjq
        apply ModuleCat.hom_ext
        exact (TensorProduct.curry
          ((linearTensorι k K X i j ≫
            g.v (i + j) q (by omega)).hom)).map_smul a x }
  map_add' g g' := by
    apply Cochain.ext
    intro i ip hip
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Cochain.ext
    intro j q hjq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  map_smul' a g := by
    apply Cochain.ext
    intro i ip hip
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Cochain.ext
    intro j q hjq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

private noncomputable def tensorUncurryComponent
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ)
    (c : Cochain K (DGLinear.homComplex k X W) p)
    (n q : ℤ) (hnq : n + p = q) (i j : ℤ)
    (hij : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (i, j) = n) :
    K.X i ⊗ (Cdg.of _ X).X j ⟶ (Cdg.of _ W).X q :=
  ModuleCat.ofHom <| TensorProduct.lift
      { toFun := fun x => (((c.v i (i + p) rfl).hom x).v j q (by
          have hij' : i + j = n := by simpa using hij
          omega)).hom
        map_add' := by
          intro x x'
          apply LinearMap.ext
          intro y
          exact congrArg (fun z : Cochain (Cdg.of _ X) (Cdg.of _ W) (i + p) =>
            (z.v j q (by
              have hij' : i + j = n := by simpa using hij
              omega)).hom y) ((c.v i (i + p) rfl).hom.map_add x x')
        map_smul' := by
          intro a x
          apply LinearMap.ext
          intro y
          exact congrArg (fun z : Cochain (Cdg.of _ X) (Cdg.of _ W) (i + p) =>
            (z.v j q (by
              have hij' : i + j = n := by simpa using hij
              omega)).hom y) ((c.v i (i + p) rfl).hom.map_smul a x) }

private noncomputable def tensorUncurryCochain
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ)
    (c : Cochain K (DGLinear.homComplex k X W) p) :
    (dgHom (linearTensorObj k K X) W).X p :=
  Cochain.mk fun n q hnq => HomologicalComplex.mapBifunctorDesc
    (K₁ := K) (K₂ := Cdg.of _ X) (F := curriedTensor (ModuleCat.{v} k))
    (c := ComplexShape.up ℤ) (tensorUncurryComponent k K X W p c n q hnq)

private theorem tensorCurryCochain_uncurry
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ)
    (c : Cochain K (DGLinear.homComplex k X W) p) :
    tensorCurryCochain k K X W p (tensorUncurryCochain k K X W p c) = c := by
  apply Cochain.ext
  intro i ip hip
  subst ip
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j q hjq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  dsimp only [tensorCurryCochain, Cochain.mk_v, LinearMap.coe_mk,
    AddHom.coe_mk]
  change
    (TensorProduct.curry
      ((linearTensorι k K X i j ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := Cdg.of _ X)
          (F := curriedTensor (ModuleCat.{v} k)) (c := ComplexShape.up ℤ)
          (tensorUncurryComponent k K X W p c (i + j) q (by omega))).hom) x) y =
      ((((c.v i (i + p) rfl).hom x).v j q (by omega)).hom y)
  rw [TensorProduct.curry_apply]
  have hdesc := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := K) (K₂ := Cdg.of _ X) (F := curriedTensor (ModuleCat.{v} k))
    (c := ComplexShape.up ℤ)
    (f := tensorUncurryComponent k K X W p c (i + j) q (by omega)) i j rfl
  have hdesc' := congrArg ModuleCat.Hom.hom hdesc
  have happ := DFunLike.congr_fun hdesc' (x ⊗ₜ[k] y)
  refine happ.trans ?_
  change
    TensorProduct.lift
      { toFun := fun x => (((c.v i (i + p) rfl).hom x).v j q (by omega)).hom
        map_add' := _
        map_smul' := _ } (x ⊗ₜ[k] y) =
      ((((c.v i (i + p) rfl).hom x).v j q hjq).hom y)
  rw [TensorProduct.lift.tmul]
  rfl

private theorem tensorUncurryCochain_curry
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ)
    (g : (dgHom (linearTensorObj k K X) W).X p) :
    tensorUncurryCochain k K X W p (tensorCurryCochain k K X W p g) = g := by
  apply Cochain.ext
  intro n q hnq
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  subst n
  simp only [tensorUncurryCochain, Cochain.mk_v,
    HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change
    (TensorProduct.curry
      ((linearTensorι k K X i j ≫
        g.v (i + j) q hnq).hom) x) y =
      ((linearTensorι k K X i j ≫
        g.v (i + j) q hnq).hom) (x ⊗ₜ[k] y)
  exact TensorProduct.curry_apply _ _ _

/-- The degreewise tensor--Hom adjunction for homogeneous cochains. -/
noncomputable def tensorCochainLinearEquiv
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ) :
    (dgHom (linearTensorObj k K X) W).X p ≃ₗ[k]
      Cochain K (DGLinear.homComplex k X W) p :=
  { tensorCurryCochain k K X W p with
    invFun := tensorUncurryCochain k K X W p
    left_inv := tensorUncurryCochain_curry k K X W p
    right_inv := tensorCurryCochain_uncurry k K X W p }

/-- The universal degree-zero cochain, obtained by currying the identity of
the total tensor product. -/
noncomputable def linearTensorUnivCochain
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    Cochain K (DGLinear.homComplex k X (linearTensorObj k K X)) 0 :=
  tensorCurryCochain k K X (linearTensorObj k K X) 0
    (Cochain.ofHom (𝟙 (Cdg.of _ (linearTensorObj k K X))))

/-- Pointwise evaluation of the universal cochain is the corresponding total
tensor summand inclusion. -/
@[simp]
theorem linearTensorUnivCochain_apply
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) (i j q : ℤ) (hjq : j + i = q)
    (x : K.X i) (y : (Cdg.of _ X).X j) :
    ((((linearTensorUnivCochain k K X).v i i (add_zero i)).hom x).v
      j q hjq).hom y =
      (linearTensorιOfEq k K X i j q (by omega)).hom (x ⊗ₜ[k] y) := by
  obtain rfl : q = i + j := by omega
  change
    (TensorProduct.curry
      ((linearTensorι k K X i j ≫
        (Cochain.ofHom (𝟙 (Cdg.of _ (linearTensorObj k K X)))).v
          (i + j) (i + j) (add_zero (i + j))).hom) x) y = _
  rw [Cochain.ofHom_v, TensorProduct.curry_apply,
    HomologicalComplex.id_f, Category.comp_id]
  rfl

/-- The total tensor differential on a pure tensor in one summand is the sum
of the horizontal differential and the signed vertical differential. -/
theorem linearTensorι_d_apply
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) (i j n n' : ℤ)
    (hij : i + j = n) (hnn' : n + 1 = n')
    (x : K.X i) (y : (Cdg.of _ X).X j) :
    ((Cdg.of _ (linearTensorObj k K X)).d n n').hom
        ((linearTensorιOfEq k K X i j n hij).hom (x ⊗ₜ[k] y)) =
      (linearTensorιOfEq k K X (i + 1) j n' (by omega)).hom
          (((K.d i (i + 1)).hom x) ⊗ₜ[k] y) +
        i.negOnePow •
          (linearTensorιOfEq k K X i (j + 1) n' (by omega)).hom
            (x ⊗ₜ[k] ((Cdg.of _ X).d j (j + 1)).hom y) := by
  have hd :
      linearTensorιOfEq k K X i j n hij ≫
          (Cdg.of _ (linearTensorObj k K X)).d n n' =
        ((curriedTensor (ModuleCat.{v} k)).map (K.d i (i + 1))).app
              ((Cdg.of _ X).X j) ≫
            linearTensorιOfEq k K X (i + 1) j n' (by omega) +
          i.negOnePow •
            ((curriedTensor (ModuleCat.{v} k)).obj (K.X i)).map
                ((Cdg.of _ X).d j (j + 1)) ≫
              linearTensorιOfEq k K X i (j + 1) n' (by omega) := by
    change
      linearTensorιOfEq k K X i j n hij ≫
          (HomologicalComplex.mapBifunctor K (Cdg.of _ X)
            (curriedTensor (ModuleCat.{v} k)) (ComplexShape.up ℤ)).d n n' = _
    dsimp only [linearTensorιOfEq]
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq
        (K₁ := K) (K₂ := Cdg.of _ X)
        (F := curriedTensor (ModuleCat.{v} k)) (c := ComplexShape.up ℤ)
        (i₁ := i) (i₁' := i + 1) rfl j n'
          (by change (i + 1) + j = n'; omega),
      HomologicalComplex.mapBifunctor.d₂_eq
        (K₁ := K) (K₂ := Cdg.of _ X)
        (F := curriedTensor (ModuleCat.{v} k)) (c := ComplexShape.up ℤ)
        i (i₂ := j) (i₂' := j + 1) rfl n'
          (by change i + (j + 1) = n'; omega)]
    change (1 : ℤˣ) • _ + (ComplexShape.up ℤ).ε i • _ = _
    simp only [one_smul, ComplexShape.ε_up_ℤ]
  have hd' := congrArg ModuleCat.Hom.hom hd
  have happ := DFunLike.congr_fun hd' (x ⊗ₜ[k] y)
  change
    ((Cdg.of _ (linearTensorObj k K X)).d n n').hom
        ((linearTensorιOfEq k K X i j n hij).hom (x ⊗ₜ[k] y)) =
      (linearTensorιOfEq k K X (i + 1) j n' (by omega)).hom
          (((K.d i (i + 1)).hom x) ⊗ₜ[k] y) +
        i.negOnePow •
          (linearTensorιOfEq k K X i (j + 1) n' (by omega)).hom
            (x ⊗ₜ[k] ((Cdg.of _ X).d j (j + 1)).hom y) at happ
  exact happ

/-- The universal cochain is closed.  Its two vertical Koszul terms have
coefficients `(-1)^i` and `(-1)^(i+1)` and cancel. -/
theorem linearTensorUnivCochain_mem
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    δ 0 1 (linearTensorUnivCochain k K X) = 0 := by
  apply Cochain.ext
  intro i ip hip
  subst ip
  rw [HomComplex.δ_zero_cochain_v]
  apply sub_eq_zero.mpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    δ i (i + 1)
      (((linearTensorUnivCochain k K X).v i i (add_zero i)).hom x) =
      ((linearTensorUnivCochain k K X).v (i + 1) (i + 1)
        (add_zero (i + 1))).hom ((K.d i (i + 1)).hom x)
  apply Cochain.ext
  intro j q hjq
  obtain rfl : q = j + (i + 1) := by omega
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [HomComplex.δ_v i (i + 1) rfl _ j (j + (i + 1)) hjq (j + i) (j + 1)
    (by omega) rfl]
  simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [linearTensorUnivCochain_apply, linearTensorUnivCochain_apply,
    linearTensorUnivCochain_apply]
  rw [linearTensorι_d_apply k K X i j (j + i) (j + (i + 1))
    (by omega) (by omega) x y, Int.negOnePow_succ, Units.neg_smul]
  abel

/-- The universal cochain bundled as a degree-zero cocycle. -/
noncomputable def linearTensorUnivCocycle
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    Cocycle K (DGLinear.homComplex k X (linearTensorObj k K X)) 0 :=
  Cocycle.mk (linearTensorUnivCochain k K X) 1 (zero_add 1)
    (linearTensorUnivCochain_mem k K X)

/-- The universal chain map from the coefficient complex to the Hom-complex
out of `X`. -/
noncomputable def linearTensorUniv
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    K ⟶ DGLinear.homComplex k X (linearTensorObj k K X) :=
  Cocycle.homOf (linearTensorUnivCocycle k K X)

/-- Forgetting the universal chain map back to a cochain recovers the
explicitly curried identity. -/
lemma cochain_ofHom_linearTensorUniv
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    Cochain.ofHom (linearTensorUniv k K X) =
      linearTensorUnivCochain k K X := by
  exact Cocycle.cochain_ofHom_homOf_eq_coe
    (linearTensorUnivCocycle k K X)

/-- Composition with the universal chain map is exactly tensor currying. -/
theorem linearCopowerCochain_linearTensorUniv
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X W : Cdg (ModuleCat.{v} k)) (p : ℤ) :
    linearCopowerCochain k (linearTensorUniv k K X) (W := W) p =
      tensorCurryCochain k K X W p := by
  apply LinearMap.ext
  intro g
  apply Cochain.ext
  intro i ip hip
  subst ip
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j q hjq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [linearCopowerCochain_apply, Cdg.dgComp_eq,
    Cochain.comp_v _ _ (by omega) j (i + j) q (by omega) (by omega)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, linearTensorUniv,
    Cocycle.homOf_f, linearTensorUnivCocycle, Cocycle.mk_coe]
  rw [linearTensorUnivCochain_apply]
  change
    (g.v (i + j) q (by omega)).hom
        ((linearTensorι k K X i j).hom (x ⊗ₜ[k] y)) =
      (TensorProduct.curry
        ((linearTensorι k K X i j ≫ g.v (i + j) q (by omega)).hom) x) y
  rw [TensorProduct.curry_apply]
  rfl

/-- Mathlib's total tensor product represents the scalar-linear copower in
the standard dg category of module complexes. -/
noncomputable def isLinearCopowerOfLinearTensor
    (K : CochainComplex (ModuleCat.{v} k) ℤ)
    (X : Cdg (ModuleCat.{v} k)) :
    IsLinearCopowerOf k K X (linearTensorObj k K X) where
  univ := linearTensorUniv k K X
  bijective W p := by
    rw [linearCopowerCochain_linearTensorUniv]
    exact (tensorCochainLinearEquiv k K X W p).bijective

/-- The standard dg category of same-universe `k`-module complexes has all
scalar-linear copowers. -/
instance hasLinearCopowers : HasLinearCopowers k (Cdg (ModuleCat.{v} k)) where
  has_linearCopower K X :=
    HasLinearCopower.of_isLinearCopower
      (isLinearCopowerOfLinearTensor k K X)

end Cdg

end CategoryTheory
