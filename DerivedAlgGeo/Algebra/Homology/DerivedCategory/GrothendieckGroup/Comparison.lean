/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.GrothendieckGroup
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.FullSubcategory
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HeartComparison

/-!
# Grothendieck comparison for a bounded derived category

For an abelian category `A`, the standard-heart map

`K₀Ab(A) →+ K₀(Dᵇ(A))`

and the cohomological Euler map constructed in
`DerivedCategory.GrothendieckGroup` are inverse.  The nontrivial direction is
proved by bounded cohomological dévissage.  Shifted single objects give the
base case, and canonical truncation triangles are lifted into the bounded
full subcategory for the induction step.

The final section packages the practical consequence for geometry: any
additive class map defined on coherent sheaves extends canonically to the
bounded derived category by precomposition with the Euler map.  No geometric
class map is manufactured here; callers must still supply the sheaf-level
map.
-/

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

attribute [local instance] TStructure.hasHeartFullSubcategory
  TStructure.heartFullSubcategoryAbelian

/-- The standard-heart comparison, expressed directly on the original
abelian category. -/
noncomputable def boundedHeartToAmbient : K₀Ab A →+ K₀ (Bounded A) :=
  (K₀Ab.toAmbient ((TStructure.t (C := A)).onBounded)).comp
    (K₀Ab.congrHom (boundedHeartEquivalence A))

@[simp]
theorem boundedHeartToAmbient_of (X : A) :
    boundedHeartToAmbient A (K₀Ab.of X) =
      K₀.of (Bounded A) ((boundedSingleFunctor A).obj X) := by
  simp [boundedHeartToAmbient]
  rfl

/-- The Euler class of a degree-zero single object is its abelian
Grothendieck class. -/
theorem boundedEulerClass_boundedSingleFunctor (X : A) :
    boundedEulerClass A ((boundedSingleFunctor A).obj X) = K₀Ab.of X := by
  rw [boundedEulerClass, K₀Ab.eulerClass, finsum_eq_single _ 0]
  · simp only [Int.negOnePow_zero, Units.val_one, one_smul]
    exact K₀Ab.of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X)
  · intro n hn
    have hn' : n < 0 ∨ 0 < n := lt_or_gt_of_ne hn
    have hzero : IsZero ((boundedHomologyFunctor A n).obj
        ((boundedSingleFunctor A).obj X)) := by
      change IsZero ((homologyFunctor A n).obj ((singleFunctor A 0).obj X))
      rcases hn' with hnlt | hnlt
      · exact isZero_of_isGE _ 0 n hnlt
      · exact isZero_of_isLE _ 0 n hnlt
    rw [K₀Ab.of_isZero hzero, smul_zero]

/-- The Euler class of a single object in degree `n` is its abelian class
with the usual parity sign.  The boundedness proof is explicit so the theorem
can be used for any chosen lift into `Dᵇ(A)`. -/
theorem boundedEulerClass_singleFunctor (n : ℤ) (X : A)
    (hX : (TStructure.t (C := A)).bounded ((singleFunctor A n).obj X)) :
    boundedEulerClass A
      (⟨(singleFunctor A n).obj X, hX⟩ : Bounded A) =
        (n.negOnePow : ℤ) • K₀Ab.of X := by
  rw [boundedEulerClass, K₀Ab.eulerClass, finsum_eq_single _ n]
  · exact congrArg ((n.negOnePow : ℤ) • ·)
      (K₀Ab.of_iso ((singleFunctorCompHomologyFunctorIso A n).app X))
  · intro m hm
    have hm' : m < n ∨ n < m := lt_or_gt_of_ne hm
    have hzero : IsZero ((boundedHomologyFunctor A m).obj
        (⟨(singleFunctor A n).obj X, hX⟩ : Bounded A)) := by
      change IsZero ((homologyFunctor A m).obj ((singleFunctor A n).obj X))
      rcases hm' with hmlt | hmlt
      · exact isZero_of_isGE _ n m hmlt
      · exact isZero_of_isLE _ n m hmlt
    rw [K₀Ab.of_isZero hzero, smul_zero]

/-- Taking the Euler class is a left inverse to the standard-heart map. -/
theorem boundedEulerClassHom_comp_boundedHeartToAmbient :
    (boundedEulerClassHom A).comp (boundedHeartToAmbient A) =
      AddMonoidHom.id (K₀Ab A) := by
  ext X
  simp [boundedEulerClass_boundedSingleFunctor]

/-- On the full standard heart, the Euler map is the inverse of the
equivalence identifying that heart with `A`. -/
theorem boundedEulerClassHom_comp_toAmbient :
    (boundedEulerClassHom A).comp
        (K₀Ab.toAmbient ((TStructure.t (C := A)).onBounded)) =
      (K₀Ab.congr (boundedHeartEquivalence A)).symm.toAddMonoidHom := by
  apply DFunLike.ext _ _
  intro x
  have h := DFunLike.congr_fun
    (boundedEulerClassHom_comp_boundedHeartToAmbient A)
    ((K₀Ab.congr (boundedHeartEquivalence A)).symm x)
  simpa [boundedHeartToAmbient] using h

private def boundedK0DevissageProperty :
    ObjectProperty (DerivedCategory A) := fun E =>
  ∃ hE : (TStructure.t (C := A)).bounded E,
    boundedHeartToAmbient A
        (boundedEulerClass A (⟨E, hE⟩ : Bounded A)) =
      K₀.of (Bounded A) (⟨E, hE⟩ : Bounded A)

private theorem boundedK0DevissageProperty_iso {E E' : DerivedCategory A}
    (e : E ≅ E') (h : boundedK0DevissageProperty A E) :
    boundedK0DevissageProperty A E' := by
  obtain ⟨hE, hEq⟩ := h
  let hE' : (TStructure.t (C := A)).bounded E' :=
    (TStructure.t (C := A)).bounded.prop_of_iso e hE
  let X : Bounded A := ⟨E, hE⟩
  let X' : Bounded A := ⟨E', hE'⟩
  let e' : X ≅ X' := Bounded.ι.preimageIso e
  refine ⟨hE', ?_⟩
  have heuler : boundedEulerClass A X = boundedEulerClass A X' := by
    rw [← boundedEulerClassHom_of A X,
      ← boundedEulerClassHom_of A X', K₀.of_iso (Bounded A) e']
  calc
    boundedHeartToAmbient A (boundedEulerClass A X') =
        boundedHeartToAmbient A (boundedEulerClass A X) :=
      congrArg (boundedHeartToAmbient A) heuler.symm
    _ = K₀.of (Bounded A) X := hEq
    _ = K₀.of (Bounded A) X' := K₀.of_iso (Bounded A) e'

private theorem boundedK0DevissageProperty_single (n : ℤ) (X : A) :
    boundedK0DevissageProperty A ((singleFunctor A n).obj X) := by
  let hX : (TStructure.t (C := A)).bounded ((singleFunctor A n).obj X) :=
    ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩
  refine ⟨hX, ?_⟩
  let X₀ : Bounded A := (boundedSingleFunctor A).obj X
  let Xn : Bounded A := ⟨(singleFunctor A n).obj X, hX⟩
  let e : ((singleFunctor A 0).obj X)⟦-n⟧ ≅
      (singleFunctor A n).obj X :=
    ((singleFunctors A).shiftIso (-n) n 0 (by omega)).app X
  let e' : X₀⟦-n⟧ ≅ Xn := Bounded.ι.preimageIso
    ((Bounded.ι.commShiftIso (-n)).app X₀ ≪≫ e)
  rw [boundedEulerClass_singleFunctor A n X hX, map_zsmul,
    boundedHeartToAmbient_of]
  calc
    (n.negOnePow : ℤ) • K₀.of (Bounded A) X₀ =
        K₀.of (Bounded A) (X₀⟦-n⟧) := by
      rw [K₀.of_shift_int, Int.natAbs_neg]
      have hcoeff : (n.negOnePow : ℤ) = (-1 : ℤ) ^ n.natAbs :=
        Int.coe_negOnePow ℤ n
      rw [hcoeff]
    _ = K₀.of (Bounded A) Xn := K₀.of_iso (Bounded A) e'

private theorem boundedK0DevissageProperty_triangle
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : boundedK0DevissageProperty A T.obj₁)
    (h₃ : boundedK0DevissageProperty A T.obj₃) :
    boundedK0DevissageProperty A T.obj₂ := by
  obtain ⟨hobj₁, heq₁⟩ := h₁
  obtain ⟨hobj₃, heq₃⟩ := h₃
  let hobj₂ : (TStructure.t (C := A)).bounded T.obj₂ :=
    (TStructure.t (C := A)).bounded.ext_of_isTriangulatedClosed₂ T hT hobj₁ hobj₃
  let hObjects : (TStructure.t (C := A)).bounded.OnTriangle T :=
    ⟨hobj₁, hobj₂, hobj₃⟩
  let T' : Triangle (Bounded A) :=
    (TStructure.t (C := A)).bounded.liftTriangle T hObjects
  have hT' : T' ∈ distTriang (Bounded A) :=
    (TStructure.t (C := A)).bounded.liftTriangle_distinguished T hObjects hT
  refine ⟨hobj₂, ?_⟩
  change boundedHeartToAmbient A (boundedEulerClass A T'.obj₂) =
    K₀.of (Bounded A) T'.obj₂
  calc
    boundedHeartToAmbient A (boundedEulerClass A T'.obj₂) =
        boundedHeartToAmbient A
          (boundedEulerClass A T'.obj₁ + boundedEulerClass A T'.obj₃) := by
      rw [boundedEulerClass_additive A T' hT']
    _ = boundedHeartToAmbient A (boundedEulerClass A T'.obj₁) +
        boundedHeartToAmbient A (boundedEulerClass A T'.obj₃) := map_add _ _ _
    _ = K₀.of (Bounded A) T'.obj₁ + K₀.of (Bounded A) T'.obj₃ := by
      change boundedHeartToAmbient A
          (boundedEulerClass A (⟨T.obj₁, hobj₁⟩ : Bounded A)) +
        boundedHeartToAmbient A
          (boundedEulerClass A (⟨T.obj₃, hobj₃⟩ : Bounded A)) =
        K₀.of (Bounded A) (⟨T.obj₁, hobj₁⟩ : Bounded A) +
          K₀.of (Bounded A) (⟨T.obj₃, hobj₃⟩ : Bounded A)
      rw [heq₁, heq₃]
    _ = K₀.of (Bounded A) T'.obj₂ :=
      (K₀.of_triangle (Bounded A) T' hT').symm

/-- Every bounded-derived class is the image of the alternating sum of its
cohomology classes.  This is the dévissage half of the comparison theorem. -/
theorem boundedHeartToAmbient_boundedEulerClass (X : Bounded A) :
    boundedHeartToAmbient A (boundedEulerClass A X) =
      K₀.of (Bounded A) X := by
  have h := bounded_induction (⊤ : ObjectProperty A)
    (boundedK0DevissageProperty A)
    (boundedK0DevissageProperty_iso A)
    (fun n Y _ => boundedK0DevissageProperty_single A n Y)
    (boundedK0DevissageProperty_triangle A)
    X.property (fun _ => trivial)
  obtain ⟨hX, hEq⟩ := h
  simpa using hEq

/-- The standard-heart map is also a left inverse to the Euler map. -/
theorem boundedHeartToAmbient_comp_boundedEulerClassHom :
    (boundedHeartToAmbient A).comp (boundedEulerClassHom A) =
      AddMonoidHom.id (K₀ (Bounded A)) := by
  ext X
  simp [boundedHeartToAmbient_boundedEulerClass]

/-- The canonical comparison `K₀Ab(A) ≃+ K₀(Dᵇ(A))`. -/
noncomputable def boundedGrothendieckGroupEquiv :
    K₀Ab A ≃+ K₀ (Bounded A) where
  toFun := boundedHeartToAmbient A
  invFun := boundedEulerClassHom A
  left_inv x := by
    have h := DFunLike.congr_fun
      (boundedEulerClassHom_comp_boundedHeartToAmbient A) x
    simpa using h
  right_inv x := by
    have h := DFunLike.congr_fun
      (boundedHeartToAmbient_comp_boundedEulerClassHom A) x
    simpa using h
  map_add' := map_add _

section ClassMap

variable {Λ : Type*} [AddCommGroup Λ]

/-- Transport an additive class map on an abelian category to its bounded
derived category by taking the cohomological Euler class. -/
noncomputable def boundedDerivedClassMap (v : K₀Ab A →+ Λ) :
    K₀ (Bounded A) →+ Λ :=
  v.comp (boundedEulerClassHom A)

/-- The transported class map restricts to the original map along the direct
standard-heart comparison. -/
theorem boundedDerivedClassMap_comp_boundedHeartToAmbient
    (v : K₀Ab A →+ Λ) :
    (boundedDerivedClassMap A v).comp (boundedHeartToAmbient A) = v := by
  rw [boundedDerivedClassMap, AddMonoidHom.comp_assoc,
    boundedEulerClassHom_comp_boundedHeartToAmbient, AddMonoidHom.comp_id]

/-- On the full standard heart, the transported class map is the original
map conjugated by the canonical heart equivalence. -/
theorem boundedDerivedClassMap_comp_toAmbient (v : K₀Ab A →+ Λ) :
    (boundedDerivedClassMap A v).comp
        (K₀Ab.toAmbient ((TStructure.t (C := A)).onBounded)) =
      v.comp (K₀Ab.congr (boundedHeartEquivalence A)).symm.toAddMonoidHom := by
  rw [boundedDerivedClassMap, AddMonoidHom.comp_assoc,
    boundedEulerClassHom_comp_toAmbient]

end ClassMap

end DerivedCategory
