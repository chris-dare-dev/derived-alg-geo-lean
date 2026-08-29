/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.CommShift
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Instances.HomotopyCategory.Enhancement

/-!
# The transported triangulated structure is Mathlib's

`dg-enhancements-e7`. `H⁰(C^dg A)` carries the pretriangulated structure
`H0Triangle.lean` builds out of dg cones, and `K(A) = HomotopyCategory A` carries
Mathlib's, built out of mapping cones. `Cdg.seam` identifies the two categories
and `Model/CommShift.lean` identifies their shifts. This file proves that the two
*structures* agree.

## What "agree" means, and why it is a set equality

`Pretriangulated.distinguishedTriangles` is a **field** of the class, so the two
structures agree exactly when the two sets of triangles correspond. No notion of
"isomorphism of triangulated structures" exists at the pin, and none is invented
here: the theorem is

    Cdg.seam_distinguishedTriangles_eq :
      {T | Cdg.seam.inverse.mapTriangle.obj T ∈ H0.distinguishedTriangles (Cdg A)}
        = HomotopyCategory.Pretriangulated.distinguishedTriangles A

an equality of two terms of `Set (Triangle (HomotopyCategory A (ComplexShape.up ℤ)))`.
`Cdg.distinguishedTriangles_eq` is the same statement read on `H⁰`, and
`Cdg.mem_distTriang_iff` is the pointwise form both come from.

Transporting a triangle needs the shift comparison, which is why
`Functor.mapTriangle` -- and hence this file -- rests on
`Cdg.h0FunctorCommShift`. Nothing here assumes the comparison; it is the
`CommShift` instance built in `HomotopyCategory/CommShift.lean`.

## The sign

The dg connecting morphism `IsConeOf.toShift` is `fst` followed by the shift with
no sign; Mathlib's `CochainComplex.mappingCone.triangle` uses `-mappingCone.fst`.
`Cdg.triangle_mor₃_eq` records that discrepancy, and `H0.coneTriangle` carries the
sign that removes it. Without it the two structures would genuinely differ:
diagonal isomorphisms of triangles realise exactly the sign patterns whose product
over the three vertices is `+1`, and negating the third map alone is not one of
them, so the disagreement could not be absorbed by an isomorphism.

## The octahedral half

The pin supplies `IsTriangulated (HomotopyCategory A (ComplexShape.up ℤ))`
(`Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`), so the octahedral
axiom transfers back along the fully faithful triangulated seam:
`IsTriangulated (H0 (Cdg A))` is an instance below. It is stated only for this
model. For a general pretriangulated dg category `C` this file proves nothing
about `IsTriangulated (H0 C)`, and nothing at the pin does either -- the
octahedron there would have to be built from the dg cone directly, which is not
`dg-enhancements-e7`'s scope.

## `backward.isDefEq.respectTransparency`

`H0 C` is a type synonym for `C`, so goals about `H0 (Cdg A)` are routinely
ill-typed at `instances` transparency and rewriting stalls. Mathlib's own
`set_option backward.isDefEq.respectTransparency false` is the sanctioned way
through, and it is used here for exactly the declarations that need it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe v u
namespace CategoryTheory
open CochainComplex CochainComplex.HomComplex Limits DGCategoryStruct DGCategory
  Pretriangulated
namespace Cdg
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]

section Cone
variable {K L : Cdg A} (f : (dgHom K L).X 0) (hf : f ∈ cocycles K L)

/-- The dg cone's degree-one projection is Mathlib's `mappingCone.fst`. -/
lemma isConeOf_fst : (isConeOf f hf).fst =
    ((mappingCone.fst (coneHom f hf)) :
      Cochain (mappingCone (coneHom f hf)) (of A K) 1) :=
  ((isConeOf f hf).splitId_unique (by
    show Cochain.comp (mappingCone.fst (coneHom f hf)).1
        (mappingCone.inl (coneHom f hf)) (by omega) +
      Cochain.comp (mappingCone.snd (coneHom f hf))
        (Cochain.ofHom (mappingCone.inr (coneHom f hf))) (by omega) =
      Cochain.ofHom (𝟙 (mappingCone (coneHom f hf)))
    exact mappingCone.id _)).1.symm

/-- The dg connecting morphism, at the *model* shift, is Mathlib's `fst`
right-shifted. -/
lemma toShift_isShiftBy : (isConeOf f hf).toShift (isShiftBy K 1) =
    (((mappingCone.fst (coneHom f hf)) :
      Cochain (mappingCone (coneHom f hf)) (of A K) 1)).rightShift 1 0 (zero_add 1) := by
  rw [IsConeOf.toShift, ← isConeOf_fst f hf]
  exact comp_shiftCocycle_id _ 1 0 (zero_add 1)

/-- **The sign.** Mathlib's standard triangle uses `-mappingCone.fst`; the dg
`toShift` is `+fst`.  This is why `H0.coneTriangle` carries a sign. -/
lemma triangle_mor₃_eq :
    (mappingCone.triangle (coneHom f hf)).mor₃ =
      Cocycle.homOf (-(toCocycle _ _
        ⟨(isConeOf f hf).toShift (isShiftBy K 1),
          (isConeOf f hf).toShift_mem_cocycles _⟩)) := by
  show Cocycle.homOf ((-mappingCone.fst (coneHom f hf)).rightShift 1 0 (zero_add 1)) = _
  refine congrArg Cocycle.homOf (Cocycle.ext ?_)
  ext p q hpq
  simp [toShift_isShiftBy f hf]
  rfl

end Cone

section Agreement
variable [HasZeroObject A]

lemma h0Functor_commShiftIso_hom_app (n : ℤ) (X : H0 (Cdg A)) :
    ((h0Functor (A := A)).commShiftIso n).hom.app X = (seamShiftIso n X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of a *model* cone triangle is Mathlib's standard triangle. -/
noncomputable def mapTriangleConeTriangleIso {K L : Cdg A} (f : cocycles K L) :
    h0Functor.mapTriangle.obj (H0.coneTriangle f (isConeOf f.1 f.2)) ≅
      mappingCone.triangleh (coneHom f.1 f.2) := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine Eq.trans ?_ (Category.id_comp _).symm
    refine (Category.comp_id _).trans ?_
    exact congrArg (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (Cocycle.homOf_ofHom_eq_self _)
  · have hcomp : (H0.coneTriangle f (isConeOf f.1 f.2)).mor₃ ≫
          (((toH0 A).commShiftIso (1 : ℤ)).inv.app K) =
        -H0.homMk ⟨(isConeOf f.1 f.2).toShift (isShiftBy K 1),
          (isConeOf f.1 f.2).toShift_mem_cocycles _⟩ := by
      rw [H0.coneTriangle_mor₃, Preadditive.neg_comp]
      refine congrArg Neg.neg ?_
      exact (H0.homMk_comp _ _).trans
        (congrArg _ (Subtype.ext (IsConeOf.toShift_comp_compare _ _ _)))
    have key : (h0Functor.mapTriangle.obj (H0.coneTriangle f (isConeOf f.1 f.2))).mor₃ =
        (mappingCone.triangleh (coneHom f.1 f.2)).mor₃ := by
      show h0Functor.map ((H0.coneTriangle f (isConeOf f.1 f.2)).mor₃) ≫
        (seamShiftIso 1 K).hom = _
      rw [seamShiftIso_hom, ← Functor.map_comp_assoc, hcomp, ← H0.homMk_neg]
      refine congrArg (fun z => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map z ≫
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ?_
      rw [triangle_mor₃_eq]
      exact congrArg Cocycle.homOf (map_neg (toCocycle _ _) _)
    exact ((congrArg _ (Functor.map_id _ _)).trans (Category.comp_id _)).trans
      (key.trans (Category.id_comp _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- **The seam is a triangulated functor.** -/
instance h0FunctorIsTriangulated : (h0Functor (A := A)).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨X, Y, g, Z, hc, ⟨e⟩⟩ := hT
    have hmodel : H0.coneTriangle g hc ≅ H0.coneTriangle g (isConeOf g.1 g.2) :=
      Pretriangulated.isoTriangleOfIso₁₂ _ _ (H0.coneTriangle_mem g hc)
        (H0.coneTriangle_mem g (isConeOf g.1 g.2)) (Iso.refl _) (Iso.refl _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact Pretriangulated.isomorphic_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished (coneHom g.1 g.2)) _
      (h0Functor.mapTriangle.mapIso (e ≪≫ hmodel) ≪≫ mapTriangleConeTriangleIso g)

/-- **The agreement theorem, as an equivalence.** -/
theorem mem_distTriang_iff (T : Pretriangulated.Triangle (H0 (Cdg A))) :
    h0Functor.mapTriangle.obj T ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) ↔
      T ∈ distTriang (H0 (Cdg A)) :=
  h0Functor.map_distinguished_iff T

/-- **The agreement theorem, as an equality of sets of triangles.** -/
theorem distinguishedTriangles_eq :
    H0.distinguishedTriangles (Cdg A) =
      h0Functor.mapTriangle.obj ⁻¹'
        HomotopyCategory.Pretriangulated.distinguishedTriangles A :=
  Set.ext fun T => (mem_distTriang_iff T).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The octahedral axiom for `H⁰(C^dg A)`.** -/
instance : IsTriangulated (H0 (Cdg A)) :=
  IsTriangulated.of_fully_faithful_triangulated_functor (h0Functor (A := A))

/-! ## The same statements, read on the seam -/

noncomputable instance seamFunctorCommShift : (seam (A := A)).functor.CommShift ℤ :=
  inferInstanceAs ((h0Functor (A := A)).CommShift ℤ)

noncomputable instance seamInverseCommShift : (seam (A := A)).inverse.CommShift ℤ :=
  (seam (A := A)).commShiftInverse ℤ

instance seamCommShift : (seam (A := A)).CommShift ℤ :=
  (seam (A := A)).commShift_of_functor ℤ

instance seamFunctorIsTriangulated : (seam (A := A)).functor.IsTriangulated :=
  inferInstanceAs ((h0Functor (A := A)).IsTriangulated)

instance seamIsTriangulated : (seam (A := A)).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

/-- **The agreement theorem, transported onto the homotopy category.** -/
theorem seam_distinguishedTriangles_eq :
    {T : Pretriangulated.Triangle (HomotopyCategory A (ComplexShape.up ℤ)) |
        (seam (A := A)).inverse.mapTriangle.obj T ∈ H0.distinguishedTriangles (Cdg A)} =
      HomotopyCategory.Pretriangulated.distinguishedTriangles A :=
  Set.ext fun T => (seam (A := A)).inverse.map_distinguished_iff T

end Agreement
end Cdg
end CategoryTheory
