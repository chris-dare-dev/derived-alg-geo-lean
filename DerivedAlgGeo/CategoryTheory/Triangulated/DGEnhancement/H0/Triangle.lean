/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import DerivedAlgGeo.CategoryTheory.Triangulated.PretriangulatedAxioms
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Cone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Rotate
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift

/-!
# The distinguished triangles of `H⁰`

`dg-enhancements-e6`. `Pretriangulated` carries its distinguished triangles as a
*field*, so transporting a triangulated structure to `H⁰` starts by saying which
triangles those are. This file says it, and discharges the two axioms that follow
from the saying rather than from any computation.

## The definition

A triangle of `H⁰ C` is distinguished when it is isomorphic to one built from a
dg cone: `X → Y → Z → X⟦1⟧` with the second map `IsConeOf.inr` and the third
`IsConeOf.toShift`, the connecting morphism `DGCategory/Cone.lean` extracts.

Two choices in that sentence are worth naming.

**The shift is the chosen one.** `toShift` accepts any `IsShiftBy X 1 X'`, but the
triangle must land in `X⟦1⟧` — the shift `HasShift (H0 C) ℤ` actually uses, which
is `IsPretriangulated.shiftWitness`'s. Using it here rather than an arbitrary
witness keeps a comparison isomorphism out of every subsequent proof; the price is
paid once, in `H0Shift.lean`, where the choice was made.

**The cone is of a representative, not of the morphism.** A morphism of `H⁰` is a
homotopy class, and a cone is built from an actual cocycle. Different
representatives give different cones — isomorphic ones, but not equal — so the
definition quantifies over a cocycle and a cone on it, and closes under
isomorphism at the end. That is also why `distinguished_cocone_triangle` needs
`Quotient.ind` rather than a direct construction.

## What this file does not do

Three of the six `Pretriangulated` fields. `contractible_distinguished` needs the
cone on an identity to be a zero object of `H⁰`; `rotate_distinguished_triangle`
and `complete_distinguished_triangle_morphism` are the two theorems the axiom
system exists for. No `Pretriangulated` instance is claimed here, and the three
lemmas below are stated in the shape those fields want so that the instance is
assembly when they land.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits Pretriangulated

namespace H0

variable {C : Type u} [DGCategory.{v} C]

/-- The morphism of `H⁰` a cocycle represents. -/
def homMk {X Y : C} (f : cocycles X Y) : (show H0 C from X) ⟶ (show H0 C from Y) :=
  QuotientAddGroup.mk f

variable (C) in
/-- The shift functors of `H⁰` are additive. `HasShift` unfolds to
`H0.shiftFunctor` only through `hasShiftMk`, which is not reducible, so instance
search needs to be told. -/
instance shiftFunctor_additive' (n : ℤ) [IsPretriangulated C] :
    (CategoryTheory.shiftFunctor (H0 C) n).Additive :=
  H0.shiftFunctor_additive C n

variable [IsPretriangulated C]

/-- The triangle a cone determines: the morphism, the cone's inclusion of the
target, and *minus* the connecting morphism into the chosen shift.

## The sign is not decoration

`IsConeOf.toShift` is `fst` followed by the shift, with no sign; the triangle's
third map is its negative. That is the convention Mathlib fixes for the model:
`CochainComplex.mappingCone.triangle` is built from `-mappingCone.fst`, and
`Cdg.triangle_mor₃_eq` records that this repository's `toShift` is `+fst`
followed by the shift on the nose. Without the sign here the two structures
would differ in the third map, and `dg-enhancements-e7`'s agreement theorem
would be false rather than hard: the sign patterns an isomorphism of triangles
can produce are exactly those whose product over the three vertices is `+1`, and
negating the third map alone is not one of them. -/
noncomputable def coneTriangle {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf f.1 Z) : Triangle (H0 C) :=
  Triangle.mk (homMk f) (homMk ⟨hc.inr, hc.inr_mem_cocycles⟩)
    (-homMk ⟨hc.toShift (IsPretriangulated.shiftWitness C X 1),
      hc.toShift_mem_cocycles _⟩)

/-- The cone triangle's first map. Stated so that the rotation proofs can rewrite
with it instead of unfolding `coneTriangle`, whose `dsimp` normal form breaks
type-correctness at `instances` transparency: `H0 C` reduces to `C`, and the
`Triangle.mk` in the unfolded term then reads its objects at the wrong type. -/
@[simp] lemma coneTriangle_mor₁ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) : (coneTriangle f hc).mor₁ = homMk f := rfl

@[simp] lemma coneTriangle_mor₂ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) :
    (coneTriangle f hc).mor₂ = homMk ⟨hc.inr, hc.inr_mem_cocycles⟩ := rfl

@[simp] lemma coneTriangle_mor₃ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) :
    (coneTriangle f hc).mor₃ =
      -homMk ⟨hc.toShift (IsPretriangulated.shiftWitness C X 1),
        hc.toShift_mem_cocycles _⟩ := rfl

variable (C) in
/-- The distinguished triangles of `H⁰`: those isomorphic to a cone triangle. -/
def distinguishedTriangles : Set (Triangle (H0 C)) :=
  {T | ∃ (X Y : C) (f : cocycles X Y) (Z : C) (hc : IsConeOf f.1 Z),
    Nonempty (T ≅ coneTriangle f hc)}

/-- A cone triangle is distinguished, by the identity isomorphism. -/
lemma coneTriangle_mem {X Y : C} (f : cocycles X Y) {Z : C} (hc : IsConeOf f.1 Z) :
    coneTriangle f hc ∈ distinguishedTriangles C :=
  ⟨X, Y, f, Z, hc, ⟨Iso.refl _⟩⟩

/-- **`isomorphic_distinguished`.** Immediate from the definition: the class is
defined as an isomorphism-closure, so this is transitivity. -/
lemma isomorphic_distinguished (T₁ : Triangle (H0 C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (H0 C)) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, Z, hc, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, Z, hc, ⟨e ≪≫ e'⟩⟩

/-- **`distinguished_cocone_triangle`.** Every morphism of `H⁰` fits into a
distinguished triangle: pick a cocycle representing it, take a dg cone on that,
and the triangle is a cone triangle on the nose. -/
lemma distinguished_cocone_triangle {X Y : H0 C} (f : X ⟶ Y) :
    ∃ (Z : H0 C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  induction f using Quotient.ind with
  | _ f =>
    obtain ⟨Z, ⟨hc⟩⟩ := IsPretriangulated.exists_cone (C := C) (X := of C X) (Y := of C Y) f.1 f.2
    exact ⟨Z, @homMk C _ (of C Y) Z ⟨hc.inr, hc.inr_mem_cocycles⟩,
      -@homMk C _ Z (IsPretriangulated.shiftObj C (of C X) 1)
        ⟨hc.toShift (IsPretriangulated.shiftWitness C (of C X) 1),
          hc.toShift_mem_cocycles _⟩,
      coneTriangle_mem (C := C) f hc⟩


omit [IsPretriangulated C] in
/-- A cone on an identity is a zero object of `H⁰`: its identity is a
coboundary, so it is zero in the quotient. `Enhancement.lean` proves the same
for an object whose dg identity vanishes on the nose; this is the version the
contractible triangle needs, where the identity is only null-homotopic. -/
lemma isZero_of_dgId_mem_coboundaries {Z : C} (h : dgId Z ∈ coboundaries Z Z) :
    IsZero (show H0 C from Z) := by
  rw [IsZero.iff_id_eq_zero]
  show (QuotientAddGroup.mk (⟨dgId Z, dgId_cocycle Z⟩ : cocycles Z Z)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact h

/-- **`contractible_distinguished`.** The triangle `X → X → 0` is distinguished:
a cone on `dgId X` is a zero object of `H⁰`, so it is isomorphic to the chosen
zero object, and every square in sight commutes because it factors through one.

The content is `IsConeOf.dgId_mem_coboundaries_of_dgId`; everything here is the
bookkeeping that turns a null-homotopy into an isomorphism of triangles. -/
lemma contractible_distinguished (X : H0 C) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨Z, ⟨hc⟩⟩ := IsPretriangulated.exists_cone (C := C) (X := of C X) (Y := of C X)
    (dgId (of C X)) (dgId_cocycle _)
  refine isomorphic_distinguished _ (coneTriangle_mem (C := C) ⟨dgId (of C X),
    dgId_cocycle _⟩ hc) _ ?_
  have hZ : IsZero (show H0 C from Z) :=
    isZero_of_dgId_mem_coboundaries (C := C) hc.dgId_mem_coboundaries_of_dgId
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((IsZero.iso (isZero_zero (H0 C)) hZ)) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact hZ.eq_of_tgt _ _
  · exact (isZero_zero (H0 C)).eq_of_src _ _

omit [IsPretriangulated C] in
/-- Two cocycles represent the same morphism of `H⁰` when they differ by a
coboundary. The quotient's own `eq_iff_sub_mem` says so; this restates it on the
underlying elements, which is the form every homotopy in the track produces. -/
lemma homMk_eq_homMk {X Y : C} {a b : cocycles X Y}
    (h : (a : (dgHom X Y).X 0) - (b : (dgHom X Y).X 0) ∈ coboundaries X Y) :
    homMk a = homMk b := by
  refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
  show ((a - b : cocycles X Y) : (dgHom X Y).X 0) ∈ coboundaries X Y
  rw [AddSubgroupClass.coe_sub]
  exact h

omit [IsPretriangulated C] in
/-- Negation of an `H⁰` morphism is negation of a representative. -/
lemma homMk_neg {X Y : C} (a : cocycles X Y) : homMk (-a) = -homMk a := rfl

omit [IsPretriangulated C] in
/-- Composition of `H⁰` morphisms is `dgComp` of representatives. -/
lemma homMk_comp {X Y Z : C} (a : cocycles X Y) (b : cocycles Y Z) :
    homMk a ≫ homMk b =
      homMk ⟨dgComp 0 0 0 (by omega) (a : (dgHom X Y).X 0) (b : (dgHom Y Z).X 0),
        Z0.comp_mem a.2 b.2⟩ :=
  rfl

section Rotate

variable {X Y Z W : C} {f : cocycles X Y} (hc : IsConeOf (f : (dgHom X Y).X 0) Z)
  (hd : IsConeOf hc.inr W)

/-- The comparison of `dg-enhancements-e6`'s rotation, as an isomorphism of `H⁰`.

Both composites were proved in `DGCategory/Rotate.lean`: one on the nose, one up
to the primitive exhibited there. In `H⁰` that difference disappears, which is
the whole reason the rotation axiom is a statement about `H⁰` and not about the
dg category. -/
noncomputable def rotateIso :
    (show H0 C from IsPretriangulated.shiftObj C X 1) ≅ (show H0 C from W) where
  hom := homMk ⟨hc.rotateBwd hd (IsPretriangulated.shiftWitness C X 1),
    hc.rotateBwd_closed hd _⟩
  inv := homMk ⟨hc.rotateFwd hd (IsPretriangulated.shiftWitness C X 1),
    hc.rotateFwd_closed hd _⟩
  hom_inv_id := by
    rw [homMk_comp]
    exact congrArg _ (Subtype.ext (hc.rotateBwd_comp_rotateFwd hd _))
  inv_hom_id := by
    rw [homMk_comp]
    exact homMk_eq_homMk (hc.rotateFwd_comp_rotateBwd_sub_dgId hd _)

@[simp] lemma rotateIso_hom :
    (rotateIso hc hd).hom = homMk ⟨hc.rotateBwd hd (IsPretriangulated.shiftWitness C X 1),
      hc.rotateBwd_closed hd _⟩ := rfl

@[simp] lemma rotateIso_inv :
    (rotateIso hc hd).inv = homMk ⟨hc.rotateFwd hd (IsPretriangulated.shiftWitness C X 1),
      hc.rotateFwd_closed hd _⟩ := rfl

/-- `rotateIso`, negated.

The cone triangle's third map carries a sign (`coneTriangle`), so the rotation
comparison has to carry one too: the second and third squares of
`rotateConeTriangleIso` each acquire the sign twice, once from the source
triangle and once from the target, and only the negated isomorphism cancels
both. -/
noncomputable def rotateIsoNeg :
    (show H0 C from IsPretriangulated.shiftObj C X 1) ≅ (show H0 C from W) where
  hom := -(rotateIso hc hd).hom
  inv := -(rotateIso hc hd).inv
  hom_inv_id := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Iso.inv_hom_id]

/-- The rotation of a cone triangle is the cone triangle on its second map. -/
noncomputable def rotateConeTriangleIso :
    (coneTriangle f hc).rotate ≅ coneTriangle ⟨hc.inr, hc.inr_mem_cocycles⟩ hd :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (rotateIsoNeg hc hd)
    -- Term mode throughout: `rw` on these goals unfolds `H0 C` to `C`, and the
    -- categorical rewrites then fail as not type-correct at `instances`
    -- transparency. `exact` elaborates against the stated goal and never does.
    (by exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      show (-homMk _) ≫ (-(rotateIso hc hd).hom) = 𝟙 _ ≫ homMk _
      rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
      exact ((homMk_comp _ _).trans
        (homMk_eq_homMk (hc.toShift_comp_rotateBwd_sub_inr hd _))).trans
        (Category.id_comp _).symm)
    (by
      have key : (rotateIso hc hd).hom ≫
            homMk ⟨hd.toShift (IsPretriangulated.shiftWitness C Y 1),
              hd.toShift_mem_cocycles _⟩ =
          -(CategoryTheory.shiftFunctor (H0 C) (1 : ℤ)).map (homMk f) :=
        (homMk_comp _ _).trans
          ((congrArg (@homMk C _ _ _) (Subtype.ext
            (hc.rotateBwd_comp_toShift hd (IsPretriangulated.shiftWitness C X 1)
              (IsPretriangulated.shiftWitness C Y 1)))).trans
            ((homMk_neg (C := C) _).trans
              (congrArg Neg.neg (H0.shiftFunctor_map_mk (C := C) 1 f).symm)))
      have h2 : (-(rotateIso hc hd).hom) ≫
            (-homMk ⟨hd.toShift (IsPretriangulated.shiftWitness C Y 1),
              hd.toShift_mem_cocycles _⟩) =
          -(CategoryTheory.shiftFunctor (H0 C) (1 : ℤ)).map (homMk f) := by
        rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, key]
      exact ((congrArg _ (Functor.map_id _ _)).trans (Category.comp_id _)).trans h2.symm)

/-- **`rotate_distinguished_triangle`, forward direction.** The rotation of a
distinguished triangle is distinguished. -/
lemma rotate_mem_of_mem (T : Triangle (H0 C)) (hT : T ∈ distinguishedTriangles C) :
    T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, Z, hc, ⟨e⟩⟩ := hT
  obtain ⟨W, ⟨hd⟩⟩ := IsPretriangulated.exists_cone (C := C) hc.inr hc.inr_mem_cocycles
  exact isomorphic_distinguished _
    (coneTriangle_mem (C := C) ⟨hc.inr, hc.inr_mem_cocycles⟩ hd) _
    ((Pretriangulated.rotate (H0 C)).mapIso e ≪≫ rotateConeTriangleIso hc hd)

end Rotate

section Lift

variable {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : cocycles X₁ Y₁} {f₂ : cocycles X₂ Y₂}
  (hc₁ : IsConeOf (f₁ : (dgHom X₁ Y₁).X 0) Z₁)
  (hc₂ : IsConeOf (f₂ : (dgHom X₂ Y₂).X 0) Z₂)

/-- **The lifting axiom, for cone triangles.** A square commuting in `H⁰` extends
to the cones, and both of the extension's squares hold on the nose.

The hypothesis is an equation in `H⁰`, so it says only that `f₁ ≫ b - a ≫ f₂` is a
coboundary. Extracting the primitive is the first step, and folding it into the
lift is what `IsConeOf.lift` does; `lift_closed` is where it is consumed. -/
lemma exists_lift_of_comm (a : cocycles X₁ X₂) (b : cocycles Y₁ Y₂)
    (comm : homMk f₁ ≫ homMk b = homMk a ≫ homMk f₂) :
    ∃ c : cocycles Z₁ Z₂,
      homMk ⟨hc₁.inr, hc₁.inr_mem_cocycles⟩ ≫ homMk c =
          homMk b ≫ homMk ⟨hc₂.inr, hc₂.inr_mem_cocycles⟩ ∧
        homMk ⟨hc₁.toShift (IsPretriangulated.shiftWitness C X₁ 1),
            hc₁.toShift_mem_cocycles _⟩ ≫
              (CategoryTheory.shiftFunctor (H0 C) (1 : ℤ)).map (homMk a) =
          homMk c ≫ homMk ⟨hc₂.toShift (IsPretriangulated.shiftWitness C X₂ 1),
            hc₂.toShift_mem_cocycles _⟩ := by
  -- The square gives a coboundary; a coboundary gives the homotopy.
  have hsub : dgComp 0 0 0 (by omega) (f₁ : (dgHom X₁ Y₁).X 0) (b : (dgHom Y₁ Y₂).X 0) -
      dgComp 0 0 0 (by omega) (a : (dgHom X₁ X₂).X 0) (f₂ : (dgHom X₂ Y₂).X 0) ∈
      coboundaries X₁ Y₂ := by
    have h := QuotientAddGroup.eq_iff_sub_mem.1
      (((homMk_comp f₁ b).symm.trans comm).trans (homMk_comp a f₂))
    rw [coboundariesIn, AddSubgroup.mem_addSubgroupOf] at h
    exact h
  obtain ⟨k, hk⟩ := hsub
  refine ⟨⟨hc₁.lift hc₂ (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) k,
    hc₁.lift_closed hc₂ _ _ _ a.2 b.2 hk⟩, ?_, ?_⟩
  · exact (homMk_comp _ _).trans
      ((congrArg (@homMk C _ _ _) (Subtype.ext (hc₁.inr_comp_lift hc₂ _ _ _))).trans
        (homMk_comp _ _).symm)
  · have h1 : homMk ⟨hc₁.lift hc₂ (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) k,
          hc₁.lift_closed hc₂ _ _ _ a.2 b.2 hk⟩ ≫
        homMk ⟨hc₂.toShift (IsPretriangulated.shiftWitness C X₂ 1),
          hc₂.toShift_mem_cocycles _⟩ =
      homMk ⟨dgComp 0 0 0 (by omega)
          (hc₁.toShift (IsPretriangulated.shiftWitness C X₁ 1))
          (IsShiftBy.mapShift (IsPretriangulated.shiftWitness C X₁ 1)
            (IsPretriangulated.shiftWitness C X₂ 1) (a : (dgHom X₁ X₂).X 0)),
        Z0.comp_mem (hc₁.toShift_mem_cocycles _)
          (IsShiftBy.mapShift_mem_cocycles _ _ a.2)⟩ :=
      (homMk_comp _ _).trans (congrArg (@homMk C _ _ _) (Subtype.ext
        (hc₁.lift_comp_toShift hc₂ (a : (dgHom X₁ X₂).X 0) (b : (dgHom Y₁ Y₂).X 0) k
          (IsPretriangulated.shiftWitness C X₁ 1)
          (IsPretriangulated.shiftWitness C X₂ 1))))
    exact ((congrArg _ (H0.shiftFunctor_map_mk (C := C) 1 a)).trans
      (homMk_comp _ _)).trans h1.symm

end Lift

section Instance

/-- **`complete_distinguished_triangle_morphism`.** A square commuting between
the first two vertices of two distinguished triangles extends to the third.

Both triangles are isomorphic to cone triangles, and `exists_lift_of_comm` is
this statement for those; `Pretriangulated.exists_lift_of_iso` conjugates the
square into them and the lift back. The two `Quotient.ind`s are what turn the
`H⁰`-morphisms `a` and `b` into the cocycles the dg construction needs -- a
different representative gives a different lift, which is why the axiom asks
only for existence. -/
lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (H0 C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ (CategoryTheory.shiftFunctor (H0 C) (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  obtain ⟨X₁, Y₁, f₁, Z₁, hc₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨X₂, Y₂, f₂, Z₂, hc₂, ⟨e₂⟩⟩ := hT₂
  refine Pretriangulated.exists_lift_of_iso e₁ e₂ ?_ a b comm
  intro a' b'
  induction a' using Quotient.ind with
  | _ a' =>
    induction b' using Quotient.ind with
    | _ b' =>
      intro comm'
      obtain ⟨c, h₁, h₂⟩ := exists_lift_of_comm hc₁ hc₂ a' b' comm'
      refine ⟨@homMk C _ Z₁ Z₂ c, h₁, ?_⟩
      -- Both cone triangles carry the sign, so it cancels: `exists_lift_of_comm`
      -- is stated on `toShift` itself.
      exact (Preadditive.neg_comp _ _).trans
        ((congrArg Neg.neg h₂).trans (Preadditive.comp_neg _ _).symm)

variable (C) in
/-- **The five axioms `H⁰` proves.** Isomorphism-closure, the contractible
triangles, a cone on every morphism, the *forward* rotation, and the completion
of a square. The rotation axiom's reverse direction is not among them: it is a
theorem about these five, proved once and generically in
`Triangulated/PretriangulatedAxioms.lean`. -/
theorem pretriangulatedAxioms : Pretriangulated.Axioms (distinguishedTriangles C) where
  isomorphic := isomorphic_distinguished
  contractible := contractible_distinguished
  cocone := distinguished_cocone_triangle
  rotate := rotate_mem_of_mem
  complete := complete_distinguished_triangle_morphism

/-- **`H⁰` of a pretriangulated dg category is pretriangulated**
(`dg-enhancements-e6`). The distinguished triangles are `distinguishedTriangles C`
-- those isomorphic to a dg cone triangle -- and every field is one of the five
lemmas above, with the reverse rotation supplied by `Axioms.mem_of_rotate_mem`. -/
noncomputable instance pretriangulated : Pretriangulated (H0 C) :=
  (pretriangulatedAxioms C).pretriangulated

variable (C) in
/-- The instance's distinguished triangles are the ones this file defined, and
`Iff.rfl` is the proof: `Axioms.pretriangulated` is reducible, so
`distTriang (H0 C)` and `distinguishedTriangles C` are the same set rather than
two sets with a comparison between them. Downstream code can therefore reach a
cone triangle through `coneTriangle_mem`. -/
lemma mem_distTriang_iff (T : Triangle (H0 C)) :
    T ∈ distTriang (H0 C) ↔ T ∈ distinguishedTriangles C := Iff.rfl

end Instance

end H0

end CategoryTheory
