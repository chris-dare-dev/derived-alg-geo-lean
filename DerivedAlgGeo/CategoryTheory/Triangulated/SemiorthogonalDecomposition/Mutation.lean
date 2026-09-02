/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Projection
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Mutation triangles and projection chains

A right-admissible triangulated subcategory has two related forms of data.
The proposition-valued form says that a right adjoint to its inclusion exists;
the chosen form records that right adjoint and its adjunction.  This file
connects the two and constructs the objectwise counit triangle

`i i⁽!⁾ X ⟶ X ⟶ L_P(X)`.

The third vertex is in `P.rightOrthogonal`.  This is the objectwise mutation
triangle available in every triangulated category.  It deliberately does not
claim a mutation *functor*: making the cone functorial is enhancement-level
data and is one of the jobs of the dg lane (#855, #853, #854).

The second half is the formal engine behind Paper II, Remark 2.3(ii).  If
successive members of a block are joined by distinguished triangles whose
third vertices are killed by the residual projection, then the projected
successive map is an isomorphism.  Iterating gives the same residual
projection for every member of the block, not only its first member.
-/

open CategoryTheory

universe w v u t

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]
variable [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {P : ObjectProperty C}

namespace RightProjectionData

/-- Extract a chosen right projection from proposition-valued right
admissibility.  This is noncomputable because admissibility only asserts that
the adjoint exists. -/
noncomputable def ofIsRightAdmissible (hP : P.IsRightAdmissible) :
    RightProjectionData P where
  projection := hP.2.choose
  adjunction := hP.2.choose_spec.some

variable (Q : RightProjectionData P)

/-- The objectwise counit triangle of a chosen right projection.

The first map is fixed to be the adjunction counit.  The third vertex and the
remaining maps are chosen from the triangulated-category axiom; the last field
is the genuine mutation conclusion that this vertex lies in the right
orthogonal of the projected component. -/
structure CounitTriangle (X : C) where
  /-- The mutation object, i.e. a cone of the projection counit. -/
  mutation : C
  /-- The second map of the counit triangle. -/
  toMutation : X ⟶ mutation
  /-- The connecting map of the counit triangle. -/
  connecting : mutation ⟶ (Q.projectObj X)⟦(1 : ℤ)⟧
  /-- The counit triangle is distinguished. -/
  distinguished :
    Pretriangulated.Triangle.mk (Q.counitApp X) toMutation connecting ∈
      distTriang C
  /-- The mutation object is right orthogonal to the projected component. -/
  mutation_mem : P.rightOrthogonal mutation

/-- Construct the objectwise mutation triangle of a chosen right projection.

The proof that the cone lies in `P.rightOrthogonal` applies the right adjoint
to the counit triangle.  Full faithfulness of the inclusion makes the mapped
counit invertible, so the mapped cone is zero; adjunction then kills every map
from a `P`-object to the original cone. -/
noncomputable def counitTriangle (hP : P.IsTriangulated) (X : C) :
    Q.CounitTriangle X := by
  letI : P.IsTriangulated := hP
  letI : P.ι.Full := P.fullyFaithfulι.full
  letI : P.ι.Faithful := P.fullyFaithfulι.faithful
  letI : IsIso Q.adjunction.unit :=
    Q.adjunction.unit_isIso_of_L_fully_faithful
  letI := Q.adjunction.rightAdjointCommShift ℤ
  letI : Q.adjunction.CommShift ℤ :=
    Q.adjunction.commShift_of_leftAdjoint ℤ
  letI : Q.projection.IsTriangulated :=
    Q.adjunction.isTriangulated_rightAdjoint
  let existsTriangle :=
    Pretriangulated.distinguished_cocone_triangle (Q.counitApp X)
  let Z := existsTriangle.choose
  let g := existsTriangle.choose_spec.choose
  let h := existsTriangle.choose_spec.choose_spec.choose
  have hT := existsTriangle.choose_spec.choose_spec.choose_spec
  refine
    { mutation := Z
      toMutation := g
      connecting := h
      distinguished := hT
      mutation_mem := ?_ }
  set_option backward.isDefEq.respectTransparency false in
    haveI : IsIso (Q.projection.map (Q.counitApp X)) := by infer_instance
  have hQZ : Limits.IsZero (Q.project Z) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (Q.projection.mapTriangle.obj
        (Pretriangulated.Triangle.mk (Q.counitApp X) g h))
      (Q.projection.map_distinguished _ hT) (by
        change IsIso (Q.projection.map (Q.counitApp X))
        infer_instance)
  intro Y f hY
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  apply (Q.adjunction.homEquiv Y' Z).injective
  exact hQZ.eq_of_tgt _ _

/-- A morphism whose cone is right orthogonal to `P` becomes an isomorphism
after applying the right projection onto `P`. -/
theorem projectMap_isIso_of_distinguished (hP : P.IsTriangulated)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk f g h ∈ distTriang C)
    (hZ : P.rightOrthogonal Z) :
    IsIso (Q.projection.map f) := by
  letI : P.IsTriangulated := hP
  letI := Q.adjunction.rightAdjointCommShift ℤ
  letI : Q.adjunction.CommShift ℤ :=
    Q.adjunction.commShift_of_leftAdjoint ℤ
  letI : Q.projection.IsTriangulated :=
    Q.adjunction.isTriangulated_rightAdjoint
  have hQZ : Limits.IsZero (Q.project Z) :=
    (Q.project_isZero_iff Z).2 (fun R a ↦ hZ a R.property)
  exact
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁
      (Q.projection.mapTriangle.obj (Pretriangulated.Triangle.mk f g h))
      (Q.projection.map_distinguished _ hT)).1 hQZ

/-- The isomorphism of projections induced by a distinguished triangle whose
third vertex is killed by the projection. -/
noncomputable def projectMapIsoOfDistinguished (hP : P.IsTriangulated)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk f g h ∈ distTriang C)
    (hZ : P.rightOrthogonal Z) :
    Q.project X ≅ Q.project Y := by
  letI : IsIso (Q.projection.map f) :=
    Q.projectMap_isIso_of_distinguished hP f g h hT hZ
  exact asIso (Q.projection.map f)

end RightProjectionData

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated.OrthogonalExceptionalBlocks

open ObjectProperty

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {I : Type t}
variable (B : OrthogonalExceptionalBlocks k C I)
variable (P : ObjectProperty C) (Q : RightProjectionData P)

/-- Distinguished triangles comparing consecutive members of every
exceptional block, with cones killed by the residual projection.

For the Enriques application the third vertex is the sheaf on the intervening
`(-2)`-curve.  The generic root only records the exact categorical condition
which the same-projection proof consumes. -/
structure ProjectionChainData where
  /-- The map from position `j` to position `j+1`. -/
  stepMap : ∀ (i : I) (j : ℕ) (hj : j + 1 < B.length i),
    (B.collection i).obj ⟨j, by omega⟩ ⟶
      (B.collection i).obj ⟨j + 1, hj⟩
  /-- A cone of each successive map. -/
  cone : ∀ (i : I) (j : ℕ) (_hj : j + 1 < B.length i), C
  /-- The second map in each successive triangle. -/
  toCone : ∀ (i : I) (j : ℕ) (hj : j + 1 < B.length i),
    (B.collection i).obj ⟨j + 1, hj⟩ ⟶ cone i j hj
  /-- The connecting map in each successive triangle. -/
  connecting : ∀ (i : I) (j : ℕ) (hj : j + 1 < B.length i),
    cone i j hj ⟶ ((B.collection i).obj ⟨j, by omega⟩)⟦(1 : ℤ)⟧
  /-- Each successive triangle is distinguished. -/
  distinguished : ∀ (i : I) (j : ℕ) (hj : j + 1 < B.length i),
    Pretriangulated.Triangle.mk (stepMap i j hj) (toCone i j hj)
        (connecting i j hj) ∈ distTriang C
  /-- Every successive cone is killed by the residual projection. -/
  cone_mem : ∀ (i : I) (j : ℕ) (hj : j + 1 < B.length i),
    P.rightOrthogonal (cone i j hj)

namespace ProjectionChainData

variable (A : ProjectionChainData B P)

/-- Consecutive members of a block have isomorphic residual projections. -/
noncomputable def stepProjectionIso (hP : P.IsTriangulated)
    (i : I) (j : ℕ)
    (hj : j + 1 < B.length i) :
    Q.project ((B.collection i).obj ⟨j, by omega⟩) ≅
      Q.project ((B.collection i).obj ⟨j + 1, hj⟩) :=
  Q.projectMapIsoOfDistinguished hP
    (A.stepMap i j hj) (A.toCone i j hj) (A.connecting i j hj)
    (A.distinguished i j hj) (A.cone_mem i j hj)

/-- Iterate the successive projection isomorphisms from the first member to
the member at natural-number position `j`. -/
noncomputable def projectionIsoFromFirst (hP : P.IsTriangulated) (i : I) :
    ∀ (j : ℕ) (hj : j < B.length i),
      Q.project (B.firstObject i) ≅
        Q.project ((B.collection i).obj ⟨j, hj⟩)
  | 0, _ => Iso.refl _
  | j + 1, hj =>
      projectionIsoFromFirst hP i j (by omega) ≪≫
        stepProjectionIso B P Q A hP i j hj

/-- **Same-projection theorem for every member of every block.**

This is Paper II, Remark 2.3(ii), in the exact generality used by the
extension argument: the residual projection of every `Lᵢⱼ` is isomorphic to
the projection of `Lᵢ₁`. -/
noncomputable def projectionIso (hP : P.IsTriangulated)
    (i : I) (j : Fin (B.length i)) :
    Q.project (B.firstObject i) ≅ Q.project ((B.collection i).obj j) :=
  projectionIsoFromFirst B P Q A hP i j.1 j.2

end ProjectionChainData

end CategoryTheory.Triangulated.OrthogonalExceptionalBlocks
