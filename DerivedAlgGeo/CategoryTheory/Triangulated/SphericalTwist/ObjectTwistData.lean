/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.LinearObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition

/-!
# The dg object twists are supplied twist data

For a pretriangulated dg category `C` and an object `E`, both dg object twists
`T_E = Cone(Hom(E,-) ⊗ E ⟶ id)` on `H⁰ C`, the additive one and the scalar-linear one, are supplied
twist data, given the Euler copower formula as a hypothesis. This is route (b) of
`SphericalTwist/Definition.lean`, checked by construction.

## Main definitions

* `CategoryTheory.LinearEvaluationData.TwistConeData.toSphericalTwistData`:
  the scalar-linear realization.
* `CategoryTheory.EvaluationData.TwistConeData.toSphericalTwistData`:
  the additive realization.

## Main results

* `CategoryTheory.LinearEvaluationData.TwistConeData.toSphericalTwistData_T` and
  `CategoryTheory.EvaluationData.TwistConeData.toSphericalTwistData_T`:
  the constructed functor is the dg twist on `H⁰`, by `rfl`. With the formula for the induced map
  on `K₀` of the root structure, they give `SphericalTwist/ObjectTwistK0.lean` and
  `SphericalTwist/LinearObjectTwistK0.lean` their `K₀` theorems.

## Implementation notes

The shift commutation and triangulatedness of the twist on `H⁰ C` are proved for every dg functor
by `CategoryTheory.DGFunctor.h0CommShift` and `CategoryTheory.DGFunctor.h0IsTriangulated`, and the
structure maps and the distinguished triangle are the projections of the object-twist triangle
functor. The one input beyond the dg construction is the class of the copower, which is the Euler
copower formula of `DGEnhancement/H0/ObjectTwistK0.lean` and
`DGEnhancement/H0/LinearEvaluationK0.lean` on the nose and is taken as the hypothesis `hV`. The two
packages are not compared: the repository has no adapter between additive and scalar-linear
copowers, and this file adds none.

## References

Seidel--Thomas, [arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2), Definition 2.5: `T_E`
on complexes of injectives, the model of route (b).

## Tags

spherical twist, dg category, object twist, copower
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated Triangulated.SphericalTwist

/-- `H⁰` of the identity dg functor is the identity on morphisms: it agrees with the identity
functor of `H⁰ C` only through the comparison isomorphism, and this is what makes the evaluation and
the first map natural transformations out of and into the identity functor. -/
private theorem h0_id_map {C : Type u} [DGCategory.{v} C] {X Y : H0 C} (f : X ⟶ Y) :
    (DGFunctor.id C).h0.map f = f := by
  have h := (DGFunctor.h0IdIso (C := C)).hom.naturality f
  simp only [DGFunctor.h0IdIso_hom_app, Functor.id_map] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

namespace LinearEvaluationData.TwistConeData

variable (k : Type w) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- **The scalar-linear dg object twist is twist data**, given the Euler copower formula `hV`. The
instances of `T` are the proved ones of the dg functor on `H⁰`; `ev`, `π`, `δ` and `distinguished`
are the three maps and the distinguished values of the object-twist triangle functor. -/
noncomputable def toSphericalTwistData (hV : V.IsEulerCopower k) :
    SphericalTwistData k (H0 C) (show H0 C from E) where
  T := K.twist.h0
  commShift := DGFunctor.h0CommShift K.twist
  isTriangulated := DGFunctor.h0IsTriangulated K.twist
  copower := V.functor.h0
  ev :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₁
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₁.symm
        rw [show ((twistTriangleFunctor K).map f).hom₂ = f from h0_id_map f] at h
        exact h }
  π :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₂
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₂.symm
        rw [show ((twistTriangleFunctor K).map f).hom₂ = f from h0_id_map f] at h
        exact h }
  δ :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₃
      naturality := fun X Y f => ((twistTriangleFunctor K).map f).comm₃.symm }
  distinguished := fun X => K.twistTriangleFunctor_obj_mem_distinguishedTriangles X
  copower_class := hV

/-- The functor of the constructed data is the dg twist on `H⁰`, on the nose. -/
@[simp]
theorem toSphericalTwistData_T (hV : V.IsEulerCopower k) :
    (K.toSphericalTwistData k hV).T = K.twist.h0 :=
  rfl

/-- The copower of the constructed data is the scalar-linear evaluation functor on `H⁰`. -/
@[simp]
theorem toSphericalTwistData_copower (hV : V.IsEulerCopower k) :
    (K.toSphericalTwistData k hV).copower = V.functor.h0 :=
  rfl

end LinearEvaluationData.TwistConeData

namespace EvaluationData.TwistConeData

variable (k : Type w) [DivisionRing k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [Linear k (H0 C)] [HomFiniteBounded k (H0 C)]
  {E : C} {V : EvaluationData E} (K : V.TwistConeData)

/-- **The additive dg object twist is twist data**, given the Euler copower formula `hV`: the
scalar-linear construction for the additive evaluation package. -/
noncomputable def toSphericalTwistData (hV : V.IsEulerCopower k) :
    SphericalTwistData k (H0 C) (show H0 C from E) where
  T := K.twist.h0
  commShift := K.twistH0CommShift
  isTriangulated := K.twistH0IsTriangulated
  copower := V.functor.h0
  ev :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₁
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₁.symm
        rw [show ((twistTriangleFunctor K).map f).hom₂ = f from h0_id_map f] at h
        exact h }
  π :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₂
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₂.symm
        rw [show ((twistTriangleFunctor K).map f).hom₂ = f from h0_id_map f] at h
        exact h }
  δ :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₃
      naturality := fun X Y f => ((twistTriangleFunctor K).map f).comm₃.symm }
  distinguished := fun X => K.twistTriangleFunctor_obj_mem_distinguishedTriangles X
  copower_class := hV

/-- The functor of the constructed data is the dg twist on `H⁰`, on the nose. -/
@[simp]
theorem toSphericalTwistData_T (hV : V.IsEulerCopower k) :
    (K.toSphericalTwistData k hV).T = K.twist.h0 :=
  rfl

/-- The copower of the constructed data is the additive evaluation functor on `H⁰`. -/
@[simp]
theorem toSphericalTwistData_copower (hV : V.IsEulerCopower k) :
    (K.toSphericalTwistData k hV).copower = V.functor.h0 :=
  rfl

end EvaluationData.TwistConeData

end CategoryTheory
