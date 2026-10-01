/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.LinearObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ObjectTwist
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition

/-!
# Route (b): the dg object twists are `SphericalTwistData`

`SphericalTwistData` (in `Definition.lean`) is an interface that constructs nothing. This file
shows that **route (b) of its encoding note, the dg enhancement, discharges every field**, so that
the three instance fields of `T` are not an unsatisfiable demand.

For a pretriangulated dg category `C` and an object `E`, the object twist
`T_E = Cone(Hom(E,-) ⊗ E ⟶ id)` is a dg functor, and

* `T.Additive`, `T.CommShift ℤ` and `T.IsTriangulated` on `H⁰ C` are **proved**:
  `DGFunctor.h0CommShift` and `DGFunctor.h0IsTriangulated` hold for every dg functor;
* the evaluation triangle is the existing functor `twistTriangleFunctor : H⁰ C ⥤ Triangle (H⁰ C)`,
  every value of which is distinguished; the three structure maps and their naturality are its
  three projections.

The one input beyond the dg construction is the copower's class, the field `copower_class`: the
rank-one formula `[Hom(E,X) ⊗ E] = χ(E,X)·[E]`, which is `IsEulerCopower` of
`DGEnhancement/H0/ObjectTwistK0.lean` and `DGEnhancement/H0/LinearEvaluationK0.lean` and the
field's type on the nose. Both constructions take it as a hypothesis `hV`. For the scalar-linear
package that is no extra assumption once all scalar-linear copowers exist:
`LinearEvaluationData.IsEulerCopower.ofHomFiniteBounded` proves it, so
`toSphericalTwistDataOfHasLinearCopowers` is a `SphericalTwistData` with no supplied field. The
additive package has no such proof.

Two constructions, one per evaluation package, and neither derived from the other: the additive
`EvaluationData` (copowers by additive cochains over `ℤ`) and the scalar-linear
`LinearEvaluationData` (copowers by `k`-linear cochains). The repository has no adapter between them
and this file adds none. They are the two producers of `SphericalTwistData` that the
single-instantiation gate asks for.

## Main definitions

* `LinearEvaluationData.TwistConeData.toSphericalTwistData`,
  `EvaluationData.TwistConeData.toSphericalTwistData` — the two realizations.
* `LinearEvaluationData.TwistConeData.toSphericalTwistDataOfHasLinearCopowers` — the scalar-linear
  one with the Euler copower formula proved.

## What this does not say

Nothing here says `T` is an autoequivalence, that `E` is spherical, or constructs a copower: the
copower object assignment is the one the evaluation data already chose.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated Triangulated.SphericalTwist

namespace LinearEvaluationData.TwistConeData

variable (k : Type w) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

omit [HomFiniteBounded k (H0 C)] in
/-- Unlike `twistTriangleFunctor_map_hom₁` and `_hom₃` this is not `rfl`: the middle vertex is
`(DGFunctor.id C).h0`, which agrees with `𝟭 (H0 C)` only through `DGFunctor.h0IdIso`. It is what
makes `ev` and `π` natural transformations out of and into `𝟭`. A request to the dg `H⁰` lane to
state it beside its siblings; private here so as not to claim their namespace. -/
private theorem twistTriangleFunctor_map_hom₂ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₂ = f := by
  change (DGFunctor.id C).h0.map f = f
  have h := (DGFunctor.h0IdIso (C := C)).hom.naturality f
  simp only [DGFunctor.h0IdIso_hom_app, Functor.id_map] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

/-- **The scalar-linear dg object twist is `SphericalTwistData`**, given the Euler copower formula.

Every field but `copower_class` is the existing dg construction on `H⁰ C`: the instances of `T` are
the proved `h0CommShift` and `h0IsTriangulated`, and `ev`, `π`, `δ` and `distinguished` are the
three maps and the distinguished values of `twistTriangleFunctor`. -/
noncomputable def toSphericalTwistData (hV : V.IsEulerCopower k) :
    SphericalTwistData k (H0 C) (show H0 C from E) where
  T := K.twist.h0
  commShift := DGFunctor.h0CommShift K.twist
  isTriangulated := DGFunctor.h0IsTriangulated K.twist
  additive := by
    letI : K.twist.h0.CommShift ℤ := DGFunctor.h0CommShift K.twist
    letI : K.twist.h0.IsTriangulated := DGFunctor.h0IsTriangulated K.twist
    infer_instance
  copower := V.functor.h0
  ev :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₁
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₁.symm
        simp only [twistTriangleFunctor_map_hom₁, twistTriangleFunctor_map_hom₂ k K] at h
        exact h }
  π :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₂
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₂.symm
        simp only [twistTriangleFunctor_map_hom₃, twistTriangleFunctor_map_hom₂ k K] at h
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

namespace LinearEvaluationData.TwistConeData

variable (k : Type v) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)] [HasLinearCopowers k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- **The scalar-linear dg object twist is `SphericalTwistData` with nothing supplied** once all
scalar-linear copowers exist: the copower's class is the theorem
`LinearEvaluationData.IsEulerCopower.ofHomFiniteBounded`, a splitting by a finite cohomology
presentation. Only the universe restriction `k : Type v` of that theorem is new. -/
noncomputable def toSphericalTwistDataOfHasLinearCopowers :
    SphericalTwistData k (H0 C) (show H0 C from E) :=
  K.toSphericalTwistData k (LinearEvaluationData.IsEulerCopower.ofHomFiniteBounded k V)

end LinearEvaluationData.TwistConeData

namespace EvaluationData.TwistConeData

variable (k : Type w) [DivisionRing k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [Linear k (H0 C)] [HomFiniteBounded k (H0 C)]
  {E : C} {V : EvaluationData E} (K : V.TwistConeData)

omit [Linear k (H0 C)] [HomFiniteBounded k (H0 C)] in
/-- The additive twin of the private lemma of the same name in the scalar-linear namespace. -/
private theorem twistTriangleFunctor_map_hom₂ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₂ = f := by
  change (DGFunctor.id C).h0.map f = f
  have h := (DGFunctor.h0IdIso (C := C)).hom.naturality f
  simp only [DGFunctor.h0IdIso_hom_app, Functor.id_map] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

/-- **The additive dg object twist is `SphericalTwistData`**, given the Euler copower formula.
The construction of `LinearEvaluationData.TwistConeData.toSphericalTwistData` for the additive
evaluation package; the two are not compared. -/
noncomputable def toSphericalTwistData (hV : V.IsEulerCopower k) :
    SphericalTwistData k (H0 C) (show H0 C from E) where
  T := K.twist.h0
  commShift := K.twistH0CommShift
  isTriangulated := K.twistH0IsTriangulated
  additive := by
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated
    infer_instance
  copower := V.functor.h0
  ev :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₁
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₁.symm
        simp only [twistTriangleFunctor_map_hom₁, twistTriangleFunctor_map_hom₂ K] at h
        exact h }
  π :=
    { app := fun X => ((twistTriangleFunctor K).obj X).mor₂
      naturality := fun X Y f => by
        have h := ((twistTriangleFunctor K).map f).comm₂.symm
        simp only [twistTriangleFunctor_map_hom₃, twistTriangleFunctor_map_hom₂ K] at h
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
