/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.RankOne
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-!
# The spherical twist functor `T_E`: the interface and its `K₀` shadow

`SphericalTwistData k C E` is the data of the Seidel--Thomas functor
`T_E = Cone(Hom^•(E,-) ⊗_k E ⟶ id)` on a `k`-linear pretriangulated category `C`:

* a triangulated endofunctor `T`, with its three instances;
* the copower functor `F ↦ Hom^•(E,F) ⊗_k E`, the evaluation `ev` to the identity, and the
  distinguished triangle `Hom^•(E,F) ⊗ E ⟶ F ⟶ T F ⟶ (Hom^•(E,F) ⊗ E)⟦1⟧`, natural in `F`;
* the class of the copower, `[Hom^•(E,F) ⊗ E] = χ(E,F)·[E]`.

The one theorem it buys is `SphericalTwistData.map_eq_twistK₀`: the induced map on `K₀` is exactly
`twistK₀ k C E` of `SphericalTwist/GrothendieckGroup.lean`. The lattice half of the lane is
therefore a consequence of this geometry and not a parallel story.

## Encoding decision (settled before any construction)

`Hom^•(E,-) ⊗_k E` is an object copowered by a complex of `k`-modules. It is neither the
Fourier--Mukai kernel twist `C.tensor.obj K` of `FourierMukai/Basic.lean` nor the geometric
`HasDerivedTensor` of `AlgebraicGeometry/DerivedCategory/Tensor/BoundedCoherent.lean`. Two routes
construct it for a concrete category.

* **(a) The derived-tensor foundation of lane 9 (`dt-1`).** It would own the Hom-complex tensor.
  It supplies neither a functorial cone nor the three instances on `T`.
* **(b) The dg enhancement.** `Algebra/Homology/DGCategory/Basic.lean` gives the Hom-complexes and
  `DGCategory/Pretriangulated/` the cones with their projections. `ObjectTwistK0.lean` and
  `LinearObjectTwistK0.lean` already build `Cone(Hom(E,-) ⊗ E ⟶ id)` as a `DGFunctor` on a
  pretriangulated dg category `C`. Its `H⁰` is a triangulated functor on `H⁰ C`, with `CommShift`
  and `IsTriangulated` *proved* (`DGFunctor.h0CommShift`, `DGFunctor.h0IsTriangulated`), and its
  evaluation triangle is the distinguished `twistTriangleFunctor`.

**Route (b) discharges `T.Additive`, `T.CommShift ℤ` and `T.IsTriangulated` for a concrete `T`**,
and `ObjectTwistData.lean` checks it: both dg object twists, additive and scalar-linear, are
`SphericalTwistData` given the Euler copower formula. The cost of (b) is that its category is
`H⁰` of a dg category, so a geometric `Dᵇ(Coh X)` is reached only through an `Enhancement`.
Route (a) is not taken and would not replace (b): it gives the tensor, not the cone.

This file takes neither route: it is the interface, in an arbitrary pretriangulated `C`, so that its
consequences are stated once and every realization inherits them. It defines no tensor product and
builds no cone, and must not: if it ever does, the shared-foundation split has been violated and
the work belongs to lane 9.

## Why the functoriality and the instances are fields

Cones are not functorial in a triangulated category, so `T F := cone (ev F)` does not define an
endofunctor; `Surface/Spherical.lean` records the trap and Seidel--Thomas name it in §1c. The
functoriality is here a **supplied field**, never a derived fact: `T` is a functor and the triangle
is a natural family.

The three instance fields are not decoration. `K₀.map` has signature
`K₀.map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]`. A cone construction gives an
object assignment, not a triangulated functor, so without the fields `K₀.map T` does not typecheck.
They are registered with `attribute [instance]`, in the shape `GroupAction.TriEquiv` uses.

## The two external inputs, and the one thing proved

* `T F` has class `[F] - [Hom^•(E,F) ⊗ E]`: **a theorem**, `class_T`, from `K₀.of_triangle` applied
  to the supplied triangle. No shift appears, because the relation is read on the first three
  vertices.
* `[Hom^•(E,F) ⊗ E] = χ(E,F)·[E]`: **not a theorem and not free**, the field `copower_class`, stated
  with the existing predicate `K₀.IsRankOne` and the fixed-source Euler character `chiRight`
  (`copower_class_chiK₀` spells it with `chiK₀`). Splitting a copower of `E` by a bounded complex of
  finite-dimensional `k`-modules into its cohomology is a Postnikov or splitting argument, and
  triangle additivity is not that: it relates the three objects of one triangle, and no triangle
  presents the copower. This is the second supplied input, after the functor itself. Lane 9's `dt-1`
  is where a proof of it would land.
* `map_eq_twistK₀`: **proved, not a field**, from the two halves above.

## What is not claimed

No spherical object is exhibited, `T_E` is not constructed on `Dᵇ(Coh X)`, and nothing says `T`
is an autoequivalence: that is the separate supplied `SphericalTwist.AutoequivalenceStatement`.
The identity on `K₀` is far weaker than any functorial statement about `T`.

## Sources

Seidel--Thomas, *Braid group actions on derived categories of coherent sheaves*,
[arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2). The triangle
`Hom^•(E,F) ⊗ E ⟶ F ⟶ T_E F` is §1c. Their Definition 2.5 builds `T_E` on complexes of injectives,
where it is functorial, which is the dg route (b) here.
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]

/-- **The data of the Seidel--Thomas twist `T_E`**, supplied rather than constructed.

`copower` is the functor `F ↦ Hom^•(E,F) ⊗_k E`; this structure does not build it, and no
tensor product is defined here. -/
structure SphericalTwistData (E : C) where
  /-- The endofunctor `T_E`. -/
  T : C ⥤ C
  /-- `T_E` is additive. -/
  additive : T.Additive
  /-- `T_E` commutes with the shift. -/
  commShift : T.CommShift ℤ
  /-- `T_E` is triangulated, for the shift commutation above. -/
  isTriangulated : T.IsTriangulated
  /-- The functor `F ↦ Hom^•(E,F) ⊗_k E`, supplied. -/
  copower : C ⥤ C
  /-- The evaluation `Hom^•(E,-) ⊗ E ⟶ 𝟭`. -/
  ev : copower ⟶ 𝟭 C
  /-- The map `F ⟶ T F`. -/
  π : 𝟭 C ⟶ T
  /-- The connecting map `T F ⟶ (Hom^•(E,F) ⊗ E)⟦1⟧`. -/
  δ : T ⟶ copower ⋙ shiftFunctor C (1 : ℤ)
  /-- The evaluation triangle is distinguished at every `F`. Naturality in `F` is that of `ev`,
  `π` and `δ`. -/
  distinguished : ∀ F : C, Triangle.mk (ev.app F) (π.app F) (δ.app F) ∈ distTriang C
  /-- **The copower's `K₀` class: the second supplied input.** `[Hom^•(E,F) ⊗ E] = χ(E,F)·[E]`,
  as the existing rank-one predicate. Not a consequence of triangle additivity; see the module
  docstring. -/
  copower_class : K₀.IsRankOne copower (chiRight k C E) (K₀.of C E)

namespace SphericalTwistData

attribute [instance] additive commShift isTriangulated

variable {k C} {E : C} (d : SphericalTwistData k C E)

/-- The evaluation triangle as one functor `C ⥤ Triangle C`, Mathlib's `Triangle.functorMk`. -/
def triangleFunctor : C ⥤ Triangle C :=
  Triangle.functorMk d.ev d.π d.δ

/-- Every value of `triangleFunctor` is distinguished. -/
theorem triangleFunctor_obj_mem_distTriang (F : C) :
    d.triangleFunctor.obj F ∈ distTriang C :=
  d.distinguished F

/-- **The class of `T F`**: `[T F] = [F] - [Hom^•(E,F) ⊗ E]`.

The argument is `K₀.of_triangle` applied to the supplied evaluation triangle
`Hom^•(E,F) ⊗ E ⟶ F ⟶ T F ⟶ ·⟦1⟧`, which says `[F] = [Hom^•(E,F) ⊗ E] + [T F]`. The shift in the
third vertex never enters, so `K₀.of_shift_int` is not used. -/
theorem class_T (F : C) :
    K₀.of C (d.T.obj F) = K₀.of C F - K₀.of C (d.copower.obj F) := by
  have h := K₀.of_triangle C _ (d.distinguished F)
  change K₀.of C F = K₀.of C (d.copower.obj F) + K₀.of C (d.T.obj F) at h
  rw [h]
  abel

/-- `[T F] = [F] - χ(E,F)·[E]`: the class formula with the copower class substituted. -/
theorem class_T_eq (F : C) :
    K₀.of C (d.T.obj F) = K₀.of C F - chiRight k C E (K₀.of C F) • K₀.of C E := by
  rw [d.class_T, d.copower_class F]

section Twist

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- The copower class with the Euler form written as `chiK₀`, the form `twistK₀` uses. -/
theorem copower_class_chiK₀ (F : C) :
    K₀.of C (d.copower.obj F) = chiK₀ k C (K₀.of C E) (K₀.of C F) • K₀.of C E := by
  rw [d.copower_class F, chiK₀_of]

/-- **The functor induces the numerical twist on `K₀`**: `K₀.map T = twistK₀ k C E`.

A theorem, not a field. It needs the two halves of the module docstring and nothing else:
`class_T` from triangle additivity and `copower_class` supplied. -/
theorem map_eq_twistK₀ : K₀.map d.T = twistK₀ k C E := by
  apply K₀.hom_ext
  intro F
  rw [K₀.map_of, twistK₀_apply, d.class_T_eq, chiK₀_of]

end Twist

end SphericalTwistData

end CategoryTheory.Triangulated.SphericalTwist
