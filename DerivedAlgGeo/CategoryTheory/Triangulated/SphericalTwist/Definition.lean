/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.RankOne
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-!
# The spherical twist functor `T_E` as supplied data

A `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData` is the Seidel--Thomas twist
`T_E = Cone(Hom^•(E,-) ⊗_k E ⟶ id)` on a `k`-linear pretriangulated category `C`, supplied and not
constructed: a triangulated endofunctor, a functor standing for `F ↦ Hom^•(E,F) ⊗_k E`, the
evaluation, a distinguished triangle `Hom^•(E,F) ⊗ E ⟶ F ⟶ T F ⟶ (Hom^•(E,F) ⊗ E)⟦1⟧` natural in
`F`, and the class of the copower in `K₀ C`.

## Main definitions

* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData`:
  the supplied functor with its instances, triangle and copower class.
* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData.triangleFunctor`:
  the triangle as one functor `C ⥤ Triangle C`.

## Main results

* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData.class_T`:
  `[T F] = [F] - [Hom^•(E,F) ⊗ E]` in `K₀ C`.
* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData.map_eq_twistK₀`:
  the induced map on `K₀` is the numerical twist.
* `CategoryTheory.Triangulated.SphericalTwist.SphericalTwistData.map_comp_comp_eq_twistK₀`:
  the induced map of a composite of three supplied twists.

## Implementation notes

*Encoding.* `Hom^•(E,-) ⊗_k E` is copowered by a complex of `k`-modules, so it is neither the kernel
twist `C.tensor.obj K` of `FourierMukai/Basic.lean` nor the geometric derived tensor class of
`AlgebraicGeometry/DerivedCategory/Tensor/BoundedCoherent.lean`. Two routes construct it.
(a) A derived tensor on an ordinary triangulated category: no repository module provides one
(#892 gave the monoidal structure of `Dᵇ(Coh X)`), and it would give the tensor but neither the cone
nor the instances on `T`. (b) The dg enhancement: the object twist is built as a dg functor in
`Algebra/Homology/DGCategory/Pretriangulated/ObjectTwist.lean` and
`Algebra/Homology/DGCategory/Pretriangulated/LinearObjectTwist.lean`; on `H⁰ C` its shift
commutation and triangulatedness are proved by `CategoryTheory.DGFunctor.h0CommShift` and
`CategoryTheory.DGFunctor.h0IsTriangulated`, and its triangle is a functor on `H⁰ C` with
distinguished values. Route (b) supplies the three instances on `T` for a concrete twist, as
`SphericalTwist/ObjectTwistData.lean` checks; its cost is that `Dᵇ(Coh X)` is reached only through
an `CategoryTheory.Enhancement`. This file takes neither route.

*Supplied, not derived.* Cones are not functorial in a triangulated category
(`AlgebraicGeometry/Surface/Spherical.lean`; Seidel--Thomas §1c), so the functor, the triangle and
the three instances on `T` are fields. `CategoryTheory.Triangulated.K₀.map` needs its functor
additive, commuting with shifts and triangulated, and a cone is an object assignment, not a
triangulated functor.

*Two external inputs.* The triangle is read on its first three vertices, with
`CategoryTheory.Triangulated.K₀.of_triangle`, which proves the class formula. The class of the
copower, `[Hom^•(E,F) ⊗ E] = χ(E,F)·[E]`, is not a corollary of triangle additivity: splitting a
copower by its cohomology is a separate argument, and no triangle presents the copower. It is a
field, the second supplied input, and the formula for the induced map is proved from the two.

## References

Seidel--Thomas, *Braid group actions on derived categories of coherent sheaves*,
[arXiv:math/0001043v2](https://arxiv.org/abs/math/0001043v2): §1c, the triangle and the
non-functoriality of cones; Definition 2.5, `T_E` on complexes of injectives.

## Tags

spherical twist, Grothendieck group, distinguished triangle
-/

universe w v u

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (k : Type w) [DivisionRing k] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HomFiniteBounded k C]

/-- **The Seidel--Thomas twist `T_E`, supplied rather than constructed.**

The field `copower` stands for `F ↦ Hom^•(E,F) ⊗_k E` and `ev` for the evaluation, but only
`copower_class` ties either to `E`. So `T` is the genuine twist only when they are the genuine
ones, as in the dg realizations of `SphericalTwist/ObjectTwistData.lean`; no field says that `E`
is spherical. -/
structure SphericalTwistData (E : C) where
  /-- The endofunctor `T_E`. -/
  T : C ⥤ C
  /-- Mathlib derives additivity from `isTriangulated`. It is a field so that the three instances
  the induced map on `K₀` consumes are registered directly, as in the bundled autoequivalence
  structure; the default supplies it when `T` has a global additivity instance, and otherwise it
  is given explicitly. -/
  additive : T.Additive := by infer_instance
  /-- `T_E` commutes with the shift. -/
  commShift : T.CommShift ℤ
  /-- `T_E` is triangulated, for the shift commutation above. -/
  isTriangulated : T.IsTriangulated
  /-- Stands for `F ↦ Hom^•(E,F) ⊗_k E`; constrained only through `copower_class`. -/
  copower : C ⥤ C
  /-- Stands for the evaluation `Hom^•(E,-) ⊗ E ⟶ 𝟭`; constrained only by `distinguished`. -/
  ev : copower ⟶ 𝟭 C
  /-- The map `F ⟶ T F`. -/
  π : 𝟭 C ⟶ T
  /-- The connecting map `T F ⟶ (copower F)⟦1⟧`. -/
  δ : T ⟶ copower ⋙ shiftFunctor C (1 : ℤ)
  /-- The evaluation triangle is distinguished at every `F`; naturality in `F` is that of `ev`,
  `π` and `δ`. -/
  distinguished : ∀ F : C, Triangle.mk (ev.app F) (π.app F) (δ.app F) ∈ distTriang C
  /-- **The second supplied input**: `[copower F] = χ(E,F)·[E]`, as the existing rank-one
  predicate. It is not a consequence of triangle additivity. -/
  copower_class : K₀.IsRankOne copower (chiRight k C E) (K₀.of C E)

namespace SphericalTwistData

attribute [instance] additive commShift isTriangulated

variable {k C} {E : C} (d : SphericalTwistData k C E)

/-- The evaluation triangle as one functor `C ⥤ Triangle C`, by Mathlib's triangle-functor
constructor. -/
def triangleFunctor : C ⥤ Triangle C :=
  Triangle.functorMk d.ev d.π d.δ

/-- The field `distinguished`, restated for `d.triangleFunctor` so that Mathlib's triangle-functor
API applies. -/
theorem triangleFunctor_obj_distinguished (F : C) :
    d.triangleFunctor.obj F ∈ distTriang C :=
  d.distinguished F

/-- **The class of `T F`**: `[T F] = [F] - [copower F]`. The additivity relation of the supplied
triangle gives `[F] = [copower F] + [T F]`; the shift in its third vertex is never read. -/
theorem class_T (F : C) :
    K₀.of C (d.T.obj F) = K₀.of C F - K₀.of C (d.copower.obj F) := by
  have h := K₀.of_triangle C _ (d.distinguished F)
  change K₀.of C F = K₀.of C (d.copower.obj F) + K₀.of C (d.T.obj F) at h
  rw [h]
  abel

/-- The class formula with the copower class substituted: `[T F] = [F] - χ(E,F)·[E]`. It is stated
with the fixed-source Euler character, which needs no linearity of the shifts; the two-variable
form, and so the numerical twist, does. -/
theorem class_T_eq_sub_chiRight_smul (F : C) :
    K₀.of C (d.T.obj F) = K₀.of C F - chiRight k C E (K₀.of C F) • K₀.of C E := by
  rw [d.class_T, d.copower_class F]

section Twist

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- The field `copower_class` read through the two-variable Euler form, in which the numerical
twist is written. -/
theorem copower_class_chiK₀ (F : C) :
    K₀.of C (d.copower.obj F) = chiK₀ k C (K₀.of C E) (K₀.of C F) • K₀.of C E := by
  rw [d.copower_class F, chiK₀_of]

/-- **The functor induces the numerical twist on `K₀`.** Both sides are additive maps out of
`K₀ C`, so it suffices to compare them on a class `[F]`, where this is the class formula with the
copower class substituted, read through the two-variable Euler form. -/
theorem map_eq_twistK₀ : K₀.map d.T = twistK₀ k C E := by
  apply K₀.hom_ext
  intro F
  rw [K₀.map_of, twistK₀_apply, d.class_T_eq_sub_chiRight_smul, chiK₀_of]

variable {E₁ E₂ E₃ : C} (d₁ : SphericalTwistData k C E₁) (d₂ : SphericalTwistData k C E₂)
  (d₃ : SphericalTwistData k C E₃)

/-- The induced map on `K₀` of the composite `d₁.T ⋙ d₂.T ⋙ d₃.T`, in diagrammatic order, is the
composite of the numerical twists with the third applied last: `τ₃ ∘ τ₂ ∘ τ₁`. -/
theorem map_comp_comp_eq_twistK₀ :
    K₀.map (d₁.T ⋙ d₂.T ⋙ d₃.T) =
      (twistK₀ k C E₃).comp ((twistK₀ k C E₂).comp (twistK₀ k C E₁)) := by
  rw [K₀.map_comp, K₀.map_comp, d₁.map_eq_twistK₀, d₂.map_eq_twistK₀, d₃.map_eq_twistK₀]
  rfl

end Twist

end SphericalTwistData

end CategoryTheory.Triangulated.SphericalTwist
