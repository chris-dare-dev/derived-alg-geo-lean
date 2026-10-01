/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle
import DerivedAlgGeo.CategoryTheory.Monoidal.ProjectionMorphism

/-!
# The projection formula for invertible module sheaves

For a morphism of schemes `f : X ⟶ Y`, a module sheaf `M` on `X` and a module sheaf `L` on `Y`,
the projection map

`projectionMap f M L : f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)`

is the unit `L ⟶ f_*f^*L` tensored with `f_*M`, followed by the tensorator of the lax monoidal
functor `pushforward f` (`pushforwardLaxMonoidal`). It is the projection morphism of the monoidal
adjunction `pullback f ⊣ pushforward f` (`CategoryTheory.Adjunction.projectionMorphism`), whose
monoidal structure is the strong structure `pullbackMonoidal` of `Modules/Pullback/Monoidal.lean`
and the lax structure of `Modules/Pushforward/Monoidal.lean`: there is one projection morphism
in each degree, and `projectionMap_eq` unfolds it to the two pieces just named.

When `L` is invertible, the projection map is an isomorphism (Stacks, Tag 01E8 in degree
`q = 0`, for a finite locally free sheaf of rank one): `isIso_projectionMap` for explicit
`LineBundleData`, and `isIso_projectionMap_of_isInvertible` for an intrinsically invertible `L`.
The proof is formal and global: a tensor-invertible object is dualizable, so the projection
morphism of a monoidal adjunction is an isomorphism for it
(`CategoryTheory.Adjunction.isIso_projectionMorphism`). It does not need a trivializing cover.

## Main definitions

* `Scheme.Modules.projectionMap`: the projection map `f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)`.
* `Scheme.Modules.projectionIso`: the projection isomorphism for `L : LineBundleData Y`.
* `Scheme.Modules.projectionNatIso`: the natural isomorphism
  `f_*(-) ⊗ L ≅ f_*(- ⊗ f^*L)` of functors in `M`.

## Main results

* `Scheme.Modules.isIso_projectionMap`, `Scheme.Modules.isIso_projectionMap_of_isInvertible`.
-/

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable section

/-- The monoidal structures on the adjunction `pullback f ⊣ pushforward f` are compatible: the
oplax part of `pullbackMonoidal` is the one induced by the lax structure of `pushforward f`. -/
instance pullbackPushforwardAdjunction_isMonoidal :
    (pullbackPushforwardAdjunction f).IsMonoidal :=
  Adjunction.instIsMonoidal_1 (pullbackPushforwardAdjunction f)

/-- **The projection map** `f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)`: the unit `L ⟶ f_*f^*L` tensored with
`f_*M`, then the tensorator of the lax monoidal functor `pushforward f`. -/
def projectionMap (M : X.Modules) (L : Y.Modules) :
    tensorObj ((pushforward f).obj M) L ⟶
      (pushforward f).obj (tensorObj M ((pullback f).obj L)) :=
  (pullbackPushforwardAdjunction f).projectionMorphism M L

/-- The projection map is built from the unit of the adjunction and the tensorator
`pushforwardTensorHom` of `pushforwardLaxMonoidal`, and from nothing else. -/
theorem projectionMap_eq (M : X.Modules) (L : Y.Modules) :
    projectionMap f M L =
      tensorHom (𝟙 ((pushforward f).obj M)) ((pullbackPushforwardAdjunction f).unit.app L) ≫
        pushforwardTensorHom f M ((pullback f).obj L) :=
  rfl

/-- The projection map is natural in `M`. -/
theorem projectionMap_naturality {M M' : X.Modules} (g : M ⟶ M') (L : Y.Modules) :
    projectionMap f M L ≫ (pushforward f).map (tensorHom g (𝟙 ((pullback f).obj L))) =
      tensorHom ((pushforward f).map g) (𝟙 L) ≫ projectionMap f M' L :=
  (pullbackPushforwardAdjunction f).projectionMorphism_naturality_left g L

/-- The projection map is natural in `L`. -/
theorem projectionMap_naturality_right (M : X.Modules) {L L' : Y.Modules} (g : L ⟶ L') :
    projectionMap f M L ≫ (pushforward f).map (tensorHom (𝟙 M) ((pullback f).map g)) =
      tensorHom (𝟙 ((pushforward f).obj M)) g ≫ projectionMap f M L' :=
  (pullbackPushforwardAdjunction f).projectionMorphism_naturality_right M g

/-- The tensor inverse of a line bundle, as the two-sided inverse data the abstract projection
formula consumes. -/
def LineBundleData.tensorInverse (L : LineBundleData Y) :
    MonoidalCategory.TensorInverse L.line where
  obj := L.inverse
  rightIso := L.tensorInverseIso
  leftIso := tensorCommIso L.inverse L.line ≪≫ L.tensorInverseIso

/-- **The projection formula for a line bundle** (Stacks, Tag 01E8 at `q = 0`, rank one):
`f_*M ⊗ L ⟶ f_*(M ⊗ f^*L)` is an isomorphism for every module sheaf `M` on `X`. -/
theorem isIso_projectionMap (M : X.Modules) (L : LineBundleData Y) :
    IsIso (projectionMap f M L.line) :=
  (pullbackPushforwardAdjunction f).isIso_projectionMorphism_of_tensorInverse M
    L.tensorInverse

/-- **The projection formula for an intrinsically invertible sheaf.** The tensor inverse is the
sheafified dual `dualLine L`. -/
theorem isIso_projectionMap_of_isInvertible (M : X.Modules) (L : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules Y.ringCatSheaf from L)] :
    IsIso (projectionMap f M L) :=
  (pullbackPushforwardAdjunction f).isIso_projectionMorphism_of_tensorInverse M
    { obj := dualLine L
      rightIso := tensorDualIso L
      leftIso := tensorCommIso (dualLine L) L ≪≫ tensorDualIso L }

/-- The projection isomorphism `f_*M ⊗ L ≅ f_*(M ⊗ f^*L)` for a line bundle `L` on `Y`. -/
def projectionIso (M : X.Modules) (L : LineBundleData Y) :
    tensorObj ((pushforward f).obj M) L.line ≅
      (pushforward f).obj (tensorObj M ((pullback f).obj L.line)) :=
  haveI := isIso_projectionMap f M L
  asIso (projectionMap f M L.line)

/-- The forward map of `projectionIso` is `projectionMap`. -/
@[simp]
theorem projectionIso_hom (M : X.Modules) (L : LineBundleData Y) :
    (projectionIso f M L).hom = projectionMap f M L.line :=
  rfl

/-- **The projection formula, natural in `M`**: for a line bundle `L` on `Y`, the functors
`M ↦ f_*M ⊗ L` and `M ↦ f_*(M ⊗ f^*L)` from `X.Modules` to `Y.Modules` are isomorphic. -/
def projectionNatIso (L : LineBundleData Y) :
    pushforward f ⋙ tensorRight L.line ≅
      tensorRight ((pullback f).obj L.line) ⋙ pushforward f :=
  NatIso.ofComponents (fun M => projectionIso f M L) fun {_ _} g =>
    (projectionMap_naturality f g L.line).symm

end

end AlgebraicGeometry.Scheme.Modules
