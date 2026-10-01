/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle
import DerivedAlgGeo.CategoryTheory.Monoidal.ProjectionMorphism

/-!
# The projection formula for line bundles

For a morphism of schemes f : X ⟶ Y, a module sheaf M on X and a module sheaf L on Y, the projection
map f_*M ⊗ L ⟶ f_*(M ⊗ f^*L) is the unit L ⟶ f_*f^*L tensored with f_*M, followed by the tensorator
of the lax monoidal pushforward. For a line bundle L, with an explicit tensor inverse, it is an
isomorphism, which is the underived case of the projection formula.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.projectionMap`: the projection map.
* `AlgebraicGeometry.Scheme.Modules.LineBundleData.tensorInverse`: the two-sided tensor inverse data
  of a line bundle.
* `AlgebraicGeometry.Scheme.Modules.projectionIso`: the projection isomorphism for a line bundle.
* `AlgebraicGeometry.Scheme.Modules.projectionNatIso`: the natural isomorphism, in M, between the
  functors M ↦ f_*M ⊗ L and M ↦ f_*(M ⊗ f^*L).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_projectionMap`: the projection map is an isomorphism for a
  line bundle.
* `AlgebraicGeometry.Scheme.Modules.projectionMap_eq`: the projection map is the unit tensored with
  the pushforward, followed by `AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom`, and nothing
  else.
* `AlgebraicGeometry.Scheme.Modules.projectionMap_naturality` and
  `AlgebraicGeometry.Scheme.Modules.projectionMap_naturality_right`: naturality in M and in L.
* `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction_isMonoidal`: the adjunction
  between pullback and pushforward is monoidal for the structures of
  `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`.

## Implementation notes

The projection map is `CategoryTheory.Adjunction.projectionMorphism` of the adjunction between
pullback and pushforward, whose invertibility at an object with a two-sided tensor inverse is
`CategoryTheory.Adjunction.isIso_projectionMorphism`. The argument is global: it needs no
trivializing cover and no restriction to opens. The statement for an intrinsically invertible sheaf,
whose tensor inverse is the sheafified dual, is
`AlgebraicGeometry.Scheme.Modules.isIso_projectionMap_of_isInvertible` in
`DerivedAlgGeo/AlgebraicGeometry/Divisors/ProjectionFormula.lean`; it is kept in that file so that
this file does not depend on the construction of duals.

## References

* The Stacks Project, Tag 01CB (Lemma 17.16.1, the stalk of a tensor product of modules on a ringed
  space), Tag 01CD (Lemma 17.16.4, pullback of a tensor product of modules on ringed spaces) and Tag
  01E8 (Lemma 20.54.2, the projection formula for a finite locally free module). The statements were
  not obtained verbatim: only summaries of those pages were fetched, so these tags give the
  literature context and are not quoted.

## Tags

projection formula, pushforward, pullback, line bundle, invertible sheaf, tensor product
-/

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable section

/-- The monoidal structures on the adjunction `pullback f ⊣ pushforward f` are compatible: the oplax
part of `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` is the one induced by the lax structure
of `pushforward f`. -/
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
`AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom` of
`AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`, and from nothing else. -/
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

/-- The projection isomorphism `f_*M ⊗ L ≅ f_*(M ⊗ f^*L)` for a line bundle `L` on `Y`. -/
def projectionIso (M : X.Modules) (L : LineBundleData Y) :
    tensorObj ((pushforward f).obj M) L.line ≅
      (pushforward f).obj (tensorObj M ((pullback f).obj L.line)) :=
  haveI := isIso_projectionMap f M L
  asIso (projectionMap f M L.line)

/-- The forward map of `AlgebraicGeometry.Scheme.Modules.projectionIso` is
`AlgebraicGeometry.Scheme.Modules.projectionMap`. -/
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
