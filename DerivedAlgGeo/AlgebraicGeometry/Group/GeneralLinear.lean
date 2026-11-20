/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The general linear group scheme

For a finite type `n` with decidable equality and a scheme `S`, `Scheme.generalLinearGroup n S`
is the group object `GL(n; S)` of `Over S` whose functor of points is
`T ↦ GL_n(Γ(T, 𝒪_T))`, naturally in `T : Over S`. It is the open subscheme `D(det)` of the affine
space `𝔸(n × n; S)` of `n × n` matrices where the determinant of the matrix of coordinates is
invertible, that is the base change to `S` of `Spec ℤ[xᵢⱼ][det⁻¹]`.

## Main definitions

* `Scheme.generalLinearGroup n S : Over S`: the scheme `GL(n; S)` over `S`.
* `Scheme.generalLinearGroup.homEquiv T`: morphisms `T ⟶ GL(n; S)` in `Over S` are the invertible
  matrices `Matrix.GeneralLinearGroup n Γ(T.left, ⊤)`. It is natural in `T`
  (`Scheme.generalLinearGroup.homEquiv_comp`) and multiplicative
  (`Scheme.generalLinearGroup.homEquiv_mul`, `Scheme.generalLinearGroup.homMulEquiv`).
* The `GrpObj` instance on `Scheme.generalLinearGroup n S`, obtained from this functor of points
  by `GrpObj.ofRepresentableBy`.
* `Scheme.generalLinearGroup.pullbackIso`: formation of `GL(n; S)` commutes with base change
  along `S' ⟶ S`, as an isomorphism `(Over.pullback g).obj GL(n; S) ≅ GL(n; S')` in `Over S'`.

## Main results

* `IsAffineHom (Scheme.generalLinearGroup n S).hom`.
* `Smooth (Scheme.generalLinearGroup n S).hom`.

## Implementation notes

The scheme is the basic open of `𝔸(n × n; S)` cut out by `det` of the coordinate matrix, so that
the open immersion `toAffineSpace` is the inclusion and morphisms into it are the morphisms to
`𝔸(n × n; S)` over which the determinant becomes a unit (`liftHom`). The group laws are not
written by hand: they come from the functor of points. Affineness is that of the inclusion of a
basic open composed with the affine `𝔸(n × n; S) ⟶ S`, and smoothness is that of an open immersion
(which is étale) composed with the smooth `𝔸(n × n; S) ⟶ S`.

`n : Type u` is an arbitrary index type with `Fintype n` and `DecidableEq n`, matching
`Matrix.GeneralLinearGroup n R`; `Fin r` (lifted to `Type u`) is the case used in practice.

## References

* [Stacks, Example 39.5.4 (Tag 022W)](https://stacks.math.columbia.edu/tag/022W), the general
  linear group scheme.

## Tags

general linear group, group scheme, functor of points, affine space
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) [Fintype n] [DecidableEq n] (S : Scheme.{u})

namespace Scheme.generalLinearGroup

/-- The matrix of the `n × n` coordinates of `𝔸(n × n; S)`. -/
def coordMatrix : Matrix n n Γ(𝔸(n × n; S), ⊤) :=
  Matrix.of fun i j ↦ AffineSpace.coord S (i, j)

/-- The determinant of the coordinate matrix of `𝔸(n × n; S)`. -/
def detCoord : Γ(𝔸(n × n; S), ⊤) := (coordMatrix n S).det

/-- The open subscheme of `𝔸(n × n; S)` where the determinant is invertible. -/
def locus : (𝔸(n × n; S)).Opens := (𝔸(n × n; S)).basicOpen (detCoord n S)

end Scheme.generalLinearGroup

/-- The general linear group scheme. -/
def Scheme.generalLinearGroup : Over S :=
  Over.mk ((Scheme.generalLinearGroup.locus n S).ι ≫ 𝔸(n × n; S) ↘ S)

namespace Scheme.generalLinearGroup

/-- The open immersion of `GL(n; S)` into `𝔸(n × n; S)`. -/
def toAffineSpace : (generalLinearGroup n S).left ⟶ 𝔸(n × n; S) := (locus n S).ι

/-- `GL(n; S)` is an open subscheme of `𝔸(n × n; S)`. -/
instance : IsOpenImmersion (toAffineSpace n S) :=
  inferInstanceAs (IsOpenImmersion (locus n S).ι)

/-- The inclusion is affine, being that of a basic open. -/
instance : IsAffineHom (toAffineSpace n S) :=
  inferInstanceAs (IsAffineHom ((𝔸(n × n; S)).basicOpen (detCoord n S)).ι)

@[reassoc (attr := simp)]
lemma toAffineSpace_over :
    toAffineSpace n S ≫ 𝔸(n × n; S) ↘ S = (generalLinearGroup n S).hom := rfl

variable {n S}

/-- The `n × n` matrix of global sections determined by a morphism to `𝔸(n × n; S)`. -/
def matrixOf {X : Scheme.{u}} (f : X ⟶ 𝔸(n × n; S)) : Matrix n n Γ(X, ⊤) :=
  Matrix.of fun i j ↦ f.appTop (AffineSpace.coord S (i, j))

/-- The determinant coordinate pulls back to the determinant of the matrix of pulled-back
coordinates. -/
lemma appTop_detCoord {X : Scheme.{u}} (f : X ⟶ 𝔸(n × n; S)) :
    f.appTop (detCoord n S) = (matrixOf f).det := by
  simp only [detCoord, coordMatrix, matrixOf]
  rw [RingHom.map_det]
  rfl

omit [Fintype n] [DecidableEq n] in
/-- The matrix of the morphism given by a vector of global sections is that vector. -/
lemma matrixOf_homOfVector {X : Scheme.{u}} (f : X ⟶ S) (v : n × n → Γ(X, ⊤)) :
    matrixOf (AffineSpace.homOfVector f v) = Matrix.of fun i j ↦ v (i, j) := by
  ext i j
  simp [matrixOf]

/-- A morphism to `GL(n; S)`, seen in `𝔸(n × n; S)`, has invertible determinant. -/
lemma isUnit_det_matrixOf_comp_toAffineSpace {X : Scheme.{u}}
    (g : X ⟶ (generalLinearGroup n S).left) :
    IsUnit (matrixOf (g ≫ toAffineSpace n S)).det := by
  rw [← appTop_detCoord, Scheme.Hom.comp_appTop]
  refine (?_ : IsUnit ((locus n S).ι.appTop (detCoord n S))).map g.appTop.hom
  rw [Scheme.Opens.ι_appTop]
  have key : ∀ (V : (𝔸(n × n; S)).Opens) (hV : V = locus n S) (hle : V ≤ ⊤),
      IsUnit ((𝔸(n × n; S)).presheaf.map (homOfLE hle).op (detCoord n S)) := by
    rintro V rfl hle
    exact RingedSpace.isUnit_res_basicOpen (X := (𝔸(n × n; S)).toRingedSpace) (U := ⊤)
      (detCoord n S)
  exact key _ (Scheme.Opens.ι_image_top _) _

/-- A morphism to `𝔸(n × n; S)` with invertible determinant factors through `GL(n; S)`. -/
def liftHom {X : Scheme.{u}} (f : X ⟶ 𝔸(n × n; S)) (h : IsUnit (matrixOf f).det) :
    X ⟶ (generalLinearGroup n S).left :=
  IsOpenImmersion.lift (toAffineSpace n S) f <| by
    change Set.range f ⊆ Set.range (locus n S).ι
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have : f ⁻¹ᵁ (locus n S) = ⊤ := by
      rw [locus, Scheme.Hom.preimage_basicOpen_top]
      exact Scheme.basicOpen_of_isUnit _ (by rwa [appTop_detCoord])
    have hy : y ∈ f ⁻¹ᵁ (locus n S) := this ▸ (trivial : y ∈ (⊤ : X.Opens))
    exact hy

@[reassoc (attr := simp)]
lemma liftHom_toAffineSpace {X : Scheme.{u}} (f : X ⟶ 𝔸(n × n; S))
    (h : IsUnit (matrixOf f).det) :
    liftHom f h ≫ toAffineSpace n S = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- Morphisms into `GL(n; S)` are determined by their composite with the open immersion into
`𝔸(n × n; S)`. -/
lemma hom_ext {X : Scheme.{u}} {f g : X ⟶ (generalLinearGroup n S).left}
    (h : f ≫ toAffineSpace n S = g ≫ toAffineSpace n S) : f = g :=
  (cancel_mono (toAffineSpace n S)).mp h

/-- The vector of entries of an invertible matrix has invertible determinant. -/
lemma isUnit_det_homOfVector {X : Scheme.{u}} (f : X ⟶ S)
    (u : Matrix.GeneralLinearGroup n Γ(X, ⊤)) :
    IsUnit (matrixOf (AffineSpace.homOfVector f
      fun p ↦ (u : Matrix n n Γ(X, ⊤)) p.1 p.2)).det := by
  rw [matrixOf_homOfVector]
  exact (Matrix.GeneralLinearGroup.det u).isUnit

variable {T : Over S}

/-- The invertible matrix of global sections determined by a point of `GL(n; S)`. -/
def toGL (g : T ⟶ generalLinearGroup n S) : Matrix.GeneralLinearGroup n Γ(T.left, ⊤) :=
  Matrix.GeneralLinearGroup.mk'' (matrixOf (g.left ≫ toAffineSpace n S)) 
    (isUnit_det_matrixOf_comp_toAffineSpace g.left)

/-- The point of `GL(n; S)` determined by an invertible matrix of global sections. -/
def ofGL (u : Matrix.GeneralLinearGroup n Γ(T.left, ⊤)) : T ⟶ generalLinearGroup n S :=
  Over.homMk
    (liftHom (AffineSpace.homOfVector T.hom fun p ↦ (u : Matrix n n Γ(T.left, ⊤)) p.1 p.2)
      (isUnit_det_homOfVector T.hom u)) (by
    rw [← toAffineSpace_over, liftHom_toAffineSpace_assoc, AffineSpace.homOfVector_over])

/-- The matrix of `toGL g` consists of the coordinates of `g`. -/
lemma coe_toGL (g : T ⟶ generalLinearGroup n S) :
    (toGL g : Matrix n n Γ(T.left, ⊤)) = matrixOf (g.left ≫ toAffineSpace n S) := rfl

/-- The point `ofGL u` has the entries of `u` as coordinates in `𝔸(n × n; S)`. -/
lemma ofGL_left_toAffineSpace (u : Matrix.GeneralLinearGroup n Γ(T.left, ⊤)) :
    (ofGL u).left ≫ toAffineSpace n S =
      AffineSpace.homOfVector T.hom fun p ↦ (u : Matrix n n Γ(T.left, ⊤)) p.1 p.2 :=
  liftHom_toAffineSpace _ (isUnit_det_homOfVector T.hom u)

variable (T) in
/-- The points of `GL(n; S)`. -/
def homEquiv : (T ⟶ generalLinearGroup n S) ≃ Matrix.GeneralLinearGroup n Γ(T.left, ⊤) where
  toFun := toGL
  invFun := ofGL
  left_inv g := by
    apply Over.OverMorphism.ext
    refine hom_ext ?_
    rw [ofGL_left_toAffineSpace]
    refine AffineSpace.hom_ext ?_ ?_
    · rw [AffineSpace.homOfVector_over, Category.assoc]
      exact (Over.w g).symm
    · intro i
      simp [coe_toGL, matrixOf]
  right_inv u := by
    ext i j
    rw [coe_toGL, ofGL_left_toAffineSpace, matrixOf_homOfVector]
    rfl

variable (n S) in
/-- The presheaf of groups `T ↦ GL_n(Γ(T, 𝒪_T))` on `Over S`, represented by `GL(n; S)`. -/
def pointsFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (Matrix.GeneralLinearGroup n Γ(T.unop.left, ⊤))
  map φ := GrpCat.ofHom (Matrix.GeneralLinearGroup.map φ.unop.left.appTop.hom)
  map_id T := by
    ext x
    simp
  map_comp φ ψ := by
    ext x
    simp [Matrix.GeneralLinearGroup.map_comp_apply]
    rfl

/-- The functor of points of `GL(n; S)` is natural in `T`. -/
lemma homEquiv_comp {T' : Over S} (φ : T' ⟶ T) (g : T ⟶ generalLinearGroup n S) :
    homEquiv T' (φ ≫ g) = Matrix.GeneralLinearGroup.map φ.left.appTop.hom (homEquiv T g) := by
  ext i j
  change matrixOf ((φ.left ≫ g.left) ≫ toAffineSpace n S) i j = _
  rw [Category.assoc]
  simp [matrixOf]
  rfl

variable (n S) in
/-- `GL(n; S)` represents the presheaf of groups `T ↦ GL_n(Γ(T, 𝒪_T))`. -/
def representableBy : (pointsFunctor n S ⋙ CategoryTheory.forget GrpCat).RepresentableBy
    (generalLinearGroup n S) where
  homEquiv := homEquiv _
  homEquiv_comp φ g := homEquiv_comp φ g

end Scheme.generalLinearGroup

/-- `GL(n; S)` is a group object of `Over S`, with the group structure of its functor of points. -/
instance : GrpObj (Scheme.generalLinearGroup n S) :=
  GrpObj.ofRepresentableBy _ (Scheme.generalLinearGroup.pointsFunctor n S)
    (Scheme.generalLinearGroup.representableBy n S)

namespace Scheme.generalLinearGroup

open scoped MonObj

variable {n S}

/-- The functor of points of `GL(n; S)` is multiplicative for the group structure on morphisms
of `Over S`. -/
lemma homEquiv_mul {T : Over S} (f g : T ⟶ generalLinearGroup n S) :
    homEquiv T (f * g) = homEquiv T f * homEquiv T g := by
  rw [Hom.mul_def]
  have hμ : μ[generalLinearGroup n S] = (representableBy n S).homEquiv'.symm
      ((representableBy n S).homEquiv' (fst _ _) * (representableBy n S).homEquiv' (snd _ _)) :=
    rfl
  rw [hμ]
  change (representableBy n S).homEquiv' _ = _
  rw [(representableBy n S).homEquiv'_comp, Equiv.apply_symm_apply, map_mul,
    ← (representableBy n S).homEquiv'_comp, ← (representableBy n S).homEquiv'_comp, lift_fst,
    lift_snd]
  rfl

variable (T) in
/-- The points of `GL(n; S)` form a group isomorphic to `GL_n(Γ(T, 𝒪_T))`. -/
def homMulEquiv : (T ⟶ generalLinearGroup n S) ≃* Matrix.GeneralLinearGroup n Γ(T.left, ⊤) :=
  { homEquiv T with map_mul' := fun f g ↦ homEquiv_mul f g }

section pullback

variable (n) {S' : Scheme.{u}} (g : S' ⟶ S)

/-- The functor of points of `GL(n; S)` along the pullback `Over S' ⥤ Over S` is that of
`GL(n; S')`. -/
def pullbackRepresentableBy : (pointsFunctor n S' ⋙ CategoryTheory.forget GrpCat).RepresentableBy
    ((Over.pullback g).obj (generalLinearGroup n S)) where
  homEquiv {T} := ((Over.mapPullbackAdj g).homEquiv T (generalLinearGroup n S)).symm.trans
    (homEquiv ((Over.map g).obj T))
  homEquiv_comp {T T'} φ ψ := by
    change homEquiv _ (((Over.mapPullbackAdj g).homEquiv _ _).symm (φ ≫ ψ)) =
      Matrix.GeneralLinearGroup.map _ (homEquiv _ (((Over.mapPullbackAdj g).homEquiv _ _).symm ψ))
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact homEquiv_comp ((Over.map g).map φ) _

/-- Formation of `GL(n; S)` commutes with base change along `g : S' ⟶ S`. -/
def pullbackIso : (Over.pullback g).obj (generalLinearGroup n S) ≅ generalLinearGroup n S' :=
  (pullbackRepresentableBy n g).uniqueUpToIso (representableBy n S')

/-- The base-change isomorphism is the one induced by the identification of points. -/
lemma homEquiv_comp_pullbackIso_hom {T : Over S'}
    (ψ : T ⟶ (Over.pullback g).obj (generalLinearGroup n S)) :
    homEquiv T (ψ ≫ (pullbackIso n g).hom) =
      homEquiv ((Over.map g).obj T) (((Over.mapPullbackAdj g).homEquiv T _).symm ψ) := by
  have e : (pullbackIso n g).hom =
      (representableBy n S').homEquiv.symm ((pullbackRepresentableBy n g).homEquiv (𝟙 _)) := rfl
  change (representableBy n S').homEquiv (ψ ≫ (pullbackIso n g).hom) = _
  rw [e, (representableBy n S').comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← (pullbackRepresentableBy n g).homEquiv_eq]
  rfl

end pullback

/-- The structure morphism of `GL(n; S)` is affine. -/
instance : IsAffineHom (generalLinearGroup n S).hom := by
  rw [← toAffineSpace_over]
  infer_instance

/-- The structure morphism of `GL(n; S)` is smooth. -/
instance : Smooth (generalLinearGroup n S).hom := by
  rw [← toAffineSpace_over]
  infer_instance

end Scheme.generalLinearGroup
end AlgebraicGeometry
