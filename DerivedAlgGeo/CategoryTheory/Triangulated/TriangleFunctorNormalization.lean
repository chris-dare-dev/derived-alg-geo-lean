/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Normalizing the first map of a triangle-valued functor

Let `T : J ⥤ Triangle C` be a natural family of triangles.  Applications
often identify its first two projected functors with more meaningful functors
`F` and `G`, and identify the transported first map with a named natural
transformation `α : F ⟶ G`.

`Triangle.FirstMapNormalizationData` packages exactly those two endpoint
isomorphisms and the required square.  It constructs a new triangle-valued
functor whose first two vertices and first map are literally `F`, `G`, and
`α`, while leaving the third projected functor unchanged.  Mathlib's
`Triangle.functorMk` and `Triangle.functorIsoMk` supply the construction and
its natural comparison with `T`.

This is an ordinary categorical interface.  It does not assert that the
triangles are distinguished, make any vertex functor exact, or make the
normalization canonical.  If the values of `T` are distinguished, the final
theorem transports that pointwise fact to the normalized family.

For two normalizations with the same named first two vertices and first map,
`FirstMapNormalizationData.ComparisonData` stores only a natural isomorphism
of their third vertices and compatibility with the remaining two maps.  It
then delegates the full triangle-family isomorphism to Mathlib's
`Triangle.functorIsoMk'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vJ vC uJ uC

namespace CategoryTheory

namespace Pretriangulated

namespace Triangle

variable {J : Type uJ} {C : Type uC}
  [Category.{vJ} J] [Category.{vC} C] [HasShift C ℤ]

/-- Data identifying the first two projections and first map of a
triangle-valued functor with named ordinary functors and a named natural
transformation.

The endpoint isomorphisms point from the raw projections to the named
functors.  This orientation makes `square` the first component of the natural
isomorphism from the raw family to its normalized form. -/
structure FirstMapNormalizationData
    (T : J ⥤ Triangle C) (F G : J ⥤ C) (α : F ⟶ G) where
  /-- Identification of the raw first projection with the named source. -/
  obj₁Iso : T ⋙ π₁ ≅ F
  /-- Identification of the raw second projection with the named target. -/
  obj₂Iso : T ⋙ π₂ ≅ G
  /-- The first map agrees with `α` after the endpoint identifications. -/
  square :
    Functor.whiskerLeft T π₁Toπ₂ ≫ obj₂Iso.hom = obj₁Iso.hom ≫ α

namespace FirstMapNormalizationData

variable {T : J ⥤ Triangle C} {F G : J ⥤ C} {α : F ⟶ G}
  (N : FirstMapNormalizationData T F G α)

/-- The unchanged third projected functor. -/
abbrev third : J ⥤ C :=
  let _ := N
  T ⋙ π₃

/-- The second map transported from the named second vertex to the unchanged
third vertex. -/
noncomputable def normalizedSecond : G ⟶ N.third :=
  N.obj₂Iso.inv ≫ Functor.whiskerLeft T π₂Toπ₃

/-- The connecting map transported to the shift of the named first vertex. -/
noncomputable def normalizedThird :
    N.third ⟶ F ⋙ CategoryTheory.shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft T π₃Toπ₁ ≫
    Functor.whiskerRight N.obj₁Iso.hom
      (CategoryTheory.shiftFunctor C (1 : ℤ))

/-- The normalized family, with literal first two vertices and literal first
map. -/
noncomputable def normalizedTriangle : J ⥤ Triangle C :=
  Triangle.functorMk α N.normalizedSecond N.normalizedThird

@[simp]
theorem normalizedTriangle_obj₁ (A : J) :
    ((N.normalizedTriangle).obj A).obj₁ = F.obj A :=
  rfl

@[simp]
theorem normalizedTriangle_obj₂ (A : J) :
    ((N.normalizedTriangle).obj A).obj₂ = G.obj A :=
  rfl

@[simp]
theorem normalizedTriangle_obj₃ (A : J) :
    ((N.normalizedTriangle).obj A).obj₃ = N.third.obj A :=
  rfl

@[simp]
theorem normalizedTriangle_mor₁ (A : J) :
    ((N.normalizedTriangle).obj A).mor₁ = α.app A :=
  rfl

@[simp]
theorem normalizedTriangle_mor₂ (A : J) :
    ((N.normalizedTriangle).obj A).mor₂ = N.normalizedSecond.app A :=
  rfl

@[simp]
theorem normalizedTriangle_mor₃ (A : J) :
    ((N.normalizedTriangle).obj A).mor₃ = N.normalizedThird.app A :=
  rfl

/-- The raw triangle family and its first-map-normalized form are naturally
isomorphic.  The comparison on the unchanged third projection is the
identity. -/
noncomputable def rawIsoNormalized : T ≅ N.normalizedTriangle :=
  Triangle.functorIsoMk _ _ N.obj₁Iso N.obj₂Iso (Iso.refl _)
    N.square
    (by
      ext A
      change (T.obj A).mor₂ ≫ 𝟙 _ =
        N.obj₂Iso.hom.app A ≫
          (N.obj₂Iso.inv.app A ≫ (T.obj A).mor₂)
      rw [Category.comp_id]
      exact (Iso.hom_inv_id_assoc (N.obj₂Iso.app A) (T.obj A).mor₂).symm)
    (by
      ext A
      change (T.obj A).mor₃ ≫
          (CategoryTheory.shiftFunctor C (1 : ℤ)).map
            (N.obj₁Iso.hom.app A) =
        𝟙 _ ≫
          ((T.obj A).mor₃ ≫
            (CategoryTheory.shiftFunctor C (1 : ℤ)).map
              (N.obj₁Iso.hom.app A))
      simp)

@[simp]
theorem rawIsoNormalized_hom_app_hom₁ (A : J) :
    ((N.rawIsoNormalized).hom.app A).hom₁ = N.obj₁Iso.hom.app A :=
  rfl

@[simp]
theorem rawIsoNormalized_hom_app_hom₂ (A : J) :
    ((N.rawIsoNormalized).hom.app A).hom₂ = N.obj₂Iso.hom.app A :=
  rfl

@[simp]
theorem rawIsoNormalized_hom_app_hom₃ (A : J) :
    ((N.rawIsoNormalized).hom.app A).hom₃ = 𝟙 _ :=
  rfl

/-! ### Comparing two normalizations with the same first map -/

/-- The remaining data needed for an endpoint-strict comparison of two
first-map-normalized triangle families with the same named first two vertices
and first map.

The interface fixes the first two comparison components to be identities.
Thus only a natural isomorphism of the third vertices and compatibility with
the second and third maps are stored. -/
structure ComparisonData
    {T₁ T₂ : J ⥤ Triangle C} {F G : J ⥤ C} {α : F ⟶ G}
    (N₁ : FirstMapNormalizationData T₁ F G α)
    (N₂ : FirstMapNormalizationData T₂ F G α) where
  /-- Natural comparison of the third vertices. -/
  thirdIso : N₁.third ≅ N₂.third
  /-- Compatibility with the maps from the common second vertex. -/
  second : N₁.normalizedSecond ≫ thirdIso.hom = N₂.normalizedSecond
  /-- Compatibility with the connecting maps to the shifted common first
  vertex. -/
  third : N₁.normalizedThird = thirdIso.hom ≫ N₂.normalizedThird

namespace ComparisonData

variable {T₁ T₂ : J ⥤ Triangle C} {F G : J ⥤ C} {α : F ⟶ G}
  {N₁ : FirstMapNormalizationData T₁ F G α}
  {N₂ : FirstMapNormalizationData T₂ F G α}
  (D : ComparisonData N₁ N₂)

/-- The natural isomorphism of normalized triangle families determined by the
third-vertex comparison.  Mathlib's triangle-functor constructor supplies the
identity components on the common first two vertices. -/
noncomputable def normalizedTriangleIso :
    N₁.normalizedTriangle ≅ N₂.normalizedTriangle :=
  Triangle.functorIsoMk' (Iso.refl F) (Iso.refl G) D.thirdIso
    (by simp) (by simpa using D.second) (by simpa using D.third)

/-- The first component of the normalized comparison is the identity. -/
@[simp]
theorem normalizedTriangleIso_hom_app_hom₁ (A : J) :
    (D.normalizedTriangleIso.hom.app A).hom₁ = 𝟙 _ :=
  rfl

/-- The second component of the normalized comparison is the identity. -/
@[simp]
theorem normalizedTriangleIso_hom_app_hom₂ (A : J) :
    (D.normalizedTriangleIso.hom.app A).hom₂ = 𝟙 _ :=
  rfl

/-- The third component of the normalized comparison is the supplied natural
isomorphism. -/
@[simp]
theorem normalizedTriangleIso_hom_app_hom₃ (A : J) :
    (D.normalizedTriangleIso.hom.app A).hom₃ = D.thirdIso.hom.app A :=
  rfl

end ComparisonData

section Distinguished

variable [Limits.HasZeroObject C] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [CategoryTheory.Pretriangulated C]

/-- Pointwise distinguishedness is preserved by first-map normalization. -/
theorem normalizedTriangle_obj_distinguished
    (hT : ∀ A : J, T.obj A ∈ distTriang C) (A : J) :
    N.normalizedTriangle.obj A ∈ distTriang C :=
  (distinguished_iff_of_iso (N.rawIsoNormalized.app A)).mp (hT A)

end Distinguished

end FirstMapNormalizationData

end Triangle

end Pretriangulated

end CategoryTheory
