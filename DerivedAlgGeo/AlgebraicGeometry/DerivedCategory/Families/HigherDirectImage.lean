/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KInjectivePushforward

/-!
# Higher direct images of module sheaves

For a morphism `f : T ⟶ U` of scheme base changes, the higher direct images of a module sheaf
`F` on `T.left` are the cohomology sheaves `R^p f_* F = H^p(Rf_* F)` of its total direct image
`Rf_*` (Stacks, Section 20.28, Tag 079V). Here `Rf_*` is
`RightDerivedPushforward.ofKInjective f`, computed from K-injective resolutions.

The total direct image is left t-exact: it sends a complex with cohomology in degrees `≥ n` to
one with cohomology in degrees `≥ n`. So the higher direct images vanish in negative degrees,
and `R^0 f_* = f_*` because pushforward is left exact. A short exact sequence of module sheaves
gives the long exact sequence of higher direct images. Restriction to an open of the target
commutes with higher direct images (Stacks, Lemma 20.7.4, Tag 01E5).

## Main definitions

* `SchemeBaseChange.higherDirectImage f p`: the functor `F ↦ R^p f_* F` on module sheaves.
* `SchemeBaseChange.higherDirectImageZeroIso f`: `R^0 f_* ≅ f_*`.
* `SchemeBaseChange.higherDirectImageδ`: the connecting map
  `R^p f_* F₃ ⟶ R^{p+1} f_* F₁` of a short exact sequence `0 → F₁ → F₂ → F₃ → 0`.
* `SchemeBaseChange.higherDirectImageRestrictIso`: for a pullback square whose right edge `j`
  is an open immersion, `j^* ∘ R^p f_* ≅ R^p f'_* ∘ j'^*` (Stacks, Tag 01E5).

## Main results

* `SchemeBaseChange.RightDerivedPushforward.isGE_ofKInjective_obj`: the total direct image is
  left t-exact.
* `SchemeBaseChange.isZero_higherDirectImage_of_neg`: `R^p f_* F = 0` for `p < 0`.
* `SchemeBaseChange.higherDirectImage_exact₁`, `higherDirectImage_exact₂` and
  `higherDirectImage_exact₃`: the long exact sequence of higher direct images.

## Implementation notes

Left t-exactness: a complex `E` with cohomology in degrees `≥ n` is isomorphic in the derived
category to a complex `L` of injective module sheaves concentrated in degrees `≥ n`
(`DerivedCategory.Plus.exists_injective_nonempty_iso`). Such a complex is K-injective, so
`Rf_* E ≅ f_* L`, and `f_* L` is concentrated in degrees `≥ n`.

The degree-zero comparison goes through the bounded-below derived category: there `Rf_*` agrees
with Mathlib's `Functor.rightDerivedFunctorPlus` (`kInjectiveDerivedFunctorPlusIso`), whose
degree-zero cohomology on a single object is the underived functor, when that functor preserves
finite limits (`rightDerivedFunctorPlusHomologyZeroSingleNatIsoOfPreservesFiniteLimits`).

Restriction to an open is exact, so it commutes with cohomology
(`mapDerivedCategoryHomologyFunctorIso`) and with the single functors
(`Functor.mapDerivedCategorySingleFunctor`). Tag 01E5 is then Tag 08FE for `Rf_*`,
`RightDerivedPushforward.ofKInjectiveRestrictIso`, applied to single objects.

## References

* [The Stacks project, Section 20.28](https://stacks.math.columbia.edu/tag/079V)
* [The Stacks project, Lemma 20.7.4](https://stacks.math.columbia.edu/tag/01E5)

## Tags

higher direct image, total direct image, right derived functor, t-exactness, restriction
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

namespace RightDerivedPushforward

/-- **Left t-exactness of the total direct image.** If `E` has cohomology in degrees `≥ n`, then
so does `Rf_* E`. -/
theorem isGE_ofKInjective_obj (f : T ⟶ U) (E : T.DerivedFiber) (n : ℤ) [E.IsGE n] :
    ((ofKInjective f).functor.obj E).IsGE n := by
  let E' : DerivedCategory.Plus T.left.Modules := ⟨E, n, inferInstance⟩
  have : E'.IsGE n := (E'.isGE_ι_obj_iff n).1 ‹_›
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso E' n
  let K := ((InjectiveObject.ι T.left.Modules).mapCochainComplexPlus.obj L).obj
  have : K.IsStrictlyGE n := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι _).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) n
    rwa [CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff]
  have : ∀ i, Injective (K.X i) := fun i ↦ (L.obj.X i).2
  have : K.IsKInjective := CochainComplex.isKInjective_of_injective K n
  have : ((complexPushforward f).obj K).IsStrictlyGE n :=
    mapHomologicalComplex_isStrictlyGE _ K n inferInstance
  let e' : DerivedCategory.Q.obj K ≅ E :=
    (DerivedCategory.Plus.QCompιIso T.left.Modules).symm.app
      ((InjectiveObject.ι T.left.Modules).mapCochainComplexPlus.obj L) ≪≫
      DerivedCategory.Plus.ι.mapIso e
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((kInjectiveDerivedFunctorObjIso (modulePushforward f) K).symm ≪≫
      (ofKInjective f).functor.mapIso e') n

end RightDerivedPushforward

open RightDerivedPushforward

/-- **The higher direct images** `R^p f_* F = H^p(Rf_* F)` of a module sheaf `F` along `f`: the
`p`-th cohomology sheaf of the total direct image (Stacks, Section 20.28, Tag 079V) of `F`
placed in degree zero. -/
def higherDirectImage (f : T ⟶ U) (p : ℤ) : T.left.Modules ⥤ U.left.Modules :=
  DerivedCategory.singleFunctor _ 0 ⋙ (ofKInjective f).functor ⋙
    DerivedCategory.homologyFunctor _ p

instance (f : T ⟶ U) (p : ℤ) : (higherDirectImage f p).Additive := by
  dsimp only [higherDirectImage]
  infer_instance

/-- The higher direct images vanish in negative degrees. -/
theorem isZero_higherDirectImage_of_neg (f : T ⟶ U) (F : T.left.Modules) {p : ℤ} (hp : p < 0) :
    IsZero ((higherDirectImage f p).obj F) := by
  have := isGE_ofKInjective_obj f ((DerivedCategory.singleFunctor _ 0).obj F) 0
  exact DerivedCategory.isZero_of_isGE _ 0 p hp

/-- **The zeroth higher direct image is the direct image**: `R^0 f_* ≅ f_*`, because
pushforward of module sheaves is left exact. -/
def higherDirectImageZeroIso (f : T ⟶ U) : higherDirectImage f 0 ≅ modulePushforward f :=
  Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (kInjectiveDerivedFunctorPlusIso (modulePushforward f)) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (modulePushforward f).rightDerivedFunctorPlusHomologyZeroSingleNatIsoOfPreservesFiniteLimits

section LongExactSequence

variable (f : T ⟶ U) {X : ShortComplex T.left.Modules} (hX : X.ShortExact)

/-- The connecting map `R^p f_* X₃ ⟶ R^q f_* X₁`, `q = p + 1`, of the long exact sequence of
higher direct images attached to a short exact sequence `0 → X₁ → X₂ → X₃ → 0`. -/
def higherDirectImageδ (p q : ℤ) (hpq : p + 1 = q) :
    (higherDirectImage f p).obj X.X₃ ⟶ (higherDirectImage f q).obj X.X₁ :=
  DerivedCategory.HomologySequence.δ
    ((ofKInjective f).functor.mapTriangle.obj hX.singleTriangle) p q hpq

include hX

private theorem mapTriangle_singleTriangle_distinguished :
    (ofKInjective f).functor.mapTriangle.obj hX.singleTriangle ∈ distTriang _ :=
  (ofKInjective f).functor.map_distinguished _ hX.singleTriangle_distinguished

/-- The composite `R^p f_* X₂ ⟶ R^p f_* X₃ ⟶ R^{p+1} f_* X₁` vanishes. -/
@[reassoc (attr := simp)]
theorem higherDirectImage_map_comp_δ (p q : ℤ) (hpq : p + 1 = q) :
    (higherDirectImage f p).map X.g ≫ higherDirectImageδ f hX p q hpq = 0 :=
  DerivedCategory.HomologySequence.comp_δ _
    (mapTriangle_singleTriangle_distinguished f hX) p q hpq

/-- The composite `R^p f_* X₃ ⟶ R^{p+1} f_* X₁ ⟶ R^{p+1} f_* X₂` vanishes. -/
@[reassoc (attr := simp)]
theorem higherDirectImageδ_comp_map (p q : ℤ) (hpq : p + 1 = q) :
    higherDirectImageδ f hX p q hpq ≫ (higherDirectImage f q).map X.f = 0 :=
  DerivedCategory.HomologySequence.δ_comp _
    (mapTriangle_singleTriangle_distinguished f hX) p q hpq

/-- Exactness of `R^p f_* X₁ ⟶ R^p f_* X₂ ⟶ R^p f_* X₃`. -/
theorem higherDirectImage_exact₂ (p : ℤ) :
    (ShortComplex.mk ((higherDirectImage f p).map X.f) ((higherDirectImage f p).map X.g)
      (by rw [← Functor.map_comp, X.zero, Functor.map_zero])).Exact :=
  DerivedCategory.HomologySequence.exact₂ _ (mapTriangle_singleTriangle_distinguished f hX) p

/-- Exactness of `R^p f_* X₂ ⟶ R^p f_* X₃ ⟶ R^{p+1} f_* X₁`. -/
theorem higherDirectImage_exact₃ (p q : ℤ) (hpq : p + 1 = q) :
    (ShortComplex.mk _ _ (higherDirectImage_map_comp_δ f hX p q hpq)).Exact :=
  DerivedCategory.HomologySequence.exact₃ _ (mapTriangle_singleTriangle_distinguished f hX) p q hpq

/-- Exactness of `R^p f_* X₃ ⟶ R^{p+1} f_* X₁ ⟶ R^{p+1} f_* X₂`. -/
theorem higherDirectImage_exact₁ (p q : ℤ) (hpq : p + 1 = q) :
    (ShortComplex.mk _ _ (higherDirectImageδ_comp_map f hX p q hpq)).Exact :=
  DerivedCategory.HomologySequence.exact₁ _ (mapTriangle_singleTriangle_distinguished f hX) p q hpq

end LongExactSequence

variable {T' U' : SchemeBaseChange S} {f : T ⟶ U} {f' : T' ⟶ U'} {j : U' ⟶ U} {j' : T' ⟶ T}

/-- **Stacks, Lemma 20.7.4 (Tag 01E5)**: higher direct images commute with restriction to an
open of the target. For a pullback square of scheme base changes whose right edge `j` is an
open immersion, `j^* ∘ R^p f_* ≅ R^p f'_* ∘ j'^*`.

Restriction along the open immersions `j` and `j'` is exact, so it commutes with cohomology and
with the single functors, and the isomorphism is Tag 08FE,
`RightDerivedPushforward.ofKInjectiveRestrictIso`, on single objects. -/
@[stacks 01E5]
def higherDirectImageRestrictIso (sq : IsPullback f' j' j f) [IsOpenImmersion j.left] (p : ℤ) :
    higherDirectImage f p ⋙ modulePullback j ≅ modulePullback j' ⋙ higherDirectImage f' p :=
  haveI := isOpenImmersion_left_of_isPullback sq
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (mapDerivedCategoryHomologyFunctorIso (modulePullback j) p).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ofKInjectiveRestrictIso sq) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((modulePullback j').mapDerivedCategorySingleFunctor 0) _ ≪≫
    Functor.associator _ _ _

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
