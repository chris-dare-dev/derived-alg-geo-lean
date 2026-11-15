/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.Basic
import DerivedAlgGeo.CategoryTheory.Sites.LocallySurjective

/-!
# Global functions of an algebraic space

The ring of global functions `Γ(X, 𝒪_X)` of an algebraic space `X` over a scheme `S`, and the
correspondence between morphisms to affine schemes and ring maps into it (Stacks 05Z1). For an
étale atlas `U → X` with `R = U ×_X U`, `Γ(X, 𝒪_X)` is the equalizer of `Γ(U) ⇉ Γ(R)`. The atlas
presents `X` as the coequalizer of `R ⇉ U` in fppf sheaves (Stacks, Section 65.9), so morphisms
from `X` to `Spec A` are the morphisms `U ⟶ Spec A` that agree on `R`, which are the ring maps
`A ⟶ Γ(U)` that agree in `Γ(R)` (Stacks 01I1).

## Main definitions

* `AlgebraicGeometry.AlgebraicSpace.globalFunctions`: the ring `Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.AlgebraicSpace.globalFunctionsMap`: its contravariant functoriality.
* `AlgebraicGeometry.AlgebraicSpace.homSpecEquiv`: over a terminal base, morphisms
  `X ⟶ Spec A` are ring maps `A ⟶ Γ(X, 𝒪_X)` (Stacks 05Z1).
* `AlgebraicGeometry.AlgebraicSpace.homForgetSpecEquiv`: over any base, morphisms from `X` to the
  presheaf `T ↦ (T.left ⟶ Spec A)` are ring maps `A ⟶ Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.AlgebraicSpace.globalFunctionsOfAtlas`: the equalizer of `Γ(U) ⇉ Γ(R)` for an
  arbitrary étale atlas `U`.

## Main results

* `AlgebraicGeometry.AlgebraicSpace.homEquivOfAtlas`: morphisms from `X` to an fppf sheaf are the
  morphisms from an étale atlas `U` that agree on `R ⇉ U`.
* `AlgebraicGeometry.AlgebraicSpace.globalFunctionsIsoOfAtlas`: `Γ(X, 𝒪_X)` does not depend on the
  atlas, up to the canonical isomorphism compatible with `homForgetSpecEquiv`.
* `AlgebraicGeometry.AlgebraicSpace.globalFunctionsOfSchemeIso`: on a scheme `T`, `Γ(T, 𝒪_T)` is
  `Γ(T.left, ⊤)`, naturally in `T`.
* `AlgebraicGeometry.AlgebraicSpace.homSpecEquiv_naturality`,
  `AlgebraicGeometry.AlgebraicSpace.homSpecEquiv_naturality_right`: naturality of Stacks 05Z1.

## Implementation notes

**Presentation.** `globalFunctions X` is the atlas equalizer for an atlas chosen by
`Classical.choice`. Consumers should use `homForgetSpecEquiv`, `homSpecEquiv`,
`globalFunctionsIsoOfAtlas` and `globalFunctionsOfSchemeIso`, never the definition. The limit of
`Γ(T, ⊤)` over all points `T → X` would be indexed by a category in `Type (u+1)`, which
`CommRingCat.{u}` has no limits for; the atlas equalizer is the small presentation.

**Coequalizer property.** It is proved, not assumed. An atlas is locally surjective for the fppf
topology because its base changes to schemes are étale surjective, hence fppf covers; this is
`isLocallySurjective_of_etale_surjective`. Descent along locally surjective morphisms into a sheaf
(`CategoryTheory.Presheaf.descOfIsLocallySurjective`) then needs no sheafification, which is not
available for `Type u`-valued presheaves on `Over S`, and no section of `U → X`.

**Functoriality and independence.** Morphisms from `X` to the presheaf `T ↦ (T.left ⟶ Spec A)`
are ring maps `A ⟶ globalFunctions X`, naturally in `A`. `globalFunctionsMap`, the independence of
the atlas and the scheme case are read off from this universal property.

**Base.** `homForgetSpecEquiv` holds over every base. Over a terminal base the presheaf
`T ↦ (T.left ⟶ Spec A)` is the functor of points of the `S`-scheme `Spec A`
(`ofSchemeSpecIsoOfIsTerminal`), and `homSpecEquiv` is stated there. The relative form,
morphisms to an affine `S`-scheme as `Γ(S, 𝒪_S)`-algebra maps, is not proved here, nor is the
structure sheaf `𝒪_X` on the étale site of `X`.

## References

* [Stacks, Lemma 66.33.1 (Tag 05Z1)](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks, Lemma 26.6.4 (Tag 01I1)](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks, Section 65.9 (Tag 0261)](https://stacks.math.columbia.edu/tag/0261)

## Tags

algebraic space, global functions, affine scheme, étale atlas
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism from a scheme to a presheaf on `Over S` whose base changes to schemes are étale
and surjective is locally surjective for the fppf topology. -/
theorem isLocallySurjective_of_etale_surjective {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S}
    {p : yoneda.obj U ⟶ F}
    (hp : (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf p) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p where
  imageSieve_mem {T} x := by
    let g : yoneda.obj T ⟶ F := yonedaEquiv.symm x
    obtain ⟨h₁, h₂⟩ := hp.property_snd g
    refine GrothendieckTopology.superset_covering _ ?_ (?_ :
      Sieve.ofArrows (fun _ : PUnit.{1} ↦ hp.rep.pullback g) (fun _ ↦ hp.rep.snd g) ∈ _)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      refine ⟨hp.rep.fst' g, ?_⟩
      have := congrArg yonedaEquiv (hp.rep.w g)
      rwa [← hp.rep.map_fst', yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply] at this
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows, Sieve.ofArrows,
        Presieve.ofArrows_pUnit]
      have : Etale (hp.rep.snd g).left := h₁
      have : Surjective (hp.rep.snd g).left := h₂
      exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _)

/-- The presheaf `T ↦ (T.left ⟶ Spec A)` is an fppf sheaf on `Over S`. -/
private theorem isSheaf_forget_comp_yoneda_Spec (A : CommRingCat.{u}) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) ((Over.forget S).op ⋙ yoneda.obj (Spec A)) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Scheme.fppfTopology.yoneda.obj (Spec A)).over S).property

/-- Morphisms from a scheme `Y` to `Spec A` are ring maps `A ⟶ Γ(Y, ⊤)` (Stacks 01I1), through the
`Γ ⊣ Spec` adjunction. -/
private noncomputable def homSpecRingEquiv (Y : Scheme.{u}) (A : CommRingCat.{u}) :
    (Y ⟶ Spec A) ≃ (A ⟶ Γ(Y, ⊤)) where
  toFun g := (Scheme.ΓSpecIso A).inv ≫ g.appTop
  invFun φ := ΓSpec.adjunction.homEquiv Y (op A) φ.op
  left_inv g := ext_to_Spec (R := A) (by
    simp only [Scheme.Γ_map_op]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _)
  right_inv φ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

private lemma homSpecRingEquiv_apply (Y : Scheme.{u}) (A : CommRingCat.{u}) (g : Y ⟶ Spec A) :
    homSpecRingEquiv Y A g = (Scheme.ΓSpecIso A).inv ≫ g.appTop :=
  rfl

section Atlas

variable {X : AlgebraicSpace S} {U : Over S} {p : yoneda.obj U ⟶ X.obj}
  (hp : (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf p)

/-- Morphisms from an algebraic space `X` to an fppf sheaf `F` are the morphisms from an étale
atlas `U` that agree on the two projections `U ×_X U ⇉ U`: the atlas presents `X` as a coequalizer
in fppf sheaves (Stacks, Section 65.9). -/
noncomputable def homEquivOfAtlas {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F) :
    (X.obj ⟶ F) ≃ {φ : yoneda.obj U ⟶ F //
      yoneda.map (hp.rep.fst' p) ≫ φ = yoneda.map (hp.rep.snd p) ≫ φ} :=
  have := isLocallySurjective_of_etale_surjective hp
  { toFun ψ := ⟨p ≫ ψ, by simp only [← Category.assoc, (hp.rep.isPullback' p).w]⟩
    invFun φ := Presheaf.descOfIsLocallySurjective p hF φ.1 fun T a b hab ↦ by
      have hab' : yoneda.map a ≫ p = yoneda.map b ≫ p := yonedaEquiv.injective (by
        rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
        exact hab)
      have := congrArg yonedaEquiv
        ((hp.rep.isPullback' p).lift (yoneda.map a) (yoneda.map b) hab' ≫= φ.2)
      rw [IsPullback.lift_fst_assoc, IsPullback.lift_snd_assoc, yonedaEquiv_comp,
        yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at this
      exact this
    left_inv ψ := Presheaf.hom_ext_of_isLocallySurjective p hF (by simp)
    right_inv φ := Subtype.ext (by simp) }

@[simp]
lemma homEquivOfAtlas_apply_coe {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F) (ψ : X.obj ⟶ F) :
    (homEquivOfAtlas hp hF ψ).1 = p ≫ ψ :=
  rfl

/-- The ring of functions on an étale atlas `U` of an algebraic space that agree on the two
projections `U ×_X U ⇉ U`: the equalizer of `Γ(U) ⇉ Γ(U ×_X U)`. -/
noncomputable abbrev globalFunctionsOfAtlas : CommRingCat.{u} :=
  equalizer (hp.rep.fst' p).left.appTop (hp.rep.snd p).left.appTop

/-- Morphisms from an algebraic space `X` to the sheaf `T ↦ (T.left ⟶ Spec A)` are ring maps from
`A` to the equalizer of `Γ(U) ⇉ Γ(U ×_X U)` for an étale atlas `U` (Stacks 05Z1). -/
noncomputable def homForgetSpecEquivOfAtlas (A : CommRingCat.{u}) :
    (X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) ≃ (A ⟶ globalFunctionsOfAtlas hp) :=
  (homEquivOfAtlas hp (isSheaf_forget_comp_yoneda_Spec A)).trans <|
    (Equiv.subtypeEquiv (yonedaEquiv.trans (homSpecRingEquiv U.left A)) fun φ ↦ by
      rw [← yonedaEquiv.apply_eq_iff_eq, ← yonedaEquiv_naturality, ← yonedaEquiv_naturality,
        ← (homSpecRingEquiv (hp.rep.pullback p).left A).apply_eq_iff_eq]
      simp [homSpecRingEquiv_apply]).trans
      (Fork.IsLimit.homIso (equalizerIsEqualizer _ _) A).symm

@[reassoc (attr := simp)]
lemma homForgetSpecEquivOfAtlas_comp_ι (A : CommRingCat.{u})
    (ψ : X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) :
    homForgetSpecEquivOfAtlas hp A ψ ≫ equalizer.ι _ _ =
      (Scheme.ΓSpecIso A).inv ≫ (yonedaEquiv (p ≫ ψ)).appTop :=
  (Fork.IsLimit.lift' (equalizerIsEqualizer _ _)
    ((Scheme.ΓSpecIso A).inv ≫ (yonedaEquiv (p ≫ ψ)).appTop) _).2

/-- `AlgebraicSpace.homForgetSpecEquivOfAtlas` is natural in the ring. -/
lemma homForgetSpecEquivOfAtlas_naturality {A B : CommRingCat.{u}} (h : A ⟶ B)
    (ψ : X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec B)) :
    homForgetSpecEquivOfAtlas hp A
        (ψ ≫ Functor.whiskerLeft (Over.forget S).op (yoneda.map (Spec.map h))) =
      h ≫ homForgetSpecEquivOfAtlas hp B ψ := by
  apply equalizer.hom_ext
  rw [homForgetSpecEquivOfAtlas_comp_ι, Category.assoc, homForgetSpecEquivOfAtlas_comp_ι,
    ← Category.assoc p, yonedaEquiv_comp, Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

end Atlas

section Corepresentation

variable {G : (Over S)ᵒᵖ ⥤ Type u} {R R' : CommRingCat.{u}}
  (e : ∀ A : CommRingCat.{u}, (G ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) ≃ (A ⟶ R))
  (e' : ∀ A : CommRingCat.{u}, (G ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) ≃ (A ⟶ R'))
  (he : ∀ {A B : CommRingCat.{u}} (h : A ⟶ B) ψ,
    e A (ψ ≫ Functor.whiskerLeft (Over.forget S).op (yoneda.map (Spec.map h))) = h ≫ e B ψ)
  (he' : ∀ {A B : CommRingCat.{u}} (h : A ⟶ B) ψ,
    e' A (ψ ≫ Functor.whiskerLeft (Over.forget S).op (yoneda.map (Spec.map h))) = h ≫ e' B ψ)

include he in
private lemma symm_comp {A B : CommRingCat.{u}} (h : A ⟶ B) (k : B ⟶ R) :
    (e A).symm (h ≫ k) =
      (e B).symm k ≫ Functor.whiskerLeft (Over.forget S).op (yoneda.map (Spec.map h)) := by
  rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]

include he he' in
/-- Two rings through which morphisms from `G` to the sheaves `T ↦ (T.left ⟶ Spec A)` factor
naturally in `A` are isomorphic. -/
private noncomputable def isoOfHomForgetSpecEquiv : R ≅ R' :=
  Yoneda.ext R R' (fun f ↦ e' _ ((e _).symm f)) (fun f ↦ e _ ((e' _).symm f)) (by simp) (by simp)
    fun f g ↦ by rw [symm_comp e he, he']

include he he' in
private lemma comp_isoOfHomForgetSpecEquiv_hom (A : CommRingCat.{u})
    (ψ : G ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) :
    e A ψ ≫ (isoOfHomForgetSpecEquiv e e' he he').hom = e' A ψ := by
  change e A ψ ≫ e' R ((e R).symm (𝟙 R)) = e' A ψ
  rw [← he', ← symm_comp e he, Category.comp_id, Equiv.symm_apply_apply]

end Corepresentation

/-- The étale atlas of `X` chosen by `AlgebraicGeometry.isAlgebraicSpace`. -/
private lemma chosenAtlas (X : AlgebraicSpace S) :
    (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf
      X.property.2.2.choose_spec.choose :=
  X.property.2.2.choose_spec.choose_spec

/-- The ring of global functions `Γ(X, 𝒪_X)` of an algebraic space: the equalizer of
`Γ(U) ⇉ Γ(U ×_X U)` for an étale atlas `U` chosen by `Classical.choice`. Use
`AlgebraicSpace.homForgetSpecEquiv`, `AlgebraicSpace.globalFunctionsIsoOfAtlas` and
`AlgebraicSpace.globalFunctionsOfSchemeIso` rather than this definition. -/
noncomputable def globalFunctions (X : AlgebraicSpace S) : CommRingCat.{u} :=
  globalFunctionsOfAtlas (chosenAtlas X)

/-- Morphisms from an algebraic space `X` to the sheaf `T ↦ (T.left ⟶ Spec A)` are ring maps
`A ⟶ Γ(X, 𝒪_X)` (Stacks 05Z1). -/
noncomputable def homForgetSpecEquiv (X : AlgebraicSpace S) (A : CommRingCat.{u}) :
    (X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) ≃ (A ⟶ globalFunctions X) :=
  homForgetSpecEquivOfAtlas (chosenAtlas X) A

/-- `AlgebraicSpace.homForgetSpecEquiv` is natural in the ring. -/
lemma homForgetSpecEquiv_naturality (X : AlgebraicSpace S) {A B : CommRingCat.{u}} (h : A ⟶ B)
    (ψ : X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec B)) :
    homForgetSpecEquiv X A
        (ψ ≫ Functor.whiskerLeft (Over.forget S).op (yoneda.map (Spec.map h))) =
      h ≫ homForgetSpecEquiv X B ψ :=
  homForgetSpecEquivOfAtlas_naturality _ h ψ

section Atlas

variable {X : AlgebraicSpace S} {U : Over S} {p : yoneda.obj U ⟶ X.obj}
  (hp : (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf p)

/-- `Γ(X, 𝒪_X)` does not depend on the chosen atlas: it is canonically isomorphic to the equalizer
of `Γ(U) ⇉ Γ(U ×_X U)` for every étale atlas `U`. -/
noncomputable def globalFunctionsIsoOfAtlas : globalFunctions X ≅ globalFunctionsOfAtlas hp :=
  isoOfHomForgetSpecEquiv (homForgetSpecEquiv X) (homForgetSpecEquivOfAtlas hp)
    (homForgetSpecEquiv_naturality X) (homForgetSpecEquivOfAtlas_naturality hp)

@[reassoc (attr := simp)]
lemma comp_globalFunctionsIsoOfAtlas_hom (A : CommRingCat.{u})
    (ψ : X.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) :
    homForgetSpecEquiv X A ψ ≫ (globalFunctionsIsoOfAtlas hp).hom =
      homForgetSpecEquivOfAtlas hp A ψ :=
  comp_isoOfHomForgetSpecEquiv_hom _ _ (homForgetSpecEquiv_naturality X)
    (homForgetSpecEquivOfAtlas_naturality hp) A ψ

end Atlas

/-- The map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` induced by a morphism of algebraic spaces `f : X ⟶ Y`. -/
noncomputable def globalFunctionsMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    globalFunctions Y ⟶ globalFunctions X :=
  homForgetSpecEquiv X _ (f.hom ≫ (homForgetSpecEquiv Y _).symm (𝟙 _))

/-- `AlgebraicSpace.homForgetSpecEquiv` is natural in the algebraic space. -/
lemma homForgetSpecEquiv_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y) {A : CommRingCat.{u}}
    (ψ : Y.obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) :
    homForgetSpecEquiv X A (f.hom ≫ ψ) = homForgetSpecEquiv Y A ψ ≫ globalFunctionsMap f := by
  conv_lhs => rw [← (homForgetSpecEquiv Y A).symm_apply_apply ψ,
    ← Category.comp_id (homForgetSpecEquiv Y A ψ),
    symm_comp _ (homForgetSpecEquiv_naturality Y), ← Category.assoc,
    homForgetSpecEquiv_naturality]
  rfl

@[simp]
lemma globalFunctionsMap_id (X : AlgebraicSpace S) : globalFunctionsMap (𝟙 X) = 𝟙 _ := by
  simp [globalFunctionsMap]

@[simp]
lemma globalFunctionsMap_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    globalFunctionsMap (f ≫ g) = globalFunctionsMap g ≫ globalFunctionsMap f := by
  rw [globalFunctionsMap, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    homForgetSpecEquiv_comp]
  rfl

/-- On a scheme `T` over `S`, `Γ(T, 𝒪_T)` is the ring of global sections `Γ(T.left, ⊤)`. -/
noncomputable def globalFunctionsOfSchemeIso (T : Over S) :
    globalFunctions ((ofScheme S).obj T) ≅ T.left.presheaf.obj (op ⊤) :=
  isoOfHomForgetSpecEquiv (homForgetSpecEquiv _)
    (fun A ↦ (yonedaEquiv.trans (homSpecRingEquiv T.left A) :
      (((ofScheme S).obj T).obj ⟶ _) ≃ _))
    (homForgetSpecEquiv_naturality _)
    fun h _ ↦ (Scheme.ΓSpecIso_inv_naturality_assoc h _).symm

@[reassoc (attr := simp)]
lemma comp_globalFunctionsOfSchemeIso_hom (T : Over S) (A : CommRingCat.{u})
    (ψ : ((ofScheme S).obj T).obj ⟶ (Over.forget S).op ⋙ yoneda.obj (Spec A)) :
    homForgetSpecEquiv ((ofScheme S).obj T) A ψ ≫ (globalFunctionsOfSchemeIso T).hom =
      (Scheme.ΓSpecIso A).inv ≫ (yonedaEquiv (X := T) ψ).appTop :=
  comp_isoOfHomForgetSpecEquiv_hom _ _ (homForgetSpecEquiv_naturality _)
    (fun h _ ↦ (Scheme.ΓSpecIso_inv_naturality_assoc h _).symm) A ψ

/-- `AlgebraicSpace.globalFunctionsOfSchemeIso` is natural: on schemes, `globalFunctionsMap` is
the pullback of global sections. -/
lemma globalFunctionsOfSchemeIso_hom_naturality {T T' : Over S} (f : T ⟶ T') :
    globalFunctionsMap ((ofScheme S).map f) ≫ (globalFunctionsOfSchemeIso T).hom =
      (globalFunctionsOfSchemeIso T').hom ≫ f.left.appTop := by
  have h₀ := (homForgetSpecEquiv ((ofScheme S).obj T') _).apply_symm_apply (𝟙 _)
  rw [← Category.id_comp (globalFunctionsMap _), ← h₀, ← homForgetSpecEquiv_comp,
    comp_globalFunctionsOfSchemeIso_hom]
  conv_rhs => rw [← Category.id_comp (globalFunctionsOfSchemeIso T').hom, ← h₀,
    comp_globalFunctionsOfSchemeIso_hom, Category.assoc,
    ← Scheme.Hom.comp_appTop]
  exact congrArg _ (congrArg Scheme.Hom.appTop (yonedaEquiv_naturality (X := T') _ f).symm)

/-- Over a terminal base, the algebraic space `Spec A` is the presheaf `T ↦ (T.left ⟶ Spec A)`. -/
noncomputable def ofSchemeSpecIsoOfIsTerminal (hS : IsTerminal S) (A : CommRingCat.{u}) :
    ((ofScheme S).obj (Over.mk (hS.from (Spec A)))).obj ≅
      (Over.forget S).op ⋙ yoneda.obj (Spec A) :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun g := g.left
      invFun g := Over.homMk g (hS.hom_ext _ _)
      left_inv _ := by cat_disch
      right_inv _ := rfl }) fun _ ↦ rfl

/-- **Stacks 05Z1**: over a terminal base `S`, such as `Spec ℤ`, morphisms from an algebraic space
`X` to `Spec A` are ring maps `A ⟶ Γ(X, 𝒪_X)`, naturally in `X` and `A`.

Only the absolute form is stated: over a non-terminal base, morphisms to an affine `S`-scheme as
maps of `Γ(S, 𝒪_S)`-algebras are not proved here. -/
noncomputable def homSpecEquiv (hS : IsTerminal S) (X : AlgebraicSpace S) (A : CommRingCat.{u}) :
    (X ⟶ (ofScheme S).obj (Over.mk (hS.from (Spec A)))) ≃ (A ⟶ globalFunctions X) where
  toFun g := homForgetSpecEquiv X A (g.hom ≫ (ofSchemeSpecIsoOfIsTerminal hS A).hom)
  invFun k := ObjectProperty.homMk
    ((homForgetSpecEquiv X A).symm k ≫ (ofSchemeSpecIsoOfIsTerminal hS A).inv)
  left_inv g := by ext1; simp
  right_inv k := by simp

lemma homSpecEquiv_apply (hS : IsTerminal S) (X : AlgebraicSpace S) (A : CommRingCat.{u})
    (g : X ⟶ (ofScheme S).obj (Over.mk (hS.from (Spec A)))) :
    homSpecEquiv hS X A g =
      homForgetSpecEquiv X A (g.hom ≫ (ofSchemeSpecIsoOfIsTerminal hS A).hom) :=
  rfl

/-- Stacks 05Z1 is natural in the algebraic space. -/
theorem homSpecEquiv_naturality (hS : IsTerminal S) {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : CommRingCat.{u}) (g : Y ⟶ (ofScheme S).obj (Over.mk (hS.from (Spec A)))) :
    homSpecEquiv hS X A (f ≫ g) = homSpecEquiv hS Y A g ≫ globalFunctionsMap f := by
  rw [homSpecEquiv_apply, homSpecEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc, homForgetSpecEquiv_comp]

/-- Stacks 05Z1 is natural in the ring. -/
theorem homSpecEquiv_naturality_right (hS : IsTerminal S) (X : AlgebraicSpace S)
    {A B : CommRingCat.{u}} (h : A ⟶ B) (g : X ⟶ (ofScheme S).obj (Over.mk (hS.from (Spec B)))) :
    homSpecEquiv hS X A (g ≫ (ofScheme S).map (Over.homMk (Spec.map h) (hS.hom_ext _ _))) =
      h ≫ homSpecEquiv hS X B g := by
  rw [homSpecEquiv_apply, homSpecEquiv_apply, ← homForgetSpecEquiv_naturality]
  rfl

end AlgebraicGeometry.AlgebraicSpace
