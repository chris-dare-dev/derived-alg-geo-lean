/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Effective descent is local

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a stack for a Grothendieck topology `J₀` and a
prestack for a Grothendieck topology `J`, and let `R` be a `J`-covering sieve on `S`. If `F`
has effective descent along the pullback of `R` to every member of a `J₀`-covering family
`v i : V i ⟶ S`, then `F` has effective descent along `R`. No relation between `J₀` and `J`
is assumed.

Effective descent along a sieve also only depends on the sieve up to local equality: if
`R₁ ≤ R₂` and `F` has effective descent along the pullback of `R₁` along every arrow of
`R₂`, then `F` has effective descent along `R₁` if and only if it has effective descent
along `R₂`. No topology is involved.

## Main definitions

None. The descent data and comparisons built in the proofs are private to this file.

## Main results

* `CategoryTheory.Pseudofunctor.isStackFor_of_isStackFor_pullback`
* `CategoryTheory.Pseudofunctor.isStackFor_iff_of_le_of_isStackFor_pullback`

## Implementation notes

Let `T` be the family of the arrows `c ≫ v i` with `c ≫ v i` in `R`, indexed by such
factorizations. Its sieve is contained in `R` and is covering for the topology of the sieves
along every pullback of which `F` is a prestack; that topology contains `J` and `J₀`. By
Mathlib's `Pseudofunctor.IsStackFor.of_le` it suffices to show that descent is effective
along `T`.

A descent datum `E` along `T` restricts to a descent datum along `R.pullback (v i)` for each
`i`, which descends to `x i` over `V i`. Over an arrow `q` of `S` that factors as `a ≫ v i`
and as `b ≫ v j`, the comparisons between the pullbacks of `x i` and `x j` are read off
from `E` on the arrows of `R.pullback q` and glued, since `F` is a `J`-prestack. They form a
descent datum along `v`, which the `J₀`-stack condition descends to an object over `S` whose
descent datum along `T` is `E`. Morphisms are handled throughout through `pullHom`, so that
no pullbacks need to exist in `C`. The gluing only uses that `F` is a prestack for the
pullback of `R` along the arrows that factor through `v`.

For `R₁ ≤ R₂`, the restriction functor from descent data along `R₂` to descent data along
`R₁` is fully faithful as soon as `F` is a prestack for the pullback of `R₁` along every arrow
of `R₂`; this generalizes Mathlib's `DescentData.fullyFaithfulPullFunctor`, which assumes `R₁`
covering for a topology for which `F` is a prestack. Effectivity along `R₁` follows from
effectivity along `R₂` by the gluing above, with `v` the family of the arrows of `R₂`.

## References

* A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*,
  arXiv:math/0412512v4, Lemma 4.25, Steps 2 and 5.
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)

## Tags

descent, stack, effective descent, local on the base
-/

universe t t' v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- `pullHom` of a composite is the composite of the `pullHom`s. -/
private lemma pullHom_comp' ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

/-- `pullHom` respects equality of the morphism being pulled back. -/
private lemma pullHom_congr ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (h : φ = φ') ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂ := by
  subst h
  rfl

/-- `pullHom` of an identity morphism is an identity morphism. -/
private lemma pullHom_id_hom ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ (f₁ : Y ⟶ X₁)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

/-- `pullHom` of a morphism into an object over the source of `f₁`, read through `mapId`. -/
private lemma pullHom_comp_mapId_inv ⦃X₁ Y : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ {f₁ : Y ⟶ X₁}
    {N : F.obj (.mk (op Y))} (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ N)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (f₂ := 𝟙 Y) (φ ≫ (F.mapId _).inv.toNatTrans.app N) g gf₁ g hgf₁ (by simp) =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.toNatTrans.app M₁ ≫
        (F.map g.op.toLoc).toFunctor.map φ := by
  simp [pullHom, mapComp'_id_comp_inv_app, ← Functor.map_comp]

section Glue

variable {W X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
  {f₁ : W ⟶ X₁} {f₂ : W ⟶ X₂}

variable (M₁ M₂ f₁ f₂) in
/-- Sections of the presheaf of morphisms between `f₁^* M₁` and `f₂^* M₂` over `y : Y ⟶ W`,
as morphisms `(y ≫ f₁)^* M₁ ⟶ (y ≫ f₂)^* M₂`. -/
private def conjHom {Y : C} (y : Y ⟶ W) :
    ((F.map y.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj M₂)) ≃
    ((F.map (y ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (y ≫ f₂).op.toLoc).toFunctor.obj M₂) :=
  Iso.homCongr
    ((Cat.Hom.toNatIso (F.mapComp' f₁.op.toLoc y.op.toLoc (y ≫ f₁).op.toLoc)).app M₁).symm
    ((Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc y.op.toLoc (y ≫ f₂).op.toLoc)).app M₂).symm

/-- `conjHom` of a pulled-back morphism is its `pullHom`. -/
private lemma conjHom_map {Y : C} (y : Y ⟶ W)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    conjHom M₁ M₂ f₁ f₂ y ((F.map y.op.toLoc).toFunctor.map φ) =
      pullHom φ y (y ≫ f₁) (y ≫ f₂) :=
  rfl

/-- `conjHom` intertwines the restriction maps of the presheaf of morphisms with
`pullHom`. -/
private lemma conjHom_pullHom {Y Z : C} (y : Y ⟶ W) (z : Z ⟶ Y) (zy : Z ⟶ W)
    (hzy : z ≫ y = zy)
    (s : (F.map y.op.toLoc).toFunctor.obj ((F.map f₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map f₂.op.toLoc).toFunctor.obj M₂)) :
    conjHom M₁ M₂ f₁ f₂ zy (pullHom s z zy zy) =
      pullHom (conjHom M₁ M₂ f₁ f₂ y s) z (zy ≫ f₁) (zy ≫ f₂) (by simp [← hzy])
        (by simp [← hzy]) := by
  subst hzy
  simp only [conjHom, pullHom, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  have h₁ := F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app f₁.op.toLoc y.op.toLoc
    z.op.toLoc (y ≫ f₁).op.toLoc (z ≫ y).op.toLoc ((z ≫ y) ≫ f₁).op.toLoc (by aesop) (by aesop)
    (by aesop) M₁
  have h₂ := F.whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv_app f₂.op.toLoc y.op.toLoc
    z.op.toLoc (y ≫ f₂).op.toLoc (z ≫ y).op.toLoc ((z ≫ y) ≫ f₂).op.toLoc (by aesop) (by aesop)
    (by aesop) M₂
  simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv] at *
  rw [reassoc_of% h₁, h₂]

/-- Restricting the section of the presheaf of morphisms given by `φ` along `y` is pulling
`φ` back along `y`. -/
private lemma presheafHom_map_presheafHomObjHomEquiv {N₁ N₂ : F.obj (.mk (op W))}
    (φ : N₁ ⟶ N₂) {Y : C} (y : Y ⟶ W) :
    (F.presheafHom N₁ N₂).map (Over.homMk y : Over.mk y ⟶ Over.mk (𝟙 W)).op
      (F.presheafHomObjHomEquiv φ) = (F.map y.op.toLoc).toFunctor.map φ := by
  change pullHom (F.presheafHomObjHomEquiv φ) y y y = _
  simp only [presheafHomObjHomEquiv_apply]
  simp [pullHom, mapComp'_id_comp_hom_app, mapComp'_id_comp_inv_app, ← Functor.map_comp]

/-- Morphisms `f₁^* M₁ ⟶ f₂^* M₂` that agree after pullback along every arrow of a sieve
along which `F` is a prestack agree. -/
private lemma pullHom_ext {U : Sieve W} (hU : F.IsPrestackFor U.arrows)
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (h : ∀ ⦃Y : C⦄ (y : Y ⟶ W), U y →
      pullHom φ y (y ≫ f₁) (y ≫ f₂) = pullHom φ' y (y ≫ f₁) (y ≫ f₂)) :
    φ = φ' := by
  apply F.presheafHomObjHomEquiv.injective
  refine (((F.isPrestackFor_iff_isSheafFor U).1 hU _ _).isSeparatedFor).ext fun T g hg ↦ ?_
  obtain ⟨Y, y, rfl⟩ := T.mk_surjective
  obtain rfl : g = Over.homMk y := by ext; simpa using Over.w g
  rw [presheafHom_map_presheafHomObjHomEquiv, presheafHom_map_presheafHomObjHomEquiv]
  apply (conjHom M₁ M₂ f₁ f₂ y).injective
  rw [conjHom_map, conjHom_map]
  exact h y hg

/-- A family of morphisms `(y ≫ f₁)^* M₁ ⟶ (y ≫ f₂)^* M₂` indexed by the arrows of a sieve
along which `F` is a prestack, compatible with pullbacks, glues to a morphism
`f₁^* M₁ ⟶ f₂^* M₂`. -/
private lemma exists_pullHom_eq {U : Sieve W} (hU : F.IsPrestackFor U.arrows)
    (Φ : ∀ ⦃Y : C⦄ (y : Y ⟶ W), U y →
      ((F.map (y ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶ (F.map (y ≫ f₂).op.toLoc).toFunctor.obj M₂))
    (hΦ : ∀ ⦃Y Z : C⦄ (y : Y ⟶ W) (hy : U y) (z : Z ⟶ Y),
      pullHom (Φ y hy) z ((z ≫ y) ≫ f₁) ((z ≫ y) ≫ f₂) (by simp) (by simp) =
        Φ (z ≫ y) (U.downward_closed hy z)) :
    ∃ φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂,
      ∀ ⦃Y : C⦄ (y : Y ⟶ W) (hy : U y), pullHom φ y (y ≫ f₁) (y ≫ f₂) = Φ y hy := by
  have mem : ∀ {T : Over W} (g : T ⟶ Over.mk (𝟙 W)),
      (Sieve.overEquiv (Over.mk (𝟙 W))).symm U g → U T.hom := fun {T} g hg ↦ by
    have h : g.left = T.hom := by simpa using Over.w g
    rw [← h]
    exact hg
  let x : Presieve.FamilyOfElements (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M₁)
      ((F.map f₂.op.toLoc).toFunctor.obj M₂)) ((Sieve.overEquiv (Over.mk (𝟙 W))).symm U).arrows :=
    fun T g hg ↦ (conjHom M₁ M₂ f₁ f₂ T.hom).symm (Φ T.hom (mem g hg))
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T T' g u hg
    apply (conjHom M₁ M₂ f₁ f₂ T'.hom).injective
    dsimp only [x]
    rw [Equiv.apply_symm_apply]
    change _ = conjHom M₁ M₂ f₁ f₂ T'.hom (pullHom _ u.left T'.hom T'.hom (Over.w u) (Over.w u))
    rw [conjHom_pullHom T.hom u.left T'.hom (Over.w u), Equiv.apply_symm_apply]
    have key : ∀ (y' : T'.left ⟶ W) (hy' : u.left ≫ T.hom = y') (h' : U y'), Φ y' h' =
        pullHom (Φ T.hom (mem g hg)) u.left (y' ≫ f₁) (y' ≫ f₂) (by simp [← hy'])
          (by simp [← hy']) := by
      rintro _ rfl _
      exact (hΦ _ _ u.left).symm
    exact key _ (Over.w u) _
  obtain ⟨σ, hσ, -⟩ := (F.isPrestackFor_iff_isSheafFor U).1 hU _ _ x hx
  refine ⟨F.presheafHomObjHomEquiv.symm σ, fun Y y hy ↦ ?_⟩
  rw [← conjHom_map, ← presheafHom_map_presheafHomObjHomEquiv, Equiv.apply_symm_apply,
    hσ (Over.homMk y : Over.mk y ⟶ Over.mk (𝟙 W)) hy]
  exact Equiv.apply_symm_apply _ _

end Glue

section PrestackTopology

variable (F)

/-- The Grothendieck topology of the sieves along every pullback of which `F` is a prestack. -/
private def prestackTopology : GrothendieckTopology C where
  sieves S := {R | ∀ ⦃Y : C⦄ (g : Y ⟶ S), F.IsPrestackFor (R.pullback g).arrows}
  top_mem' S Y g := by
    rw [Sieve.pullback_top, isPrestackFor_iff_isSheafFor]
    intro M N
    rw [show (Sieve.overEquiv (Over.mk (𝟙 Y))).symm ⊤ = ⊤ from OrderIso.map_top _]
    exact Presieve.isSheafFor_top _
  pullback_stable' S Y R f hR Z g := by
    rw [← Sieve.pullback_comp]
    exact hR (g ≫ f)
  transitive' S R hR U hU Y g := by
    rw [isPrestackFor_iff_isSheafFor]
    intro M N
    refine Presieve.isSheafFor_trans (F.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm (R.pullback g)) _
      ((F.isPrestackFor_iff_isSheafFor _).1 (hR g) M N) (fun T f _ ↦ ?_) (fun T f hf ↦ ?_)
    · refine (IsPrestackFor.isSheafFor' T ?_ M N).isSeparatedFor
      rw [Sieve.overEquiv_pullback, OrderIso.apply_symm_apply, ← Sieve.pullback_comp]
      exact hR _
    · refine IsPrestackFor.isSheafFor' T ?_ M N
      rw [Sieve.overEquiv_pullback, OrderIso.apply_symm_apply, ← Sieve.pullback_comp]
      simpa using hU (show R (f.left ≫ g) from hf) (𝟙 _)

/-- `F` is a prestack for `prestackTopology F`. -/
private lemma isPrestack_prestackTopology : F.IsPrestack (prestackTopology F) :=
  IsPrestack.of_isPrestackFor fun S R hR ↦ by simpa using hR (𝟙 S)

/-- A topology for which `F` is a prestack is contained in `prestackTopology F`. -/
private lemma le_prestackTopology (J : GrothendieckTopology C) [F.IsPrestack J] :
    J ≤ prestackTopology F :=
  fun _ _ hR _ g ↦ F.isPrestackFor' _ (J.pullback_stable g hR)

end PrestackTopology

section DescentHom

variable {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- The compatibility of a family of morphisms out of the pullbacks of `M` with a descent
datum `D`, rewritten with `pullHom`. -/
private lemma toDescentData_comm_iff {M : F.obj (.mk (op S))} {D : F.DescentData f}
    (φ : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ⟶ D.obj i) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (φ i₁) ≫ D.hom q f₁ f₂ hf₁ hf₂ =
        ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ ≫
          (F.map f₂.op.toLoc).toFunctor.map (φ i₂) ↔
      pullHom (f₂ := 𝟙 _) (φ i₁ ≫ (F.mapId _).inv.toNatTrans.app _) f₁ q f₁ hf₁ (by simp) ≫
          D.hom q f₁ f₂ hf₁ hf₂ =
        pullHom (f₂ := 𝟙 _) (φ i₂ ≫ (F.mapId _).inv.toNatTrans.app _) f₂ q f₂ hf₂ (by simp) := by
  have hM : ((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app M ≫
        (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app M :=
    rfl
  rw [pullHom_comp_mapId_inv, pullHom_comp_mapId_inv, hM]
  let c₁ := (Cat.Hom.toNatIso (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
    (by grind))).app M
  constructor
  · intro H
    exact (Category.assoc _ _ _).trans ((congrArg (c₁.hom ≫ ·)
      (H.trans (Category.assoc _ _ _))).trans (c₁.hom_inv_id_assoc _))
  · intro H
    exact (c₁.inv_hom_id_assoc _).symm.trans ((congrArg (c₁.inv ≫ ·)
      ((Category.assoc _ _ _).symm.trans H)).trans (Category.assoc _ _ _).symm)

/-- The components of an isomorphism of descent data. -/
private def DescentData.isoApp {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by rw [← DescentData.comp_hom, e.hom_inv_id, DescentData.id_hom]
  inv_hom_id := by rw [← DescentData.comp_hom, e.inv_hom_id, DescentData.id_hom]

end DescentHom

section Local

variable {ι : Type t} {S : C} {V : ι → C} (v : ∀ i, V i ⟶ S) (R : Sieve S)

/-- The arrows `c : Y ⟶ V i` of `R.pullback (v i)`, that is, with `c ≫ v i` in `R`. -/
private abbrev BlockIdx (i : ι) := Σ Y : C, {c : Y ⟶ V i // R (c ≫ v i)}

/-- The arrows of `R` that factor through some `v i`, indexed by such a factorization. -/
private abbrev LocalIdx := Σ i, BlockIdx v R i

/-- The family of arrows of `R` that factor through some `v i`. -/
private abbrev localFamily (k : LocalIdx v R) : k.2.1 ⟶ S := k.2.2.1 ≫ v k.1

variable {v R}

/-- The restriction of a descent datum for `localFamily v R` to the arrows factoring through
`v i`, as a descent datum relative to `V i`. -/
private def blockDescentData (E : F.DescentData (localFamily v R)) (i : ι) :
    F.DescentData (fun (k : BlockIdx v R i) ↦ k.2.1) where
  obj k := E.obj ⟨i, k⟩
  hom Y q k₁ k₂ f₁ f₂ hf₁ hf₂ := E.hom (q ≫ v i) (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂
    (by rw [← hf₁, Category.assoc]) (by rw [← hf₂, Category.assoc])
  pullHom_hom Y' Y g q q' hq k₁ k₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    E.pullHom_hom g (q ≫ v i) (q' ≫ v i) (by rw [← hq, Category.assoc])
      (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂
      (by rw [← hf₁, Category.assoc]) (by rw [← hf₂, Category.assoc]) gf₁ gf₂ hgf₁ hgf₂
  hom_self Y q k g hg := E.hom_self (q ≫ v i) (i := ⟨i, k⟩) g (by rw [← hg, Category.assoc])
  hom_comp Y q k₁ k₂ k₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    E.hom_comp (q ≫ v i) (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) (i₃ := ⟨i, k₃⟩) f₁ f₂ f₃
      (by rw [← hf₁, Category.assoc]) (by rw [← hf₂, Category.assoc])
      (by rw [← hf₃, Category.assoc])

/-- Transport of the membership of an arrow in `R` along an equation. -/
private lemma mem_of_comp_eq {i : ι} {Y : C} {c : Y ⟶ V i} {q : Y ⟶ S} (hc : c ≫ v i = q)
    (hq : R q) : R (c ≫ v i) :=
  hc ▸ hq

variable {E : F.DescentData (localFamily v R)} {x : ∀ i, F.obj (.mk (op (V i)))}
  (e : ∀ i, (F.toDescentData (fun (k : BlockIdx v R i) ↦ k.2.1)).obj (x i) ≅
    blockDescentData E i)

/-- The comparison of the pullbacks of `x i` with the objects of `E`, through `mapId`. -/
private def blockIso (i : ι) {Y : C} (c : Y ⟶ V i) (hc : R (c ≫ v i)) :
    (F.map c.op.toLoc).toFunctor.obj (x i) ≅
      (F.map (𝟙 Y).op.toLoc).toFunctor.obj (E.obj ⟨i, Y, c, hc⟩) :=
  DescentData.isoApp (e i) ⟨Y, c, hc⟩ ≪≫ ((Cat.Hom.toNatIso (F.mapId _)).app _).symm

/-- The underlying morphism of `blockIso`. -/
private lemma blockIso_hom (i : ι) {Y : C} (c : Y ⟶ V i) (hc : R (c ≫ v i)) :
    (blockIso e i c hc).hom = (e i).hom.hom ⟨Y, c, hc⟩ ≫ (F.mapId _).inv.toNatTrans.app _ :=
  rfl

/-- `blockIso` is compatible with the descent data, in `pullHom` form. -/
private lemma blockIso_hom_comm (i : ι) {Y₁ Y₂ Z : C} (c₁ : Y₁ ⟶ V i) (hc₁ : R (c₁ ≫ v i))
    (c₂ : Y₂ ⟶ V i) (hc₂ : R (c₂ ≫ v i)) (z₁ : Z ⟶ Y₁) (z₂ : Z ⟶ Y₂) (c : Z ⟶ V i)
    (h₁ : z₁ ≫ c₁ = c) (h₂ : z₂ ≫ c₂ = c) (q : Z ⟶ S) (hq : c ≫ v i = q) :
    pullHom (blockIso e i c₁ hc₁).hom z₁ c z₁ h₁ (by simp) ≫
        E.hom q (i₁ := ⟨i, Y₁, c₁, hc₁⟩) (i₂ := ⟨i, Y₂, c₂, hc₂⟩) z₁ z₂
          (by simp [← hq, ← h₁]) (by simp [← hq, ← h₂]) =
      pullHom (blockIso e i c₂ hc₂).hom z₂ c z₂ h₂ (by simp) := by
  subst hq
  rw [blockIso_hom, blockIso_hom]
  exact (toDescentData_comm_iff (fun k ↦ (e i).hom.hom k) c (i₁ := ⟨Y₁, c₁, hc₁⟩)
    (i₂ := ⟨Y₂, c₂, hc₂⟩) z₁ z₂ h₁ h₂).1
    ((e i).hom.comm c (i₁ := ⟨Y₁, c₁, hc₁⟩) (i₂ := ⟨Y₂, c₂, hc₂⟩) z₁ z₂ h₁ h₂)

/-- Pulling `blockIso` back along `z` gives `blockIso` at `z ≫ c`, up to `E`. -/
private lemma blockIso_hom_pullHom (i : ι) {Y Z : C} (c : Y ⟶ V i) (hc : R (c ≫ v i))
    (z : Z ⟶ Y) (c' : Z ⟶ V i) (hc' : z ≫ c = c') (hc'' : R (c' ≫ v i))
    (q : Z ⟶ S) (hq : c' ≫ v i = q) :
    pullHom (blockIso e i c hc).hom z c' z hc' (by simp) =
      (blockIso e i c' hc'').hom ≫ E.hom q (i₁ := ⟨i, Z, c', hc''⟩) (i₂ := ⟨i, Y, c, hc⟩) (𝟙 Z) z
        (by simp [← hq]) (by simp [← hq, ← hc']) := by
  have := blockIso_hom_comm e i c' hc'' c hc (𝟙 Z) z c' (by simp) hc' q hq
  rw [pullHom_id] at this
  exact this.symm

/-- The inverse of `blockIso` pulled back along `z`. -/
private lemma blockIso_inv_pullHom (i : ι) {Y Z : C} (c : Y ⟶ V i) (hc : R (c ≫ v i))
    (z : Z ⟶ Y) (c' : Z ⟶ V i) (hc' : z ≫ c = c') (hc'' : R (c' ≫ v i))
    (q : Z ⟶ S) (hq : c' ≫ v i = q) :
    pullHom (blockIso e i c hc).inv z z c' (by simp) hc' =
      E.hom q (i₁ := ⟨i, Y, c, hc⟩) (i₂ := ⟨i, Z, c', hc''⟩) z (𝟙 Z) (by simp [← hq, ← hc'])
          (by simp [← hq]) ≫ (blockIso e i c' hc'').inv := by
  have h := blockIso_hom_pullHom e i c hc z c' hc' hc'' q hq
  rw [← cancel_epi ((blockIso e i c' hc'').hom ≫ E.hom q (i₁ := ⟨i, Z, c', hc''⟩)
    (i₂ := ⟨i, Y, c, hc⟩) (𝟙 Z) z (by simp [← hq]) (by simp [← hq, ← hc']))]
  conv_lhs => rw [← h, ← pullHom_comp', Iso.hom_inv_id, pullHom_id_hom]
  rw [Category.assoc, E.hom_comp_assoc, E.hom_self, Category.id_comp, Iso.hom_inv_id]
  simp [localFamily, ← hq]

/-- The comparison between the pullbacks of `x i` and `x j` to an arrow of `R` factoring
through both `v i` and `v j`, read off from `E`. -/
private def overlapHom {i j : ι} {Y : C} (q : Y ⟶ S) (hq : R q) (c : Y ⟶ V i) (d : Y ⟶ V j)
    (hc : c ≫ v i = q) (hd : d ≫ v j = q) :
    (F.map c.op.toLoc).toFunctor.obj (x i) ⟶ (F.map d.op.toLoc).toFunctor.obj (x j) :=
  (blockIso e i c (mem_of_comp_eq hc hq)).hom ≫
    E.hom q (i₁ := ⟨i, Y, c, mem_of_comp_eq hc hq⟩) (i₂ := ⟨j, Y, d, mem_of_comp_eq hd hq⟩)
      (𝟙 Y) (𝟙 Y) (by simp [hc]) (by simp [hd]) ≫
    (blockIso e j d (mem_of_comp_eq hd hq)).inv

/-- `overlapHom` is compatible with pullbacks. -/
private lemma overlapHom_pullHom {i j : ι} {Y Z : C} (q : Y ⟶ S) (hq : R q) (c : Y ⟶ V i)
    (d : Y ⟶ V j) (hc : c ≫ v i = q) (hd : d ≫ v j = q) (z : Z ⟶ Y) (q' : Z ⟶ S) (hq' : z ≫ q = q')
    (hq'' : R q') (c' : Z ⟶ V i) (d' : Z ⟶ V j) (hc' : z ≫ c = c') (hd' : z ≫ d = d') :
    pullHom (overlapHom e q hq c d hc hd) z c' d' hc' hd' =
      overlapHom e q' hq'' c' d' (by rw [← hc', ← hq', Category.assoc, hc])
        (by rw [← hd', ← hq', Category.assoc, hd]) := by
  subst hq' hc' hd'
  simp only [overlapHom]
  rw [pullHom_comp' _ _ z (z ≫ c) z (z ≫ d) rfl (by simp) rfl,
    pullHom_comp' _ _ z z z (z ≫ d) (by simp) (by simp) rfl,
    blockIso_hom_pullHom e i c _ z (z ≫ c) rfl (mem_of_comp_eq (by simp [hc]) hq'')
      (z ≫ q) (by simp [hc]),
    blockIso_inv_pullHom e j d _ z (z ≫ d) rfl (mem_of_comp_eq (by simp [hd]) hq'')
      (z ≫ q) (by simp [hd]),
    E.pullHom_hom z q (z ≫ q) rfl
      (i₁ := ⟨i, Y, c, mem_of_comp_eq hc hq⟩) (i₂ := ⟨j, Y, d, mem_of_comp_eq hd hq⟩)
      (𝟙 Y) (𝟙 Y) (by simp [hc]) (by simp [hd]) z z (by simp) (by simp)]
  rw [Category.assoc, E.hom_comp_assoc, E.hom_comp_assoc]

/-- `overlapHom` is the identity on the diagonal. -/
private lemma overlapHom_self {i : ι} {Y : C} (q : Y ⟶ S) (hq : R q) (c : Y ⟶ V i)
    (hc : c ≫ v i = q) :
    overlapHom e q hq c c hc hc = 𝟙 _ := by
  rw [overlapHom, E.hom_self, Category.id_comp, Iso.hom_inv_id]
  simp [localFamily, hc]

/-- `overlapHom` satisfies the cocycle condition. -/
private lemma overlapHom_comp {i j k : ι} {Y : C} (q : Y ⟶ S) (hq : R q) (c : Y ⟶ V i)
    (d : Y ⟶ V j) (d' : Y ⟶ V k) (hc : c ≫ v i = q) (hd : d ≫ v j = q) (hd' : d' ≫ v k = q) :
    overlapHom e q hq c d hc hd ≫ overlapHom e q hq d d' hd hd' =
      overlapHom e q hq c d' hc hd' := by
  simp only [overlapHom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [E.hom_comp_assoc]

/-- An arrow that factors through `v i` lies in the sieve generated by `v`. -/
private lemma ofArrows_of_comp_eq {i : ι} {W : C} {a : W ⟶ V i} {q : W ⟶ S} (ha : a ≫ v i = q) :
    Sieve.ofArrows V v q :=
  ha ▸ (Sieve.ofArrows V v).downward_closed (Sieve.ofArrows_mk V v i) a

variable (hR : ∀ ⦃W : C⦄ (q : W ⟶ S), Sieve.ofArrows V v q → F.IsPrestackFor (R.pullback q).arrows)

include hR in
/-- The comparisons `overlapHom` over the arrows of `R.pullback q` glue. -/
private lemma exists_coverHom {W : C} (q : W ⟶ S) {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j)
    (ha : a ≫ v i = q) (hb : b ≫ v j = q) :
    ∃ φ : (F.map a.op.toLoc).toFunctor.obj (x i) ⟶ (F.map b.op.toLoc).toFunctor.obj (x j),
      ∀ ⦃Y : C⦄ (y : Y ⟶ W) (hy : R (y ≫ q)), pullHom φ y (y ≫ a) (y ≫ b) =
        overlapHom e (y ≫ q) hy (y ≫ a) (y ≫ b) (by simp [ha]) (by simp [hb]) :=
  exists_pullHom_eq (hR q (ofArrows_of_comp_eq ha))
    (fun Y y hy ↦ overlapHom e (y ≫ q) hy (y ≫ a) (y ≫ b) (by simp [ha]) (by simp [hb]))
    (fun Y Z y hy z ↦ overlapHom_pullHom e _ _ _ _ _ _ z _ (by simp) _ _ _ (by simp) (by simp))

/-- The gluing morphisms of the descent datum relative to `v`. -/
private noncomputable def coverHom {W : C} (q : W ⟶ S) {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j)
    (ha : a ≫ v i = q) (hb : b ≫ v j = q) :
    (F.map a.op.toLoc).toFunctor.obj (x i) ⟶ (F.map b.op.toLoc).toFunctor.obj (x j) :=
  (exists_coverHom e hR q a b ha hb).choose

/-- The pullbacks of `coverHom` along the arrows of `R.pullback q` are `overlapHom`. -/
private lemma pullHom_coverHom {W : C} (q : W ⟶ S) {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j)
    (ha : a ≫ v i = q) (hb : b ≫ v j = q) {Y : C} (y : Y ⟶ W) (q' : Y ⟶ S)
    (hq' : y ≫ q = q') (hq'' : R q') (a' : Y ⟶ V i) (b' : Y ⟶ V j) (ha' : y ≫ a = a')
    (hb' : y ≫ b = b') :
    pullHom (coverHom e hR q a b ha hb) y a' b' ha' hb' =
      overlapHom e q' hq'' a' b' (by rw [← ha', ← hq', Category.assoc, ha])
        (by rw [← hb', ← hq', Category.assoc, hb]) := by
  subst hq' ha' hb'
  exact (exists_coverHom e hR q a b ha hb).choose_spec y hq''

/-- The descent datum relative to `v` obtained by gluing the comparisons `overlapHom`. -/
private noncomputable def coverDescentData : F.DescentData v where
  obj := x
  hom W q i j a b ha hb := coverHom e hR q a b ha hb
  pullHom_hom W' W g q q' hq i j a b ha hb ga gb hga hgb := by
    refine pullHom_ext
      (hR q' (hq ▸ (Sieve.ofArrows V v).downward_closed (ofArrows_of_comp_eq ha) g))
      fun Y y hy ↦ ?_
    replace hy : R (y ≫ q') := hy
    rw [pullHom_pullHom, pullHom_coverHom e hR q a b ha hb (y ≫ g) (y ≫ q') (by simp [← hq]) hy
      (y ≫ ga) (y ≫ gb) (by simp [← hga]) (by simp [← hgb]),
      pullHom_coverHom e hR q' ga gb _ _ y (y ≫ q') rfl hy (y ≫ ga) (y ≫ gb) rfl rfl]
  hom_self W q i a ha := by
    refine pullHom_ext (hR q (ofArrows_of_comp_eq ha))
      fun Y y hy ↦ ?_
    replace hy : R (y ≫ q) := hy
    rw [pullHom_coverHom e hR q a a ha ha y (y ≫ q) rfl hy (y ≫ a) (y ≫ a) rfl rfl, overlapHom_self,
      pullHom_id_hom]
  hom_comp W q i j k a b c ha hb hc := by
    refine pullHom_ext (hR q (ofArrows_of_comp_eq ha))
      fun Y y hy ↦ ?_
    replace hy : R (y ≫ q) := hy
    rw [pullHom_comp' _ _ y (y ≫ a) (y ≫ b) (y ≫ c) rfl rfl rfl,
      pullHom_coverHom e hR q a b ha hb y (y ≫ q) rfl hy (y ≫ a) (y ≫ b) rfl rfl,
      pullHom_coverHom e hR q b c hb hc y (y ≫ q) rfl hy (y ≫ b) (y ≫ c) rfl rfl,
      pullHom_coverHom e hR q a c ha hc y (y ≫ q) rfl hy (y ≫ a) (y ≫ c) rfl rfl, overlapHom_comp]

/-- Over an arrow of `R`, `coverHom` is `overlapHom`. -/
private lemma coverHom_eq_overlapHom {W : C} (q : W ⟶ S) (hq : R q) {i j : ι} (a : W ⟶ V i)
    (b : W ⟶ V j) (ha : a ≫ v i = q) (hb : b ≫ v j = q) :
    coverHom e hR q a b ha hb = overlapHom e q hq a b ha hb := by
  have := pullHom_coverHom e hR q a b ha hb (𝟙 W) q (by simp) hq a b (by simp) (by simp)
  rwa [pullHom_id] at this

variable {x₀ : F.obj (.mk (op S))} (κ : (F.toDescentData v).obj x₀ ≅ coverDescentData e hR)

/-- The components of `κ`, typed as morphisms out of the pullbacks of `x₀`. -/
private def gluedHom (i : ι) : (F.map (v i).op.toLoc).toFunctor.obj x₀ ⟶ x i :=
  κ.hom.hom i

/-- `gluedHom` is compatible with `overlapHom`, in `pullHom` form. -/
private lemma gluedHom_comm {W : C} (q : W ⟶ S) (hq : R q) {i j : ι} (a : W ⟶ V i)
    (b : W ⟶ V j) (ha : a ≫ v i = q) (hb : b ≫ v j = q) :
    pullHom (f₂ := 𝟙 _) (gluedHom e hR κ i ≫ (F.mapId _).inv.toNatTrans.app _) a q a ha
        (by simp) ≫ overlapHom e q hq a b ha hb =
      pullHom (f₂ := 𝟙 _) (gluedHom e hR κ j ≫ (F.mapId _).inv.toNatTrans.app _) b q b hb
        (by simp) := by
  rw [← coverHom_eq_overlapHom e hR q hq a b ha hb]
  exact (toDescentData_comm_iff (M := x₀) (D := coverDescentData e hR) (fun i ↦ gluedHom e hR κ i) q
    a b ha hb).1 (κ.hom.comm q a b ha hb)

/-- The comparison of the pullbacks of the glued object with the objects of `E`. -/
private noncomputable def localIso (k : LocalIdx v R) :
    (F.map (localFamily v R k).op.toLoc).toFunctor.obj x₀ ≅ E.obj k :=
  (Cat.Hom.toNatIso (F.mapComp' (v k.1).op.toLoc k.2.2.1.op.toLoc
      (k.2.2.1 ≫ v k.1).op.toLoc (by grind))).app x₀ ≪≫
    (F.map k.2.2.1.op.toLoc).toFunctor.mapIso (DescentData.isoApp κ k.1) ≪≫
    DescentData.isoApp (e k.1) k.2

/-- `localIso` factors through `gluedHom` and `blockIso`. -/
private lemma localIso_hom_comp_mapId_inv (i : ι) {Y : C} (c : Y ⟶ V i) (hc : R (c ≫ v i)) :
    (localIso e hR κ ⟨i, Y, c, hc⟩).hom ≫ (F.mapId _).inv.toNatTrans.app _ =
      pullHom (f₂ := 𝟙 _) (gluedHom e hR κ i ≫ (F.mapId _).inv.toNatTrans.app _) c (c ≫ v i) c
        rfl (by simp) ≫ (blockIso e i c hc).hom := by
  rw [pullHom_comp_mapId_inv, blockIso_hom]
  change ((F.mapComp' (v i).op.toLoc c.op.toLoc (c ≫ v i).op.toLoc (by grind)).hom.toNatTrans.app
    x₀ ≫ (F.map c.op.toLoc).toFunctor.map (κ.hom.hom i) ≫ (e i).hom.hom ⟨Y, c, hc⟩) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg _ (Category.assoc _ _ _)).trans
    (Category.assoc _ _ _).symm)

/-- `localIso` pulled back along `z`. -/
private lemma pullHom_localIso (i : ι) {Y Z : C} (c : Y ⟶ V i) (hc : R (c ≫ v i)) (z : Z ⟶ Y)
    (q : Z ⟶ S) (hz : z ≫ c ≫ v i = q) (hzc : R ((z ≫ c) ≫ v i)) :
    pullHom (f₂ := 𝟙 _) ((localIso e hR κ ⟨i, Y, c, hc⟩).hom ≫ (F.mapId _).inv.toNatTrans.app _)
        z q z hz (by simp) =
      pullHom (f₂ := 𝟙 _) (gluedHom e hR κ i ≫ (F.mapId _).inv.toNatTrans.app _) (z ≫ c) q
          (z ≫ c) (by simp [hz]) (by simp) ≫
        (blockIso e i (z ≫ c) hzc).hom ≫
          E.hom q (i₁ := ⟨i, Z, z ≫ c, hzc⟩) (i₂ := ⟨i, Y, c, hc⟩) (𝟙 Z) z
            (by simp [localFamily, hz]) hz := by
  refine (pullHom_congr (localIso_hom_comp_mapId_inv e hR κ i c hc) z q z hz (by simp)).trans ?_
  rw [pullHom_comp' _ _ z q (z ≫ c) z hz rfl (by simp),
    pullHom_pullHom, blockIso_hom_pullHom e i c hc z (z ≫ c) rfl hzc q (by simp [hz])]

/-- The glued object `x₀` has descent datum `E` along `localFamily v R`. -/
private noncomputable def toDescentDataGluedIso :
    (F.toDescentData (localFamily v R)).obj x₀ ≅ E :=
  DescentData.isoMk (fun k ↦ localIso e hR κ k) (by
    rintro Y q ⟨i₁, Y₁, c₁, hc₁⟩ ⟨i₂, Y₂, c₂, hc₂⟩ f₁ f₂ hf₁ hf₂
    have hq : R q := hf₁ ▸ R.downward_closed hc₁ f₁
    refine (toDescentData_comm_iff (fun k ↦ (localIso e hR κ k).hom) q f₁ f₂ hf₁ hf₂).2 ?_
    rw [pullHom_localIso e hR κ i₁ c₁ hc₁ f₁ q hf₁ (by simpa [hf₁] using hq),
      pullHom_localIso e hR κ i₂ c₂ hc₂ f₂ q hf₂ (by simpa [hf₂] using hq),
      ← gluedHom_comm e hR κ q hq (f₁ ≫ c₁) (f₂ ≫ c₂) (by simp [hf₁]) (by simp [hf₂])]
    simp only [overlapHom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [E.hom_comp, E.hom_comp])

end Local

/-- The family indexed by `BlockIdx v R i` generates `R.pullback (v i)`. -/
private lemma sieve_ofArrows_block {ι : Type t} {S : C} {V : ι → C} (v : ∀ i, V i ⟶ S)
    (R : Sieve S) (i : ι) :
    Sieve.ofArrows (fun k : BlockIdx v R i ↦ k.1) (fun k ↦ k.2.1) = R.pullback (v i) := by
  ext Y g
  rw [Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨k, a, rfl⟩
    exact (R.pullback (v i)).downward_closed k.2.2 a
  · intro hg
    exact ⟨⟨Y, g, hg⟩, 𝟙 Y, (Category.id_comp g).symm⟩

/-- If `F` is a prestack for the pullback of `R` along every arrow that factors through `v`,
has effective descent along `v` and along the pullback of `R` to every `V i`, then every
descent datum along `localFamily v R` is effective. -/
private lemma essSurj_toDescentData_localFamily {ι : Type t} {S : C} {V : ι → C}
    {v : ∀ i, V i ⟶ S} {R : Sieve S}
    (hR : ∀ ⦃W : C⦄ (q : W ⟶ S), Sieve.ofArrows V v q → F.IsPrestackFor (R.pullback q).arrows)
    (hv : (F.toDescentData v).EssSurj) (h : ∀ i, F.IsStackFor (R.pullback (v i)).arrows) :
    (F.toDescentData (localFamily v R)).EssSurj := ⟨fun E ↦ by
  have hx (i : ι) := by
    have : (F.toDescentData (fun k : BlockIdx v R i ↦ k.2.1)).IsEquivalence := by
      rw [← isStackFor_ofArrows_iff]
      refine (F.isStackFor_iff_of_sieve_eq ?_).1 (h i)
      rw [Sieve.generate_sieve]
      exact (sieve_ofArrows_block v R i).symm
    exact Functor.EssSurj.mem_essImage (F.toDescentData _) (blockDescentData E i)
  choose x hx using hx
  obtain ⟨x₀, ⟨κ⟩⟩ := Functor.EssSurj.mem_essImage (F.toDescentData v)
    (coverDescentData (fun i ↦ (hx i).some) hR)
  exact ⟨x₀, ⟨toDescentDataGluedIso (fun i ↦ (hx i).some) hR κ⟩⟩⟩

variable (F)

/-- Effective descent is local on the base. Let `F` be a stack for `J₀` and a prestack for
`J`, let `R` be a `J`-covering sieve on `S`, and let `v i : V i ⟶ S` be a `J₀`-covering
family. If `F` has effective descent along the pullback of `R` to every `V i`, then `F` has
effective descent along `R`.

The local descents are glued along `v` with the comparisons on overlaps that the prestack
condition for `J` determines, as in Vistoli, *Notes on Grothendieck topologies, fibered
categories and descent theory*, Lemma 4.25, Step 5. Mathlib's
`GrothendieckTopology.OneHypercover.isSheafFor_of_pullback` is the analogue for sheaves of
types. -/
theorem isStackFor_of_isStackFor_pullback {J₀ J : GrothendieckTopology C}
    [F.IsStack J₀] [F.IsPrestack J] {S : C} {R : Sieve S} (hR : R ∈ J S)
    {ι : Type t} {V : ι → C} (v : ∀ i, V i ⟶ S) (hv : Sieve.ofArrows V v ∈ J₀ S)
    (h : ∀ i, F.IsStackFor (R.pullback (v i)).arrows) :
    F.IsStackFor R.arrows := by
  have hK : Sieve.ofArrows _ (localFamily v R) ∈ prestackTopology F S := by
    refine (prestackTopology F).transitive (le_prestackTopology F J₀ _ hv) _ fun Y g hg ↦ ?_
    obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).1 hg
    refine (prestackTopology F).superset_covering (fun Z y hy ↦ ?_)
      (le_prestackTopology F J _ (J.pullback_stable (c ≫ v i) hR))
    exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨⟨i, Z, y ≫ c, by simpa using hy⟩, 𝟙 Z, by simp [localFamily]⟩
  haveI := isPrestack_prestackTopology F
  have hff := F.fullyFaithfulToDescentData (J := prestackTopology F) (localFamily v R) hK
  have := F.isEquivalence_toDescentData v hv
  have := essSurj_toDescentData_localFamily
    (fun _ q _ ↦ F.isPrestackFor' _ (J.pullback_stable q hR)) inferInstance h
  have := hff.full
  have := hff.faithful
  have : (F.toDescentData (localFamily v R)).IsEquivalence := { }
  refine IsStackFor.of_le F ((F.isStackFor_ofArrows_iff _).2 this) (J := prestackTopology F)
    hK ?_
  rintro Y g ⟨k⟩
  exact k.2.2.2

variable {F}

section Refine

/-- Morphisms `M ⟶ N` whose pullbacks along the arrows of a sieve along which `F` is a
prestack agree are equal. -/
private lemma hom_ext_of_isPrestackFor {W : C} {M N : F.obj (.mk (op W))} {U : Sieve W}
    (hU : F.IsPrestackFor U.arrows) {φ φ' : M ⟶ N}
    (h : ∀ ⦃Y : C⦄ (y : Y ⟶ W), U y →
      (F.map y.op.toLoc).toFunctor.map φ = (F.map y.op.toLoc).toFunctor.map φ') :
    φ = φ' := by
  apply F.presheafHomObjHomEquiv.injective
  refine (((F.isPrestackFor_iff_isSheafFor U).1 hU _ _).isSeparatedFor).ext fun T g hg ↦ ?_
  obtain ⟨Y, y, rfl⟩ := T.mk_surjective
  obtain rfl : g = Over.homMk y := by ext; simpa using Over.w g
  rw [presheafHom_map_presheafHomObjHomEquiv, presheafHom_map_presheafHomObjHomEquiv]
  exact h y hg

/-- A family of morphisms `y^* M ⟶ y^* N` indexed by the arrows `y` of a sieve along which
`F` is a prestack, compatible with pullbacks, glues to a morphism `M ⟶ N`. -/
private lemma exists_hom_map_eq {W : C} {M N : F.obj (.mk (op W))} {U : Sieve W}
    (hU : F.IsPrestackFor U.arrows)
    (Φ : ∀ ⦃Y : C⦄ (y : Y ⟶ W), U y →
      ((F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map y.op.toLoc).toFunctor.obj N))
    (hΦ : ∀ ⦃Y Z : C⦄ (y : Y ⟶ W) (hy : U y) (z : Z ⟶ Y),
      pullHom (Φ y hy) z (z ≫ y) (z ≫ y) = Φ (z ≫ y) (U.downward_closed hy z)) :
    ∃ φ : M ⟶ N, ∀ ⦃Y : C⦄ (y : Y ⟶ W) (hy : U y),
      (F.map y.op.toLoc).toFunctor.map φ = Φ y hy := by
  have mem : ∀ {T : Over W} (g : T ⟶ Over.mk (𝟙 W)),
      (Sieve.overEquiv (Over.mk (𝟙 W))).symm U g → U T.hom := fun {T} g hg ↦ by
    have h : g.left = T.hom := by simpa using Over.w g
    rw [← h]
    exact hg
  let x : Presieve.FamilyOfElements (F.presheafHom M N)
      ((Sieve.overEquiv (Over.mk (𝟙 W))).symm U).arrows :=
    fun T g hg ↦ Φ T.hom (mem g hg)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T T' g u hg
    change _ = pullHom _ u.left T'.hom T'.hom (Over.w u) (Over.w u)
    have key : ∀ (y' : T'.left ⟶ W) (hy' : u.left ≫ T.hom = y') (h' : U y'), Φ y' h' =
        pullHom (Φ T.hom (mem g hg)) u.left y' y' hy' hy' := by
      rintro _ rfl _
      exact (hΦ _ _ u.left).symm
    exact key _ (Over.w u) _
  obtain ⟨σ, hσ, -⟩ := (F.isPrestackFor_iff_isSheafFor U).1 hU _ _ x hx
  refine ⟨F.presheafHomObjHomEquiv.symm σ, fun Y y hy ↦ ?_⟩
  rw [← presheafHom_map_presheafHomObjHomEquiv, Equiv.apply_symm_apply,
    hσ (Over.homMk y : Over.mk y ⟶ Over.mk (𝟙 W)) hy]
  rfl

/-- `pullHom` of the pullback of a morphism along `f₁` is its pullback along the composite. -/
private lemma pullHom_map ⦃X₁ : C⦄ ⦃M₁ M₂ : F.obj (.mk (op X₁))⦄ (φ : M₁ ⟶ M₂) ⦃Y : C⦄
    (f₁ : Y ⟶ X₁) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map φ) g gf₁ gf₁ hgf₁ hgf₁ =
      (F.map gf₁.op.toLoc).toFunctor.map φ := by
  rw [pullHom, ← mapComp'_hom_naturality_assoc, Cat.Hom.hom_inv_id_toNatTrans_app,
    Category.comp_id]

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j ≫ 𝟙 S)
  {D₁ D₂ : F.DescentData f}
  (φ : (DescentData.pullFunctor F w).obj D₁ ⟶ (DescentData.pullFunctor F w).obj D₂)

/-- The component of `φ` at `j`, typed as a morphism between pullbacks along `p' j`. -/
private def refineComp (j : ι') :
    (F.map (p' j).op.toLoc).toFunctor.obj (D₁.obj (α j)) ⟶
      (F.map (p' j).op.toLoc).toFunctor.obj (D₂.obj (α j)) :=
  φ.hom j

/-- The morphism `y^* (D₁.obj i) ⟶ y^* (D₂.obj i)` read off from `φ` through a factorization
of `y ≫ f i` through `f' j`. -/
private def refineHom ⦃i : ι⦄ ⦃Y : C⦄ (y : Y ⟶ X i) (q : Y ⟶ S) (hy : y ≫ f i = q) ⦃j : ι'⦄
    (a : Y ⟶ X' j) (b : Y ⟶ X (α j)) (hab : a ≫ p' j = b) (hb : b ≫ f (α j) = q) :
    (F.map y.op.toLoc).toFunctor.obj (D₁.obj i) ⟶ (F.map y.op.toLoc).toFunctor.obj (D₂.obj i) :=
  D₁.hom q y b hy hb ≫ pullHom (refineComp w φ j) a b b hab hab ≫ D₂.hom q b y hb hy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of `φ` with the descent data, in `pullHom` form. -/
private lemma pullHom_hom_comp_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃j₁ j₂ : ι'⦄ (a₁ : Y ⟶ X' j₁)
    (a₂ : Y ⟶ X' j₂) (b₁ : Y ⟶ X (α j₁)) (b₂ : Y ⟶ X (α j₂)) (hab₁ : a₁ ≫ p' j₁ = b₁)
    (hab₂ : a₂ ≫ p' j₂ = b₂) (hb₁ : b₁ ≫ f (α j₁) = q) (hb₂ : b₂ ≫ f (α j₂) = q) :
    pullHom (refineComp w φ j₁) a₁ b₁ b₁ hab₁ hab₁ ≫ D₂.hom q b₁ b₂ hb₁ hb₂ =
      D₁.hom q b₁ b₂ hb₁ hb₂ ≫ pullHom (refineComp w φ j₂) a₂ b₂ b₂ hab₂ hab₂ := by
  have ha₁ : a₁ ≫ f' j₁ = q := by
    simpa [← hb₁, ← hab₁] using (congrArg (a₁ ≫ ·) (w j₁)).symm
  have ha₂ : a₂ ≫ f' j₂ = q := by
    simpa [← hb₂, ← hab₂] using (congrArg (a₂ ≫ ·) (w j₂)).symm
  have : (F.map a₁.op.toLoc).toFunctor.map (refineComp w φ j₁) ≫
      DescentData.pullFunctorObjHom w D₂ (a₁ ≫ f' j₁) a₁ a₂ rfl (ha₂.trans ha₁.symm) =
        DescentData.pullFunctorObjHom w D₁ (a₁ ≫ f' j₁) a₁ a₂ rfl (ha₂.trans ha₁.symm) ≫
          (F.map a₂.op.toLoc).toFunctor.map (refineComp w φ j₂) :=
    φ.comm q a₁ a₂ ha₁ ha₂
  rw [DescentData.pullFunctorObjHom_eq _ _ _ _ _ q b₁ b₂ rfl (ha₂.trans ha₁.symm)
      (by simp [ha₁]) hab₁ hab₂,
    DescentData.pullFunctorObjHom_eq _ _ _ _ _ q b₁ b₂ rfl (ha₂.trans ha₁.symm)
      (by simp [ha₁]) hab₁ hab₂,
    map_eq_pullHom _ _ _ _ hab₁ hab₁, map_eq_pullHom _ _ _ _ hab₂ hab₂] at this
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, cancel_epi] at this
  simp only [← Category.assoc, cancel_mono] at this
  exact this

/-- `refineHom` does not depend on the factorization. -/
private lemma refineHom_congr ⦃i : ι⦄ ⦃Y : C⦄ (y : Y ⟶ X i) (q : Y ⟶ S) (hy : y ≫ f i = q)
    ⦃j₁ : ι'⦄ (a₁ : Y ⟶ X' j₁) (b₁ : Y ⟶ X (α j₁)) (hab₁ : a₁ ≫ p' j₁ = b₁)
    (hb₁ : b₁ ≫ f (α j₁) = q) (q' : Y ⟶ S) (hy' : y ≫ f i = q') ⦃j₂ : ι'⦄ (a₂ : Y ⟶ X' j₂)
    (b₂ : Y ⟶ X (α j₂)) (hab₂ : a₂ ≫ p' j₂ = b₂) (hb₂ : b₂ ≫ f (α j₂) = q') :
    refineHom w φ y q hy a₁ b₁ hab₁ hb₁ = refineHom w φ y q' hy' a₂ b₂ hab₂ hb₂ := by
  obtain rfl : q = q' := hy.symm.trans hy'
  rw [refineHom, refineHom, ← D₂.hom_comp q b₁ b₂ y hb₁ hb₂ hy,
    reassoc_of% (pullHom_hom_comp_hom w φ q a₁ a₂ b₁ b₂ hab₁ hab₂ hb₁ hb₂), D₁.hom_comp_assoc]

/-- `refineHom` is compatible with pullbacks. -/
private lemma pullHom_refineHom ⦃i : ι⦄ ⦃Y : C⦄ (y : Y ⟶ X i) (q : Y ⟶ S) (hy : y ≫ f i = q)
    ⦃j : ι'⦄ (a : Y ⟶ X' j) (b : Y ⟶ X (α j)) (hab : a ≫ p' j = b) (hb : b ≫ f (α j) = q)
    ⦃Z : C⦄ (z : Z ⟶ Y) :
    pullHom (refineHom w φ y q hy a b hab hb) z (z ≫ y) (z ≫ y) =
      refineHom w φ (z ≫ y) (z ≫ q) (by simp [hy]) (z ≫ a) (z ≫ b) (by simp [hab])
        (by simp [hb]) := by
  rw [refineHom, refineHom, pullHom_comp' _ _ z (z ≫ y) (z ≫ b) (z ≫ y) rfl rfl rfl,
    pullHom_comp' _ _ z (z ≫ b) (z ≫ b) (z ≫ y) rfl rfl rfl,
    D₁.pullHom_hom z q (z ≫ q) rfl y b hy hb (z ≫ y) (z ≫ b) rfl rfl,
    D₂.pullHom_hom z q (z ≫ q) rfl b y hb hy (z ≫ b) (z ≫ y) rfl rfl, pullHom_pullHom]

variable (hf' : ∀ ⦃W : C⦄ (q : W ⟶ S), Sieve.ofArrows X f q →
  F.IsPrestackFor ((Sieve.ofArrows X' f').pullback q).arrows)

include w in
/-- An arrow `y` with `y ≫ f i` in the sieve generated by `f'` factors through some `f' j`. -/
private lemma exists_fac {i : ι} {Y : C} {y : Y ⟶ X i}
    (hy : (Sieve.ofArrows X' f').pullback (f i) y) :
    ∃ (j : ι') (a : Y ⟶ X' j), (a ≫ p' j) ≫ f (α j) = y ≫ f i := by
  obtain ⟨j, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hy
  exact ⟨j, a, by rw [Category.assoc, w, Category.comp_id, ha]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hf' in
/-- The generalization of Mathlib's `DescentData.faithful_pullFunctor` in which only the
pullbacks of the sieve generated by `f'` along the arrows of the sieve generated by `f` are
assumed to be sieves along which `F` is a prestack. -/
private lemma faithful_pullFunctor_of_isPrestackFor :
    (DescentData.pullFunctor F (p := 𝟙 S) w).Faithful where
  map_injective {D₁ D₂ ψ₁ ψ₂} hψ := by
    ext i
    refine hom_ext_of_isPrestackFor (hf' (f i) (Sieve.ofArrows_mk _ _ i)) fun Y y hy ↦ ?_
    obtain ⟨j, a, hb⟩ := exists_fac w hy
    have h₁ := ψ₁.comm (y ≫ f i) y (a ≫ p' j) rfl hb
    have h₂ := ψ₂.comm (y ≫ f i) y (a ≫ p' j) rfl hb
    have h : (F.map (a ≫ p' j).op.toLoc).toFunctor.map (ψ₁.hom (α j)) =
        (F.map (a ≫ p' j).op.toLoc).toFunctor.map (ψ₂.hom (α j)) := by
      have h' : (F.map (p' j).op.toLoc).toFunctor.map (ψ₁.hom (α j)) =
          (F.map (p' j).op.toLoc).toFunctor.map (ψ₂.hom (α j)) :=
        congrArg (fun ψ ↦ ψ.hom j) hψ
      rw [← pullHom_map _ (p' j) a _ rfl, ← pullHom_map _ (p' j) a _ rfl, h']
    rw [← cancel_mono (D₂.hom (y ≫ f i) y (a ≫ p' j) rfl hb), h₁, h₂, h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hf' in
/-- The generalization of Mathlib's `DescentData.full_pullFunctor` in which only the
pullbacks of the sieve generated by `f'` along the arrows of the sieve generated by `f` are
assumed to be sieves along which `F` is a prestack. -/
private lemma full_pullFunctor_of_isPrestackFor :
    (DescentData.pullFunctor F (p := 𝟙 S) w).Full where
  map_surjective {D₁ D₂} φ := by
    choose j a ha using fun (i : ι) (Y : C) (y : Y ⟶ X i)
      (hy : (Sieve.ofArrows X' f').pullback (f i) y) ↦ exists_fac w hy
    have H (i : ι) := exists_hom_map_eq (M := D₁.obj i) (N := D₂.obj i)
      (hf' (f i) (Sieve.ofArrows_mk _ _ i))
      (fun Y y hy ↦ refineHom w φ y (y ≫ f i) rfl (a i Y y hy) _ rfl (ha i Y y hy))
      (fun Y Z y hy z ↦ (pullHom_refineHom w φ _ _ _ _ _ _ _ z).trans
        (refineHom_congr w φ _ _ _ _ _ _ _ _ rfl _ _ rfl _))
    choose ψ hψ using H
    have hψ' (i : ι) ⦃Y : C⦄ (y : Y ⟶ X i) (q : Y ⟶ S) (hy : y ≫ f i = q) ⦃j : ι'⦄
        (a : Y ⟶ X' j) (b : Y ⟶ X (α j)) (hab : a ≫ p' j = b) (hb : b ≫ f (α j) = q) :
        (F.map y.op.toLoc).toFunctor.map (ψ i) = refineHom w φ y q hy a b hab hb := by
      have hy' : (Sieve.ofArrows X' f').pullback (f i) y := by
        refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, a, ?_⟩
        rw [hy, ← hb, ← hab, Category.assoc, w, Category.comp_id]
      rw [hψ i y hy']
      exact refineHom_congr w φ _ _ _ _ _ _ _ _ hy _ _ hab hb
    refine ⟨{ hom := ψ, comm := fun W q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ ?_ }, ?_⟩
    · have hq : Sieve.ofArrows X f q := hf₁ ▸
        (Sieve.ofArrows X f).downward_closed (Sieve.ofArrows_mk _ _ i₁) f₁
      refine pullHom_ext (hf' q hq) fun Y y hy ↦ ?_
      obtain ⟨j, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hy
      have hb : (c ≫ p' j) ≫ f (α j) = y ≫ q := by
        rw [Category.assoc, w, Category.comp_id, hc]
      rw [pullHom_comp' _ _ y (y ≫ f₁) (y ≫ f₁) (y ≫ f₂) rfl rfl rfl,
        pullHom_comp' _ _ y (y ≫ f₁) (y ≫ f₂) (y ≫ f₂) rfl rfl rfl, pullHom_map, pullHom_map,
        D₂.pullHom_hom y q (y ≫ q) rfl f₁ f₂ hf₁ hf₂ (y ≫ f₁) (y ≫ f₂) rfl rfl,
        D₁.pullHom_hom y q (y ≫ q) rfl f₁ f₂ hf₁ hf₂ (y ≫ f₁) (y ≫ f₂) rfl rfl,
        hψ' i₁ (y ≫ f₁) (y ≫ q) (by simp [hf₁]) c _ rfl hb,
        hψ' i₂ (y ≫ f₂) (y ≫ q) (by simp [hf₂]) c _ rfl hb]
      simp only [refineHom, Category.assoc, DescentData.hom_comp, DescentData.hom_comp_assoc]
    · ext j
      change (F.map (p' j).op.toLoc).toFunctor.map (ψ (α j)) = refineComp w φ j
      have hj : p' j ≫ f (α j) = f' j := by rw [w, Category.comp_id]
      rw [hψ' (α j) (p' j) (f' j) hj (𝟙 _) (p' j) (Category.id_comp _) hj, refineHom,
        D₁.hom_self _ _ hj, D₂.hom_self _ _ hj, pullHom_id, Category.id_comp, Category.comp_id]

include hf' in
/-- The generalization of Mathlib's `DescentData.fullyFaithfulPullFunctor` in which only the
pullbacks of the sieve generated by `f'` along the arrows of the sieve generated by `f` are
assumed to be sieves along which `F` is a prestack. -/
private noncomputable def fullyFaithfulPullFunctorOfIsPrestackFor :
    (DescentData.pullFunctor F (p := 𝟙 S) w).FullyFaithful := by
  have := faithful_pullFunctor_of_isPrestackFor w hf'
  have := full_pullFunctor_of_isPrestackFor w hf'
  exact .ofFullyFaithful _

end Refine

/-- The arrows of `R₁` that factor through an arrow of `R₂`, indexed by such a
factorization, generate `R₁` when `R₁ ≤ R₂`. -/
private lemma generate_localFamily_eq {S : C} {R₁ R₂ : Sieve S} (hle : R₁ ≤ R₂) :
    Sieve.generate (Presieve.ofArrows _
      (localFamily (fun (k : R₂.arrows.category) ↦ k.obj.hom) R₁)) =
      Sieve.generate R₁.arrows := by
  rw [Sieve.generate_sieve]
  refine le_antisymm ?_ fun Y g hg ↦ ?_
  · rw [Sieve.generate_le_iff]
    rintro Y g ⟨k⟩
    exact k.2.2.2
  · let k : LocalIdx (fun (k : R₂.arrows.category) ↦ k.obj.hom) R₁ :=
      ⟨⟨Over.mk g, hle g hg⟩, Y, 𝟙 Y, by simpa using hg⟩
    exact ⟨Y, 𝟙 Y, _, Presieve.ofArrows.mk k, by simp [k, localFamily]⟩

variable (F)

/-- Let `R₁ ≤ R₂` be sieves on `S` such that `F` has effective descent along the pullback of
`R₁` along every arrow of `R₂`. Then `F` has effective descent along `R₁` if and only if it
has effective descent along `R₂`.

This holds in particular when `F` is a stack for a Grothendieck topology `J₀` and the pullback
of `R₁` along every arrow of `R₂` is `J₀`-covering. For `J₀` the big Zariski topology and
`R₁ ≤ R₂` the sieves generated by a family `X i ⟶ S` and by the induced morphism
`∐ X i ⟶ S`, this is the reduction to a single morphism in Step 2 of the proof of Vistoli,
*Notes on Grothendieck topologies, fibered categories and descent theory*, Lemma 4.25, which
Vistoli derives from his Lemmas 4.26 and 4.27.

Mathlib's `Pseudofunctor.IsStackFor.of_le` gives the implication from `R₁` to `R₂` when `R₁`
is covering for a topology for which `F` is a prestack; here no topology is involved. -/
theorem isStackFor_iff_of_le_of_isStackFor_pullback {S : C} {R₁ R₂ : Sieve S} (hle : R₁ ≤ R₂)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ S), R₂ g → F.IsStackFor (R₁.pullback g).arrows) :
    F.IsStackFor R₁.arrows ↔ F.IsStackFor R₂.arrows := by
  let f₂ := fun (k : R₂.arrows.category) ↦ k.obj.hom
  let f₁ := fun (k : R₁.arrows.category) ↦ k.obj.hom
  have w : ∀ k : R₁.arrows.category,
      𝟙 _ ≫ f₂ ⟨k.obj, hle _ k.property⟩ = f₁ k ≫ 𝟙 S := by simp [f₁, f₂]
  have hf' : ∀ ⦃W : C⦄ (q : W ⟶ S), Sieve.ofArrows _ f₂ q →
      F.IsPrestackFor ((Sieve.ofArrows _ f₁).pullback q).arrows := fun W q hq ↦ by
    rw [Sieve.ofArrows_category] at hq ⊢
    exact (h q hq).isPrestackFor
  have hΦ := fullyFaithfulPullFunctorOfIsPrestackFor w hf'
  have := hΦ.full
  have := hΦ.faithful
  let e : F.toDescentData f₂ ⋙ DescentData.pullFunctor F w ≅ F.toDescentData f₁ :=
    DescentData.toDescentDataCompPullFunctorIso _ _ ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _
  constructor
  · intro h₁
    rw [isStackFor_iff] at h₁ ⊢
    have h₂ : (F.toDescentData f₂).FullyFaithful :=
      .ofCompFaithful (G := DescentData.pullFunctor F w)
        ((Functor.FullyFaithful.ofFullyFaithful (F.toDescentData f₁)).ofIso e.symm)
    have := h₂.full
    have := h₂.faithful
    have : (F.toDescentData f₂).EssSurj := ⟨fun D ↦ ⟨_, ⟨hΦ.preimageIso
      (e.app _ ≪≫ (F.toDescentData f₁).objObjPreimageIso
        ((DescentData.pullFunctor F w).obj D))⟩⟩⟩
    exact { }
  · intro h₂
    have hpre : F.IsPrestackFor R₁.arrows := by
      rw [isPrestackFor_iff]
      rw [isStackFor_iff] at h₂
      exact ⟨((Functor.FullyFaithful.ofFullyFaithful (F.toDescentData f₂)).comp hΦ).ofIso e⟩
    rw [← F.isPrestackFor_iff_of_sieve_eq (generate_localFamily_eq hle),
      isPrestackFor_ofArrows_iff] at hpre
    have hess := essSurj_toDescentData_localFamily (F := F) (v := f₂) (R := R₁)
      (fun W q hq ↦ (h q (by rwa [Sieve.ofArrows_category] at hq)).isPrestackFor)
      h₂.essSurj (fun k ↦ h _ k.property)
    have := hpre.some.full
    have := hpre.some.faithful
    have : (F.toDescentData (localFamily f₂ R₁)).IsEquivalence := { }
    rw [← F.isStackFor_iff_of_sieve_eq (generate_localFamily_eq hle), isStackFor_ofArrows_iff]
    exact this

end CategoryTheory.Pseudofunctor
