/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Effective descent is local on the base

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a stack for a Grothendieck topology `J₀` and a
prestack for a Grothendieck topology `J`, and let `R` be a `J`-covering sieve on `S`. If `F`
has effective descent along the pullback of `R` to every member of a `J₀`-covering family
`v i : V i ⟶ S`, then `F` has effective descent along `R`. No relation between `J₀` and `J`
is assumed.

## Main definitions

None. The descent data and comparisons built in the proof are private to this file.

## Main results

* `CategoryTheory.Pseudofunctor.isStackFor_of_isStackFor_pullback`

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
no pullbacks need to exist in `C`.

## References

* A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*,
  arXiv:math/0412512v4, Lemma 4.25, Step 5.
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)

## Tags

descent, stack, effective descent, local on the base
-/

universe t v' v u' u

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

variable {J : GrothendieckTopology C} [F.IsPrestack J] (hR : R ∈ J S)

include hR in
/-- The comparisons `overlapHom` over the arrows of `R.pullback q` glue. -/
private lemma exists_coverHom {W : C} (q : W ⟶ S) {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j)
    (ha : a ≫ v i = q) (hb : b ≫ v j = q) :
    ∃ φ : (F.map a.op.toLoc).toFunctor.obj (x i) ⟶ (F.map b.op.toLoc).toFunctor.obj (x j),
      ∀ ⦃Y : C⦄ (y : Y ⟶ W) (hy : R (y ≫ q)), pullHom φ y (y ≫ a) (y ≫ b) =
        overlapHom e (y ≫ q) hy (y ≫ a) (y ≫ b) (by simp [ha]) (by simp [hb]) :=
  exists_pullHom_eq (F.isPrestackFor' (R.pullback q) (J.pullback_stable q hR))
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
    refine pullHom_ext (F.isPrestackFor' (R.pullback q') (J.pullback_stable q' hR))
      fun Y y hy ↦ ?_
    replace hy : R (y ≫ q') := hy
    rw [pullHom_pullHom, pullHom_coverHom e hR q a b ha hb (y ≫ g) (y ≫ q') (by simp [← hq]) hy
      (y ≫ ga) (y ≫ gb) (by simp [← hga]) (by simp [← hgb]),
      pullHom_coverHom e hR q' ga gb _ _ y (y ≫ q') rfl hy (y ≫ ga) (y ≫ gb) rfl rfl]
  hom_self W q i a ha := by
    refine pullHom_ext (F.isPrestackFor' (R.pullback q) (J.pullback_stable q hR))
      fun Y y hy ↦ ?_
    replace hy : R (y ≫ q) := hy
    rw [pullHom_coverHom e hR q a a ha ha y (y ≫ q) rfl hy (y ≫ a) (y ≫ a) rfl rfl, overlapHom_self,
      pullHom_id_hom]
  hom_comp W q i j k a b c ha hb hc := by
    refine pullHom_ext (F.isPrestackFor' (R.pullback q) (J.pullback_stable q hR))
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
  have hblock (i : ι) : (F.toDescentData (fun k : BlockIdx v R i ↦ k.2.1)).IsEquivalence := by
    rw [← isStackFor_ofArrows_iff]
    refine (F.isStackFor_iff_of_sieve_eq ?_).1 (h i)
    rw [Sieve.generate_sieve]
    exact (sieve_ofArrows_block v R i).symm
  have hK : Sieve.ofArrows _ (localFamily v R) ∈ prestackTopology F S := by
    refine (prestackTopology F).transitive (le_prestackTopology F J₀ _ hv) _ fun Y g hg ↦ ?_
    obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).1 hg
    refine (prestackTopology F).superset_covering (fun Z y hy ↦ ?_)
      (le_prestackTopology F J _ (J.pullback_stable (c ≫ v i) hR))
    exact (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨⟨i, Z, y ≫ c, by simpa using hy⟩, 𝟙 Z, by simp [localFamily]⟩
  haveI := isPrestack_prestackTopology F
  have hff := F.fullyFaithfulToDescentData (J := prestackTopology F) (localFamily v R) hK
  have : (F.toDescentData (localFamily v R)).EssSurj := ⟨fun E ↦ by
    have hx (i : ι) := by
      haveI := hblock i
      exact Functor.EssSurj.mem_essImage (F.toDescentData _) (blockDescentData E i)
    choose x hx using hx
    have := F.isEquivalence_toDescentData v hv
    obtain ⟨x₀, ⟨κ⟩⟩ := Functor.EssSurj.mem_essImage (F.toDescentData v)
      (coverDescentData (fun i ↦ (hx i).some) hR)
    exact ⟨x₀, ⟨toDescentDataGluedIso (fun i ↦ (hx i).some) hR κ⟩⟩⟩
  have := hff.full
  have := hff.faithful
  have : (F.toDescentData (localFamily v R)).IsEquivalence := { }
  refine IsStackFor.of_le F ((F.isStackFor_ofArrows_iff _).2 this) (J := prestackTopology F)
    hK ?_
  rintro Y g ⟨k⟩
  exact k.2.2.2

end CategoryTheory.Pseudofunctor
