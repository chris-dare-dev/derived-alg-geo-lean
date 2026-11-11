/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data along strong transformations

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be pseudofunctors and `α : F ⟶ G` a strong
transformation. For a family of morphisms `f i : X i ⟶ S`, descent data relative to `f`
map functorially along `α`, compatibly with restriction from `S`.

## Main definitions

* `Pseudofunctor.DescentData.map f α`: the functor `F.DescentData f ⥤ G.DescentData f`. It
  applies the components of `α` to the objects of a descent datum and conjugates the gluing
  morphisms by the naturality isomorphisms of `α`.
* `Pseudofunctor.toDescentDataCompMapIso f α`: restriction to descent data commutes with `α`
  up to the naturality isomorphisms of `α`.
* `Pseudofunctor.DescentData.mapId`, `Pseudofunctor.DescentData.mapComp` and
  `Pseudofunctor.DescentData.mapIso`: compatibility with identities, composition and
  invertible modifications.

## Main results

* `Pseudofunctor.DescentData.faithful_map`, `Pseudofunctor.DescentData.full_map` and
  `Pseudofunctor.DescentData.isEquivalence_map`: `DescentData.map f α` is faithful, full,
  or an equivalence of categories whenever every component `(α.app X).toFunctor` is.

## Implementation notes

The cocycle condition of a mapped descent datum is checked with the compositors `mapComp'`
of `F` and `G`, whose composite is prescribed, so no `eqToHom` transport appears.
Essential surjectivity chooses preimages componentwise and transports the gluing morphisms
along the fully faithful components. No inverse strong transformation `G ⟶ F` is
constructed.

## References

* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W): its proof
  transports pullbacks, morphisms and effective descent along an equivalence of categories
  over the site; this file supplies those steps for pseudofunctors.

## Tags

descent data, strong transformation, pseudofunctor, stack
-/

set_option backward.defeqAttrib.useBackward true

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- The naturality isomorphism of `α` at a composite `fg`, compared with those at `f` and
`g` through the compositors `mapComp'` of `F` and `G`. -/
@[reassoc]
private lemma naturality_mapComp'_hom_app (α : F ⟶ G) {a b c : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg) (M : F.obj a) :
    (α.app c).toFunctor.map ((F.mapComp' f g fg h).hom.toNatTrans.app M) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj M) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app M) =
      (α.naturality fg).hom.toNatTrans.app M ≫
        (G.mapComp' f g fg h).hom.toNatTrans.app ((α.app a).toFunctor.obj M) := by
  subst h
  simp only [mapComp'_eq_mapComp]
  have := congr_arg (fun t ↦ t.toNatTrans.app M) (α.naturality_comp f g)
  dsimp at this
  simpa only [Category.id_comp, Category.comp_id] using this.symm

@[reassoc]
private lemma naturality_mapComp'_inv_app (α : F ⟶ G) {a b c : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg) (M : F.obj a) :
    (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj M) ≫
        (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app M) ≫
          (G.mapComp' f g fg h).inv.toNatTrans.app ((α.app a).toFunctor.obj M) =
      (α.app c).toFunctor.map ((F.mapComp' f g fg h).inv.toNatTrans.app M) ≫
        (α.naturality fg).hom.toNatTrans.app M := by
  rw [← cancel_epi ((α.app c).toFunctor.map ((F.mapComp' f g fg h).hom.toNatTrans.app M)),
    naturality_mapComp'_hom_app_assoc, ← Functor.map_comp_assoc]
  simp

/-- Conjugating a morphism by the naturality isomorphisms of `α` commutes with `pullHom`. -/
private lemma pullHom_naturality (α : F ⟶ G) ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((α.naturality f₁.op.toLoc).inv.toNatTrans.app M₁ ≫
        (α.app _).toFunctor.map φ ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app M₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (α.naturality gf₁.op.toLoc).inv.toNatTrans.app M₁ ≫
        (α.app _).toFunctor.map (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ≫
        (α.naturality gf₂.op.toLoc).hom.toNatTrans.app M₂ := by
  rw [← cancel_epi ((α.naturality gf₁.op.toLoc).hom.toNatTrans.app M₁)]
  dsimp only [pullHom]
  simp only [Functor.map_comp, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [← naturality_mapComp'_inv_app]
  have := (α.naturality g.op.toLoc).hom.toNatTrans.naturality φ
  dsimp at this
  rw [reassoc_of% this, ← naturality_mapComp'_hom_app_assoc,
    ← Functor.map_comp_assoc _ ((α.naturality f₁.op.toLoc).hom.toNatTrans.app M₁)]
  simp

/-- `pullHom` commutes with pre- and postcomposition by pulled-back morphisms. -/
private lemma pullHom_conj ⦃X₁ X₂ : C⦄ ⦃M₁ M₁' : G.obj (.mk (op X₁))⦄
    ⦃M₂ M₂' : G.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ (a : M₁ ⟶ M₁')
    (ψ : (G.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (G.map f₂.op.toLoc).toFunctor.obj M₂')
    (b : M₂' ⟶ M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((G.map f₁.op.toLoc).toFunctor.map a ≫ ψ ≫ (G.map f₂.op.toLoc).toFunctor.map b)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (G.map gf₁.op.toLoc).toFunctor.map a ≫ pullHom ψ g gf₁ gf₂ hgf₁ hgf₂ ≫
        (G.map gf₂.op.toLoc).toFunctor.map b := by
  simp [pullHom]

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Descent data are functorial along strong transformations: the components of `α` are
applied to the objects of a descent datum, and its gluing morphisms are conjugated by the
naturality isomorphisms of `α`. -/
@[simps]
def DescentData.map (α : F ⟶ G) : F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (α.app _).toFunctor.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (α.app _).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
            (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [pullHom_naturality, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self Y q i g hg := by simp [D.hom_self q g hg]
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
        rw [← Functor.map_comp_assoc, D.hom_comp] }
  map {D₁ D₂} φ :=
    { hom i := (α.app _).toFunctor.map (φ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have h₁ := (α.naturality f₁.op.toLoc).inv.toNatTrans.naturality (φ.hom i₁)
        have h₂ := (α.naturality f₂.op.toLoc).hom.toNatTrans.naturality (φ.hom i₂)
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc]
        rw [reassoc_of% h₁, ← Functor.map_comp_assoc, φ.comm q f₁ f₂ hf₁ hf₂,
          Functor.map_comp_assoc, h₂] }

/-- Restriction to descent data commutes with a strong transformation `α`, up to the
naturality isomorphisms of `α`. -/
@[simps!]
def toDescentDataCompMapIso (α : F ⟶ G) :
    F.toDescentData f ⋙ DescentData.map f α ≅
      (α.app (.mk (op S))).toFunctor ⋙ G.toDescentData f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk
      (fun i ↦ (Cat.Hom.toNatIso (α.naturality (f i).op.toLoc)).app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        dsimp
        rw [← cancel_epi ((α.naturality f₁.op.toLoc).hom.toNatTrans.app _)]
        simp only [Functor.map_comp, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
        rw [naturality_mapComp'_hom_app, naturality_mapComp'_inv_app_assoc]))
    (fun φ ↦ by
      ext i
      exact (α.naturality (f i).op.toLoc).hom.toNatTrans.naturality φ)

namespace DescentData

set_option backward.isDefEq.respectTransparency false in
/-- `DescentData.map` sends the identity strong transformation to the identity functor. -/
@[simps!]
def mapId : DescentData.map f (𝟙 F) ≅ 𝟭 (F.DescentData f) :=
  NatIso.ofComponents (fun D ↦ isoMk (fun i ↦ Iso.refl (D.obj i))
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by simp))

set_option backward.isDefEq.respectTransparency false in
/-- `DescentData.map` sends a composite of strong transformations to the composite of the
induced functors. -/
@[simps!]
def mapComp (α : F ⟶ G) (β : G ⟶ H) :
    DescentData.map f (α ≫ β) ≅ DescentData.map f α ⋙ DescentData.map f β :=
  NatIso.ofComponents (fun D ↦ isoMk
    (fun i ↦ Iso.refl ((β.app _).toFunctor.obj ((α.app _).toFunctor.obj (D.obj i))))
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by simp))

/-- An invertible modification induces an isomorphism of the induced functors. -/
@[simps!]
def mapIso {α α' : F ⟶ G} (e : α ≅ α') :
    DescentData.map f α ≅ DescentData.map f α' :=
  NatIso.ofComponents
    (fun D ↦ isoMk
      (fun i ↦
        { hom := (e.hom.as.app _).toNatTrans.app (D.obj i)
          inv := (e.inv.as.app _).toNatTrans.app (D.obj i)
          hom_inv_id :=
            congr_arg (fun m ↦ (m.as.app (.mk (op (X i)))).toNatTrans.app (D.obj i)) e.hom_inv_id
          inv_hom_id :=
            congr_arg (fun m ↦ (m.as.app (.mk (op (X i)))).toNatTrans.app (D.obj i))
              e.inv_hom_id })
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        have h₁ := congr_arg (fun t ↦ t.toNatTrans.app (D.obj i₁))
          (e.hom.as.naturality f₁.op.toLoc)
        have h₂ := congr_arg (fun t ↦ t.toNatTrans.app (D.obj i₂))
          (e.hom.as.naturality f₂.op.toLoc)
        have h₃ := (e.hom.as.app (.mk (op Y))).toNatTrans.naturality (D.hom q f₁ f₂ hf₁ hf₂)
        dsimp at h₁ h₂ h₃ ⊢
        rw [← cancel_epi ((α.naturality f₁.op.toLoc).hom.toNatTrans.app (D.obj i₁)),
          ← reassoc_of% h₁]
        simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
        rw [← reassoc_of% h₃, h₂]))
    (fun φ ↦ by
      ext i
      exact (e.hom.as.app _).toNatTrans.naturality _)

instance faithful_map (α : F ⟶ G) [∀ X, (α.app X).toFunctor.Faithful] :
    (DescentData.map f α).Faithful where
  map_injective {D₁ D₂} φ ψ h := by
    ext i
    exact (α.app _).toFunctor.map_injective (congr_arg (fun χ ↦ χ.hom i) h)

set_option backward.isDefEq.respectTransparency false in
instance full_map (α : F ⟶ G) [∀ X, (α.app X).toFunctor.Full]
    [∀ X, (α.app X).toFunctor.Faithful] : (DescentData.map f α).Full where
  map_surjective {D₁ D₂} ψ := by
    refine ⟨{ hom i := (α.app _).toFunctor.preimage (ψ.hom i), comm := ?_ }, ?_⟩
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      apply (α.app (.mk (op Y))).toFunctor.map_injective
      have h₁ := (α.naturality f₁.op.toLoc).hom.toNatTrans.naturality
        ((α.app _).toFunctor.preimage (ψ.hom i₁))
      have h₂ := (α.naturality f₂.op.toLoc).hom.toNatTrans.naturality
        ((α.app _).toFunctor.preimage (ψ.hom i₂))
      have h₃ := ψ.comm q f₁ f₂ hf₁ hf₂
      dsimp at h₁ h₂ h₃
      simp only [Functor.map_preimage] at h₁ h₂
      simp only [Category.assoc] at h₃
      rw [← cancel_mono ((α.naturality f₂.op.toLoc).hom.toNatTrans.app (D₂.obj i₂))]
      simp only [Functor.map_comp, Category.assoc]
      rw [h₂, ← cancel_epi ((α.naturality f₁.op.toLoc).inv.toNatTrans.app (D₁.obj i₁)),
        ← h₃, ← cancel_epi ((α.naturality f₁.op.toLoc).hom.toNatTrans.app (D₁.obj i₁))]
      simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      rw [← reassoc_of% h₁, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    · ext i
      exact Functor.map_preimage _ _

instance isEquivalence_map (α : F ⟶ G) [∀ X, (α.app X).toFunctor.IsEquivalence] :
    (DescentData.map f α).IsEquivalence where
  essSurj := ⟨fun E ↦ by
    refine ⟨
      { obj i := (α.app (.mk (op (X i)))).toFunctor.objPreimage (E.obj i)
        hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (α.app (.mk (op Y))).toFunctor.preimage
          ((α.naturality f₁.op.toLoc).hom.toNatTrans.app _ ≫
            (G.map f₁.op.toLoc).toFunctor.map
              ((α.app (.mk (op (X i₁)))).toFunctor.objObjPreimageIso (E.obj i₁)).hom ≫
            E.hom q f₁ f₂ hf₁ hf₂ ≫
            (G.map f₂.op.toLoc).toFunctor.map
              ((α.app (.mk (op (X i₂)))).toFunctor.objObjPreimageIso (E.obj i₂)).inv ≫
            (α.naturality f₂.op.toLoc).inv.toNatTrans.app _)
        pullHom_hom := ?_
        hom_self := ?_
        hom_comp := ?_ },
      ⟨isoMk (fun i ↦ (α.app (.mk (op (X i)))).toFunctor.objObjPreimageIso (E.obj i)) ?_⟩⟩
    · intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      apply (α.app (.mk (op Y'))).toFunctor.map_injective
      rw [Functor.map_preimage,
        ← cancel_epi ((α.naturality gf₁.op.toLoc).inv.toNatTrans.app _),
        ← cancel_mono ((α.naturality gf₂.op.toLoc).hom.toNatTrans.app _)]
      simp only [Category.assoc]
      rw [← pullHom_naturality]
      simp only [Functor.map_preimage, Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
        Cat.Hom.inv_hom_id_toNatTrans_app]
      dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj]
      simp only [Category.comp_id]
      rw [pullHom_conj, E.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
    · intro Y q i g hg
      apply (α.app (.mk (op Y))).toFunctor.map_injective
      simp [E.hom_self q g hg]
    · intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
      apply (α.app (.mk (op Y))).toFunctor.map_injective
      simp
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      simp⟩

end DescentData

end CategoryTheory.Pseudofunctor
