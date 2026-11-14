/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent data along one morphism as comonad coalgebras

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` be a pseudofunctor to adjunctions, so that each
`g : Y ⟶ X` has a pullback functor `g^*` (the left adjoint `(F.map g.op.toLoc).l`) with a right
adjoint `g_*`. Descent data are taken for the left adjoints, the `Cat`-valued pseudofunctor
`F.comp Adj.forget₁`.

Let `f : X ⟶ S`, let `sq` be a chosen pullback of `f` along itself, with projections `p₁` and
`p₂`, and let `sq₃` be a chosen triple pullback. If the base change morphisms of `sq` and of
`sq₃.chosenPullback` are isomorphisms, descent data along `f` over these chosen pullbacks are
coalgebras for the comonad `f^* f_*` (Bénabou–Roubaud), compatibly with the comparison functors
from objects over `S`. Consequently `F.comp Adj.forget₁` has effective descent along `f` exactly
when `f^*` is comonadic.

## Main definitions

* `Pseudofunctor.baseChange h`: the base change morphism `f₁^* (f₂)_* ⟶ (p₁)_* p₂^*` of a
  chosen pullback `h` of `f₁` and `f₂`, a 2-morphism of `Cat`.
* `Pseudofunctor.descentDataCoalgebraEquivalence`: the equivalence between descent data along
  `f` over `sq` and `sq₃` and coalgebras for the comonad of `f^* ⊣ f_*`.
* `Pseudofunctor.toDescentDataCompDescentDataCoalgebraEquivalenceIso`: the comparison functor
  from objects over `S`, followed by that equivalence, is `Comonad.comparison`.
* `Pseudofunctor.descentDataAsCoalgebraEquivalence`: the comparison with Mathlib's
  `DescentDataAsCoalgebra` for an index type with a unique element.

## Main results

* `Pseudofunctor.isStackFor_singleton_iff_isEquivalence_comparison`: under the two base change
  hypotheses, `F.comp Adj.forget₁` is a stack for `Presieve.singleton f` if and only if
  `Comonad.comparison` of `f^* ⊣ f_*` is an equivalence.

## Implementation notes

A descent datum `φ : p₁^* N ⟶ p₂^* N` corresponds, by the adjunction `p₁^* ⊣ (p₁)_*`, to a
morphism `N ⟶ (p₁)_* p₂^* N`, and by the inverse of the base change morphism of `sq` to a
morphism `N ⟶ f^* f_* N`. The forward direction `c ↦ p₁^* c ≫ (p₁^* f^* ≅ p₂^* f^*) ≫ p₂^* ε`
needs no hypothesis. The cocycle condition and coassociativity are compared through one map
from `N ⟶ f^* f_* f^* f_* N` to morphisms over the triple pullback; it is injective because it
factors through the two base change morphisms, the second one rewriting `p₂^* (p₁)_*` over
`sq₃.chosenPullback`.

Both base change morphisms are assumed invertible as 2-morphisms of `Cat`, not only on the
essential image of `f^*`.

The internal computations use the pullback functors of `F.comp Adj.forget₁` throughout and
convert to the left adjoints of `F` only at the statements, so the simp lemma that unfolds
`Pseudofunctor.comp` is disabled in this file.

## References

* J. Bénabou, J. Roubaud, *Monades et descente*, C. R. Acad. Sci. Paris Sér. A-B 270 (1970).

## Tags

descent, comonad, coalgebra, base change, Bénabou–Roubaud
-/

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory Limits LocallyDiscreteOpToCat

-- Keep `(F.comp Adj.forget₁).map g` from unfolding to `(F.map g).l`, so that the lemmas about
-- the compositors of `F.comp Adj.forget₁` keep applying.
attribute [-simp] Pseudofunctor.comp_toPrelaxFunctor

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'})

private lemma op_toLoc_comp_eq {Y Y' Z : C} {g : Y' ⟶ Y} {k : Y ⟶ Z} {q : Y' ⟶ Z}
    (h : g ≫ k = q) : k.op.toLoc ≫ g.op.toLoc = q.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]

/-- The pushforward functor `g_*`, between the fibres of `F.comp Adj.forget₁`. -/
private def pushforward {X Y : C} (g : Y ⟶ X) :
    (F.comp Adj.forget₁).obj (.mk (op Y)) ⥤ (F.comp Adj.forget₁).obj (.mk (op X)) :=
  (F.map g.op.toLoc).r.toFunctor

/-- The adjunction `g^* ⊣ g_*`, with `g^*` the pullback functor of `F.comp Adj.forget₁`. -/
private def adjOfCat {X Y : C} (g : Y ⟶ X) :
    ((F.comp Adj.forget₁).map g.op.toLoc).toFunctor ⊣ pushforward F g :=
  Adjunction.ofCat (F.map g.op.toLoc).adj

section

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} (h : ChosenPullback f₁ f₂)

/-- The comparison `p₁^* f₁^* K ⟶ p₂^* f₂^* K` through `p^* K`. -/
private def twist (K : (F.comp Adj.forget₁).obj (.mk (op S))) :
    ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.obj
        (((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj K) ⟶
      ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.obj
        (((F.comp Adj.forget₁).map f₂.op.toLoc).toFunctor.obj K) :=
  ((F.comp Adj.forget₁).mapComp' f₁.op.toLoc h.p₁.op.toLoc h.p.op.toLoc
      (op_toLoc_comp_eq h.hp₁)).inv.toNatTrans.app K ≫
    ((F.comp Adj.forget₁).mapComp' f₂.op.toLoc h.p₂.op.toLoc h.p.op.toLoc
      (op_toLoc_comp_eq h.hp₂)).hom.toNatTrans.app K

@[reassoc]
private lemma twist_naturality {K K' : (F.comp Adj.forget₁).obj (.mk (op S))} (x : K ⟶ K') :
    ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.map x) ≫ twist F h K' =
      twist F h K ≫ ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).map f₂.op.toLoc).toFunctor.map x) := by
  simp [twist]

/-- The components of `baseChange`. -/
private def baseChangeApp (M : (F.comp Adj.forget₁).obj (.mk (op X₂))) :
    ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M) ⟶
      (pushforward F h.p₁).obj (((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.obj M) :=
  (adjOfCat F h.p₁).unit.app _ ≫ (pushforward F h.p₁).map (twist F h _ ≫
    ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map ((adjOfCat F f₂).counit.app M))

private lemma baseChangeApp_naturality {M M' : (F.comp Adj.forget₁).obj (.mk (op X₂))}
    (g : M ⟶ M') :
    ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.map ((pushforward F f₂).map g) ≫
      baseChangeApp F h M' = baseChangeApp F h M ≫ (pushforward F h.p₁).map
        (((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map g) := by
  dsimp only [baseChangeApp]
  rw [← Adjunction.unit_naturality_assoc]
  simp only [Category.assoc, ← Functor.map_comp, twist_naturality_assoc,
    Adjunction.counit_naturality]

/-- The base change morphism `f₁^* (f₂)_* ⟶ (p₁)_* p₂^*` of a chosen pullback `h` of `f₁` and
`f₂`, a 2-morphism of `Cat`. At an object `M` over `X₂` it is the composite of three maps:

* the unit `f₁^* (f₂)_* M ⟶ (p₁)_* p₁^* f₁^* (f₂)_* M` of the adjunction `p₁^* ⊣ (p₁)_*`;
* the image under `(p₁)_*` of the compositor isomorphism `p₁^* f₁^* ≅ p^* ≅ p₂^* f₂^*` given
  by `h.condition`, built from the compositors `mapComp'` of `F.comp Adj.forget₁`;
* the image under `(p₁)_* p₂^*` of the counit `f₂^* (f₂)_* M ⟶ M` of `f₂^* ⊣ (f₂)_*`. -/
def baseChange : (F.map f₂.op.toLoc).r ≫ (F.map f₁.op.toLoc).l ⟶
      (F.map h.p₂.op.toLoc).l ≫ (F.map h.p₁.op.toLoc).r :=
  Cat.Hom₂.ofNatTrans
    { app M := baseChangeApp F h M
      naturality _ _ g := baseChangeApp_naturality F h g }

private lemma baseChange_app (M : (F.comp Adj.forget₁).obj (.mk (op X₂))) :
    (F.baseChange h).toNatTrans.app M = baseChangeApp F h M := rfl

private instance [IsIso (F.baseChange h)] (M : (F.comp Adj.forget₁).obj (.mk (op X₂))) :
    IsIso (baseChangeApp F h M) := by
  have : IsIso (F.baseChange h).toNatTrans :=
    inferInstanceAs (IsIso (asIso (F.baseChange h)).hom.toNatTrans)
  exact NatIso.isIso_app_of_isIso (F.baseChange h).toNatTrans M

/-- The morphism `p₁^* N ⟶ p₂^* M` attached to `c : N ⟶ f₁^* (f₂)_* M`. -/
private def descentHom {N : (F.comp Adj.forget₁).obj (.mk (op X₁))}
    {M : (F.comp Adj.forget₁).obj (.mk (op X₂))}
    (c : N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M)) :
    ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.obj N ⟶
      ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.obj M :=
  ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.map c ≫ twist F h _ ≫
    ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map ((adjOfCat F f₂).counit.app M)

section

variable {N N' : (F.comp Adj.forget₁).obj (.mk (op X₁))}
  {M M' : (F.comp Adj.forget₁).obj (.mk (op X₂))}

private lemma descentHom_eq
    (c : N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M)) :
    descentHom F h c = ((adjOfCat F h.p₁).homEquiv _ _).symm (c ≫ baseChangeApp F h M) := by
  simp [descentHom, baseChangeApp, Adjunction.homEquiv_counit]

private lemma descentHom_comp_left (g : N' ⟶ N)
    (c : N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M)) :
    descentHom F h (g ≫ c) =
      ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.map g ≫ descentHom F h c := by
  simp [descentHom]

private lemma descentHom_comp_right
    (c : N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M))
    (g : M ⟶ M') :
    descentHom F h (c ≫ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.map
        ((pushforward F f₂).map g)) =
      descentHom F h c ≫ ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map g := by
  simp only [descentHom, Functor.map_comp, Category.assoc, twist_naturality_assoc]
  simp only [← Functor.map_comp, Adjunction.counit_naturality]

variable [IsIso (F.baseChange h)]

private lemma descentHom_injective :
    Function.Injective (descentHom F h (N := N) (M := M)) := by
  intro c c' hc
  rw [descentHom_eq, descentHom_eq] at hc
  exact (cancel_mono (baseChangeApp F h M)).1
    (((adjOfCat F h.p₁).homEquiv _ _).symm.injective hc)

/-- The inverse of `descentHom` when the base change morphism is an isomorphism. -/
private noncomputable def descentHomInv
    (φ : ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.obj N ⟶
      ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.obj M) :
    N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M) :=
  (adjOfCat F h.p₁).homEquiv _ _ φ ≫ inv (baseChangeApp F h M)

@[simp]
private lemma descentHom_descentHomInv
    (φ : ((F.comp Adj.forget₁).map h.p₁.op.toLoc).toFunctor.obj N ⟶
      ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.obj M) :
    descentHom F h (descentHomInv F h φ) = φ := by
  simp [descentHom_eq, descentHomInv]

@[simp]
private lemma descentHomInv_descentHom
    (c : N ⟶ ((F.comp Adj.forget₁).map f₁.op.toLoc).toFunctor.obj ((pushforward F f₂).obj M)) :
    descentHomInv F h (descentHom F h c) = c :=
  descentHom_injective F h (by simp)

end

end

@[reassoc]
private lemma pullHom_map_comp_map {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} ⦃X₁ X₂ : C⦄
    {M₁ M₁' : G.obj (.mk (op X₁))} {M₂ M₂' : G.obj (.mk (op X₂))} ⦃Y : C⦄ {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂} (a : M₁ ⟶ M₁')
    (φ : (G.map f₁.op.toLoc).toFunctor.obj M₁' ⟶ (G.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : M₂ ⟶ M₂') ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom ((G.map f₁.op.toLoc).toFunctor.map a ≫ φ ≫ (G.map f₂.op.toLoc).toFunctor.map b)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (G.map gf₁.op.toLoc).toFunctor.map a ≫ pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
        (G.map gf₂.op.toLoc).toFunctor.map b := by
  simp only [pullHom, Functor.map_comp, Category.assoc, mapComp'_inv_naturality]
  rw [← mapComp'_hom_naturality_assoc]

section

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)

private lemma pullHom_twist (K : (F.comp Adj.forget₁).obj (.mk (op S))) ⦃Y : C⦄
    (g : Y ⟶ sq.pullback) (g₁ g₂ : Y ⟶ X) (hg₁ : g ≫ sq.p₁ = g₁) (hg₂ : g ≫ sq.p₂ = g₂)
    (q : Y ⟶ S) (hq₁ : g₁ ≫ f = q) (hq₂ : g₂ ≫ f = q) :
    pullHom (twist F sq K) g g₁ g₂ hg₁ hg₂ =
      ((F.comp Adj.forget₁).mapComp' f.op.toLoc g₁.op.toLoc q.op.toLoc
          (op_toLoc_comp_eq hq₁)).inv.toNatTrans.app K ≫
        ((F.comp Adj.forget₁).mapComp' f.op.toLoc g₂.op.toLoc q.op.toLoc
          (op_toLoc_comp_eq hq₂)).hom.toNatTrans.app K :=
  (DescentData.ofObj (F := F.comp Adj.forget₁) (f := fun (_ : Unit) ↦ f) K).pullHom_hom g sq.p
    q (by rw [← hq₁, ← hg₁, Category.assoc, sq.hp₁]) (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂
    (by simp) (by simp) g₁ g₂ hg₁ hg₂

private lemma pullHom_descentHom {N M : (F.comp Adj.forget₁).obj (.mk (op X))}
    (c : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj M))
    ⦃Y : C⦄ (g : Y ⟶ sq.pullback) (g₁ g₂ : Y ⟶ X) (hg₁ : g ≫ sq.p₁ = g₁)
    (hg₂ : g ≫ sq.p₂ = g₂) (q : Y ⟶ S) (hq₁ : g₁ ≫ f = q) (hq₂ : g₂ ≫ f = q) :
    pullHom (descentHom F sq c) g g₁ g₂ hg₁ hg₂ =
      ((F.comp Adj.forget₁).map g₁.op.toLoc).toFunctor.map c ≫
        ((F.comp Adj.forget₁).mapComp' f.op.toLoc g₁.op.toLoc q.op.toLoc
          (op_toLoc_comp_eq hq₁)).inv.toNatTrans.app _ ≫
        ((F.comp Adj.forget₁).mapComp' f.op.toLoc g₂.op.toLoc q.op.toLoc
          (op_toLoc_comp_eq hq₂)).hom.toNatTrans.app _ ≫
        ((F.comp Adj.forget₁).map g₂.op.toLoc).toFunctor.map ((adjOfCat F f).counit.app M) := by
  rw [descentHom, pullHom_map_comp_map, pullHom_twist F sq _ g g₁ g₂ hg₁ hg₂ q hq₁ hq₂,
    Category.assoc]

private lemma map_id_eq_id_iff {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (x : N ⟶ N) :
    ((F.comp Adj.forget₁).map (𝟙 X).op.toLoc).toFunctor.map x = 𝟙 _ ↔ x = 𝟙 N := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by rw [hx, Functor.map_id]⟩
  have := mapId'_hom_naturality (F.comp Adj.forget₁) (𝟙 X).op.toLoc rfl x
  rw [hx, Category.id_comp] at this
  exact (cancel_epi _).1 (this.symm.trans (Category.comp_id _).symm)

private lemma pullHom_descentHom_self_iff {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (a : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))
    (d : X ⟶ sq.pullback) (hd₁ : d ≫ sq.p₁ = 𝟙 X) (hd₂ : d ≫ sq.p₂ = 𝟙 X) :
    pullHom (descentHom F sq a) d (𝟙 X) (𝟙 X) hd₁ hd₂ = 𝟙 _ ↔
      a ≫ (adjOfCat F f).counit.app N = 𝟙 N := by
  rw [pullHom_descentHom F sq a d _ _ hd₁ hd₂ f (by simp) (by simp),
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc, ← Functor.map_comp, map_id_eq_id_iff F]

end

section

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)

/-- The morphism over the triple product through which coassociativity is compared with the
cocycle condition. -/
private def cocycleMap {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (c : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj
      (((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N)))) :
    ((F.comp Adj.forget₁).map sq₃.p₁.op.toLoc).toFunctor.obj N ⟶
      ((F.comp Adj.forget₁).map sq₃.p₃.op.toLoc).toFunctor.obj N :=
  ((F.comp Adj.forget₁).map sq₃.p₁.op.toLoc).toFunctor.map c ≫
    ((F.comp Adj.forget₁).mapComp' f.op.toLoc sq₃.p₁.op.toLoc sq₃.p.op.toLoc
      (op_toLoc_comp_eq sq₃.w₁)).inv.toNatTrans.app _ ≫
    ((F.comp Adj.forget₁).mapComp' f.op.toLoc sq₃.p₂.op.toLoc sq₃.p.op.toLoc
      (op_toLoc_comp_eq sq₃.w₂)).hom.toNatTrans.app _ ≫
    ((F.comp Adj.forget₁).map sq₃.p₂.op.toLoc).toFunctor.map ((adjOfCat F f).counit.app _) ≫
    ((F.comp Adj.forget₁).mapComp' f.op.toLoc sq₃.p₂.op.toLoc sq₃.p.op.toLoc
      (op_toLoc_comp_eq sq₃.w₂)).inv.toNatTrans.app _ ≫
    ((F.comp Adj.forget₁).mapComp' f.op.toLoc sq₃.p₃.op.toLoc sq₃.p.op.toLoc
      (op_toLoc_comp_eq sq₃.w₃)).hom.toNatTrans.app _ ≫
    ((F.comp Adj.forget₁).map sq₃.p₃.op.toLoc).toFunctor.map ((adjOfCat F f).counit.app N)

private lemma pullHom_comp_pullHom_descentHom {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (a : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))
    (g₁₂ g₂₃ : sq₃.pullback ⟶ sq.pullback) (h₁ : g₁₂ ≫ sq.p₁ = sq₃.p₁)
    (h₂ : g₁₂ ≫ sq.p₂ = sq₃.p₂) (h₂' : g₂₃ ≫ sq.p₁ = sq₃.p₂) (h₃ : g₂₃ ≫ sq.p₂ = sq₃.p₃) :
    pullHom (descentHom F sq a) g₁₂ sq₃.p₁ sq₃.p₂ h₁ h₂ ≫
        pullHom (descentHom F sq a) g₂₃ sq₃.p₂ sq₃.p₃ h₂' h₃ =
      cocycleMap F sq sq₃ (a ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map
        ((pushforward F f).map a)) := by
  rw [pullHom_descentHom F sq a g₁₂ _ _ h₁ h₂ sq₃.p sq₃.w₁ sq₃.w₂,
    pullHom_descentHom F sq a g₂₃ _ _ h₂' h₃ sq₃.p sq₃.w₂ sq₃.w₃]
  simp only [cocycleMap, Functor.map_comp, Category.assoc]
  rw [mapComp'_inv_naturality_assoc, mapComp'_hom_naturality_assoc,
    ← Functor.map_comp_assoc _
      (((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map ((pushforward F f).map a)),
    (adjOfCat F f).counit_naturality a, Functor.map_comp_assoc]

private lemma pullHom_descentHom_p₁₃ {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (a : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))
    (g₁₃ : sq₃.pullback ⟶ sq.pullback) (h₁ : g₁₃ ≫ sq.p₁ = sq₃.p₁)
    (h₃ : g₁₃ ≫ sq.p₂ = sq₃.p₃) :
    pullHom (descentHom F sq a) g₁₃ sq₃.p₁ sq₃.p₃ h₁ h₃ =
      cocycleMap F sq sq₃ (a ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map
        ((adjOfCat F f).unit.app ((pushforward F f).obj N))) := by
  rw [pullHom_descentHom F sq a g₁₃ _ _ h₁ h₃ sq₃.p sq₃.w₁ sq₃.w₃]
  simp only [cocycleMap, Functor.map_comp, Category.assoc]
  rw [mapComp'_inv_naturality_assoc, mapComp'_hom_naturality_assoc,
    ← Functor.map_comp_assoc ((F.comp Adj.forget₁).map sq₃.p₂.op.toLoc).toFunctor,
    Adjunction.left_triangle_components, Functor.map_id, Category.id_comp,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

private lemma descentHom_chosenPullback_comp {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (d : ((F.comp Adj.forget₁).map sq.p₁.op.toLoc).toFunctor.obj N ⟶
      ((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.obj
        (((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))) :
    descentHom F sq₃.chosenPullback
        (d ≫ ((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.map (baseChangeApp F sq N)) =
      ((F.comp Adj.forget₁).map sq₃.chosenPullback.p₁.op.toLoc).toFunctor.map d ≫
        twist F sq₃.chosenPullback _ ≫
        ((F.comp Adj.forget₁).map sq₃.chosenPullback.p₂.op.toLoc).toFunctor.map
          (descentHom F sq (𝟙 _)) := by
  rw [descentHom, descentHom_eq F sq, Adjunction.homEquiv_counit, Category.id_comp,
    Functor.map_comp, Category.assoc, twist_naturality_assoc, ← Functor.map_comp]

private lemma map_twist_map_eq {A B D : (F.comp Adj.forget₁).obj (.mk (op X))}
    (d : ((F.comp Adj.forget₁).map sq.p₁.op.toLoc).toFunctor.obj A ⟶
      ((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.obj B)
    (e : ((F.comp Adj.forget₁).map sq.p₁.op.toLoc).toFunctor.obj B ⟶
      ((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.obj D) :
    ((F.comp Adj.forget₁).map sq₃.chosenPullback.p₁.op.toLoc).toFunctor.map d ≫
        twist F sq₃.chosenPullback B ≫
        ((F.comp Adj.forget₁).map sq₃.chosenPullback.p₂.op.toLoc).toFunctor.map e =
      ((F.comp Adj.forget₁).mapComp' sq.p₁.op.toLoc sq₃.chosenPullback.p₁.op.toLoc
          sq₃.p₁.op.toLoc (op_toLoc_comp_eq sq₃.hp₁)).inv.toNatTrans.app A ≫
        pullHom d sq₃.chosenPullback.p₁ sq₃.p₁ sq₃.chosenPullback.p sq₃.hp₁
          sq₃.chosenPullback.hp₁ ≫
        pullHom e sq₃.chosenPullback.p₂ sq₃.chosenPullback.p sq₃.p₃ sq₃.chosenPullback.hp₂
          sq₃.hp₃ ≫
        ((F.comp Adj.forget₁).mapComp' sq.p₂.op.toLoc sq₃.chosenPullback.p₂.op.toLoc
          sq₃.p₃.op.toLoc (op_toLoc_comp_eq sq₃.hp₃)).hom.toNatTrans.app D := by
  simp [pullHom, twist]

@[reassoc]
private lemma pullHom_comp_pullHom_eq_cocycleMap {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (c : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj
      (((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N)))) :
    pullHom (descentHom F sq c) sq₃.chosenPullback.p₁ sq₃.p₁ sq₃.chosenPullback.p sq₃.hp₁
        sq₃.chosenPullback.hp₁ ≫
      pullHom (descentHom F sq (𝟙 _)) sq₃.chosenPullback.p₂ sq₃.chosenPullback.p sq₃.p₃
        sq₃.chosenPullback.hp₂ sq₃.hp₃ =
      cocycleMap F sq sq₃ c := by
  rw [pullHom_descentHom F sq c sq₃.chosenPullback.p₁ sq₃.p₁ sq₃.chosenPullback.p sq₃.hp₁
      sq₃.chosenPullback.hp₁ sq₃.p sq₃.w₁ sq₃.w₂,
    pullHom_descentHom F sq _ sq₃.chosenPullback.p₂ sq₃.chosenPullback.p sq₃.p₃
      sq₃.chosenPullback.hp₂ sq₃.hp₃ sq₃.p sq₃.w₂ sq₃.w₃]
  simp only [Functor.map_id, Category.id_comp, Category.assoc]
  rfl

private lemma pullHom_comp_pullHom_descentHom_of_coassoc
    {N : (F.comp Adj.forget₁).obj (.mk (op X))}
    (a : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))
    (ha : a ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map ((pushforward F f).map a) =
      a ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map
        ((adjOfCat F f).unit.app ((pushforward F f).obj N)))
    (g₁₂ g₂₃ g₁₃ : sq₃.pullback ⟶ sq.pullback) (h₁ : g₁₂ ≫ sq.p₁ = sq₃.p₁)
    (h₂ : g₁₂ ≫ sq.p₂ = sq₃.p₂) (h₂' : g₂₃ ≫ sq.p₁ = sq₃.p₂) (h₃ : g₂₃ ≫ sq.p₂ = sq₃.p₃)
    (h₁' : g₁₃ ≫ sq.p₁ = sq₃.p₁) (h₃' : g₁₃ ≫ sq.p₂ = sq₃.p₃) :
    pullHom (descentHom F sq a) g₁₂ sq₃.p₁ sq₃.p₂ h₁ h₂ ≫
        pullHom (descentHom F sq a) g₂₃ sq₃.p₂ sq₃.p₃ h₂' h₃ =
      pullHom (descentHom F sq a) g₁₃ sq₃.p₁ sq₃.p₃ h₁' h₃' := by
  rw [pullHom_comp_pullHom_descentHom, pullHom_descentHom_p₁₃, ha]

private lemma cocycleMap_injective [IsIso (F.baseChange sq)]
    [IsIso (F.baseChange sq₃.chosenPullback)] {N : (F.comp Adj.forget₁).obj (.mk (op X))} :
    Function.Injective (cocycleMap F sq sq₃ (N := N)) := by
  intro c c' hcc'
  apply descentHom_injective F sq
  apply (cancel_mono (((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.map
    (baseChangeApp F sq N))).1
  apply descentHom_injective F sq₃.chosenPullback
  rw [descentHom_chosenPullback_comp, descentHom_chosenPullback_comp, map_twist_map_eq,
    map_twist_map_eq, pullHom_comp_pullHom_eq_cocycleMap_assoc,
    pullHom_comp_pullHom_eq_cocycleMap_assoc, hcc']

end

section

variable {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)

private lemma descentHom_map_unit (M : (F.comp Adj.forget₁).obj (.mk (op S))) :
    descentHom F sq (N := ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj M)
      (M := ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj M)
      (((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map ((adjOfCat F f).unit.app M)) =
      twist F sq M := by
  rw [descentHom, twist_naturality_assoc, ← Functor.map_comp,
    (adjOfCat F f).left_triangle_components M, Functor.map_id, Category.comp_id]

private lemma descentHom_comm {N N' : (F.comp Adj.forget₁).obj (.mk (op X))}
    (a : N ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N))
    (a' : N' ⟶ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj ((pushforward F f).obj N'))
    (g : N ⟶ N')
    (h : a ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map ((pushforward F f).map g) =
      g ≫ a') :
    ((F.comp Adj.forget₁).map sq.p₁.op.toLoc).toFunctor.map g ≫ descentHom F sq a' =
      descentHom F sq a ≫ ((F.comp Adj.forget₁).map sq.p₂.op.toLoc).toFunctor.map g := by
  rw [← descentHom_comp_left, ← descentHom_comp_right, h]

private lemma descentHomInv_twist [IsIso (F.baseChange sq)]
    (M : (F.comp Adj.forget₁).obj (.mk (op S))) :
    descentHomInv F sq (N := ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj M)
      (M := ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.obj M) (twist F sq M) =
      ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map ((adjOfCat F f).unit.app M) := by
  rw [← descentHom_map_unit, descentHomInv_descentHom]

end

section

variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {ι : Type t} {X S : C} {f : X ⟶ S}
  {sq : ChosenPullback f f} {sq₃ : ChosenPullback₃ sq sq sq}

private lemma DescentData'.hom_eqToHom
    (D : G.DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃)) {i₁ i₂ j₁ j₂ : ι}
    (h₁ : i₁ = j₁) (h₂ : i₂ = j₂) :
    (G.map sq.p₁.op.toLoc).toFunctor.map (eqToHom (congrArg D.obj h₁)) ≫ D.hom j₁ j₂ =
      D.hom i₁ i₂ ≫ (G.map sq.p₂.op.toLoc).toFunctor.map (eqToHom (congrArg D.obj h₂)) := by
  subst h₁ h₂
  simp

private lemma DescentData'.Hom.hom_eqToHom
    {D₁ D₂ : G.DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃)} (φ : D₁ ⟶ D₂) {i j : ι}
    (h : i = j) :
    φ.hom i ≫ eqToHom (congrArg D₂.obj h) = eqToHom (congrArg D₁.obj h) ≫ φ.hom j := by
  subst h
  simp

end

section

variable (ι : Type t) [Unique ι] {X S : C} (f : X ⟶ S) (sq : ChosenPullback f f)
  (sq₃ : ChosenPullback₃ sq sq sq)

/-- The functor from descent data to coalgebras. -/
private noncomputable def toCoalgebra [IsIso (F.baseChange sq)]
    [IsIso (F.baseChange sq₃.chosenPullback)] :
    (F.comp Adj.forget₁).DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃) ⥤
      (Adjunction.ofCat (F.map f.op.toLoc).adj).toComonad.Coalgebra where
  obj D :=
    { A := D.obj default
      a := descentHomInv F sq (D.hom default default)
      counit := by
        have h := D.pullHom'_hom_self default
        dsimp only [DescentData'.pullHom'] at h
        rw [← descentHom_descentHomInv F sq (D.hom default default)] at h
        exact (pullHom_descentHom_self_iff F sq _ _ _ _).1 h
      coassoc := by
        have h := D.pullHom'_hom_comp default default default
        dsimp only [DescentData'.pullHom'] at h
        rw [← descentHom_descentHomInv F sq (D.hom default default),
          pullHom_comp_pullHom_descentHom F sq sq₃,
          pullHom_descentHom_p₁₃ F sq sq₃] at h
        exact cocycleMap_injective F sq sq₃ h.symm }
  map {D₁ D₂} φ :=
    { f := φ.hom default
      h := by
        apply descentHom_injective F sq
        change descentHom F sq (_ ≫ ((F.comp Adj.forget₁).map f.op.toLoc).toFunctor.map
          ((pushforward F f).map (φ.hom default))) = descentHom F sq (φ.hom default ≫ _)
        rw [descentHom_comp_right, descentHom_comp_left, descentHom_descentHomInv,
          descentHom_descentHomInv]
        exact (φ.comm default default).symm }

/-- The functor from coalgebras to descent data. -/
private def ofCoalgebra :
    (Adjunction.ofCat (F.map f.op.toLoc).adj).toComonad.Coalgebra ⥤
      (F.comp Adj.forget₁).DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃) where
  obj A :=
    { obj _ := A.A
      hom _ _ := descentHom F sq A.a
      pullHom'_hom_self _ := (pullHom_descentHom_self_iff F sq A.a _ _ _).2 A.counit
      pullHom'_hom_comp _ _ _ :=
        pullHom_comp_pullHom_descentHom_of_coassoc F sq sq₃ A.a A.coassoc.symm
          _ _ _ _ _ _ _ _ _ }
  map {A B} φ :=
    { hom _ := φ.f
      comm _ _ := descentHom_comm F sq A.a B.a φ.f φ.h }

/-- **Bénabou–Roubaud for one morphism.** If the base change morphisms of the chosen pullback
`sq` of `f` along itself and of `sq₃.chosenPullback` are isomorphisms, descent data for
`F.comp Adj.forget₁` along `f` over `sq` and `sq₃`, indexed by a type `ι` with a unique element,
are equivalent to coalgebras for the comonad `f^* f_*` of `f^* ⊣ f_*`.

A descent datum `φ : p₁^* N ⟶ p₂^* N` goes to the coalgebra structure `N ⟶ f^* f_* N` obtained
from the transpose `N ⟶ (p₁)_* p₂^* N` of `φ` by the inverse of the base change morphism of
`sq`. The base change morphism of `sq₃.chosenPullback` is used only to show that coassociativity
follows from the cocycle condition. -/
noncomputable def descentDataCoalgebraEquivalence (hsq : IsIso (F.baseChange sq))
    (hsq₃ : IsIso (F.baseChange sq₃.chosenPullback)) :
    (F.comp Adj.forget₁).DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃) ≌
      (Adjunction.ofCat (F.map f.op.toLoc).adj).toComonad.Coalgebra :=
  haveI := hsq
  haveI := hsq₃
  Equivalence.mk (toCoalgebra F ι f sq sq₃) (ofCoalgebra F ι f sq sq₃)
    (NatIso.ofComponents
      (fun D ↦ DescentData'.isoMk
        (fun i ↦ eqToIso (congrArg D.obj (Subsingleton.elim i default)))
        (fun i₁ i₂ ↦ by
          simpa [toCoalgebra, ofCoalgebra] using DescentData'.hom_eqToHom D
            (Subsingleton.elim i₁ default) (Subsingleton.elim i₂ default)))
      (fun {D₁ D₂} φ ↦ by
        ext i
        simpa [toCoalgebra, ofCoalgebra] using
          DescentData'.Hom.hom_eqToHom φ (Subsingleton.elim i default)))
    (NatIso.ofComponents
      (fun A ↦ Comonad.Coalgebra.isoMk (Iso.refl _) (by
        rw [Iso.refl_hom]
        erw [Functor.map_id]
        exact (Category.comp_id _).trans ((descentHomInv_descentHom F sq A.a).trans
          (Category.id_comp _).symm)))
      (fun {A B} φ ↦ by
        ext
        exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- The comparison functor from objects over `S` to descent data along `f`, followed by
`descentDataCoalgebraEquivalence`, is `Comonad.comparison` of the adjunction `f^* ⊣ f_*`. -/
noncomputable def toDescentDataCompDescentDataCoalgebraEquivalenceIso
    (hsq : IsIso (F.baseChange sq)) (hsq₃ : IsIso (F.baseChange sq₃.chosenPullback)) :
    (F.comp Adj.forget₁).toDescentData (fun (_ : ι) ↦ f) ⋙
        (DescentData'.descentDataEquivalence _ _ _).inverse ⋙
        (F.descentDataCoalgebraEquivalence ι f sq sq₃ hsq hsq₃).functor ≅
      Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj) :=
  haveI := hsq
  NatIso.ofComponents
    (fun M ↦ Comonad.Coalgebra.isoMk (Iso.refl _) (by
      rw [Iso.refl_hom]
      erw [Functor.map_id]
      exact (Category.comp_id _).trans ((descentHomInv_twist F sq M).trans
        (Category.id_comp _).symm)))
    (fun {M N} g ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- If the base change morphisms of `sq` and `sq₃.chosenPullback` are isomorphisms,
`F.comp Adj.forget₁` has effective descent along `f` if and only if `f^*` is comonadic, that is,
if and only if `Comonad.comparison` of `f^* ⊣ f_*` is an equivalence. -/
theorem isStackFor_singleton_iff_isEquivalence_comparison
    (hsq : IsIso (F.baseChange sq)) (hsq₃ : IsIso (F.baseChange sq₃.chosenPullback)) :
    (F.comp Adj.forget₁).IsStackFor (Presieve.singleton f) ↔
      (Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj)).IsEquivalence := by
  rw [← Presieve.ofArrows_pUnit.{0}, isStackFor_ofArrows_iff]
  refine Iff.trans ?_ (Functor.isEquivalence_iff_of_iso
    (F.toDescentDataCompDescentDataCoalgebraEquivalenceIso PUnit f sq sq₃ hsq hsq₃))
  constructor
  · intro h
    exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h inferInstance
  · intro h
    exact @Functor.isEquivalence_of_comp_right _ _ _ _ _ _ _
      ((DescentData'.descentDataEquivalence _ _ _).inverse ⋙
        (F.descentDataCoalgebraEquivalence PUnit f sq sq₃ hsq hsq₃).functor) inferInstance h

/-- The TODO of `Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra`, "Compare
`DescentDataAsCoalgebra` with `DescentData` when suitable pullbacks exist and certain base change
morphisms are isomorphisms", for an index type `ι` with a unique element: if the base change
morphisms of `sq` and `sq₃.chosenPullback` are isomorphisms, descent data for
`F.comp Adj.forget₁` along `f` over `sq` and `sq₃` are equivalent to
`F.DescentDataAsCoalgebra (fun (_ : ι) ↦ f)`. `DescentData'.descentDataEquivalence` relates the
source to `DescentData`.

The comparison for a family of morphisms indexed by an arbitrary type is not proved here. -/
noncomputable def descentDataAsCoalgebraEquivalence
    (hsq : IsIso (F.baseChange sq)) (hsq₃ : IsIso (F.baseChange sq₃.chosenPullback)) :
    (F.comp Adj.forget₁).DescentData' (fun (_ _ : ι) ↦ sq) (fun _ _ _ ↦ sq₃) ≌
      F.DescentDataAsCoalgebra (fun (_ : ι) ↦ f) :=
  (F.descentDataCoalgebraEquivalence ι f sq sq₃ hsq hsq₃).trans
    (DescentDataAsCoalgebra.coalgebraEquivalence F ι f).symm

end

end CategoryTheory.Pseudofunctor
