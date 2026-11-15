/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Batteries.Tactic.OpenPrivate
import DerivedAlgGeo.Algebra.Category.ModuleCat.Pseudofunctor
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change for modules along pushout squares of rings

A pullback square in `CommRingCatᵒᵖ` is a pushout square of commutative rings

```
R  --a₁-->  R₁
|           |
a₂          q₁
v           v
R₂ --q₂-->  P
```

and the base change morphism of `CommRingCat.moduleCatAdjPseudofunctor` at such a square is, at
an `R₂`-module `M`, the `R₁`-linear map `R₁ ⊗[R] M ⟶ P ⊗[R₂] M` with `r ⊗ m ↦ q₁ r ⊗ m`. Because
`P` is the tensor product `R₁ ⊗[R] R₂`, this map is inverse to Mathlib's
`Algebra.IsPushout.cancelBaseChange`, so the base change morphism is an isomorphism for every
chosen pullback, with no hypothesis on the rings or the module.

## Main definitions

None.

## Main results

* `CommRingCat.isIso_baseChange_moduleCatAdjPseudofunctor`: the base change morphism of
  `moduleCatAdjPseudofunctor` at any chosen pullback in `CommRingCatᵒᵖ` is an isomorphism.

## Implementation notes

The components of `Pseudofunctor.baseChange` are first rewritten into extension and restriction
of scalars, with the compositors of the pseudofunctor replaced by named components of
`ModuleCat.extendScalarsComp`. Naming these components keeps the kernel from unfolding them when
it compares the two descriptions. The resulting map is then evaluated on `1 ⊗ m`, which
determines it by `R₁`-linearity.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M), whose proof uses the same
  identification `(R₁ ⊗_R R₂) ⊗_{R₂} M ≅ R₁ ⊗_R M`.

## Tags

module, base change, pushout, extension of scalars, Beck–Chevalley
-/

universe v' v u' u

open CategoryTheory Bicategory Opposite Limits ModuleCat
open scoped TensorProduct ChangeOfRings

namespace CategoryTheory.Pseudofunctor

open private baseChangeApp twist adjOfCat pushforward from
  DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'})
  {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} (h : ChosenPullback f₁ f₂)

/-- The components of `Pseudofunctor.baseChange`. -/
private lemma baseChange_toNatTrans_app (M : (F.obj (.mk (op X₂))).obj) :
    (F.baseChange h).toNatTrans.app M =
      (Adjunction.ofCat (F.map h.p₁.op.toLoc).adj).unit.app _ ≫
        (F.map h.p₁.op.toLoc).r.toFunctor.map
          ((((F.comp Adj.forget₁).mapComp' f₁.op.toLoc h.p₁.op.toLoc h.p.op.toLoc
              (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h.hp₁])).inv.toNatTrans.app _ ≫
            ((F.comp Adj.forget₁).mapComp' f₂.op.toLoc h.p₂.op.toLoc h.p.op.toLoc
              (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h.hp₂])).hom.toNatTrans.app _) ≫
            ((F.comp Adj.forget₁).map h.p₂.op.toLoc).toFunctor.map
              ((Adjunction.ofCat (F.map f₂.op.toLoc).adj).counit.app M)) := by
  dsimp only [Pseudofunctor.baseChange]
  unfold baseChangeApp twist adjOfCat pushforward
  rfl

end CategoryTheory.Pseudofunctor

namespace CommRingCat

noncomputable section

/-! ### Module-level components -/

section Components

variable {R₁ R₂ R₃ : CommRingCat.{u}} (f₁₂ : R₁ ⟶ R₂) (f₂₃ : R₂ ⟶ R₃) (f₁₃ : R₁ ⟶ R₃)
  (hf : f₁₂ ≫ f₂₃ = f₁₃)

/-- `1 ⊗ m` in an extension of scalars. -/
private abbrev oneTmul {R S : CommRingCat.{u}} (φ : R ⟶ S) {M : ModuleCat.{u} R} (m : M) :
    (extendScalars φ.hom).obj M :=
  (1 : S) ⊗ₜ[R, φ.hom] m

/-- The compositor `extendScalars f₁₃ ≅ extendScalars f₁₂ ⋙ extendScalars f₂₃` for
`f₁₂ ≫ f₂₃ = f₁₃`. -/
private def extendScalarsCompOfEq :
    extendScalars.{u, u, u} f₁₃.hom ≅ extendScalars f₁₂.hom ⋙ extendScalars f₂₃.hom :=
  eqToIso (by rw [← hf]; rfl) ≪≫ extendScalarsComp f₁₂.hom f₂₃.hom

/-- The component of `extendScalarsCompOfEq` at `K`. -/
private def compHomApp (K : ModuleCat.{u} R₁) :
    (extendScalars f₁₃.hom).obj K ⟶ (extendScalars f₂₃.hom).obj ((extendScalars f₁₂.hom).obj K) :=
  (extendScalarsCompOfEq f₁₂ f₂₃ f₁₃ hf).hom.app K

/-- The component of the inverse of `extendScalarsCompOfEq` at `K`. -/
private def compInvApp (K : ModuleCat.{u} R₁) :
    (extendScalars f₂₃.hom).obj ((extendScalars f₁₂.hom).obj K) ⟶ (extendScalars f₁₃.hom).obj K :=
  (extendScalarsCompOfEq f₁₂ f₂₃ f₁₃ hf).inv.app K

private lemma compHomApp_oneTmul (K : ModuleCat.{u} R₁) (k : K) :
    compHomApp f₁₂ f₂₃ f₁₃ hf K (oneTmul f₁₃ k) = oneTmul f₂₃ (oneTmul f₁₂ k) := by
  subst hf
  exact extendScalarsComp_hom_app_one_tmul f₁₂.hom f₂₃.hom K k

private lemma compInvApp_oneTmul (K : ModuleCat.{u} R₁) (k : K) :
    compInvApp f₁₂ f₂₃ f₁₃ hf K (oneTmul f₂₃ (oneTmul f₁₂ k)) = oneTmul f₁₃ k := by
  rw [← compHomApp_oneTmul f₁₂ f₂₃ f₁₃ hf K k]
  exact Iso.hom_inv_id_apply ((extendScalarsCompOfEq f₁₂ f₂₃ f₁₃ hf).app K) _

end Components

/-! ### The pseudofunctor in terms of modules -/

section Leaves

variable {b b' : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (g : b ⟶ b')

private lemma unit_app_eq (N : (moduleCatAdjPseudofunctor.comp Adj.forget₁).obj b) :
    (Adjunction.ofCat (moduleCatAdjPseudofunctor.map g).adj).unit.app N =
      (extendRestrictScalarsAdj.{u} g.as.unop.unop.hom).unit.app N :=
  rfl

private lemma counit_app_eq (N : (moduleCatAdjPseudofunctor.obj b').obj) :
    (Adjunction.ofCat (moduleCatAdjPseudofunctor.map g).adj).counit.app N =
      (extendRestrictScalarsAdj.{u} g.as.unop.unop.hom).counit.app N :=
  rfl

private lemma r_map_eq {N N' : (moduleCatAdjPseudofunctor.obj b').obj} (φ : N ⟶ N') :
    (moduleCatAdjPseudofunctor.map g).r.toFunctor.map φ =
      (restrictScalars g.as.unop.unop.hom).map φ :=
  rfl

private lemma l_map_eq {N N' : (moduleCatAdjPseudofunctor.comp Adj.forget₁).obj b}
    (φ : N ⟶ N') :
    ((moduleCatAdjPseudofunctor.comp Adj.forget₁).map g).toFunctor.map φ =
      (extendScalars g.as.unop.unop.hom).map φ :=
  rfl

variable {b₀ b₁ b₂ : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
  (fg : b₀ ⟶ b₂) (hfg : f ≫ g = fg)

private lemma mapComp'_hom_app_eq (N : (moduleCatAdjPseudofunctor.obj b₀).obj) :
    ((moduleCatAdjPseudofunctor.comp Adj.forget₁).mapComp' f g fg hfg).hom.toNatTrans.app N =
      compHomApp f.as.unop.unop g.as.unop.unop fg.as.unop.unop (by rw [← hfg]; rfl) N := by
  subst hfg
  rfl

private lemma mapComp'_inv_app_eq (N : (moduleCatAdjPseudofunctor.obj b₀).obj) :
    ((moduleCatAdjPseudofunctor.comp Adj.forget₁).mapComp' f g fg hfg).inv.toNatTrans.app N =
      compInvApp f.as.unop.unop g.as.unop.unop fg.as.unop.unop (by rw [← hfg]; rfl) N := by
  subst hfg
  rfl

end Leaves

/-! ### The base change map of a square of rings -/

section Square

variable {R R₁ R₂ P : CommRingCat.{u}} (a₁ : R ⟶ R₁) (a₂ : R ⟶ R₂) (q₁ : R₁ ⟶ P) (q₂ : R₂ ⟶ P)
  (q : R ⟶ P) (h₁ : a₁ ≫ q₁ = q) (h₂ : a₂ ≫ q₂ = q)

/-- The base change map `R₁ ⊗[R] M ⟶ P ⊗[R₂] M` of a commutative square of rings. -/
private abbrev baseChangeMap (M : ModuleCat.{u} R₂) :
    (extendScalars a₁.hom).obj ((restrictScalars a₂.hom).obj M) ⟶
      (restrictScalars q₁.hom).obj ((extendScalars q₂.hom).obj M) :=
  (extendRestrictScalarsAdj.{u} q₁.hom).unit.app
      ((extendScalars a₁.hom).obj ((restrictScalars a₂.hom).obj M)) ≫
    (restrictScalars q₁.hom).map
      ((compInvApp a₁ q₁ q h₁ ((restrictScalars a₂.hom).obj M) ≫
          compHomApp a₂ q₂ q h₂ ((restrictScalars a₂.hom).obj M)) ≫
        (extendScalars q₂.hom).map ((extendRestrictScalarsAdj.{u} a₂.hom).counit.app M))

private lemma counit_app_oneTmul (M : ModuleCat.{u} R₂) (m : (restrictScalars a₂.hom).obj M) :
    (extendRestrictScalarsAdj.{u} a₂.hom).counit.app M (oneTmul a₂ m) = m :=
  extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := a₂.hom) M m

private lemma baseChangeMap_oneTmul (M : ModuleCat.{u} R₂) (m : (restrictScalars a₂.hom).obj M) :
    baseChangeMap a₁ a₂ q₁ q₂ q h₁ h₂ M (oneTmul a₁ m) = oneTmul q₂ (M := M) m := by
  change (extendScalars q₂.hom).map ((extendRestrictScalarsAdj.{u} a₂.hom).counit.app M)
    (compHomApp a₂ q₂ q h₂ _ (compInvApp a₁ q₁ q h₁ _ (oneTmul q₁ (oneTmul a₁ m)))) = _
  rw [compInvApp_oneTmul, compHomApp_oneTmul]
  change oneTmul q₂ ((extendRestrictScalarsAdj.{u} a₂.hom).counit.app M (oneTmul a₂ m)) = _
  rw [counit_app_oneTmul]

private lemma isIso_baseChangeMap (hpo : IsPushout a₁ a₂ q₁ q₂) (M : ModuleCat.{u} R₂) :
    IsIso (baseChangeMap a₁ a₂ q₁ q₂ q h₁ h₂ M) := by
  let : Algebra R R₁ := a₁.hom.toAlgebra
  let : Algebra R R₂ := a₂.hom.toAlgebra
  let : Algebra R₁ P := q₁.hom.toAlgebra
  let : Algebra R₂ P := q₂.hom.toAlgebra
  let : Algebra R P := q.hom.toAlgebra
  have : IsScalarTower R R₁ P := .of_algebraMap_eq fun r ↦ by
    change q.hom r = (a₁ ≫ q₁).hom r
    rw [h₁]
  have : IsScalarTower R R₂ P := .of_algebraMap_eq fun r ↦ by
    change q.hom r = (a₂ ≫ q₂).hom r
    rw [h₂]
  have : Algebra.IsPushout R R₁ R₂ P := CommRingCat.isPushout_iff_isPushout.mp hpo
  let : Module R M := Module.compHom M a₂.hom
  have : IsScalarTower R R₂ M := .of_algebraMap_smul fun _ _ ↦ rfl
  let e := Algebra.IsPushout.cancelBaseChange R R₁ R₂ P M
  have key (x : (extendScalars a₁.hom).obj ((restrictScalars a₂.hom).obj M)) :
      baseChangeMap a₁ a₂ q₁ q₂ q h₁ h₂ M x = e.symm x := by
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
      change (R₁ : Type u) at r
      have h₃ : r ⊗ₜ[R, a₁.hom] m = r • oneTmul a₁ (M := (restrictScalars a₂.hom).obj M) m :=
        (congrArg (fun s : R₁ ↦ s ⊗ₜ[R, a₁.hom] m) (mul_one r)).symm
      have h₄ : q₁.hom r ⊗ₜ[R₂, q₂.hom] (m : M) =
          @HSMul.hSMul R₁ ((restrictScalars q₁.hom).obj ((extendScalars q₂.hom).obj M)) _ _ r
            (oneTmul q₂ (M := M) m) :=
        (congrArg (fun s : P ↦ s ⊗ₜ[R₂, q₂.hom] (m : M)) (mul_one (q₁.hom r))).symm
      exact ((congrArg _ h₃).trans ((map_smul _ r _).trans ((congrArg (r • ·)
        (baseChangeMap_oneTmul a₁ a₂ q₁ q₂ q h₁ h₂ M m)).trans h₄.symm))).trans
        (Algebra.IsPushout.cancelBaseChange_symm_tmul R R₁ R₂ P M r m).symm
    | add x y hx hy =>
      exact (map_add (ConcreteCategory.hom (baseChangeMap a₁ a₂ q₁ q₂ q h₁ h₂ M)) x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add e.symm x y).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ e.symm.injective ((key x).symm.trans (hxy.trans (key y))), fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := e.symm.surjective y
  exact ⟨x, key x⟩

end Square

/-- A 2-morphism of `Cat` whose underlying natural transformation is an isomorphism is an
isomorphism. -/
private lemma isIso_of_isIso_toNatTrans {C D : Cat.{v, u'}} {F G : C ⟶ D} (η : F ⟶ G)
    [IsIso η.toNatTrans] : IsIso η :=
  ⟨⟨Cat.Hom₂.ofNatTrans (inv η.toNatTrans), by ext1; simp, by ext1; simp⟩⟩

variable {A₁ A₂ A : CommRingCat.{u}ᵒᵖ} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} (h : ChosenPullback f₁ f₂)

private lemma baseChange_toNatTrans_app_eq (M : (moduleCatAdjPseudofunctor.obj (.mk (op A₂))).obj) :
    (moduleCatAdjPseudofunctor.baseChange h).toNatTrans.app M =
      baseChangeMap f₁.unop f₂.unop h.p₁.unop h.p₂.unop h.p.unop
        (congrArg Quiver.Hom.unop h.hp₁) (congrArg Quiver.Hom.unop h.hp₂) M := by
  have e := Pseudofunctor.baseChange_toNatTrans_app moduleCatAdjPseudofunctor h M
  rw [unit_app_eq, counit_app_eq, mapComp'_inv_app_eq, mapComp'_hom_app_eq] at e
  conv at e => rhs; arg 2; arg 2; arg 2; erw [l_map_eq]
  conv at e => rhs; arg 2; erw [r_map_eq]
  exact e

/-- **Base change for modules.** For every chosen pullback in `CommRingCatᵒᵖ`, that is, every
pushout square of commutative rings, the base change morphism of `moduleCatAdjPseudofunctor` is
an isomorphism: at an `R₂`-module `M` it is `R₁ ⊗[R] M ≅ P ⊗[R₂] M`, `r ⊗ m ↦ q₁ r ⊗ m`. -/
theorem isIso_baseChange_moduleCatAdjPseudofunctor :
    IsIso (moduleCatAdjPseudofunctor.baseChange h) := by
  have hpo : IsPushout f₁.unop f₂.unop h.p₁.unop h.p₂.unop := h.isPullback.unop.flip
  have (M : (moduleCatAdjPseudofunctor.obj (.mk (op A₂))).obj) :
      IsIso ((moduleCatAdjPseudofunctor.baseChange h).toNatTrans.app M) := by
    rw [baseChange_toNatTrans_app_eq h M]
    exact isIso_baseChangeMap _ _ _ _ _ _ _ hpo M
  have : IsIso (moduleCatAdjPseudofunctor.baseChange h).toNatTrans :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_isIso_toNatTrans _

end

end CommRingCat
