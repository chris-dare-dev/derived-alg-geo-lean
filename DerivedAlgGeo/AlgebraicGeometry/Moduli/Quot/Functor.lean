/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Isomorphism
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Zero
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic

/-!
# The functor of flat, finitely presented quotients

For a morphism of schemes `p : X ⟶ S` and a module sheaf `F` on `X`, `quotFunctor p F` sends a
scheme `T` over `S` to the set of quotients `F_T ↠ Q` on `X_T = X ×_S T`, where `F_T` is the
pullback of `F` and `Q` is of finite presentation and flat over `T`. Two quotients are the same
point when they are isomorphic under `F_T`. A morphism `T' ⟶ T` over `S` acts by pullback along
`X_{T'} ⟶ X_T`.

## Main definitions

* `AlgebraicGeometry.quotBaseChange` — the pullback `F_T` of `F` to `X ×_S T`.
* `AlgebraicGeometry.quotFunctor.baseChangeHom`, `AlgebraicGeometry.quotFunctor.baseChangeIso` —
  the morphism `X ×_S T' ⟶ X ×_S T` induced by `T' ⟶ T`, and `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T`.
* `AlgebraicGeometry.ModuleQuotient.IsFlatFinitePresentation` — a quotient whose target is of
  finite presentation and flat over a given base.
* `AlgebraicGeometry.quotFunctor` — the functor `(Over S)ᵒᵖ ⥤ Type u` of isomorphism classes of
  such quotients.
* `AlgebraicGeometry.quotFunctor.zeroPoint` — the zero quotient `F_T ↠ 0`, a point over every `T`.

## Main results

* `AlgebraicGeometry.ModuleQuotient.small_isIsomorphicSetoid` — isomorphism classes of quotients
  of one module sheaf form a `u`-small type, so the values of `quotFunctor` live in `Type u`.

## Implementation notes

The points over `T` are `Shrink.{u}` of the isomorphism classes, in Mathlib's
`isIsomorphicSetoid`, of the full subcategory of admissible quotients. Isomorphism classes of
quotients of `G` inject into the subobjects of `op G`. These are small: `X.Modules` is
Grothendieck abelian, hence well-powered, and an abelian well-powered category is co-well-powered
(`Abelian.wellPowered_opposite`).

Base change along `g : T' ⟶ T` pulls a quotient back along `X_{T'} ⟶ X_T` and reads it on
`F_{T'}` through the comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` built from `pullbackComp` and
`pullbackCongr`. Flatness survives because `X_{T'}` is a pullback of `X_T ⟶ T` along `g`
(`IsFlatOver.of_isPullback`); finite presentation survives every pullback
(`isFinitePresentation_pullback`). The functor laws are Mathlib's pseudofunctor coherences for
pullback of module sheaves, `pseudofunctor_right_unitality` and
`pseudofunctor_associativity`.

The admissibility predicate is stated for any morphism `q : Y ⟶ T` and any module sheaf on `Y`;
the functor uses it for `X_T ⟶ T` and `F_T`.

## References

* [Stacks, Tag 082M](https://stacks.math.columbia.edu/tag/082M): Situation 99.7.1 defines the
  functor of quotients and, in Equation 0CZL, its subfunctor `Q^fp` of finitely presented
  quotients.
* [Stacks, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR): Situation 99.8.1 defines the
  Quot functor, whose quotients also have support proper over `T`.
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, §1, which
  identifies two quotients when they are isomorphic under the source and remarks that this is the
  condition `ker(q) = ker(q')`.

## Tags

Quot functor, quotient, flat, finite presentation, base change, moduli
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry

noncomputable section

section Admissible

variable {Y T : Scheme.{u}}

/-- A quotient presentation of a module sheaf on `Y` is admissible over `q : Y ⟶ T` when its
target is of finite presentation and flat over `T`. -/
def ModuleQuotient.IsFlatFinitePresentation (q : Y ⟶ T) {G : Y.Modules} :
    ObjectProperty (ModuleQuotient G) := fun r ↦
  SheafOfModules.IsFinitePresentation r.target ∧ Scheme.Modules.IsFlatOver q r.target

instance (q : Y ⟶ T) {G : Y.Modules} :
    (ModuleQuotient.IsFlatFinitePresentation q (G := G)).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨SheafOfModules.IsFinitePresentation.of_iso.{u}
      ((ModuleQuotient.targetFunctor G).mapIso e) h.1,
      h.2.of_iso ((ModuleQuotient.targetFunctor G).mapIso e)⟩

/-- Isomorphism classes of quotient presentations of a module sheaf, in any full subcategory,
form a `u`-small type: sending a quotient `G ⟶ Q` to the subobject `op Q ⟶ op G` is injective, and
`Y.Modules` is co-well-powered. -/
instance ModuleQuotient.small_isIsomorphicSetoid {G : Y.Modules}
    (P : ObjectProperty (ModuleQuotient G)) :
    Small.{u} (Quotient (isIsomorphicSetoid P.FullSubcategory)) := by
  let φ : Quotient (isIsomorphicSetoid P.FullSubcategory) → Subobject (op G) :=
    Quotient.lift (fun r ↦ Subobject.mk r.obj.hom.op) fun r s ⟨e⟩ ↦ by
      let t : r.obj.target ≅ s.obj.target :=
        (ModuleQuotient.targetFunctor G).mapIso (P.ι.mapIso e)
      refine Subobject.mk_eq_mk_of_comm _ _ t.symm.op (Quiver.Hom.unop_inj ?_)
      simp only [Iso.op_hom, Iso.symm_hom, unop_comp, Quiver.Hom.unop_op]
      rw [Iso.comp_inv_eq]
      exact ((P.ι.map e.hom).comm).symm
  refine small_of_injective (f := φ) fun x y h ↦ ?_
  induction x using Quotient.inductionOn with | h r => ?_
  induction y using Quotient.inductionOn with | h s => ?_
  let i := Subobject.isoOfMkEqMk _ _ h
  have w : i.hom ≫ s.obj.hom.op = r.obj.hom.op := Subobject.ofMkLEMk_comp _
  exact Quotient.sound ⟨(P.isoMk (ModuleQuotient.isoMk i.unop
    (Quiver.Hom.op_inj (by simpa using w)))).symm⟩

end Admissible

section Coherence

open Scheme.Modules

/-- Pulling back along a morphism equal to the identity, read through the composition
comparison, is the comparison for `φ' = φ`. -/
private lemma pullbackCongr_comp_pullbackId {Y Z : Scheme.{u}} (φ : Y ⟶ Z) {b : Y ⟶ Y}
    (hb : b = 𝟙 Y) {φ' : Y ⟶ Z} (w : φ' = b ≫ φ) (M : Z.Modules) :
    (pullbackCongr w).hom.app M ≫ (pullbackComp b φ).inv.app M ≫
      (pullbackCongr hb).hom.app _ ≫ (pullbackId Y).hom.app _ =
      (pullbackCongr (w.trans (by rw [hb, Category.id_comp]))).hom.app M := by
  subst hb w
  have h := NatTrans.congr_app (pseudofunctor_right_unitality φ) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  simpa [pullbackCongr] using h

set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphisms for pullback along a composite agree with those along its two
factors. -/
private lemma pullbackCongr_comp_assoc {Y₂ Y₁ Y₀ Z : Scheme.{u}} (a : Y₂ ⟶ Y₁) (b : Y₁ ⟶ Y₀)
    {c : Y₂ ⟶ Y₀} (hc : a ≫ b = c) (φ₀ : Y₀ ⟶ Z) {φ₁ : Y₁ ⟶ Z} {φ₂ : Y₂ ⟶ Z}
    (w₁ : φ₁ = b ≫ φ₀) (w₂ : φ₂ = a ≫ φ₁) (w₃ : φ₂ = c ≫ φ₀) (M : Z.Modules) :
    ((pullbackCongr w₂).hom.app M ≫ (pullbackComp a φ₁).inv.app M) ≫
      (Scheme.Modules.pullback a).map
        ((pullbackCongr w₁).hom.app M ≫ (pullbackComp b φ₀).inv.app M) ≫
        (pullbackComp a b).hom.app _ ≫ (pullbackCongr hc).hom.app _ =
      (pullbackCongr w₃).hom.app M ≫ (pullbackComp c φ₀).inv.app M := by
  subst hc w₁ w₂
  have h := NatTrans.congr_app (pseudofunctor_associativity a b φ₀) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
  rw [← cancel_mono ((pullbackComp (a ≫ b) φ₀).hom.app M)]
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc, eqToHom_refl, Iso.inv_hom_id_app] at h ⊢
  exact h

end Coherence

section BaseChange

open Scheme.Modules

variable {Y Y' Y'' : Scheme.{u}} {G : Y.Modules} {G' : Y'.Modules} {G'' : Y''.Modules}

/-- A quotient of `G` pulled back along `b : Y' ⟶ Y` and read on `G'` through `e`. -/
private abbrev pullbackVia (b : Y' ⟶ Y) (e : G' ≅ (Scheme.Modules.pullback b).obj G)
    (q : ModuleQuotient G) : ModuleQuotient G' :=
  (q.pullback b).precomp e.hom

private def pullbackViaIso (b : Y' ⟶ Y) (e : G' ≅ (Scheme.Modules.pullback b).obj G)
    {q r : ModuleQuotient G} (i : q ≅ r) : pullbackVia b e q ≅ pullbackVia b e r :=
  ModuleQuotient.isoMk ((Scheme.Modules.pullback b).mapIso
    ((ModuleQuotient.targetFunctor G).mapIso i)) (by
    change (e.hom ≫ (Scheme.Modules.pullback b).map q.hom) ≫
      (Scheme.Modules.pullback b).map i.hom.right = e.hom ≫ (Scheme.Modules.pullback b).map r.hom
    rw [Category.assoc, ← Functor.map_comp, i.hom.comm])

private def pullbackViaId {b : Y ⟶ Y} (hb : b = 𝟙 Y)
    (e : G ≅ (Scheme.Modules.pullback b).obj G)
    (he : e.hom ≫ (pullbackCongr hb).hom.app G ≫ (pullbackId Y).hom.app G = 𝟙 G)
    (q : ModuleQuotient G) : pullbackVia b e q ≅ q :=
  ModuleQuotient.isoMk ((pullbackCongr hb).app q.target ≪≫ (pullbackId Y).app q.target) (by
    change (e.hom ≫ (Scheme.Modules.pullback b).map q.hom) ≫
      (pullbackCongr hb).hom.app q.target ≫ (pullbackId Y).hom.app q.target = q.hom
    have h₁ := (pullbackCongr hb).hom.naturality q.hom
    have h₂ := (pullbackId Y).hom.naturality q.hom
    simp only [Functor.id_map] at h₂
    simp only [Category.assoc]
    rw [reassoc_of% h₁, h₂, reassoc_of% he])

private def pullbackViaComp (a : Y'' ⟶ Y') (b : Y' ⟶ Y) {c : Y'' ⟶ Y} (hc : a ≫ b = c)
    (e₁ : G' ≅ (Scheme.Modules.pullback b).obj G)
    (e₂ : G'' ≅ (Scheme.Modules.pullback a).obj G')
    (e₃ : G'' ≅ (Scheme.Modules.pullback c).obj G)
    (he : e₂.hom ≫ (Scheme.Modules.pullback a).map e₁.hom ≫ (pullbackComp a b).hom.app G ≫
      (pullbackCongr hc).hom.app G = e₃.hom)
    (q : ModuleQuotient G) : pullbackVia a e₂ (pullbackVia b e₁ q) ≅ pullbackVia c e₃ q :=
  ModuleQuotient.isoMk ((pullbackComp a b).app q.target ≪≫ (pullbackCongr hc).app q.target) (by
    change (e₂.hom ≫ (Scheme.Modules.pullback a).map (e₁.hom ≫
      (Scheme.Modules.pullback b).map q.hom)) ≫ (pullbackComp a b).hom.app q.target ≫
        (pullbackCongr hc).hom.app q.target = e₃.hom ≫ (Scheme.Modules.pullback c).map q.hom
    have h₁ := (pullbackComp a b).hom.naturality q.hom
    have h₂ := (pullbackCongr hc).hom.naturality q.hom
    simp only [Functor.comp_map] at h₁
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₁, h₂, ← he]
    simp only [Category.assoc])

/-- Pullback preserves admissible quotients along a pullback square. -/
private lemma isFlatFinitePresentation_pullbackVia {T T' : Scheme.{u}} {q : Y ⟶ T}
    {snd : Y' ⟶ T'} {h : T' ⟶ T} {b : Y' ⟶ Y} (H : IsPullback b snd q h)
    (e : G' ≅ (Scheme.Modules.pullback b).obj G) {r : ModuleQuotient G}
    (hr : ModuleQuotient.IsFlatFinitePresentation q r) :
    ModuleQuotient.IsFlatFinitePresentation snd (pullbackVia b e r) :=
  ⟨isFinitePresentation_pullback b r.target hr.1, hr.2.of_isPullback H⟩

end BaseChange

variable {X S : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)

open Scheme.Modules quotFunctor

/-- The full subcategory of admissible quotients of `F_T`. -/
private abbrev Adm (T : Over S) :=
  (ModuleQuotient.IsFlatFinitePresentation (pullback.snd p T.hom)
    (G := quotBaseChange p F T)).FullSubcategory

/-- Base change of one admissible quotient along `g : T' ⟶ T`. -/
private def baseChangeObj {T' T : Over S} (g : T' ⟶ T) (r : Adm p F T) : Adm p F T' :=
  ⟨pullbackVia (baseChangeHom p g) (baseChangeIso p F g) r.obj,
    isFlatFinitePresentation_pullbackVia (isPullback_baseChangeHom p g) _ r.property⟩

/-- Base change on isomorphism classes of admissible quotients. -/
private def baseChangeClass {T' T : Over S} (g : T' ⟶ T) :
    Quotient (isIsomorphicSetoid (Adm p F T)) → Quotient (isIsomorphicSetoid (Adm p F T')) :=
  Quotient.map (baseChangeObj p F g) fun _ _ ⟨i⟩ ↦
    ⟨ObjectProperty.isoMk _ (pullbackViaIso _ _ ((ObjectProperty.ι _).mapIso i))⟩

private lemma baseChangeClass_id (T : Over S) (x : Quotient (isIsomorphicSetoid (Adm p F T))) :
    baseChangeClass p F (𝟙 T) x = x := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound
    ⟨ObjectProperty.isoMk _ (pullbackViaId (baseChangeHom_id p T) _ ?_ r.obj)⟩
  have h := pullbackCongr_comp_pullbackId (pullback.fst p T.hom) (baseChangeHom_id p T)
    (baseChangeHom_fst p (𝟙 T)) F
  rw [baseChangeIso_hom, Category.assoc, h]
  simp [Scheme.Modules.pullbackCongr]

private lemma baseChangeClass_comp {T'' T' T : Over S} (k : T'' ⟶ T') (g : T' ⟶ T)
    (x : Quotient (isIsomorphicSetoid (Adm p F T))) :
    baseChangeClass p F (k ≫ g) x = baseChangeClass p F k (baseChangeClass p F g x) := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound ⟨ObjectProperty.isoMk _
    (pullbackViaComp _ _ (baseChangeHom_comp p k g) _ _ _ ?_ r.obj).symm⟩
  rw [baseChangeIso_hom, baseChangeIso_hom, baseChangeIso_hom]
  exact pullbackCongr_comp_assoc _ _ (baseChangeHom_comp p k g) (pullback.fst p T.hom)
    (baseChangeHom_fst p g) (baseChangeHom_fst p k) (baseChangeHom_fst p (k ≫ g)) F

/-- **The functor of flat, finitely presented quotients.** For `p : X ⟶ S` and a module sheaf
`F` on `X`, it sends `T` over `S` to the isomorphism classes of quotients `F_T ↠ Q` on
`X_T = X ×_S T` with `Q` of finite presentation and flat over `T`; a morphism `T' ⟶ T` acts by
pullback along `X_{T'} ⟶ X_T`.

This is Stacks' `Q^fp_{F/X/S}` (Situation 082M, Equation 0CZL), with schemes in place of
algebraic spaces and no quasi-coherence assumed of `F`. Stacks identifies two quotients with the
same kernel; in an abelian category an epimorphism is the cokernel of its kernel, so this is
isomorphism under `F_T`, the relation used here and by Nitsure (§1).

When `p` is of finite presentation and proper this is Grothendieck's Quot functor
`Quot_{F/X/S}` (Situation 09TR), whose quotients must also have support proper over `T`: a module
of finite type has closed support, and a closed subscheme of `X_T` is proper over `T`. Without
properness the two differ. For `p : 𝔸¹_k ⟶ Spec k` and `F = 𝒪`, let `Z = V(tx - 1)` in
`𝔸¹ × Spec k[t]`. Then `𝒪_Z` is finitely presented as an `𝒪`-module, with one generator and one
relation, and `𝒪_Z ≅ k[t, t⁻¹]` is flat over `k[t]`, so `𝒪 ↠ 𝒪_Z` is a point over `Spec k[t]`.
Its support `Z` maps onto `D(t)`, which is not closed, so `Z` is not proper over `Spec k[t]`. -/
@[stacks 0CZL]
def quotFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (Quotient (isIsomorphicSetoid
    (ModuleQuotient.IsFlatFinitePresentation (pullback.snd p T.unop.hom)
      (G := quotBaseChange p F T.unop)).FullSubcategory))
  map g := TypeCat.ofHom fun x ↦
    equivShrink _ (baseChangeClass p F g.unop ((equivShrink _).symm x))
  map_id T := by
    ext x
    simp [baseChangeClass_id]
  map_comp f g := by
    ext x
    simp [baseChangeClass_comp]

/-- The zero quotient `F_T ↠ 0` is a point of `quotFunctor p F` over every `T`. -/
def quotFunctor.zeroPoint (T : Over S) : (quotFunctor p F).obj (op T) :=
  equivShrink _ (Quotient.mk _ ⟨ModuleQuotient.toZero _,
    (Scheme.coherent (Limits.pullback p T.hom)).prop_of_isZero (isZero_zero _),
    Scheme.Modules.IsFlatOver.of_isZero (isZero_zero _)⟩)

end

end AlgebraicGeometry
