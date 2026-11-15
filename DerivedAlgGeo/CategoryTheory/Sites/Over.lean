/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Over

/-!
# Over categories of sites

Cocontinuity of a functor between arbitrary sites passes to the induced functor between their
over categories. This construction is independent of any geometric realization of the sites.

A presheaf `G` on `Over X` has a total presheaf `Y ↦ Σ (p : Y ⟶ X), G (Y, p)` on `C`, the
presheaf `j_{X!} G` of Stacks 00Y1. When `yoneda.obj X` is a sheaf, `G` is a sheaf for the
slice topology `J.over X` exactly when its total presheaf is a `J`-sheaf.

## Main definitions

* `CategoryTheory.Over.totalPresheaf`: the total presheaf of a presheaf on `Over X`.
* `CategoryTheory.Over.totalPresheafπ`: its projection to the lifted representable presheaf.

## Main results

* `CategoryTheory.Over.post_isCocontinuous`
* `CategoryTheory.GrothendieckTopology.isSheaf_over_iff_isSheaf_totalPresheaf`

## Implementation notes

The total presheaf section has its own universe-general variables
`{C : Type u₁} [Category.{v₁} C]`, so that it applies to `Scheme.{u} : Type (u + 1)`; the
cocontinuity section above it fixes `Category.{u} C` with `C : Type u`. For `G` valued in
`Type w` the total presheaf is valued in `Type (max v₁ w)`, so the projection lands in
`yoneda.obj X ⋙ uliftFunctor.{w}`.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)

## Tags

site, over category, slice topology, sheaf, cocontinuous
-/

universe w v₁ u₁ u

open CategoryTheory

namespace CategoryTheory.Over

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsCocontinuous J K] (X : C)

/-- Cocontinuity passes to the induced functor on over categories. -/
instance post_isCocontinuous :
    (Over.post (X := X) F).IsCocontinuous (J.over X) (K.over (F.obj X)) where
  cover_lift {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    have h := F.cover_lift J K hS
    convert h using 1
    ext Z g
    rw [Sieve.overEquiv_iff]
    dsimp [Sieve.functorPullback, Presieve.functorPullback]
    let A : Over X := Over.mk (g ≫ U.hom)
    let a : (Over.post F).obj A ⟶ (Over.post F).obj U :=
      (Over.post F).map (Over.homMk g)
    let B : Over (F.obj X) := Over.mk (F.map g ≫ F.map U.hom)
    let b : B ⟶ (Over.post F).obj U := Over.homMk (F.map g)
    constructor
    · intro hg
      apply (Sieve.overEquiv_iff (Y := Over.mk (F.map U.hom)) S (F.map g)).mpr
      change S b
      change S a at hg
      let p : B ⟶ (Over.post F).obj A := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ F.map (g ≫ U.hom) = F.map g ≫ F.map U.hom
        simpa only [Category.id_comp] using F.map_comp g U.hom)
      have hp := S.downward_closed hg p
      rw [show p ≫ a = b by ext; exact Category.id_comp _] at hp
      exact hp
    · intro hg
      have hg :=
        (Sieve.overEquiv_iff (Y := Over.mk (F.map U.hom)) S (F.map g)).mp hg
      change S b at hg
      change S a
      let p : (Over.post F).obj A ⟶ B := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ F.map g ≫ F.map U.hom = F.map (g ≫ U.hom)
        simpa only [Category.id_comp] using (F.map_comp g U.hom).symm)
      have hp := S.downward_closed hg p
      rw [show p ≫ b = a by ext; exact Category.id_comp _] at hp
      exact hp

end CategoryTheory.Over

section TotalPresheaf

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {X : C}

namespace Over

variable (G : (Over X)ᵒᵖ ⥤ Type w)

/-- Two restrictions of a section of `G` to objects with the same underlying object agree
up to the identification of their structure morphisms. -/
private lemma map_heq_map {Y : C} {Z : Over X} {p₁ p₂ : Y ⟶ X} (u₁ : Over.mk p₁ ⟶ Z)
    (u₂ : Over.mk p₂ ⟶ Z) (h : p₁ = p₂) (h' : u₁.left = u₂.left) (s : G.obj (op Z)) :
    G.map u₁.op s ≍ G.map u₂.op s := by
  subst h
  obtain rfl : u₁ = u₂ := Over.OverMorphism.ext h'
  rfl

/-- The total presheaf `Y ↦ Σ (p : Y ⟶ X), G.obj (op (Over.mk p))` of a presheaf `G` on
`Over X`. This is the presheaf `j_{X!} G` of Stacks 00Y1. -/
@[stacks 00Y1]
def totalPresheaf : Cᵒᵖ ⥤ Type (max v₁ w) where
  obj Y := Σ p : Y.unop ⟶ X, G.obj (op (Over.mk p))
  map f := ↾fun s ↦ ⟨f.unop ≫ s.1,
    G.map (Over.homMk f.unop : Over.mk (f.unop ≫ s.1) ⟶ Over.mk s.1).op s.2⟩
  map_id Y := by
    ext ⟨p, g⟩
    · simp
    · dsimp
      refine (map_heq_map G _ (𝟙 (Over.mk p)) (Category.id_comp p) rfl g).trans ?_
      simp
  map_comp f g := by
    ext ⟨p, s⟩
    · simp
    · dsimp
      rw [← comp_apply, ← Functor.map_comp, ← op_comp]
      apply map_heq_map G
      · simp
      · simp

/-- The total presheaf acts on a pair `(p, s)` by precomposing `p` and restricting `s`. -/
@[simp]
lemma totalPresheaf_map_apply {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') (s : (totalPresheaf G).obj Y) :
    (totalPresheaf G).map f s = ⟨f.unop ≫ s.1,
      G.map (Over.homMk f.unop : Over.mk (f.unop ≫ s.1) ⟶ Over.mk s.1).op s.2⟩ :=
  rfl

/-- The first projection of the total presheaf, to the lifted representable presheaf. -/
@[simps]
def totalPresheafπ : totalPresheaf G ⟶ yoneda.obj X ⋙ uliftFunctor.{w} where
  app Y := ↾fun s ↦ ULift.up s.1

variable {G}

/-- The section of `G` over `W` given by an element of the total presheaf over `W.left` that
lies over `W.hom`. -/
private def totalPresheafEv (W : Over X) (s : (totalPresheaf G).obj (op W.left))
    (h : s.1 = W.hom) : G.obj (op W) :=
  G.map (Over.homMk (𝟙 W.left) (by simp [h]) : W ⟶ Over.mk s.1).op s.2

private lemma totalPresheafEv_congr {W : Over X} {s t : (totalPresheaf G).obj (op W.left)}
    (hst : s = t) (h : s.1 = W.hom) :
    totalPresheafEv W s h = totalPresheafEv W t (hst ▸ h) := by
  subst hst
  rfl

private lemma totalPresheafEv_mk {Y : C} (p : Y ⟶ X) (g : G.obj (op (Over.mk p))) :
    totalPresheafEv (Over.mk p) ⟨p, g⟩ rfl = g := by
  dsimp [totalPresheafEv]
  rw [show (Over.homMk (𝟙 Y) : Over.mk p ⟶ Over.mk p) = 𝟙 _ by ext; simp]
  simp

private lemma totalPresheafEv_map {W W' : Over X} (u : W ⟶ W')
    (s : (totalPresheaf G).obj (op W'.left)) (h : s.1 = W'.hom) :
    totalPresheafEv W ((totalPresheaf G).map u.left.op s) (by simp [h, Over.w u]) =
      G.map u.op (totalPresheafEv W' s h) := by
  dsimp [totalPresheafEv]
  simp only [← comp_apply, ← Functor.map_comp, ← op_comp]
  congr 3
  ext
  simp

private lemma totalPresheaf_ext {Y : C} {p : Y ⟶ X} {a : G.obj (op (Over.mk p))}
    {t : (totalPresheaf G).obj (op Y)} (h : p = t.1)
    (h' : a = totalPresheafEv (Over.mk p) t h.symm) :
    (⟨p, a⟩ : (totalPresheaf G).obj (op Y)) = t := by
  obtain ⟨p', b⟩ := t
  obtain rfl : p = p' := h
  rw [totalPresheafEv_mk] at h'
  rw [h']

end Over

namespace GrothendieckTopology

open Over

variable (J : GrothendieckTopology C)

/-- If `yoneda.obj X` is a `J`-sheaf and `G` is a `J.over X`-sheaf, then the total presheaf of
`G` is a `J`-sheaf. -/
private lemma isSheaf_totalPresheaf_of_isSheaf_over
    (hX : Presieve.IsSheaf J (CategoryTheory.yoneda.obj X))
    {G : (Over X)ᵒᵖ ⥤ Type w} (hG : Presieve.IsSheaf (J.over X) G) :
    Presieve.IsSheaf J (totalPresheaf G) := by
  intro Y S hS x hx
  let x₁ : Presieve.FamilyOfElements (CategoryTheory.yoneda.obj X) S.arrows :=
    fun _ f hf ↦ (x f hf).1
  have hx₁ : x₁.Compatible := fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg Sigma.fst (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨p, hp, hp_uniq⟩ : ∃! p : Y ⟶ X, x₁.IsAmalgamation p := hX S hS x₁ hx₁
  replace hp : ∀ ⦃Z : C⦄ (f : Z ⟶ Y) (hf : S f), f ≫ p = (x f hf).1 := hp
  let S' := (Sieve.overEquiv (Over.mk p)).symm S
  let y : Presieve.FamilyOfElements G S'.arrows := fun W u hu ↦
    totalPresheafEv W (x u.left hu) ((hp u.left hu).symm.trans (Over.w u))
  have hy : y.Compatible := by
    intro W₁ W₂ W g₁ g₂ u₁ u₂ h₁ h₂ w
    have hw : g₁.left ≫ u₁.left = g₂.left ≫ u₂.left := congr_arg CommaMorphism.left w
    exact (totalPresheafEv_map g₁ _ _).symm.trans
      ((totalPresheafEv_congr (hx g₁.left g₂.left h₁ h₂ hw) _).trans
        (totalPresheafEv_map g₂ _ _))
  obtain ⟨g, hg, hg_uniq⟩ := hG S' (J.overEquiv_symm_mem_over _ _ hS) y hy
  refine ⟨⟨p, g⟩, fun Z f hf ↦ ?_, fun t ht ↦ ?_⟩
  · exact totalPresheaf_ext (hp f hf) (hg (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) hf)
  · have htp : t.1 = p := hp_uniq t.1 fun Z f hf ↦ congr_arg Sigma.fst (ht f hf)
    refine (totalPresheaf_ext (G := G) htp.symm ?_).symm
    refine (hg_uniq _ fun W u hu ↦ ?_).symm
    exact (totalPresheafEv_map u t _).symm.trans (totalPresheafEv_congr (ht u.left hu) _)

/-- If `yoneda.obj X` is `J`-separated and the total presheaf of `G` is a `J`-sheaf, then `G`
is a `J.over X`-sheaf. -/
private lemma isSheaf_over_of_isSheaf_totalPresheaf
    (hX : Presieve.IsSeparated J (CategoryTheory.yoneda.obj X))
    {G : (Over X)ᵒᵖ ⥤ Type w} (hG : Presieve.IsSheaf J (totalPresheaf G)) :
    Presieve.IsSheaf (J.over X) G := by
  intro Y' S' hS' y hy
  obtain ⟨Y, p, rfl⟩ := Y'.mk_surjective
  let S := Sieve.overEquiv (Over.mk p) S'
  let x : Presieve.FamilyOfElements (totalPresheaf G) S.arrows := fun _ f hf ↦
    ⟨f ≫ p, y (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) ((Sieve.overEquiv_iff S' f).1 hf)⟩
  have hx : x.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have hw : g₁ ≫ f₁ ≫ p = g₂ ≫ f₂ ≫ p := by rw [reassoc_of% w]
    refine totalPresheaf_ext hw ((hy (Over.homMk g₁ : Over.mk (g₁ ≫ f₁ ≫ p) ⟶ Over.mk (f₁ ≫ p))
      (Over.homMk g₂ hw.symm : Over.mk (g₁ ≫ f₁ ≫ p) ⟶ Over.mk (f₂ ≫ p))
      ((Sieve.overEquiv_iff S' f₁).1 h₁) ((Sieve.overEquiv_iff S' f₂).1 h₂)
      (by ext; simpa using w)).trans ?_)
    exact (congr_arg (G.map _) (totalPresheafEv_mk (f₂ ≫ p) _)).symm.trans
      (totalPresheafEv_map (Over.homMk g₂ hw.symm : Over.mk (g₁ ≫ f₁ ≫ p) ⟶ Over.mk (f₂ ≫ p))
        (x f₂ h₂) rfl).symm
  obtain ⟨t, ht, ht_uniq⟩ := hG S hS' x hx
  have htp : t.1 = p := hX S hS' (fun _ f _ ↦ f ≫ p) t.1 p
    (fun Z f hf ↦ congr_arg Sigma.fst (ht f hf)) (fun Z f hf ↦ rfl)
  refine ⟨totalPresheafEv (Over.mk p) t htp, fun W u hu ↦ ?_, fun g' hg' ↦ ?_⟩
  · let v : Over.mk (u.left ≫ p) ⟶ W :=
      Over.homMk (𝟙 W.left) ((Category.id_comp W.hom).trans (Over.w u).symm)
    let u' : Over.mk (u.left ≫ p) ⟶ Over.mk p := Over.homMk u.left rfl
    have hvu : v ≫ u = u' := by ext; simp [v, u']
    have hu' : S'.arrows u' := hvu ▸ S'.downward_closed hu v
    have key : ∀ (u' : W ⟶ Over.mk p) (hu'' : S' u'), u' = u → y u' hu'' = y u hu := by
      rintro _ _ rfl
      rfl
    refine (totalPresheafEv_map u t htp).symm.trans
      ((totalPresheafEv_congr (ht u.left ((Sieve.overEquiv_iff S' u.left).2 hu')) _).trans ?_)
    refine (hy.to_sieveCompatible _ _ hu').symm.trans (key _ _ ?_)
    ext
    simp [u']
  · have := ht_uniq ⟨p, g'⟩ fun Z f hf ↦
      congr_arg (Sigma.mk (f ≫ p)) (hg' (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) _)
    exact (totalPresheafEv_mk p g').symm.trans (totalPresheafEv_congr this rfl)

/-- Let `yoneda.obj X` be a `J`-sheaf. A presheaf `G` on `Over X` is a sheaf for the slice
topology `J.over X` if and only if its total presheaf `Y ↦ Σ (p : Y ⟶ X), G (Y, p)` is a
`J`-sheaf.

This is the object-level content of Stacks 00Y1, where `j_{X!}` identifies sheaves on `C/X`
with sheaves over `h_X^#`. When `w = v₁`, the total presheaf with its projection
`Over.totalPresheafπ` realizes on objects the equivalence
`CategoryTheory.overEquivPresheafCostructuredArrow` between presheaves on `Over X` and
presheaves over `yoneda.obj X`, which this criterion refines to sheaves.

Only the separatedness of `yoneda.obj X` is used to show that `G` is a sheaf when its total
presheaf is one. -/
@[stacks 00Y1]
theorem isSheaf_over_iff_isSheaf_totalPresheaf
    (hX : Presieve.IsSheaf J (CategoryTheory.yoneda.obj X)) (G : (Over X)ᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (J.over X) G ↔ Presieve.IsSheaf J (totalPresheaf G) :=
  ⟨isSheaf_totalPresheaf_of_isSheaf_over J hX,
    isSheaf_over_of_isSheaf_totalPresheaf J hX.isSeparated⟩

/-- The criterion applies to a large category with small Hom types, such as
`Scheme.{u} : Type (u + 1)` with `Category.{u} Scheme.{u}`. -/
example {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) {X : C}
    (hX : Presieve.IsSheaf J (CategoryTheory.yoneda.obj X)) (G : (Over X)ᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (J.over X) G ↔ Presieve.IsSheaf J (totalPresheaf G) :=
  J.isSheaf_over_iff_isSheaf_totalPresheaf hX G

end GrothendieckTopology

end CategoryTheory

end TotalPresheaf
