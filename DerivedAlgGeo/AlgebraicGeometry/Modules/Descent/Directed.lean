/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing module sheaves along a directed system of open immersions

Let `X` be a scheme with open immersions `ι j : P j ⟶ X` indexed by a preorder `J`, with
`P i ⟶ P j` over `X` for `i ≤ j`, such that two charts meet in a union of charts below both.
Module sheaves `F j` on `P j` with maps `φ : F j ⟶ (P i ⟶ P j)_* F i` that compose and are
bijective on sections over opens of `P i` glue to a module sheaf on `X` whose restriction to
`P k` is `F k`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.DirectedGluingData X`: the data.
* `AlgebraicGeometry.Scheme.Modules.DirectedGluingData.glue`: the glued module sheaf, the
  subsheaf of `∏ⱼ (ι j)_* F j` of the families compatible under every `φ`.
* `AlgebraicGeometry.Scheme.Modules.DirectedGluingData.glueRestrictIso`: its restriction to `P k`
  is `F k`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.DirectedGluingData.glueRestrictIso_hom_app`: on sections, the
  isomorphism takes the `k`-th member of a compatible family.

## Implementation notes

The glued sheaf is the limit of the `(ι j)_* F j` over `Jᵒᵖ`, cut out of the product as in
`AlgebraicGeometry.Scheme.ZariskiDescent.glue`. That construction asks for a descent datum,
which quantifies over every test scheme mapping to two members of the cover. Here the overlaps
are unions of smaller members of the same family, so the transition maps `φ` are only needed
along `i ≤ j`, and no cocycle condition beyond `φ_comp` is asked. This is the shape of the
relative `Proj` over the affine Zariski site, whose charts over a basic open `D(f) ⊆ U` are open
in the chart over `U`.

The comparison with `F k` is bijective on sections. A compatible family is determined by its
`k`-th member: every chart `P j` is covered, over `ι k (T)`, by images of charts `P i` with
`i ≤ j` and `i ≤ k`, on which `φ` is injective. Conversely a section of `F k` is transported to
each such `P i`, pulled back to `P j` by the inverse of `φ`, and the pieces glue in `F j` by the
sheaf condition.

## References

* [Stacks, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK): glueing sheaves, Lemma 6.33.2
  (Tag 00AL), here for a family whose overlaps are covered by members of the family.

## Tags

module sheaf, gluing, directed system, open immersion
-/

universe u

open CategoryTheory Opposite Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- **A directed system of module sheaves on open subschemes.** Open immersions `ι j : P j ⟶ X`
indexed by a preorder, with maps `map h : P i ⟶ P j` over `X` for `h : i ≤ j`, such that two
members meet in a union of members below both; and module sheaves `obj j` on `P j` with maps
`φ h : obj j ⟶ (map h)_* (obj i)` that compose and are bijective on sections over the images of
opens of `P i`. -/
structure DirectedGluingData (X : Scheme.{u}) where
  /-- The index preorder. -/
  J : Type u
  [preorder : Preorder J]
  /-- The open subschemes. -/
  P : J → Scheme.{u}
  /-- The open immersions into `X`. -/
  ι (j : J) : P j ⟶ X
  [isOpenImmersion_ι (j : J) : IsOpenImmersion (ι j)]
  /-- The inclusions `P i ⟶ P j` for `i ≤ j`. -/
  map {i j : J} (h : i ≤ j) : P i ⟶ P j
  [isOpenImmersion_map {i j : J} (h : i ≤ j) : IsOpenImmersion (map h)]
  map_ι {i j : J} (h : i ≤ j) : map h ≫ ι j = ι i
  /-- Two members meet in a union of members below both. -/
  exists_le {i j : J} {x : X} (hi : x ∈ (ι i).opensRange) (hj : x ∈ (ι j).opensRange) :
    ∃ k, ∃ (_ : k ≤ i) (_ : k ≤ j), x ∈ (ι k).opensRange
  /-- The module sheaves. -/
  obj (j : J) : (P j).Modules
  /-- The transition maps. -/
  φ {i j : J} (h : i ≤ j) : obj j ⟶ (pushforward (map h)).obj (obj i)
  φ_comp {k i j : J} (hki : k ≤ i) (hij : i ≤ j) (A : (P j).Opens) (s : Γ(obj j, A))
    (C : (P k).Opens) (hC₁ : C ≤ map hki ⁻¹ᵁ map hij ⁻¹ᵁ A)
    (hC₂ : C ≤ map (hki.trans hij) ⁻¹ᵁ A) :
    (obj k).presheaf.map (homOfLE hC₁).op ((φ hki).app (map hij ⁻¹ᵁ A) ((φ hij).app A s)) =
      (obj k).presheaf.map (homOfLE hC₂).op ((φ (hki.trans hij)).app A s)
  bijective {i j : J} (h : i ≤ j) (B : (P i).Opens) :
    Function.Bijective ((φ h).app (map h ''ᵁ B))

namespace DirectedGluingData

attribute [instance] preorder isOpenImmersion_ι isOpenImmersion_map

variable {X : Scheme.{u}} (D : DirectedGluingData X)

/-! ## Restrictions and transition maps on sections -/

/-- Restriction of sections, along an inequality of opens. -/
private noncomputable abbrev res {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (h : B ≤ A) :
    Γ(M, A) ⟶ Γ(M, B) :=
  M.presheaf.map (homOfLE h).op

private lemma res_res {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opens} (h₁ : B ≤ A)
    (h₂ : C ≤ B) (s : Γ(M, A)) : res M h₂ (res M h₁ s) = res M (h₂.trans h₁) s :=
  resSection_trans M h₁ h₂ s

private lemma res_self {Y : Scheme.{u}} (M : Y.Modules) {A : Y.Opens} (h : A ≤ A)
    (s : Γ(M, A)) : res M h s = s := by
  change M.presheaf.map (homOfLE h).op s = s
  rw [show (homOfLE h).op = 𝟙 (op A) from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

private lemma map_apply_congr {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens}
    (α β : op A ⟶ op B) (s : Γ(M, A)) : M.presheaf.map α s = M.presheaf.map β s := by
  rw [Subsingleton.elim α β]

/-- The transition map on sections, from an open `A` of `P j` to an open `B ≤ (map h)⁻¹ A` of
`P i`. -/
noncomputable def trans {i j : D.J} (h : i ≤ j) {A : (D.P j).Opens} {B : (D.P i).Opens}
    (hB : B ≤ D.map h ⁻¹ᵁ A) : Γ(D.obj j, A) ⟶ Γ(D.obj i, B) :=
  (D.φ h).app A ≫ res (D.obj i) hB

lemma trans_apply {i j : D.J} (h : i ≤ j) {A : (D.P j).Opens} {B : (D.P i).Opens}
    (hB : B ≤ D.map h ⁻¹ᵁ A) (s : Γ(D.obj j, A)) :
    D.trans h hB s = res (D.obj i) hB ((D.φ h).app A s) :=
  rfl

/-- Restricting after a transition map is a transition map. -/
lemma res_trans {i j : D.J} (h : i ≤ j) {A : (D.P j).Opens} {B B' : (D.P i).Opens}
    (hB : B ≤ D.map h ⁻¹ᵁ A) (hB' : B' ≤ B) (s : Γ(D.obj j, A)) :
    res (D.obj i) hB' (D.trans h hB s) = D.trans h (hB'.trans hB) s :=
  res_res _ _ _ _

/-- A transition map after restricting is a transition map. -/
lemma trans_res {i j : D.J} (h : i ≤ j) {A A' : (D.P j).Opens} {B : (D.P i).Opens}
    (hA : A' ≤ A) (hB : B ≤ D.map h ⁻¹ᵁ A') (s : Γ(D.obj j, A)) :
    D.trans h hB (res (D.obj j) hA s) =
      D.trans h (hB.trans ((D.map h).preimage_mono hA)) s := by
  rw [trans_apply, trans_apply]
  have := homApp_res (D.φ h) hA s
  change res (D.obj i) hB ((D.φ h).app A' (res (D.obj j) hA s)) = _
  rw [← this]
  exact res_res _ _ _ _

/-- Transition maps compose. -/
lemma trans_trans {k i j : D.J} (hki : k ≤ i) (hij : i ≤ j) {A : (D.P j).Opens}
    {B : (D.P i).Opens} {C : (D.P k).Opens} (hB : B ≤ D.map hij ⁻¹ᵁ A)
    (hC : C ≤ D.map hki ⁻¹ᵁ B) (hC' : C ≤ D.map (hki.trans hij) ⁻¹ᵁ A) (s : Γ(D.obj j, A)) :
    D.trans hki hC (D.trans hij hB s) = D.trans (hki.trans hij) hC' s := by
  have h₁ : (D.obj k).presheaf.map (homOfLE hC).op ((D.φ hki).app B
      ((D.obj i).presheaf.map (homOfLE hB).op ((D.φ hij).app A s))) =
      (D.obj k).presheaf.map (homOfLE hC).op ((D.obj k).presheaf.map
        (homOfLE ((D.map hki).preimage_mono hB)).op
        ((D.φ hki).app (D.map hij ⁻¹ᵁ A) ((D.φ hij).app A s))) :=
    congrArg _ (homApp_res (D.φ hki) hB _).symm
  refine h₁.trans ((res_res _ _ _ _).trans ?_)
  exact D.φ_comp hki hij A s C _ hC'

lemma map_comp {k i j : D.J} (hki : k ≤ i) (hij : i ≤ j) :
    D.map hki ≫ D.map hij = D.map (hki.trans hij) := by
  rw [← cancel_mono (D.ι j), Category.assoc, D.map_ι, D.map_ι, D.map_ι]

lemma preimage_ι {i j : D.J} (h : i ≤ j) (W : X.Opens) :
    D.map h ⁻¹ᵁ D.ι j ⁻¹ᵁ W = D.ι i ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, D.map_ι]

/-- The transition map is bijective from the image of an open. -/
lemma trans_bijective {i j : D.J} (h : i ≤ j) (B : (D.P i).Opens)
    (hB : B ≤ D.map h ⁻¹ᵁ D.map h ''ᵁ B) :
    Function.Bijective (D.trans h hB) := by
  have e : D.map h ⁻¹ᵁ D.map h ''ᵁ B = B := (D.map h).preimage_image_eq B
  have hres : Function.Bijective (res (D.obj i) hB) := by
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ⟨res (D.obj i) e.le x, ?_⟩⟩
    · have := congrArg (res (D.obj i) e.le) hxy
      simp only [res_res, res_self] at this
      exact this
    · rw [res_res, res_self]
  exact hres.comp (D.bijective h B)

/-! ## Covering the charts by smaller charts -/

/-- A point of `P j` mapping into the members `i` and `i'` lies in the image of a member below
both. -/
lemma exists_map_eq {i i' j : D.J} (x : D.P j) (hi : D.ι j x ∈ (D.ι i).opensRange)
    (hi' : D.ι j x ∈ (D.ι i').opensRange) :
    ∃ l, ∃ (_ : l ≤ i) (_ : l ≤ i') (hlj : l ≤ j) (w : D.P l), D.map hlj w = x := by
  obtain ⟨l, hli, hlj', ⟨w, hw⟩⟩ := D.exists_le hi (Set.mem_range_self (f := D.ι j) x)
  obtain ⟨l', hl'l, hl'i', ⟨w', hw'⟩⟩ := D.exists_le (show D.ι j x ∈ (D.ι l).opensRange from
    ⟨w, hw⟩) hi'
  refine ⟨l', hl'l.trans hli, hl'i', hl'l.trans hlj', w', (D.ι j).isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, D.map_ι, hw']


section Product

variable {Y : Scheme.{u}} {I : Type u} (Q : I → Y.Modules) (W : Y.Opens)

/-- Taking sections over an open, as a functor to types. -/
private noncomputable abbrev sectionsFunctor : Y.Modules ⥤ Type u :=
  toPresheaf Y ⋙ (CategoryTheory.evaluation _ _).obj (op W) ⋙ CategoryTheory.forget AddCommGrpCat

private instance : PreservesLimits (sectionsFunctor (Y := Y) W) :=
  have : PreservesLimits ((CategoryTheory.evaluation (Y.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W) ⋙
      CategoryTheory.forget AddCommGrpCat) := comp_preservesLimits _ _
  comp_preservesLimits _ _

/-- The sections of a product over an open are the families of sections. -/
private noncomputable def piSectionsEquiv : Γ(∏ᶜ Q, W) ≃ ∀ i, Γ(Q i, W) :=
  (Types.isLimitEquivSections (isLimitOfPreserves (sectionsFunctor W)
    (limit.isLimit (Discrete.functor Q)))).trans
    { toFun s i := s.1 ⟨i⟩
      invFun s := ⟨fun i ↦ s i.as, by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; rfl⟩
      left_inv s := rfl
      right_inv s := rfl }

private lemma piSectionsEquiv_apply (x : Γ(∏ᶜ Q, W)) (i : I) :
    piSectionsEquiv Q W x i = (Pi.π Q i).app W x := rfl

private lemma pi_π_app_piSectionsEquiv_symm (s : ∀ i, Γ(Q i, W)) (i : I) :
    (Pi.π Q i).app W ((piSectionsEquiv Q W).symm s) = s i := by
  rw [← piSectionsEquiv_apply, Equiv.apply_symm_apply]

private lemma pi_sections_ext {x y : Γ(∏ᶜ Q, W)}
    (h : ∀ i, (Pi.π Q i).app W x = (Pi.π Q i).app W y) : x = y :=
  (piSectionsEquiv Q W).injective (funext h)

end Product

/-! ## The glued module sheaf -/

/-- The product of the pushforwards of the module sheaves. -/
noncomputable abbrev prod : X.Modules :=
  ∏ᶜ fun j ↦ (pushforward (D.ι j)).obj (D.obj j)

/-- The pairs `i ≤ j` of indices. -/
abbrev Pair : Type u := {p : D.J × D.J // p.1 ≤ p.2}

/-- The `j`-th member, moved to `P i` by `φ`, for a pair `i ≤ j`. -/
noncomputable def left (p : D.Pair) : D.prod ⟶ (pushforward (D.ι p.1.1)).obj (D.obj p.1.1) :=
  Pi.π _ p.1.2 ≫ (pushforward (D.ι p.1.2)).map (D.φ p.2) ≫
    (pushforwardComp (D.map p.2) (D.ι p.1.2)).hom.app _ ≫
    (pushforwardCongr (D.map_ι p.2)).hom.app _

/-- The `i`-th member, for a pair `i ≤ j`. -/
noncomputable def right (p : D.Pair) : D.prod ⟶ (pushforward (D.ι p.1.1)).obj (D.obj p.1.1) :=
  Pi.π _ p.1.1

/-- Two sections of a module sheaf agreeing on a covering sieve are equal. -/
private lemma section_eq_of_mem_grothendieckTopology (M : X.Modules) {W : X.Opens}
    (R : Sieve W) (hR : R ∈ Opens.grothendieckTopology X W) {s t : Γ(M, W)}
    (h : ∀ ⦃V : X.Opens⦄ (g : V ⟶ W), R g → M.presheaf.map g.op s = M.presheaf.map g.op t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun p : Σ V : X.Opens, {g : V ⟶ W // R g} ↦ p.1) W (fun p ↦ p.2.1) ?_ s t
    fun p ↦ h _ p.2.2
  intro x hx
  obtain ⟨V, g, hg, hxV⟩ := hR x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, g, hg⟩, hxV⟩

/-- The compatible families: the sections of the product whose members agree under every
transition map. -/
noncomputable def glueSubmodule : D.prod.Submodule where
  obj W := ⨅ p : D.Pair, LinearMap.ker ((D.left p - D.right p).val.app W).hom
  map {W W'} g x hx := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_comap] at hx ⊢
    intro p
    have h := PresheafOfModules.naturality_apply (D.left p - D.right p).val g x
    rw [hx p, map_zero] at h
    exact h
  isSheaf W x hx := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro p
    refine section_eq_of_mem_grothendieckTopology
      ((pushforward (D.ι p.1.1)).obj (D.obj p.1.1)) _ hx fun V g hg ↦ ?_
    have hg' : ((D.left p - D.right p).val.app (op V)).hom (D.prod.val.map g.op x) = 0 := by
      have h₀ : (show D.prod.val.obj (op V) from D.prod.val.map g.op x) ∈
          ⨅ q : D.Pair, LinearMap.ker ((D.left q - D.right q).val.app (op V)).hom := hg
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h₀ p)
    have h := PresheafOfModules.naturality_apply (D.left p - D.right p).val g.op x
    exact h.symm.trans (hg'.trans (map_zero _).symm)

/-- **The glued module sheaf.** -/
noncomputable abbrev glue : X.Modules := D.glueSubmodule.toSheafOfModules

/-! ## Sections of the glued sheaf -/

/-- Two sections agreeing on the members of a cover are equal. -/
private lemma sec_ext {Y : Scheme.{u}} (M : Y.Modules) {V : Y.Opens} {I : Type u}
    (U : I → Y.Opens) (hU : ∀ i, U i ≤ V) (hcover : V ≤ iSup U) (s t : Γ(M, V))
    (h : ∀ i, res M (hU i) s = res M (hU i) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ U V (fun i ↦ homOfLE (hU i)) hcover
    s t h

/-- Sections on the members of a cover that agree on overlaps glue. -/
private lemma sec_glue {Y : Scheme.{u}} (M : Y.Modules) {V : Y.Opens} {I : Type u}
    (U : I → Y.Opens) (hU : ∀ i, U i ≤ V) (hcover : V ≤ iSup U) (sf : ∀ i, Γ(M, U i))
    (h : ∀ i i', res M (inf_le_left : U i ⊓ U i' ≤ U i) (sf i) =
      res M (inf_le_right : U i ⊓ U i' ≤ U i') (sf i')) :
    ∃ s : Γ(M, V), ∀ i, res M (hU i) s = sf i :=
  (TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U V (fun i ↦ homOfLE (hU i))
    hcover sf h).exists

/-- The `j`-th member of a section of the product. -/
noncomputable def piπ (j : D.J) (W : X.Opens) : Γ(D.prod, W) ⟶ Γ(D.obj j, D.ι j ⁻¹ᵁ W) :=
  Modules.Hom.app (Pi.π (fun j ↦ (pushforward (D.ι j)).obj (D.obj j)) j) W

lemma left_app (p : D.Pair) (W : X.Opens) (y : Γ(D.prod, W)) :
    (D.left p).app W y = D.trans p.2 (D.preimage_ι p.2 W).ge (D.piπ p.1.2 W y) := by
  rw [trans_apply]
  simp only [left, Modules.Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  exact map_apply_congr _ _ _ _

lemma right_app (p : D.Pair) (W : X.Opens) (y : Γ(D.prod, W)) :
    (D.right p).app W y = D.piπ p.1.1 W y :=
  rfl

/-- A section of the product is compatible when `left` and `right` agree on it for all pairs. -/
lemma mem_glueSubmodule {W : X.Opens} (y : Γ(D.prod, W)) :
    (show D.prod.val.obj (op W) from y) ∈ D.glueSubmodule.obj (op W) ↔
      ∀ p : D.Pair, (D.left p).app W y = (D.right p).app W y := by
  change (show D.prod.val.obj (op W) from y) ∈ ⨅ p : D.Pair,
    LinearMap.ker ((D.left p - D.right p).val.app (op W)).hom ↔ _
  rw [Submodule.mem_iInf]
  exact ⟨fun h p ↦ sub_eq_zero.mp (LinearMap.mem_ker.mp (h p)),
    fun h p ↦ LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h p))⟩

/-- A section of the product is a compatible family when every transition map takes its `j`-th
member to its `i`-th member. -/
lemma mem_glueSubmodule_iff {W : X.Opens} (y : Γ(D.prod, W)) :
    (show D.prod.val.obj (op W) from y) ∈ D.glueSubmodule.obj (op W) ↔
      ∀ (i j : D.J) (h : i ≤ j),
        D.trans h (D.preimage_ι h W).ge (D.piπ j W y) = D.piπ i W y := by
  rw [mem_glueSubmodule]
  refine ⟨fun H i j h ↦ ?_, fun H p ↦ ?_⟩
  · have e := H ⟨(i, j), h⟩
    rw [left_app, right_app] at e
    exact e
  · rw [left_app, right_app]
    exact H p.1.1 p.1.2 p.2

/-- The comparison of the restriction of the glued module sheaf to `P k` with `obj k`. -/
noncomputable def glueRestrict (k : D.J) : D.glue.restrict (D.ι k) ⟶ D.obj k :=
  (restrictFunctor (D.ι k)).map (D.glueSubmodule.ι ≫
    Pi.π (fun j ↦ (pushforward (D.ι j)).obj (D.obj j)) k) ≫
    (restrictAdjunction (D.ι k)).counit.app (D.obj k)

/-- On sections, the comparison takes the `k`-th member. -/
lemma glueRestrict_app (k : D.J) (T : (D.P k).Opens) (x : Γ(D.glue, D.ι k ''ᵁ T)) :
    (D.glueRestrict k).app T x =
      res (D.obj k) ((D.ι k).preimage_image_eq T).ge (D.piπ k (D.ι k ''ᵁ T) x.1) :=
  map_apply_congr _ _ _ _

/-! ## Covering lemmas -/

/-- Over `W ⊆ ι k (P k)`, the chart `P j` is covered by the images of the charts below `j` and
`k`. -/
lemma preimage_le_iSup (k j : D.J) {W : X.Opens} (hW : W ≤ (D.ι k).opensRange) :
    D.ι j ⁻¹ᵁ W ≤ ⨆ l : {l : D.J // l ≤ j ∧ l ≤ k}, D.map l.2.1 ''ᵁ D.ι l.1 ⁻¹ᵁ W := by
  intro x hx
  obtain ⟨l, hlj, hlk, hlj', w, rfl⟩ :=
    D.exists_map_eq (i := j) (i' := k) x ⟨x, rfl⟩ (hW hx)
  refine Opens.mem_iSup.mpr ⟨⟨l, hlj, hlk⟩, ⟨w, ?_, rfl⟩⟩
  change D.ι l w ∈ W
  rw [← D.map_ι hlj', Scheme.Hom.comp_apply]
  exact hx

/-- The overlap of the images of two charts below `j` is covered by the images of the charts
below both. -/
lemma inf_le_iSup {i i' j : D.J} (hij : i ≤ j) (hi'j : i' ≤ j) (W : X.Opens) :
    D.map hij ''ᵁ D.ι i ⁻¹ᵁ W ⊓ D.map hi'j ''ᵁ D.ι i' ⁻¹ᵁ W ≤
      ⨆ l : {l : D.J // l ≤ i ∧ l ≤ i'}, D.map (l.2.1.trans hij) ''ᵁ D.ι l.1 ⁻¹ᵁ W := by
  rintro x ⟨⟨z, hz, rfl⟩, ⟨z', hz', hzz'⟩⟩
  have h₁ : D.ι j (D.map hij z) ∈ (D.ι i).opensRange :=
    ⟨z, by rw [← Scheme.Hom.comp_apply, D.map_ι]⟩
  have h₂ : D.ι j (D.map hij z) ∈ (D.ι i').opensRange :=
    ⟨z', by
      have e : D.map hi'j z' = D.map hij z := hzz'
      rw [← e, ← Scheme.Hom.comp_apply, D.map_ι]⟩
  obtain ⟨l, hli, hli', hlj, w, hw⟩ := D.exists_map_eq _ h₁ h₂
  refine Opens.mem_iSup.mpr ⟨⟨l, hli, hli'⟩, ⟨w, ?_, hw⟩⟩
  change D.ι l w ∈ W
  have : D.ι l w = D.ι i z := by
    rw [← D.map_ι hlj, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, D.map_ι]
  rw [this]
  exact hz

/-- The image of a chart below `j` lies over its preimage. -/
lemma image_le_preimage {i j : D.J} (h : i ≤ j) (W : X.Opens) :
    D.map h ''ᵁ D.ι i ⁻¹ᵁ W ≤ D.ι j ⁻¹ᵁ W := by
  rw [← D.preimage_ι h W]
  exact (D.map h).image_preimage_le _

lemma le_preimage_image {i j : D.J} (h : i ≤ j) (B : (D.P i).Opens) :
    B ≤ D.map h ⁻¹ᵁ D.map h ''ᵁ B :=
  ((D.map h).preimage_image_eq B).ge

/-! ## The comparison is bijective on sections -/

/-- A compatible family over `W ⊆ ι k (P k)` whose `k`-th member vanishes is zero. -/
lemma eq_zero_of_piπ_eq_zero {k : D.J} {W : X.Opens} (hWk : W ≤ (D.ι k).opensRange)
    (y : Γ(D.prod, W)) (hcomp : ∀ (i j : D.J) (h : i ≤ j),
      D.trans h (D.preimage_ι h W).ge (D.piπ j W y) = D.piπ i W y)
    (hk : D.piπ k W y = 0) : y = 0 := by
  have hj (j : D.J) : D.piπ j W y = 0 := by
    refine sec_ext (D.obj j) (fun l : {l : D.J // l ≤ j ∧ l ≤ k} ↦
      D.map l.2.1 ''ᵁ D.ι l.1 ⁻¹ᵁ W) (fun l ↦ D.image_le_preimage l.2.1 W)
      (D.preimage_le_iSup k j hWk) _ _ fun ⟨l, hlj, hlk⟩ ↦ ?_
    rw [map_zero]
    apply (D.trans_bijective hlj (D.ι l ⁻¹ᵁ W) (D.le_preimage_image hlj _)).injective
    rw [map_zero, trans_res]
    exact (hcomp l j hlj).trans ((hcomp l k hlk).symm.trans (by rw [hk, map_zero]))
  exact pi_sections_ext _ _ fun j ↦ (hj j).trans (map_zero _).symm

/-- The comparison is injective on sections: a compatible family is determined by its `k`-th
member. -/
lemma glueRestrict_app_injective (k : D.J) (T : (D.P k).Opens) :
    Function.Injective ((D.glueRestrict k).app T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hy := (D.mem_glueSubmodule_iff (W := D.ι k ''ᵁ T) x.1).mp x.2
  have h₁ : res (D.obj k) ((D.ι k).preimage_image_eq T).ge
      (D.piπ k (D.ι k ''ᵁ T) x.1) = 0 :=
    (D.glueRestrict_app k T x).symm.trans hx
  have h₂ := congrArg (res (D.obj k) ((D.ι k).preimage_image_eq T).le) h₁
  rw [res_res, res_self, map_zero] at h₂
  exact Subtype.ext ((D.eq_zero_of_piπ_eq_zero ((D.ι k).image_le_opensRange T) x.1 hy h₂).trans
    rfl)


lemma image_le_image {m l j : D.J} (hml : m ≤ l) (hlj : l ≤ j) (W : X.Opens) :
    D.map (hml.trans hlj) ''ᵁ D.ι m ⁻¹ᵁ W ≤ D.map hlj ''ᵁ D.ι l ⁻¹ᵁ W := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨D.map hml z, D.image_le_preimage hml W ⟨z, hz, rfl⟩, ?_⟩
  change D.map hlj (D.map hml z) = D.map (hml.trans hlj) z
  rw [← Scheme.Hom.comp_apply, D.map_comp]

/-! ### Extending a section of the `k`-th member to a compatible family -/

section Extension

variable {k : D.J} {W : X.Opens} (hWk : W ≤ (D.ι k).opensRange) (t : Γ(D.obj k, D.ι k ⁻¹ᵁ W))

/-- The section over the image of `P l` in `P j` that `φ` takes to the transport of `t`. -/
noncomputable def extPiece {j : D.J} (l : {l : D.J // l ≤ j ∧ l ≤ k}) :
    Γ(D.obj j, D.map l.2.1 ''ᵁ D.ι l.1 ⁻¹ᵁ W) :=
  (Equiv.ofBijective _ (D.trans_bijective l.2.1 (D.ι l.1 ⁻¹ᵁ W)
    (D.le_preimage_image l.2.1 _))).symm (D.trans l.2.2 (D.preimage_ι l.2.2 W).ge t)

lemma trans_extPiece_self {j : D.J} (l : {l : D.J // l ≤ j ∧ l ≤ k}) :
    D.trans l.2.1 (D.le_preimage_image l.2.1 _) (D.extPiece t l) =
      D.trans l.2.2 (D.preimage_ι l.2.2 W).ge t :=
  Equiv.ofBijective_apply_symm_apply _ _ _

lemma trans_extPiece {j : D.J} (l : {l : D.J // l ≤ j ∧ l ≤ k}) {m : D.J} (hml : m ≤ l.1)
    {C : (D.P m).Opens}
    (hC₁ : C ≤ D.map (hml.trans l.2.1) ⁻¹ᵁ D.map l.2.1 ''ᵁ D.ι l.1 ⁻¹ᵁ W)
    (hC₂ : C ≤ D.map (hml.trans l.2.2) ⁻¹ᵁ D.ι k ⁻¹ᵁ W) :
    D.trans (hml.trans l.2.1) hC₁ (D.extPiece t l) = D.trans (hml.trans l.2.2) hC₂ t := by
  have hC : C ≤ D.map hml ⁻¹ᵁ D.ι l.1 ⁻¹ᵁ W := by
    rw [D.preimage_ι]
    rwa [D.preimage_ι] at hC₂
  rw [← D.trans_trans hml l.2.1 (D.le_preimage_image l.2.1 _) hC hC₁, trans_extPiece_self,
    D.trans_trans hml l.2.2 _ hC hC₂]

include hWk in
lemma exists_ext (j : D.J) : ∃ s : Γ(D.obj j, D.ι j ⁻¹ᵁ W),
    ∀ l : {l : D.J // l ≤ j ∧ l ≤ k},
      res (D.obj j) (D.image_le_preimage l.2.1 W) s = D.extPiece t l := by
  refine sec_glue (D.obj j) _ (fun l ↦ D.image_le_preimage l.2.1 W)
    (D.preimage_le_iSup k j hWk) _ fun ⟨l, hlj, hlk⟩ ⟨l', hl'j, hl'k⟩ ↦ ?_
  refine sec_ext (D.obj j) (fun m : {m : D.J // m ≤ l ∧ m ≤ l'} ↦
      D.map (m.2.1.trans hlj) ''ᵁ D.ι m.1 ⁻¹ᵁ W)
    (fun m ↦ le_inf (D.image_le_image m.2.1 hlj W) (D.image_le_image m.2.2 hl'j W))
    (D.inf_le_iSup hlj hl'j W) _ _ fun ⟨m, hml, hml'⟩ ↦ ?_
  rw [res_res, res_res]
  apply (D.trans_bijective (hml.trans hlj) (D.ι m ⁻¹ᵁ W) (D.le_preimage_image _ _)).injective
  rw [trans_res, trans_res]
  exact (D.trans_extPiece t ⟨l, hlj, hlk⟩ hml _ (D.preimage_ι _ W).ge).trans
    (D.trans_extPiece t ⟨l', hl'j, hl'k⟩ hml' _ (D.preimage_ι _ W).ge).symm

/-- The `j`-th member of the extension of `t`. -/
noncomputable def ext (j : D.J) : Γ(D.obj j, D.ι j ⁻¹ᵁ W) :=
  (D.exists_ext hWk t j).choose

lemma ext_spec (j : D.J) (l : {l : D.J // l ≤ j ∧ l ≤ k}) :
    res (D.obj j) (D.image_le_preimage l.2.1 W) (D.ext hWk t j) = D.extPiece t l :=
  (D.exists_ext hWk t j).choose_spec l

/-- The extension is a compatible family. -/
lemma trans_ext {i j : D.J} (h : i ≤ j) :
    D.trans h (D.preimage_ι h W).ge (D.ext hWk t j) = D.ext hWk t i := by
  refine sec_ext (D.obj i) (fun m : {m : D.J // m ≤ i ∧ m ≤ k} ↦
      D.map m.2.1 ''ᵁ D.ι m.1 ⁻¹ᵁ W) (fun m ↦ D.image_le_preimage m.2.1 W)
    (D.preimage_le_iSup k i hWk) _ _ fun ⟨m, hmi, hmk⟩ ↦ ?_
  apply (D.trans_bijective hmi (D.ι m ⁻¹ᵁ W) (D.le_preimage_image _ _)).injective
  rw [D.ext_spec hWk t i ⟨m, hmi, hmk⟩, trans_res,
    D.trans_trans hmi h _ _ ((D.preimage_ι _ W).ge),
    ← D.trans_res (hmi.trans h) (D.image_le_preimage (hmi.trans h) W) (D.le_preimage_image _ _),
    D.ext_spec hWk t j ⟨m, hmi.trans h, hmk⟩]
  exact (D.trans_extPiece t ⟨m, hmi.trans h, hmk⟩ le_rfl _ (D.preimage_ι _ W).ge).trans
    (D.trans_extPiece t ⟨m, hmi, hmk⟩ le_rfl _ (D.preimage_ι _ W).ge).symm

/-- The `k`-th member of the extension is `t`. -/
lemma ext_self : D.ext hWk t k = t := by
  refine sec_ext (D.obj k) (fun m : {m : D.J // m ≤ k ∧ m ≤ k} ↦
      D.map m.2.1 ''ᵁ D.ι m.1 ⁻¹ᵁ W) (fun m ↦ D.image_le_preimage m.2.1 W)
    (D.preimage_le_iSup k k hWk) _ _ fun ⟨m, hmk, hmk'⟩ ↦ ?_
  apply (D.trans_bijective hmk (D.ι m ⁻¹ᵁ W) (D.le_preimage_image _ _)).injective
  rw [D.ext_spec hWk t k ⟨m, hmk, hmk'⟩, trans_res]
  exact D.trans_extPiece t ⟨m, hmk, hmk'⟩ le_rfl _ (D.preimage_ι _ W).ge

/-- The extension, as a section of the product. -/
noncomputable def extProd : Γ(D.prod, W) :=
  (piSectionsEquiv (fun j ↦ (pushforward (D.ι j)).obj (D.obj j)) W).symm (D.ext hWk t)

lemma piπ_extProd (j : D.J) : D.piπ j W (D.extProd hWk t) = D.ext hWk t j :=
  pi_π_app_piSectionsEquiv_symm _ _ _ j

lemma extProd_mem : (show D.prod.val.obj (op W) from D.extProd hWk t) ∈
    D.glueSubmodule.obj (op W) := by
  rw [mem_glueSubmodule_iff]
  intro i j h
  rw [piπ_extProd, piπ_extProd]
  exact D.trans_ext hWk t h

end Extension

/-- The comparison is surjective on sections: a section of the `k`-th member extends to a
compatible family. -/
lemma glueRestrict_app_surjective (k : D.J) (T : (D.P k).Opens) :
    Function.Surjective ((D.glueRestrict k).app T) := by
  intro t
  have hWk : D.ι k ''ᵁ T ≤ (D.ι k).opensRange := (D.ι k).image_le_opensRange T
  set t' := res (D.obj k) ((D.ι k).preimage_image_eq T).le t
  refine ⟨⟨D.extProd hWk t', D.extProd_mem hWk t'⟩, ?_⟩
  refine (D.glueRestrict_app k T _).trans ?_
  change res (D.obj k) _ (D.piπ k _ (D.extProd hWk t')) = t
  rw [piπ_extProd, ext_self, res_res, res_self]

instance (k : D.J) : IsIso (D.glueRestrict k) :=
  Hom.isIso_iff_isIso_app.mpr fun T ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨D.glueRestrict_app_injective k T, D.glueRestrict_app_surjective k T⟩

/-- **The restriction of the glued module sheaf to `P k` is `obj k`.** -/
noncomputable def glueRestrictIso (k : D.J) : D.glue.restrict (D.ι k) ≅ D.obj k :=
  asIso (D.glueRestrict k)

/-- On sections, the isomorphism takes the `k`-th member of a compatible family. -/
lemma glueRestrictIso_hom_app (k : D.J) (T : (D.P k).Opens) (x : Γ(D.glue, D.ι k ''ᵁ T)) :
    (D.glueRestrictIso k).hom.app T x =
      res (D.obj k) ((D.ι k).preimage_image_eq T).ge (D.piπ k (D.ι k ''ᵁ T) x.1) :=
  D.glueRestrict_app k T x

end DirectedGluingData

end AlgebraicGeometry.Scheme.Modules
