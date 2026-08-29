/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseBounds

/-!
# Operations on repository-owned HN filtrations

This module supplies the elementary filtration constructors and transports
needed by phase truncations.  It remains on the Mathlib-only side of the
ownership boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The empty HN filtration of a zero object. -/
def HNFiltration.zero {P : ℝ → ObjectProperty C} (E : C) (hE : IsZero E) :
    HNFiltration C P E where
  n := 0
  chain := ComposableArrows.mk₀ E
  triangle := fun i => Fin.elim0 i
  triangle_dist := fun i => Fin.elim0 i
  triangle_obj₁ := fun i => Fin.elim0 i
  triangle_obj₂ := fun i => Fin.elim0 i
  base_isZero := by simpa [ComposableArrows.left] using hE
  top_iso := ⟨by simpa [ComposableArrows.right] using Iso.refl E⟩
  φ := fun i => Fin.elim0 i
  hφ := fun i => Fin.elim0 i
  semistable := fun i => Fin.elim0 i

/-- The one-factor HN filtration of a semistable object. -/
def HNFiltration.single {P : ℝ → ObjectProperty C} (S : C) (φ : ℝ)
    (hS : P φ S) : HNFiltration C P S where
  n := 1
  chain := ComposableArrows.mk₁ (0 : (0 : C) ⟶ S)
  triangle := fun _ => Triangle.mk (0 : (0 : C) ⟶ S) (𝟙 S) 0
  triangle_dist := fun _ => contractible_distinguished₁ S
  triangle_obj₁ := fun _ =>
    ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  triangle_obj₂ := fun _ =>
    ⟨eqToIso (by simp [ComposableArrows.obj', ComposableArrows.mk₁_obj])⟩
  base_isZero := isZero_zero C
  top_iso := ⟨eqToIso (by simp [ComposableArrows.right, ComposableArrows.mk₁_obj])⟩
  φ := fun _ => φ
  hφ := fun _ _ h => by omega
  semistable := fun i => by
    have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi
    exact hS

/-- A one-factor HN filtration identifies its ambient object with its unique
semistable factor. -/
theorem HNFiltration.semistable_of_length_one
    {P : ℝ → ObjectProperty C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    {Y : C} (G : HNFiltration C P Y) (hG : G.n = 1) :
    P (G.φ ⟨0, by omega⟩) Y := by
  let j : Fin G.n := ⟨0, by omega⟩
  let T := G.triangle j
  have hT₁ : IsZero T.obj₁ :=
    IsZero.of_iso G.base_isZero (Classical.choice (G.triangle_obj₁ j))
  haveI : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (G.triangle_dist j)).mp hT₁
  have htop : G.chain.obj' (0 + 1) (by omega) = G.chain.obj (Fin.last G.n) :=
    congrArg G.chain.obj (Fin.ext (by simp [Fin.last, hG]))
  let e : T.obj₂ ≅ Y :=
    (Classical.choice (G.triangle_obj₂ j)).trans
      ((eqToIso htop).trans (Classical.choice G.top_iso))
  letI : (P (G.φ j)).IsClosedUnderIsomorphisms := hPiso (G.φ j)
  exact (P (G.φ j)).prop_of_iso ((e.symm.trans (asIso T.mor₂)).symm)
    (G.semistable j)

/-- Keep the first `k` factors of an HN filtration. -/
def HNFiltration.prefix {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) :
    HNFiltration C P (F.chain.obj ⟨k, by omega⟩) where
  n := k
  chain := ComposableArrows.mkOfObjOfMapSucc
    (fun i : Fin (k + 1) => F.chain.obj ⟨i, by omega⟩)
    (fun i : Fin k => F.chain.map' i (i + 1) (by omega) (by omega))
  triangle := fun i => F.triangle ⟨i, by omega⟩
  triangle_dist := fun i => F.triangle_dist ⟨i, by omega⟩
  triangle_obj₁ := fun i => F.triangle_obj₁ ⟨i, by omega⟩
  triangle_obj₂ := fun i => F.triangle_obj₂ ⟨i, by omega⟩
  base_isZero := F.base_isZero
  top_iso := ⟨Iso.refl _⟩
  φ := fun i => F.φ ⟨i, by omega⟩
  hφ := by
    intro i j hij
    exact F.hφ (Fin.mk_lt_mk.mpr hij)
  semistable := fun i => F.semistable ⟨i, by omega⟩

@[simp]
theorem HNFiltration.prefix_φ {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n)
    (i : Fin k) : (F.prefix C k hk).φ i = F.φ ⟨i, by omega⟩ := rfl

/-- The lowest phase of a nonempty prefix is its last retained phase. -/
theorem HNFiltration.prefix_phiMinus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k) :
    (F.prefix C k hk).phiMinus C hk₀ = F.φ ⟨k - 1, by omega⟩ := by
  rfl

/-- A filtration prefix whose factors all lie strictly above a cutoff has its
lowest phase strictly above that cutoff. -/
theorem HNFiltration.prefix_phiMinus_gt {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k)
    (t : ℝ) (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by omega⟩) :
    t < (F.prefix C k hk).phiMinus C hk₀ := by
  rw [F.prefix_phiMinus C k hk hk₀]
  exact ht ⟨k - 1, by omega⟩

/-- A chain object inherits a strict lower phase bound from all factors in
the prefix ending at that object. -/
theorem HNFiltration.chain_obj_gtProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k)
    (t : ℝ) (ht : ∀ j : Fin k, t < F.φ ⟨j.val, by omega⟩) :
    s.gtProp C t (F.chain.obj ⟨k, by omega⟩) :=
  Or.inr ⟨F.prefix C k hk, hk₀, F.prefix_phiMinus_gt C k hk hk₀ t ht⟩

/-- A chain object inherits a weak upper phase bound from all factors in the
prefix ending at that object. -/
theorem HNFiltration.chain_obj_leProp (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (k : ℕ) (hk : k ≤ F.n) (hk₀ : 0 < k)
    (t : ℝ) (ht : ∀ j : Fin k, F.φ ⟨j.val, by omega⟩ ≤ t) :
    s.leProp C t (F.chain.obj ⟨k, by omega⟩) := by
  refine Or.inr ⟨F.prefix C k hk, hk₀, ?_⟩
  exact ht ⟨0, hk₀⟩

/-- Append one lower-phase semistable factor along a distinguished triangle. -/
def HNFiltration.appendFactor {P : ℝ → ObjectProperty C} {Y Z : C}
    (G : HNFiltration C P Y) (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : T.obj₁ ≅ Y) (e₂ : T.obj₂ ≅ Z) (ψ : ℝ) (hψ : P ψ T.obj₃)
    (hψ_lt : ∀ i : Fin G.n, ψ < G.φ i) : HNFiltration C P Z := by
  let obj : Fin (G.n + 2) → C := fun i =>
    if h : i ≤ G.n then G.chain.obj ⟨i, by omega⟩ else Z
  let last : G.chain.obj (Fin.last G.n) ⟶ Z :=
    (Classical.choice G.top_iso).hom ≫ e₁.inv ≫ T.mor₁ ≫ e₂.hom
  have mapSucc : ∀ i : Fin (G.n + 1), obj (Fin.castSucc i) ⟶ obj (Fin.succ i) := by
    rintro ⟨i, hi⟩
    simp only [obj, Fin.castSucc_mk, Fin.succ_mk]
    by_cases h : i + 1 ≤ G.n
    · simp only [show i ≤ G.n by omega, h, dite_true]
      exact G.chain.map' i (i + 1) (by omega) (by omega)
    · simp only [show i ≤ G.n by omega, h, dite_true, dite_false]
      exact eqToHom (by congr 1; ext; simp [Fin.val_last]; omega) ≫ last
  exact
    { n := G.n + 1
      chain := ComposableArrows.mkOfObjOfMapSucc obj mapSucc
      triangle := fun i => if h : i < G.n then G.triangle ⟨i, h⟩ else T
      triangle_dist := fun i => by
        split_ifs with h
        · exact G.triangle_dist ⟨i, h⟩
        · exact hT
      triangle_obj₁ := fun i => by
        have chainObj : ∀ k (hk : k ≤ G.n),
            (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨k, by omega⟩ =
              G.chain.obj ⟨k, by omega⟩ := by
          intro k hk
          simp [ComposableArrows.mkOfObjOfMapSucc_obj, obj, hk]
        split_ifs with h
        · exact ⟨(Classical.choice (G.triangle_obj₁ ⟨i, h⟩)).trans
            (eqToIso (by simpa [ComposableArrows.obj'] using (chainObj i (by omega)).symm))⟩
        · have hi : i = G.n := by omega
          exact ⟨e₁.trans ((Classical.choice G.top_iso).symm.trans (eqToIso (by
            change G.chain.obj (Fin.last G.n) =
              (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj' i _
            simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
              obj, show i ≤ G.n by omega, dite_true]
            congr 1
            ext
            simp [Fin.val_last, hi])))⟩
      triangle_obj₂ := fun i => by
        have chainObj : ∀ k (hk : k ≤ G.n),
            (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨k, by omega⟩ =
              G.chain.obj ⟨k, by omega⟩ := by
          intro k hk
          simp [ComposableArrows.mkOfObjOfMapSucc_obj, obj, hk]
        split_ifs with h
        · exact ⟨(Classical.choice (G.triangle_obj₂ ⟨i, h⟩)).trans
            (eqToIso (by simpa [ComposableArrows.obj'] using
              (chainObj (i + 1) (by omega)).symm))⟩
        · exact ⟨e₂.trans (eqToIso (by
            simp only [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
              obj, show ¬(i + 1 ≤ G.n) by omega, dite_false]))⟩
      base_isZero := by
        change IsZero ((ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj ⟨0, by omega⟩)
        simp only [ComposableArrows.mkOfObjOfMapSucc_obj, obj,
          show (0 : ℕ) ≤ G.n by omega, dite_true]
        exact G.base_isZero
      top_iso := ⟨by
        change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).obj
            ⟨G.n + 1, by omega⟩ ≅ Z
        simp only [ComposableArrows.mkOfObjOfMapSucc_obj, obj,
          show ¬(G.n + 1 ≤ G.n) by omega, dite_false]
        exact Iso.refl Z⟩
      φ := fun i => if h : i < G.n then G.φ ⟨i, h⟩ else ψ
      hφ := by
        intro i j hij
        rcases i with ⟨a, ha⟩
        rcases j with ⟨b, hb⟩
        have hab : a < b := Fin.mk_lt_mk.mp hij
        change (if h : b < G.n then G.φ ⟨b, h⟩ else ψ) <
          (if h : a < G.n then G.φ ⟨a, h⟩ else ψ)
        by_cases hb' : b < G.n
        · have ha' : a < G.n := by omega
          simp only [hb', ha', dite_true]
          exact G.hφ (Fin.mk_lt_mk.mpr hab)
        · by_cases ha' : a < G.n
          · simp only [hb', ha', dite_true, dite_false]
            exact hψ_lt ⟨a, ha'⟩
          · omega
      semistable := fun i => by
        change P (if h : i < G.n then G.φ ⟨i, h⟩ else ψ)
          ((if h : i < G.n then G.triangle ⟨i, h⟩ else T).obj₃)
        split_ifs with h
        · exact G.semistable ⟨i, h⟩
        · exact hψ }

/-- Splice a one-factor quotient filtration onto an HN filtration across a
distinguished triangle. -/
def HNFiltration.appendLengthOne
    {P : ℝ → ObjectProperty C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    {X E Y : C} (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (hGY : GY.n = 1)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hsep : ∀ j : Fin GX.n, GY.φ ⟨0, by omega⟩ < GX.φ j) :
    HNFiltration C P E :=
  GX.appendFactor C (Triangle.mk f g h) hT (Iso.refl _) (Iso.refl _)
    (GY.φ ⟨0, by omega⟩) (GY.semistable_of_length_one C hPiso hGY) hsep

/-- Lower and upper phase bounds pass through a one-factor HN splice. -/
theorem HNFiltration.appendLengthOne_phase_bounds
    {P : ℝ → ObjectProperty C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    {X E Y : C} (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (hGY : GY.n = 1)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hsep : ∀ j : Fin GX.n, GY.φ ⟨0, by omega⟩ < GX.φ j)
    (t U : ℝ)
    (hX : ∀ j : Fin GX.n, t < GX.φ j ∧ GX.φ j ≤ U)
    (hY : t < GY.φ ⟨0, by omega⟩ ∧ GY.φ ⟨0, by omega⟩ ≤ U) :
    ∀ j : Fin (GX.appendLengthOne C hPiso GY hGY f g h hT hsep).n,
      t < (GX.appendLengthOne C hPiso GY hGY f g h hT hsep).φ j ∧
        (GX.appendLengthOne C hPiso GY hGY f g h hT hsep).φ j ≤ U := by
  intro j
  simp only [HNFiltration.appendLengthOne, HNFiltration.appendFactor]
  split_ifs with hj
  · exact hX ⟨j.val, hj⟩
  · exact hY

/-- If the quotient term of a distinguished triangle has an empty HN
filtration, transport the filtration of the first term across the resulting
isomorphism to the middle term. -/
def HNFiltration.ofTriangleThirdZero
    {P : ℝ → ObjectProperty C}
    {X E Y : C} (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (hGY : GY.n = 0)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) :
    HNFiltration C P E := by
  have hY : IsZero Y := GY.isZero_of_length_zero hGY
  letI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hY
  exact GX.ofIso C (asIso f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Assemble an owner HN filtration across a distinguished triangle when all
phases of the quotient filtration are strictly below all phases of the
subobject filtration. The output retains any common strict lower phase bound. -/
theorem HNFiltration.exists_of_distinguished_triangle
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {X E Y : C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (t : ℝ)
    (hX_gt : ∀ j : Fin GX.n, t < GX.φ j)
    (hY_gt : ∀ i : Fin GY.n, t < GY.φ i)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) :
    ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j := by
  suffices hmain :
      ∀ (m : ℕ) {Y : C} (GY : HNFiltration C P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          ∀ (t : ℝ),
          (∀ j : Fin GX.n, t < GX.φ j) →
          (∀ i : Fin GY.n, t < GY.φ i) →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          ∃ G : HNFiltration C P E, ∀ j : Fin G.n, t < G.φ j by
    exact hmain GY.n GY le_rfl f g h hT t hX_gt hY_gt hsep
  intro m
  induction m with
  | zero =>
      intro Y GY hn E f g h hT t hX_gt _ _
      have hYn : GY.n = 0 := by omega
      let G := GX.ofTriangleThirdZero C GY hYn f g h hT
      refine ⟨G, ?_⟩
      intro j
      change t < GX.φ j
      exact hX_gt j
  | succ m ih =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep
      by_cases hYn : GY.n = 0
      · let G := GX.ofTriangleThirdZero C GY hYn f g h hT
        refine ⟨G, ?_⟩
        intro j
        change t < GX.φ j
        exact hX_gt j
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        by_cases hYone : GY.n = 1
        · let G := GX.appendLengthOne C hPiso GY hYone f g h hT
            (fun j => hsep ⟨0, by omega⟩ j)
          refine ⟨G, ?_⟩
          intro j
          simp only [G, HNFiltration.appendLengthOne, HNFiltration.appendFactor]
          split_ifs with hj
          · exact hX_gt ⟨j.val, hj⟩
          · exact hY_gt ⟨0, by omega⟩
        · have hYtwo : 2 ≤ GY.n := by omega
          let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
          let GY' := GY.prefix C (GY.n - 1) (by omega)
          let Tlast := GY.triangle jLast
          let e₁ := Classical.choice (GY.triangle_obj₁ jLast)
          let e₂ := Classical.choice (GY.triangle_obj₂ jLast)
          let eY := by
            have hchainN : GY.chain.obj' (GY.n - 1 + 1) (by omega) =
                GY.chain.obj (Fin.last GY.n) :=
              congrArg GY.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            exact e₂.trans ((eqToIso hchainN).trans (Classical.choice GY.top_iso))
          let f23 : GY.chain.obj ⟨GY.n - 1, by omega⟩ ⟶ Y :=
            e₁.inv ≫ Tlast.mor₁ ≫ eY.hom
          let g23 : Y ⟶ Tlast.obj₃ :=
            eY.inv ≫ Tlast.mor₂
          let h23 : Tlast.obj₃ ⟶ GY.chain.obj ⟨GY.n - 1, by omega⟩⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hT23 : Triangle.mk f23 g23 h23 ∈ distTriang C := by
            refine isomorphic_distinguished _ (GY.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm eY.symm (Iso.refl _)
              (by simp [Tlast, f23, eY])
              (by simp [Tlast, g23, eY])
              (by simp [Tlast, h23])
          obtain ⟨Z, f13, h13, hT13⟩ := distinguished_cocone_triangle₁ (g ≫ g23)
          let oct := Triangulated.someOctahedron'
            (show g ≫ g23 = g ≫ g23 by rfl) hT hT23 hT13
          have hsep' :
              ∀ i : Fin GY'.n, ∀ j : Fin GX.n, GY'.φ i < GX.φ j := by
            intro i j
            have hi : i.val < GY.n - 1 := i.is_lt
            exact hsep ⟨i.val, by omega⟩ j
          have hX_gt_last : ∀ j : Fin GX.n, GY.φ jLast < GX.φ j :=
            fun j => hsep jLast j
          have hY'_gt_last : ∀ i : Fin GY'.n, GY.φ jLast < GY'.φ i := by
            intro i
            have hi : i.val < GY.n - 1 := i.is_lt
            change GY.φ jLast < GY.φ ⟨i.val, by omega⟩
            exact GY.hφ (Fin.mk_lt_mk.mpr (by omega))
          obtain ⟨GZ, hGZ⟩ := ih GY' (by
            change GY.n - 1 ≤ m
            omega) oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃ oct.mem
            (GY.φ jLast) hX_gt_last hY'_gt_last hsep'
          have hlast_gt_t : t < GY.φ jLast := hY_gt jLast
          refine ⟨GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
            (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ, ?_⟩
          intro j
          by_cases hj : j.val < GZ.n
          · have hsmall :
                GY.φ jLast <
                  (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                    (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast)
                    hGZ).φ j := by
              simpa [HNFiltration.appendFactor, hj] using hGZ ⟨j.val, hj⟩
            exact hlast_gt_t.trans hsmall
          · have hjLast :
                (GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
                  (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast)
                  hGZ).φ j = GY.φ jLast := by
              simp [HNFiltration.appendFactor, hj]
            exact hjLast.symm ▸ hlast_gt_t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Upper-bound companion to `exists_of_distinguished_triangle`: a common
phase window for the input filtrations is retained by the assembled one. -/
theorem HNFiltration.exists_of_distinguished_triangle_phase_bounds
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {X E Y : C}
    (hPiso : ∀ φ : ℝ, (P φ).IsClosedUnderIsomorphisms)
    (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (t U : ℝ)
    (hX_gt : ∀ j : Fin GX.n, t < GX.φ j)
    (hY_gt : ∀ i : Fin GY.n, t < GY.φ i)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j)
    (hX_le : ∀ j : Fin GX.n, GX.φ j ≤ U)
    (hY_le : ∀ i : Fin GY.n, GY.φ i ≤ U) :
    ∃ G : HNFiltration C P E,
      (∀ j : Fin G.n, t < G.φ j) ∧ (∀ j : Fin G.n, G.φ j ≤ U) := by
  suffices hmain :
      ∀ (m : ℕ) {Y : C} (GY : HNFiltration C P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          ∀ (t : ℝ),
          (∀ j : Fin GX.n, t < GX.φ j) →
          (∀ i : Fin GY.n, t < GY.φ i) →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          (∀ j : Fin GX.n, GX.φ j ≤ U) →
          (∀ i : Fin GY.n, GY.φ i ≤ U) →
          ∃ G : HNFiltration C P E,
            (∀ j : Fin G.n, t < G.φ j) ∧ (∀ j : Fin G.n, G.φ j ≤ U) by
    exact hmain GY.n GY le_rfl f g h hT t hX_gt hY_gt hsep hX_le hY_le
  intro m
  induction m with
  | zero =>
      intro Y GY hn E f g h hT t hX_gt _ _ hX_le _
      have hYn : GY.n = 0 := by omega
      let G := GX.ofTriangleThirdZero C GY hYn f g h hT
      refine ⟨G, fun j => ?_, fun j => ?_⟩
      · change t < GX.φ j
        exact hX_gt j
      · change GX.φ j ≤ U
        exact hX_le j
  | succ m ih =>
      intro Y GY hn E f g h hT t hX_gt hY_gt hsep hX_le hY_le
      by_cases hYn : GY.n = 0
      · let G := GX.ofTriangleThirdZero C GY hYn f g h hT
        refine ⟨G, fun j => ?_, fun j => ?_⟩
        · change t < GX.φ j
          exact hX_gt j
        · change GX.φ j ≤ U
          exact hX_le j
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        by_cases hYone : GY.n = 1
        · let j0 : Fin GY.n := ⟨0, by omega⟩
          let G := GX.appendLengthOne C hPiso GY hYone f g h hT
            (fun j => hsep j0 j)
          refine ⟨G, fun j => ?_, fun j => ?_⟩
          · simp only [G, HNFiltration.appendLengthOne, HNFiltration.appendFactor]
            split_ifs with hj
            · exact hX_gt ⟨j.val, hj⟩
            · exact hY_gt j0
          · simp only [G, HNFiltration.appendLengthOne, HNFiltration.appendFactor]
            split_ifs with hj
            · exact hX_le ⟨j.val, hj⟩
            · exact hY_le j0
        · have hYtwo : 2 ≤ GY.n := by omega
          let jLast : Fin GY.n := ⟨GY.n - 1, by omega⟩
          let GY' := GY.prefix C (GY.n - 1) (by omega)
          let Tlast := GY.triangle jLast
          let e₁ := Classical.choice (GY.triangle_obj₁ jLast)
          let e₂ := Classical.choice (GY.triangle_obj₂ jLast)
          let eY := by
            have hchainN : GY.chain.obj' (GY.n - 1 + 1) (by omega) =
                GY.chain.obj (Fin.last GY.n) :=
              congrArg GY.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            exact e₂.trans ((eqToIso hchainN).trans (Classical.choice GY.top_iso))
          let f23 : GY.chain.obj ⟨GY.n - 1, by omega⟩ ⟶ Y :=
            e₁.inv ≫ Tlast.mor₁ ≫ eY.hom
          let g23 : Y ⟶ Tlast.obj₃ := eY.inv ≫ Tlast.mor₂
          let h23 : Tlast.obj₃ ⟶ GY.chain.obj ⟨GY.n - 1, by omega⟩⟦(1 : ℤ)⟧ :=
            Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hT23 : Triangle.mk f23 g23 h23 ∈ distTriang C := by
            refine isomorphic_distinguished _ (GY.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm eY.symm (Iso.refl _)
              (by simp [Tlast, f23, eY])
              (by simp [Tlast, g23, eY])
              (by simp [Tlast, h23])
          obtain ⟨Z, f13, h13, hT13⟩ := distinguished_cocone_triangle₁ (g ≫ g23)
          let oct := Triangulated.someOctahedron'
            (show g ≫ g23 = g ≫ g23 by rfl) hT hT23 hT13
          have hsep' : ∀ i : Fin GY'.n, ∀ j : Fin GX.n, GY'.φ i < GX.φ j := by
            intro i j
            have hi : i.val < GY.n - 1 := i.is_lt
            exact hsep ⟨i.val, by omega⟩ j
          have hX_gt_last : ∀ j : Fin GX.n, GY.φ jLast < GX.φ j :=
            fun j => hsep jLast j
          have hY'_gt_last : ∀ i : Fin GY'.n, GY.φ jLast < GY'.φ i := by
            intro i
            have hi : i.val < GY.n - 1 := i.is_lt
            change GY.φ jLast < GY.φ ⟨i.val, by omega⟩
            exact GY.hφ (Fin.mk_lt_mk.mpr (by omega))
          obtain ⟨GZ, hGZ_lo, hGZ_le⟩ := ih GY' (by
            change GY.n - 1 ≤ m
            omega) oct.triangle.mor₁ oct.triangle.mor₂ oct.triangle.mor₃ oct.mem
            (GY.φ jLast) hX_gt_last hY'_gt_last hsep' hX_le
            (fun i => by
              have hi : i.val < GY.n - 1 := i.is_lt
              exact hY_le ⟨i.val, by omega⟩)
          have hlast_gt_t : t < GY.φ jLast := hY_gt jLast
          let G := GZ.appendFactor C (Triangle.mk f13 (g ≫ g23) h13) hT13
            (Iso.refl _) (Iso.refl _) (GY.φ jLast) (GY.semistable jLast) hGZ_lo
          refine ⟨G, fun j => ?_, fun j => ?_⟩
          · simp only [G, HNFiltration.appendFactor]
            split_ifs with hj
            · exact hlast_gt_t.trans (hGZ_lo ⟨j.val, hj⟩)
            · exact hlast_gt_t
          · simp only [G, HNFiltration.appendFactor]
            split_ifs with hj
            · exact hGZ_le ⟨j.val, hj⟩
            · exact hY_le jLast

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Split a generic owner HN filtration at a real cutoff. The upper term has
all phases above the cutoff, while the quotient term has all phases at most
the cutoff. The construction also records the phase bounds needed for later
filtration assembly. -/
theorem HNFiltration.exists_split_at_cutoff
    [IsTriangulated C]
    {P : ℝ → ObjectProperty C} {A : C}
    (F : HNFiltration C P A) (t : ℝ) :
    ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (∀ j : Fin GX.n, t < GX.φ j) ∧
      (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
      (∀ (_ : 0 < F.n) (j : Fin GY.n),
        F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) ∧
      (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i) := by
  suffices hmain :
      ∀ (m : ℕ) (A : C) (F : HNFiltration C P A), F.n ≤ m →
        ∃ (X Y : C) (GX : HNFiltration C P X) (GY : HNFiltration C P Y)
          (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C ∧
          (∀ j : Fin GX.n, t < GX.φ j) ∧
          (∀ j : Fin GY.n, GY.φ j ≤ t) ∧
          (∀ (_ : 0 < F.n) (j : Fin GY.n),
            F.φ ⟨F.n - 1, by omega⟩ ≤ GY.φ j) ∧
          (∀ j : Fin GX.n, ∃ i : Fin F.n, GX.φ j = F.φ i) by
    exact hmain F.n A F le_rfl
  intro m
  induction m with
  | zero =>
      intro A F hFn
      have hn : F.n = 0 := by omega
      refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
      · intro j
        exact False.elim (by simpa [hn] using j.is_lt)
      · intro j
        exact Fin.elim0 j
      · intro hn0 j
        exact False.elim (by omega)
      · intro j
        exact False.elim (by simpa [hn] using j.isLt)
  | succ m ih =>
      intro A F hFn
      by_cases hn : F.n = 0
      · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
          𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
        · intro j
          exact False.elim (by simpa [hn] using j.is_lt)
        · intro j
          exact Fin.elim0 j
        · intro hn0 j
          exact False.elim (by omega)
        · intro j
          exact False.elim (by simpa [hn] using j.isLt)
      · have hn0 : 0 < F.n := Nat.pos_of_ne_zero hn
        by_cases hlast_gt : t < F.φ ⟨F.n - 1, by omega⟩
        · refine ⟨A, 0, F, HNFiltration.zero C (P := P) 0 (isZero_zero C),
            𝟙 A, 0, 0, contractible_distinguished A, ?_, ?_, ?_, ?_⟩
          · intro j
            exact hlast_gt.trans_le (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
          · intro j
            exact Fin.elim0 j
          · intro _ j
            exact Fin.elim0 j
          · intro j
            exact ⟨j, rfl⟩
        · have hlast_le : F.φ ⟨F.n - 1, by omega⟩ ≤ t := le_of_not_gt hlast_gt
          by_cases hFone : F.n = 1
          · refine ⟨0, A, HNFiltration.zero C (P := P) 0 (isZero_zero C), F,
              0, 𝟙 A, 0, contractible_distinguished₁ A, ?_, ?_, ?_, ?_⟩
            · intro j
              exact Fin.elim0 j
            · intro j
              have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
              subst j
              simpa [hFone] using hlast_le
            · intro _ j
              have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
              subst j
              simp [hFone]
            · intro j
              exact Fin.elim0 j
          · have hn2 : 2 ≤ F.n := by omega
            let G := F.prefix C (F.n - 1) (by omega)
            obtain ⟨X, Y', GX, GY', f', g', h', hT', hGX_gt, hGY'_le,
                hGY'_bound, hGX_contain⟩ :=
              ih (F.chain.obj' (F.n - 1) (by omega)) G (by
                change F.n - 1 ≤ m
                omega)
            let jLast : Fin F.n := ⟨F.n - 1, by omega⟩
            let T := F.triangle jLast
            let e₁ := Classical.choice (F.triangle_obj₁ jLast)
            let e₂ := Classical.choice (F.triangle_obj₂ jLast)
            let eA := Classical.choice F.top_iso
            have hchainN : F.chain.obj' (F.n - 1 + 1) (by omega) =
                F.chain.obj (Fin.last F.n) :=
              congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
            let e₂A : T.obj₂ ≅ A := e₂.trans ((eqToIso hchainN).trans eA)
            let u₂₃ : F.chain.obj' (F.n - 1) (by omega) ⟶ A :=
              e₁.inv ≫ T.mor₁ ≫ e₂A.hom
            let Tiso := Triangle.isoMk
              (Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂)
                (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')) T
              e₁.symm e₂A.symm (Iso.refl _)
              (by simp [u₂₃, e₂A])
              (by simp [e₂A])
              (by simp)
            have hTu₂₃ :
                Triangle.mk u₂₃ (e₂A.inv ≫ T.mor₂)
                    (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈ distTriang C :=
              isomorphic_distinguished _ (F.triangle_dist jLast) _ Tiso
            have hGn : 0 < G.n := by
              change 0 < F.n - 1
              omega
            have hφlast_lt :
                ∀ j : Fin GY'.n, F.φ jLast < GY'.φ j := by
              intro j
              calc
                F.φ jLast < F.φ ⟨F.n - 2, by omega⟩ :=
                  F.hφ (Fin.mk_lt_mk.mpr (by omega))
                _ = G.φ ⟨G.n - 1, by omega⟩ := by
                  change F.φ ⟨F.n - 2, _⟩ = F.φ ⟨(F.n - 1) - 1, _⟩
                  congr 1
                _ ≤ GY'.φ j := hGY'_bound hGn j
            obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u₂₃)
            let oct := Triangulated.someOctahedron rfl hT' hTu₂₃ h₁₃
            let GZ := GY'.appendFactor C oct.triangle oct.mem (Iso.refl _)
              (Iso.refl _) (F.φ jLast) (F.semistable jLast) hφlast_lt
            refine ⟨X, Z, GX, GZ, f' ≫ u₂₃, v₁₃, w₁₃, h₁₃, hGX_gt, ?_, ?_, ?_⟩
            · intro j
              change GZ.φ j ≤ t
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact hGY'_le ⟨j.val, hj⟩
              · exact hlast_le
            · intro _ j
              change F.φ jLast ≤ GZ.φ j
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact (hφlast_lt ⟨j.val, hj⟩).le
              · exact le_rfl
            · intro j
              obtain ⟨iG, hiG⟩ := hGX_contain j
              have hi_lt := iG.isLt
              change iG.val < F.n - 1 at hi_lt
              exact ⟨⟨iG.val, by omega⟩, by
                simp [G, HNFiltration.prefix] at hiG
                exact hiG⟩

/-- Shift every stage and factor of an HN filtration. -/
def HNFiltration.shift (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) : HNFiltration C s.P (E⟦a⟧) where
  n := F.n
  chain := F.chain ⋙ shiftFunctor C a
  triangle := fun i => (Triangle.shiftFunctor C a).obj (F.triangle i)
  triangle_dist := fun i => Triangle.shift_distinguished _ (F.triangle_dist i) a
  triangle_obj₁ := fun i =>
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₁ i))⟩
  triangle_obj₂ := fun i =>
    ⟨(shiftFunctor C a).mapIso (Classical.choice (F.triangle_obj₂ i))⟩
  base_isZero := (shiftFunctor C a).map_isZero F.base_isZero
  top_iso := ⟨(shiftFunctor C a).mapIso (Classical.choice F.top_iso)⟩
  φ := fun i => F.φ i + a
  hφ := by
    intro i j hij
    simpa [add_comm] using add_lt_add_right (F.hφ hij) a
  semistable := fun i => (s.shift_int C (F.φ i) _ a).mp (F.semistable i)

@[simp]
theorem HNFiltration.shift_phiPlus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shift C s a).phiPlus C h = F.phiPlus C h + a := rfl

@[simp]
theorem HNFiltration.shift_phiMinus (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (a : ℤ) (h : 0 < F.n) :
    (F.shift C s a).phiMinus C h = F.phiMinus C h + a := rfl

/-! ### Transporting phase cuts by shifts -/

/-- Shifting an upper phase cut shifts its endpoint by the same integer. -/
theorem Slicing.leProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.leProp C t X) : s.leProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hle⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_le_add_right hle (a : ℝ)

/-- Shifting a strict lower phase cut shifts its endpoint by the same integer. -/
theorem Slicing.gtProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.gtProp C t X) : s.gtProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hgt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_lt_add_right hgt (a : ℝ)

/-- Shifting a strict upper phase cut shifts its endpoint by the same integer. -/
theorem Slicing.ltProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.ltProp C t X) : s.ltProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hlt⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_lt_add_right hlt (a : ℝ)

/-- Shifting a lower phase cut shifts its endpoint by the same integer. -/
theorem Slicing.geProp_shift (s : Slicing C) (t : ℝ) (X : C) (a : ℤ)
    (hX : s.geProp C t X) : s.geProp C (t + a) (X⟦a⟧) := by
  rcases hX with hX | ⟨F, hF, hge⟩
  · exact Or.inl ((shiftFunctor C a).map_isZero hX)
  · refine Or.inr ⟨F.shift C s a, hF, ?_⟩
    simpa using add_le_add_right hge (a : ℝ)

/-! ### Reading phase bounds from filtrations -/

theorem Slicing.leProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, F.φ i ≤ t) (hn : 0 < F.n) :
    s.leProp C t E := Or.inr ⟨F, hn, h ⟨0, hn⟩⟩

theorem Slicing.gtProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, t < F.φ i) (hn : 0 < F.n) :
    s.gtProp C t E := Or.inr ⟨F, hn, h ⟨F.n - 1, by omega⟩⟩

theorem Slicing.ltProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, F.φ i < t) (hn : 0 < F.n) :
    s.ltProp C t E := Or.inr ⟨F, hn, h ⟨0, hn⟩⟩

theorem Slicing.geProp_of_hn (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) (h : ∀ i, t ≤ F.φ i) (hn : 0 < F.n) :
    s.geProp C t E := Or.inr ⟨F, hn, h ⟨F.n - 1, by omega⟩⟩

/-- A semistable object lies below any weak upper phase bound. -/
theorem Slicing.leProp_of_semistable (s : Slicing C) {S : C} {φ t : ℝ}
    (hS : s.P φ S) (h : φ ≤ t) : s.leProp C t S :=
  s.leProp_of_hn C (HNFiltration.single C S φ hS) t
    (fun _ => by simpa [HNFiltration.single] using h) (by change 0 < 1; omega)

/-- A semistable object lies above any strict lower phase bound. -/
theorem Slicing.gtProp_of_semistable (s : Slicing C) {S : C} {φ t : ℝ}
    (hS : s.P φ S) (h : t < φ) : s.gtProp C t S :=
  s.gtProp_of_hn C (HNFiltration.single C S φ hS) t
    (fun _ => by simpa [HNFiltration.single] using h) (by change 0 < 1; omega)

/-- A semistable object lies in the weak lower phase cut at its own phase. -/
theorem Slicing.geProp_of_semistable (s : Slicing C) {S : C} {φ : ℝ}
    (hS : s.P φ S) : s.geProp C φ S :=
  s.geProp_of_hn C (HNFiltration.single C S φ hS) φ
    (fun _ => by simp [HNFiltration.single]) (by change 0 < 1; omega)

/-- Split an HN-filtered interval object at a cutoff, exposing the phase-cut
properties and the inherited strict upper bound needed by deformation HN
recursion. -/
theorem Slicing.exists_split_at_cutoff (s : Slicing C) [IsTriangulated C]
    {a b t : ℝ} {E : C} (F : HNFiltration C s.P E)
    (hF : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.gtProp C t X ∧ s.leProp C t Y ∧
      s.ltProp C b X := by
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, _, hGXorig⟩ :=
    F.exists_split_at_cutoff C t
  have hXgt : s.gtProp C t X := by
    by_cases hn : 0 < GX.n
    · exact s.gtProp_of_hn C GX t hGX hn
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  have hYle : s.leProp C t Y := by
    by_cases hn : 0 < GY.n
    · exact s.leProp_of_hn C GY t hGY hn
    · exact Or.inl (GY.isZero_of_length_zero (by omega))
  have hXlt : s.ltProp C b X := by
    by_cases hn : 0 < GX.n
    · apply s.ltProp_of_hn C GX b _ hn
      intro j
      obtain ⟨i, hi⟩ := hGXorig j
      rw [hi]
      exact (hF i).2
    · exact Or.inl (GX.isZero_of_length_zero (by omega))
  exact ⟨X, Y, f, g, h, hT, hXgt, hYle, hXlt⟩

end CategoryTheory.Triangulated
