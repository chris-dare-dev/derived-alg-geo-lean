/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.CoreConsequences

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniqueness and finiteness of Harder--Narasimhan mass

This file closes the gap between the choice-free mass envelope introduced in
`WeakStabilityCondition/StabilityCondition/Metric/Mass/Basic.lean` and the usual mass of an arbitrary HN filtration.

The categorical input is a head--tail decomposition.  Octahedral induction
turns an HN tower into a distinguished triangle

```
  F₀ ⟶ E ⟶ E_{< φ₀} ⟶ F₀[1]
```

whose third object carries the tail HN filtration.  For two filtrations with
nonzero first factors, the first phases agree.  The t-structure induced by the
phase-shifted slicing then identifies the two head--tail triangles.  Induction
on the total filtration length, deleting zero first factors when necessary,
proves equality of all finite mass sums.

The induction never consults the compatibility ray of the stability condition:
it runs on the slicing and on an additive charge alone.  It is therefore stated
for a bare carrier `(s : Slicing C, Z : K₀ C →+ ℂ)` — `classCharge`,
`HNFiltration.classMass`, `Slicing.classMass` — and the `WithClassMap` forms at
the end of the file are one-line restatements at `(σ.slicing, σ.Z.comp v)`.  This is
what lets the weak stability conditions of §14, whose closed compatibility ray
cannot inhabit `WithClassMap`, reuse the whole development
(`WeakStabilityCondition/StabilityCondition/WeakCompatibility/Mass.lean`).
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- An additive charge on the class lattice, evaluated on the `K₀` class of an
object.  This is `PreStabilityCondition.WithClassMap.charge` with the charge
decoupled from any prestability structure, so the mass-uniqueness induction in
this file can serve any carrier providing a slicing and a charge — in
particular the weak stability conditions of §14, whose closed compatibility
ray cannot inhabit `WithClassMap`. -/
abbrev classCharge (Z : K₀ C →+ ℂ) (E : C) : ℂ := Z (K₀.of C E)

omit [IsTriangulated C] in
private lemma classCharge_isZero (Z : K₀ C →+ ℂ) {E : C} (hE : IsZero E) :
    classCharge Z E = 0 := by
  simp [classCharge, K₀.of_isZero C hE]

/-- The finite mass sum of one HN filtration, for a bare additive charge.
`HNFiltration.mass` is definitionally this at `Z = σ.Z.comp v`, because `charge` is an
abbreviation for `Z ∘ classOf`. -/
def HNFiltration.classMass (Z : K₀ C →+ ℂ) {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) : ℝ≥0∞ :=
  ∑ i : Fin F.n, ENNReal.ofReal ‖classCharge Z (F.factor i)‖

/-- The choice-free mass envelope of an object, for a slicing and a bare
additive charge.  `stabilityMass` is definitionally this at `(σ.slicing, σ.Z.comp v)`. -/
def Slicing.classMass (s : Slicing C) (Z : K₀ C →+ ℂ) (E : C) : ℝ≥0∞ :=
  ⨆ F : HNFiltration C s.P E, F.classMass Z

private def factorMass (Z : K₀ C →+ ℂ) (E : C) : ℝ≥0∞ :=
  ENNReal.ofReal ‖classCharge Z E‖

omit [IsTriangulated C] in
private lemma factorMass_eq_zero_of_isZero (Z : K₀ C →+ ℂ) {E : C} (hE : IsZero E) :
    factorMass Z E = 0 := by
  simp [factorMass, classCharge_isZero Z hE]

omit [IsTriangulated C] in
private lemma HNFiltration.classMass_dropFirst
    {s : Slicing C} (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hn : 1 < F.n)
    (hzero : IsZero (F.factor ⟨0, by lia⟩)) :
    (F.dropFirst C hn hzero).classMass Z = F.classMass Z := by
  unfold HNFiltration.classMass
  have hhead : ENNReal.ofReal ‖classCharge Z (F.factor ⟨0, by lia⟩)‖ = 0 :=
    factorMass_eq_zero_of_isZero Z hzero
  let f : Fin F.n → ℝ≥0∞ := fun i ↦ ENNReal.ofReal ‖classCharge Z (F.factor i)‖
  calc
    ∑ i : Fin (F.n - 1),
        ENNReal.ofReal ‖classCharge Z ((F.dropFirst C hn hzero).factor i)‖ =
        ∑ i ∈ Finset.univ.erase (⟨0, by lia⟩ : Fin F.n), f i := by
      apply Finset.sum_bij (fun i _ ↦ (⟨i.val + 1, by lia⟩ : Fin F.n))
      · intro i _
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact Fin.ne_of_gt (by simp)
      · intro i _ j _ hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)
      · intro j hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
        let i : Fin (F.n - 1) := ⟨j.val - 1, by
          have hj0 : 0 < j.val := Nat.pos_of_ne_zero (by
            intro h
            apply hj
            exact Fin.ext h)
          lia⟩
        refine ⟨i, Finset.mem_univ _, ?_⟩
        exact Fin.ext (by
          have hj0 : 0 < j.val := Nat.pos_of_ne_zero (by
            intro h
            apply hj
            exact Fin.ext h)
          simp only [i]
          lia)
      · intro i _
        rfl
    _ = ∑ i : Fin F.n, f i := by
      rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ ⟨0, by lia⟩)]
      change _ = f ⟨0, by lia⟩ + _
      rw [show f ⟨0, by lia⟩ = 0 from hhead, zero_add]

omit [IsTriangulated C] in
private lemma factorMass_congr (Z : K₀ C →+ ℂ) {E E' : C} (e : E ≅ E') :
    factorMass Z E = factorMass Z E' := by
  simp only [factorMass]
  rw [show classCharge Z E = classCharge Z E' from congrArg Z (K₀.of_iso C e)]

omit [IsTriangulated C] in
private lemma HNFiltration.classMass_appendFactor
    {s : Slicing C} (Z : K₀ C →+ ℂ) {Y X : C}
    (G : HNFiltration C s.P Y)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ Y) (eT₂ : T.obj₂ ≅ X)
    (ψ : ℝ) (hψ : s.P ψ T.obj₃)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    (G.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).classMass Z =
      G.classMass Z + factorMass Z T.obj₃ := by
  unfold HNFiltration.classMass
  change (∑ i : Fin (G.n + 1),
      ENNReal.ofReal ‖classCharge Z ((G.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).factor i)‖) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change ENNReal.ofReal ‖classCharge Z
      ((if h : i.val < G.n then G.triangle ⟨i.val, h⟩ else T).obj₃)‖ = _
    simp only [i.isLt, dite_true]
    congr 4
  · change ENNReal.ofReal ‖classCharge Z
      ((if h : (Fin.last G.n).val < G.n then
        G.triangle ⟨(Fin.last G.n).val, h⟩ else T).obj₃)‖ = _
    simp [factorMass, Fin.val_last]

omit [IsTriangulated C] in
private lemma HNFiltration.classMass_prefix_last
    {s : Slicing C} (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hn : 1 < F.n) :
    (F.prefix C (F.n - 1) (by lia)).classMass Z +
        factorMass Z (F.factor ⟨F.n - 1, by lia⟩) = F.classMass Z := by
  unfold HNFiltration.classMass
  let f : Fin F.n → ℝ≥0∞ := fun i ↦ ENNReal.ofReal ‖classCharge Z (F.factor i)‖
  calc
    (∑ i : Fin (F.n - 1),
        ENNReal.ofReal ‖classCharge Z
          ((F.prefix C (F.n - 1) (by lia)).factor i)‖) +
        factorMass Z (F.factor ⟨F.n - 1, by lia⟩) =
        (∑ i ∈ Finset.univ.erase (⟨F.n - 1, by lia⟩ : Fin F.n), f i) +
          f ⟨F.n - 1, by lia⟩ := by
      congr 1
      · apply Finset.sum_bij (fun i _ ↦ (⟨i.val, by lia⟩ : Fin F.n))
        · intro i _
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by lia))
        · intro i _ j _ hij
          exact Fin.ext (by simpa using congrArg Fin.val hij)
        · intro j hj
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
          have hjlt : j.val < F.n - 1 := by
            have hjle : j.val ≤ F.n - 1 := by lia
            exact lt_of_le_of_ne hjle (by
              intro h
              apply hj
              exact Fin.ext h)
          exact ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro i _
          rfl
    _ = ∑ i : Fin F.n, f i :=
      Finset.sum_erase_add Finset.univ f
        (Finset.mem_univ (⟨F.n - 1, by lia⟩ : Fin F.n))

/-- Split an HN filtration into its highest-phase factor and an HN-filtered
tail.  The mass and the phase list split in the same operation. -/
private theorem HNFiltration.exists_headTail
    {s : Slicing C} (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C s.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      F.classMass Z = factorMass Z (F.factor ⟨0, hn⟩) + G.classMass Z ∧
      G.n = F.n - 1 ∧
      ∀ j : Fin G.n, ∃ i : Fin F.n,
        i.val = j.val + 1 ∧ G.φ j = F.φ i := by
  suffices hmain : ∀ (m : ℕ) {E : C} (F : HNFiltration C s.P E),
      F.n ≤ m → ∀ hn : 0 < F.n,
      ∃ (Y : C) (G : HNFiltration C s.P Y)
        (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
        (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        F.classMass Z = factorMass Z (F.factor ⟨0, hn⟩) + G.classMass Z ∧
        G.n = F.n - 1 ∧
        ∀ j : Fin G.n, ∃ i : Fin F.n,
          i.val = j.val + 1 ∧ G.φ j = F.φ i by
    exact hmain F.n F le_rfl hn
  intro m
  induction m with
  | zero =>
      intro E F hFm hn
      omega
  | succ m ih =>
      intro E F hFm hn
      by_cases hn1 : F.n = 1
      · let i0 : Fin F.n := ⟨0, hn⟩
        let T := F.triangle i0
        let e₁ := Classical.choice (F.triangle_obj₁ i0)
        let e₂ := Classical.choice (F.triangle_obj₂ i0)
        have hT₁ : IsZero T.obj₁ := by
          exact F.base_isZero.of_iso e₁
        haveI : IsIso T.mor₂ :=
          (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist i0)).mp hT₁
        have hchain1 : F.chain.obj' 1 (by lia) = F.chain.right := by
          congr 1
          omega
        let e₂E : T.obj₂ ≅ E :=
          e₂.trans ((eqToIso hchain1).trans (Classical.choice F.top_iso))
        let e : F.factor i0 ≅ E := (asIso T.mor₂).symm.trans e₂E
        let G := HNFiltration.zero (P := s.P) C (0 : C) (isZero_zero C)
        refine ⟨0, G, e.hom, 0, 0, ?_, ?_, ?_, ?_⟩
        · apply isomorphic_distinguished _ (contractible_distinguished (F.factor i0))
          exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
            (by simp [contractibleTriangle])
            (by simp) (by simp)
        · unfold HNFiltration.classMass
          change (∑ x : Fin F.n, ENNReal.ofReal ‖classCharge Z (F.factor x)‖) =
            ENNReal.ofReal ‖classCharge Z (F.factor ⟨0, hn⟩)‖ + 0
          rw [add_zero]
          apply Finset.sum_eq_single i0
          · intro j _ hji
            exact absurd (Fin.ext (by have := j.isLt; omega)) hji
          · simp
        · change 0 = F.n - 1
          omega
        · intro j
          exact Fin.elim0 j
      · have hn2 : 2 ≤ F.n := by omega
        let A := F.chain.obj' (F.n - 1) (by lia)
        let P := F.prefix C (F.n - 1) (by lia)
        have hPn : 0 < P.n := by
          change 0 < F.n - 1
          omega
        obtain ⟨Y', G', f', g', h', hT', hmass', hnG', hφ'⟩ :=
          ih P (by change F.n - 1 ≤ m; omega) hPn
        let ilast : Fin F.n := ⟨F.n - 1, by lia⟩
        let T := F.triangle ilast
        let e₁ := Classical.choice (F.triangle_obj₁ ilast)
        let e₂ := Classical.choice (F.triangle_obj₂ ilast)
        let eE := Classical.choice F.top_iso
        have hchainN : F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
          congr 1
          omega
        let e₂E : T.obj₂ ≅ E := e₂.trans ((eqToIso hchainN).trans eE)
        let u : A ⟶ E := e₁.inv ≫ T.mor₁ ≫ e₂E.hom
        let TAE : Triangle C := Triangle.mk u (e₂E.inv ≫ T.mor₂)
          (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')
        have hTAE : TAE ∈ distTriang C := by
          apply isomorphic_distinguished _ (F.triangle_dist ilast)
          exact Triangle.isoMk TAE T e₁.symm e₂E.symm (Iso.refl _)
            (by simp [TAE, u, e₂E]) (by simp [TAE, e₂E]) (by simp [TAE])
        obtain ⟨X₃, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u)
        let oct := Triangulated.someOctahedron rfl hT' hTAE h₁₃
        have hlast_lt : ∀ j : Fin G'.n, F.φ ilast < G'.φ j := by
          intro j
          obtain ⟨i, hi, hphase⟩ := hφ' j
          rw [hphase]
          exact F.hφ (Fin.mk_lt_mk.mpr (by
            change (ilast : Fin F.n).val > i.val
            simp only [ilast]
            have hiP := i.isLt
            change i.val < F.n - 1 at hiP
            omega))
        let GZ := G'.appendFactor C oct.triangle oct.mem (Iso.refl _)
          (Iso.refl _) (F.φ ilast) (F.semistable ilast) hlast_lt
        have hGZmass : GZ.classMass Z = G'.classMass Z + factorMass Z T.obj₃ :=
          G'.classMass_appendFactor Z oct.triangle oct.mem (Iso.refl _) (Iso.refl _)
            (F.φ ilast) (F.semistable ilast) hlast_lt
        have hGZn : GZ.n = F.n - 1 := by
          change G'.n + 1 = F.n - 1
          rw [hnG']
          change (F.n - 1 - 1) + 1 = F.n - 1
          omega
        have hphead : factorMass Z (P.factor ⟨0, hPn⟩) =
            factorMass Z (F.factor ⟨0, hn⟩) := by
          change ENNReal.ofReal ‖classCharge Z (F.triangle ⟨0, by lia⟩).obj₃‖ =
            ENNReal.ofReal ‖classCharge Z (F.triangle ⟨0, hn⟩).obj₃‖
          congr 4
        have hplast : factorMass Z (F.factor ilast) = factorMass Z T.obj₃ := rfl
        refine ⟨X₃, GZ, f' ≫ u, v₁₃, w₁₃, h₁₃, ?_, ?_, ?_⟩
        · calc
            F.classMass Z = P.classMass Z + factorMass Z (F.factor ilast) :=
              (F.classMass_prefix_last Z hn2).symm
            _ = (factorMass Z (P.factor ⟨0, hPn⟩) + G'.classMass Z) +
                factorMass Z (F.factor ilast) := by
              rw [show CategoryTheory.Triangulated.HNFiltration.classMass Z P =
                  factorMass Z (P.factor ⟨0, hPn⟩) + G'.classMass Z by
                simpa using hmass']
            _ = factorMass Z (F.factor ⟨0, hn⟩) +
                (G'.classMass Z + factorMass Z T.obj₃) := by
                  rw [hphead]
                  rw [hplast]
                  rw [add_assoc]
            _ = factorMass Z (F.factor ⟨0, hn⟩) + GZ.classMass Z := by
                  rw [hGZmass]
        · exact hGZn
        · intro j
          change ∃ i : Fin F.n, i.val = j.val + 1 ∧
            (if h : j.val < G'.n then G'.φ ⟨j.val, h⟩ else F.φ ilast) = F.φ i
          split_ifs with hj
          · obtain ⟨i, hi, hphase⟩ := hφ' ⟨j.val, hj⟩
            let iF : Fin F.n := ⟨i.val, by
              have hiP := i.isLt
              change i.val < F.n - 1 at hiP
              omega⟩
            refine ⟨iF, ?_, ?_⟩
            · simpa [iF] using hi
            · calc
                G'.φ ⟨j.val, hj⟩ = P.φ i := hphase
                _ = F.φ iF := by rfl
          · have hjlast : j.val = G'.n := by
              have hjbound := j.isLt
              change j.val < G'.n + 1 at hjbound
              omega
            refine ⟨ilast, ?_, rfl⟩
            simp only [ilast]
            rw [hjlast]
            have hG'n : G'.n = F.n - 2 := by
              rw [hnG']
              rfl
            rw [hG'n]
            omega

omit [IsTriangulated C] in
/-- Every HN filtration of a zero object has zero mass.  This also rules out
spurious positive mass coming from a nontrivial tower of a zero object. -/
theorem HNFiltration.classMass_eq_zero_of_isZero
    {s : Slicing C} (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hE : IsZero E) :
    F.classMass Z = 0 := by
  suffices hmain : ∀ (m : ℕ) {E : C}
      (F : HNFiltration C s.P E), F.n ≤ m → IsZero E → F.classMass Z = 0 by
    exact hmain F.n F le_rfl hE
  intro m
  induction m with
  | zero =>
      intro E F hFm _
      have hn : F.n = 0 := by omega
      unfold HNFiltration.classMass
      apply Finset.sum_eq_zero
      intro i _
      exact absurd i.isLt (by omega)
  | succ m ih =>
      intro E F hFm hE
      by_cases hn0 : F.n = 0
      · unfold HNFiltration.classMass
        apply Finset.sum_eq_zero
        intro i _
        exact absurd i.isLt (by omega)
      have hn : 0 < F.n := Nat.pos_of_ne_zero hn0
      have hhead : IsZero (F.factor ⟨0, hn⟩) :=
        F.isZero_factor_zero_of_hom_eq_zero C s hn fun f ↦ hE.eq_of_tgt f 0
      by_cases hn1 : F.n = 1
      · unfold HNFiltration.classMass
        let i0 : Fin F.n := ⟨0, hn⟩
        calc
          (∑ i : Fin F.n, ENNReal.ofReal ‖classCharge Z (F.factor i)‖) =
              ENNReal.ofReal ‖classCharge Z (F.factor i0)‖ := by
            apply Finset.sum_eq_single i0
            · intro j _ hji
              exact absurd (Fin.ext (by have := j.isLt; omega)) hji
            · simp
          _ = 0 := factorMass_eq_zero_of_isZero Z hhead
      · have hn2 : 1 < F.n := by omega
        let G := F.dropFirst C hn2 hhead
        rw [← F.classMass_dropFirst Z hn2 hhead]
        exact ih G (by change F.n - 1 ≤ m; omega) hE

/-- **HN mass is independent of the chosen HN filtration.** -/
theorem HNFiltration.classMass_eq_classMass
    {s : Slicing C} (Z : K₀ C →+ ℂ) {E : C}
    (F G : HNFiltration C s.P E) : F.classMass Z = G.classMass Z := by
  suffices hmain : ∀ (m : ℕ) {E : C}
      (F G : HNFiltration C s.P E), F.n + G.n ≤ m →
      F.classMass Z = G.classMass Z by
    exact hmain (F.n + G.n) F G le_rfl
  intro m
  induction m with
  | zero =>
      intro E F G hlen
      have hE : IsZero E := F.isZero_of_length_zero (by omega)
      rw [F.classMass_eq_zero_of_isZero Z hE, G.classMass_eq_zero_of_isZero Z hE]
  | succ m ih =>
      intro E F G hlen
      by_cases hE : IsZero E
      · rw [F.classMass_eq_zero_of_isZero Z hE, G.classMass_eq_zero_of_isZero Z hE]
      have hnF : 0 < F.n := F.n_pos C hE
      have hnG : 0 < G.n := G.n_pos C hE
      by_cases hzF : IsZero (F.factor ⟨0, hnF⟩)
      · have hnF2 : 1 < F.n := by
          by_contra h
          have hnF1 : F.n = 1 := by omega
          obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hE
          have hi0 : i = ⟨0, hnF⟩ := Fin.ext (by have := i.isLt; omega)
          exact hi (hi0 ▸ hzF)
        let F' := F.dropFirst C hnF2 hzF
        rw [← F.classMass_dropFirst Z hnF2 hzF]
        exact ih F' G (by change F.n - 1 + G.n ≤ m; omega)
      by_cases hzG : IsZero (G.factor ⟨0, hnG⟩)
      · have hnG2 : 1 < G.n := by
          by_contra h
          have hnG1 : G.n = 1 := by omega
          obtain ⟨i, hi⟩ := G.exists_nonzero_factor C hE
          have hi0 : i = ⟨0, hnG⟩ := Fin.ext (by have := i.isLt; omega)
          exact hi (hi0 ▸ hzG)
        let G' := G.dropFirst C hnG2 hzG
        rw [← G.classMass_dropFirst Z hnG2 hzG]
        exact ih F G' (by change F.n + (G.n - 1) ≤ m; omega)
      have hphase : F.φ ⟨0, hnF⟩ = G.φ ⟨0, hnG⟩ :=
        CategoryTheory.Triangulated.HNFiltration.phiPlus_eq_of_firstFactors_nonzero
          C s F G hnF hnG hzF hzG
      obtain ⟨YF, TF, fF, gF, dF, htriF, hmassF, hnTF, hφTF⟩ :=
        F.exists_headTail Z hnF
      obtain ⟨YG, TG, fG, gG, dG, htriG, hmassG, hnTG, hφTG⟩ :=
        G.exists_headTail Z hnG
      let φ := F.φ ⟨0, hnF⟩
      have hheadF : s.geProp C φ (F.factor ⟨0, hnF⟩) := by
        apply s.geProp_of_hn C
          (HNFiltration.single C (F.factor ⟨0, hnF⟩) φ (F.semistable ⟨0, hnF⟩)) φ
        · intro j
          exact le_rfl
        · change 0 < 1
          omega
      have hheadG : s.geProp C φ (G.factor ⟨0, hnG⟩) := by
        have hs : s.P φ (G.factor ⟨0, hnG⟩) := by
          dsimp only [φ]
          rw [hphase]
          exact G.semistable ⟨0, hnG⟩
        apply s.geProp_of_hn C
          (HNFiltration.single C (G.factor ⟨0, hnG⟩) φ hs) φ
        · intro j
          exact le_rfl
        · change 0 < 1
          omega
      have htailF : s.ltProp C φ YF := by
        by_cases hzero : TF.n = 0
        · exact Or.inl (TF.isZero_of_length_zero hzero)
        · apply s.ltProp_of_hn C TF φ
          · intro j
            obtain ⟨i, hi, hφi⟩ := hφTF j
            rw [hφi]
            exact F.hφ (Fin.mk_lt_mk.mpr (by omega))
          · exact Nat.pos_of_ne_zero hzero
      have htailG : s.ltProp C φ YG := by
        by_cases hzero : TG.n = 0
        · exact Or.inl (TG.isZero_of_length_zero hzero)
        · apply s.ltProp_of_hn C TG φ
          · intro j
            obtain ⟨i, hi, hφi⟩ := hφTG j
            rw [hφi]
            calc
              G.φ i < G.φ ⟨0, hnG⟩ := G.hφ (Fin.mk_lt_mk.mpr (by omega))
              _ = φ := hphase.symm
          · exact Nat.pos_of_ne_zero hzero
      let sφ := s.phaseShift C φ
      let t := sφ.toDualTStructure C
      have hheadFLE : t.IsLE (F.factor ⟨0, hnF⟩) 0 := by
        have hs : sφ.geProp C 0 (F.factor ⟨0, hnF⟩) :=
          (s.phaseShift_geProp_zero C φ _).mpr hheadF
        refine ⟨?_⟩
        dsimp only [t, CategoryTheory.Triangulated.Slicing.toDualTStructure]
        simpa only [Int.cast_zero, neg_zero] using hs
      have hheadGLE : t.IsLE (G.factor ⟨0, hnG⟩) 0 := by
        have hs : sφ.geProp C 0 (G.factor ⟨0, hnG⟩) :=
          (s.phaseShift_geProp_zero C φ _).mpr hheadG
        refine ⟨?_⟩
        dsimp only [t, CategoryTheory.Triangulated.Slicing.toDualTStructure]
        simpa only [Int.cast_zero, neg_zero] using hs
      have htailFGE : t.IsGE YF 1 := by
        have hs : sφ.ltProp C 0 YF :=
          (s.phaseShift_ltProp_zero C φ _).mpr htailF
        refine ⟨?_⟩
        dsimp only [t, CategoryTheory.Triangulated.Slicing.toDualTStructure]
        simpa only [Int.cast_one, sub_self] using hs
      have htailGGE : t.IsGE YG 1 := by
        have hs : sφ.ltProp C 0 YG :=
          (s.phaseShift_ltProp_zero C φ _).mpr htailG
        refine ⟨?_⟩
        dsimp only [t, CategoryTheory.Triangulated.Slicing.toDualTStructure]
        simpa only [Int.cast_one, sub_self] using hs
      obtain ⟨eT, _⟩ := t.triangle_iso_exists htriF htriG (Iso.refl E)
        0 1 hheadFLE htailFGE hheadGLE htailGGE
      let eHead : F.factor ⟨0, hnF⟩ ≅ G.factor ⟨0, hnG⟩ :=
        { hom := eT.hom.hom₁
          inv := eT.inv.hom₁
          hom_inv_id := eT.hom_inv_id_triangle_hom₁
          inv_hom_id := eT.inv_hom_id_triangle_hom₁ }
      let eTail : YF ≅ YG :=
        { hom := eT.hom.hom₃
          inv := eT.inv.hom₃
          hom_inv_id := eT.hom_inv_id_triangle_hom₃
          inv_hom_id := eT.inv_hom_id_triangle_hom₃ }
      have hheadMass : factorMass Z (F.factor ⟨0, hnF⟩) =
          factorMass Z (G.factor ⟨0, hnG⟩) :=
        factorMass_congr Z eHead
      have htailMass : TF.classMass Z = TG.classMass Z := by
        have hrec := ih
          (CategoryTheory.Triangulated.HNFiltration.ofIso C TF eTail) TG (by
          change TF.n + TG.n ≤ m
          rw [hnTF, hnTG]
          omega)
        exact hrec
      calc
        F.classMass Z = factorMass Z (F.factor ⟨0, hnF⟩) + TF.classMass Z := hmassF
        _ = factorMass Z (G.factor ⟨0, hnG⟩) + TG.classMass Z := by
          rw [hheadMass, htailMass]
        _ = G.classMass Z := hmassG.symm

/-- The choice-free mass envelope is the mass sum of every HN filtration. -/
theorem Slicing.classMass_eq_classMass
    (s : Slicing C) (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) : s.classMass Z E = F.classMass Z := by
  apply le_antisymm
  · refine iSup_le fun G ↦ ?_
    exact le_of_eq (G.classMass_eq_classMass Z F)
  · exact le_iSup (fun G : HNFiltration C s.P E ↦ G.classMass Z) F

/-- The ordinary HN mass is always finite. -/
theorem Slicing.classMass_ne_top
    (s : Slicing C) (Z : K₀ C →+ ℂ) (E : C) :
    s.classMass Z E ≠ ⊤ := by
  obtain ⟨F⟩ := s.hn_exists E
  rw [Slicing.classMass_eq_classMass s Z F]
  unfold HNFiltration.classMass
  rw [ENNReal.sum_ne_top]
  intro i _
  exact ENNReal.ofReal_ne_top

theorem Slicing.classMass_lt_top
    (s : Slicing C) (Z : K₀ C →+ ℂ) (E : C) :
    s.classMass Z E < ⊤ :=
  (lt_top_iff_ne_top).2 (Slicing.classMass_ne_top s Z E)

/-- Real-valued form of the mass identification: this is the literal finite
sum of the norms of the HN-factor charges. -/
theorem Slicing.classMass_toReal_eq_sum
    (s : Slicing C) (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) :
    (s.classMass Z E).toReal =
      ∑ i : Fin F.n, ‖classCharge Z (F.factor i)‖ := by
  rw [Slicing.classMass_eq_classMass s Z F]
  unfold HNFiltration.classMass
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.toReal_ofReal (norm_nonneg _)
  · intro i _
    exact ENNReal.ofReal_ne_top
/-- A semistable object's mass is the norm of its charge, in `ℝ≥0∞`.

The `toReal` form is `stabilityMass_toReal_eq_norm_charge`; this is the
un-truncated statement, which is what an additive splitting argument needs. -/
theorem Slicing.classMass_eq_ofReal_norm_classCharge
    (s : Slicing C) (Z : K₀ C →+ ℂ) {E : C} {φ : ℝ}
    (hP : s.P φ E) :
    s.classMass Z E = ENNReal.ofReal ‖classCharge Z E‖ := by
  rw [Slicing.classMass_eq_classMass s Z (HNFiltration.single C E φ hP)]
  change (∑ _ : Fin 1, ENNReal.ofReal ‖classCharge Z E‖) = _
  simp

/-- Public head/tail split of the mass, stated entirely in `stabilityMass`.

`exists_headTail` is private and phrased with the private `factorMass`; this is
the form downstream files can use. The head is the top HN factor, the tail is
HN-filtered with one fewer factor, and the mass splits additively across the
distinguished triangle joining them. -/
theorem Slicing.exists_headTail_classMass
    (s : Slicing C) (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C s.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.classMass Z E =
        s.classMass Z (F.factor ⟨0, hn⟩) + s.classMass Z Y ∧
      G.n = F.n - 1 := by
  obtain ⟨Y, G, f, g, h, hT, hmass, hGn, _⟩ := F.exists_headTail Z hn
  refine ⟨Y, G, f, g, h, hT, ?_, hGn⟩
  rw [Slicing.classMass_eq_classMass s Z F, hmass, Slicing.classMass_eq_classMass s Z G,
    Slicing.classMass_eq_ofReal_norm_classCharge s Z (F.semistable ⟨0, hn⟩)]
  rfl

/-- Split off the highest-phase HN factor, preserving both the mass identity and
the indexing of every phase in the tail.

This is the public form used by inductive mass arguments: unlike
`Slicing.exists_headTail_classMass`, it retains the phase correspondence needed to
re-establish strict HN separation after an octahedral step. -/
theorem HNFiltration.exists_headTail_classMass
    (s : Slicing C) (Z : K₀ C →+ ℂ) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C s.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (s.classMass Z E).toReal =
        ‖classCharge Z (F.factor ⟨0, hn⟩)‖ + (s.classMass Z Y).toReal ∧
      G.n = F.n - 1 ∧
      ∀ j : Fin G.n, ∃ i : Fin F.n,
        i.val = j.val + 1 ∧ G.φ j = F.φ i := by
  obtain ⟨Y, G, f, g, h, hT, hmass, hGn, hφ⟩ := F.exists_headTail Z hn
  refine ⟨Y, G, f, g, h, hT, ?_, hGn, hφ⟩
  have hsplit : s.classMass Z E =
      s.classMass Z (F.factor ⟨0, hn⟩) + s.classMass Z Y := by
    rw [Slicing.classMass_eq_classMass s Z F, hmass, Slicing.classMass_eq_classMass s Z G,
      Slicing.classMass_eq_ofReal_norm_classCharge s Z (F.semistable ⟨0, hn⟩)]
    rfl
  rw [hsplit, ENNReal.toReal_add]
  · simp [Slicing.classMass_eq_ofReal_norm_classCharge s Z (F.semistable ⟨0, hn⟩)]
  · exact Slicing.classMass_ne_top s Z _
  · exact Slicing.classMass_ne_top s Z _
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ## The `WithClassMap` forms

Everything above is proved for a bare slicing and additive charge; the forms
below restate the public results for `StabilityCondition.WithClassMap`, which
is how the rest of the metric track consumes them.  `charge` is an
abbreviation for `Z ∘ classOf`, so each proof is the general theorem applied
at `(σ.slicing, σ.Z.comp v)`. -/

omit [IsTriangulated C] in
/-- Every HN filtration of a zero object has zero mass.  This also rules out
spurious positive mass coming from a nontrivial tower of a zero object. -/
theorem HNFiltration.mass_eq_zero_of_isZero
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hE : IsZero E) :
    F.mass σ = 0 :=
  F.classMass_eq_zero_of_isZero (σ.Z.comp v) hE

/-- **HN mass is independent of the chosen HN filtration.** -/
theorem HNFiltration.mass_eq_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F G : HNFiltration C σ.slicing.P E) : F.mass σ = G.mass σ :=
  F.classMass_eq_classMass (σ.Z.comp v) G

/-- The choice-free mass envelope is the mass sum of every HN filtration. -/
theorem stabilityMass_eq_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) : stabilityMass σ E = F.mass σ :=
  Slicing.classMass_eq_classMass σ.slicing (σ.Z.comp v) F

/-- The ordinary HN mass is always finite. -/
theorem stabilityMass_ne_top
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E ≠ ⊤ :=
  Slicing.classMass_ne_top σ.slicing (σ.Z.comp v) E

theorem stabilityMass_lt_top
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E < ⊤ :=
  Slicing.classMass_lt_top σ.slicing (σ.Z.comp v) E

/-- Real-valued form of the mass identification: this is the literal finite
sum of the norms of the HN-factor charges. -/
theorem stabilityMass_toReal_eq_sum
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (stabilityMass σ E).toReal =
      ∑ i : Fin F.n, ‖σ.charge (F.factor i)‖ :=
  Slicing.classMass_toReal_eq_sum σ.slicing (σ.Z.comp v) F

/-- A semistable object's mass is the norm of its charge, in `ℝ≥0∞`.

The `toReal` form is `stabilityMass_toReal_eq_norm_charge`; this is the
un-truncated statement, which is what an additive splitting argument needs. -/
theorem stabilityMass_eq_ofReal_norm_charge
    (σ : StabilityCondition.WithClassMap C v) {E : C} {φ : ℝ}
    (hP : σ.slicing.P φ E) :
    stabilityMass σ E = ENNReal.ofReal ‖σ.charge E‖ :=
  Slicing.classMass_eq_ofReal_norm_classCharge σ.slicing (σ.Z.comp v) hP

/-- Public head/tail split of the mass, stated entirely in `stabilityMass`.

`exists_headTail` is private and phrased with the private `factorMass`; this is
the form downstream files can use. The head is the top HN factor, the tail is
HN-filtered with one fewer factor, and the mass splits additively across the
distinguished triangle joining them. -/
theorem exists_headTail_stabilityMass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C σ.slicing.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      stabilityMass σ E =
        stabilityMass σ (F.factor ⟨0, hn⟩) + stabilityMass σ Y ∧
      G.n = F.n - 1 :=
  Slicing.exists_headTail_classMass σ.slicing (σ.Z.comp v) F hn

/-- Split off the highest-phase HN factor, preserving both the mass identity and
the indexing of every phase in the tail.

This is the public form used by inductive mass arguments: unlike
`exists_headTail_stabilityMass`, it retains the phase correspondence needed to
re-establish strict HN separation after an octahedral step. -/
theorem HNFiltration.exists_headTail_mass
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C σ.slicing.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      (stabilityMass σ E).toReal =
        ‖σ.charge (F.factor ⟨0, hn⟩)‖ + (stabilityMass σ Y).toReal ∧
      G.n = F.n - 1 ∧
      ∀ j : Fin G.n, ∃ i : Fin F.n,
        i.val = j.val + 1 ∧ G.φ j = F.φ i :=
  HNFiltration.exists_headTail_classMass σ.slicing (σ.Z.comp v) F hn

/-- Mass vanishes exactly on zero objects. -/
@[simp]
theorem stabilityMass_eq_zero_iff
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ E = 0 ↔ IsZero E := by
  constructor
  · intro hmass
    by_contra hE
    exact (ne_of_gt (stabilityMass_pos σ hE)) hmass
  · intro hE
    obtain ⟨F⟩ := σ.slicing.hn_exists E
    rw [stabilityMass_eq_mass σ F,
      CategoryTheory.Triangulated.HNFiltration.mass_eq_zero_of_isZero σ F hE]

/-- The real-valued mass coordinate is strictly positive on nonzero objects. -/
theorem stabilityMass_toReal_pos
    (σ : StabilityCondition.WithClassMap C v) {E : C} (hE : ¬IsZero E) :
    0 < (stabilityMass σ E).toReal :=
  ENNReal.toReal_pos (ne_of_gt (stabilityMass_pos σ hE)) (stabilityMass_ne_top σ E)

end

end CategoryTheory.Triangulated
