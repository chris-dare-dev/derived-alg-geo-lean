/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Adjacent layers of a column-filtered total complex

For a cohomological bicomplex of abelian groups, two consecutive stupid column truncations form a
degreewise split short exact sequence. Their quotient is the newly added column. After totalizing,
the mapping cone of the inclusion is quasi-isomorphic to that column shifted by its horizontal
degree. This identifies the initial page of the column-filtration spectral sequence with vertical
column homology.
-/

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe w

variable (K : HomologicalComplex₂ AddCommGrpCat.{w}
  (ComplexShape.up ℤ) (ComplexShape.up ℤ))

noncomputable def truncatedBicomplex (p : ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE p)

noncomputable def singleColumnBicomplex (p : ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) p).obj (K.X p)

noncomputable def singleColumnXIso (p i : ℤ) (hi : i = p) :
    (singleColumnBicomplex K p).X i ≅ K.X p := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (K.X p)

@[reassoc (attr := simp)]
lemma singleColumnXIso_hom_inv_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).hom.f j ≫
      (singleColumnXIso K p i hi').inv.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
lemma singleColumnXIso_inv_hom_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).inv.f j ≫
      (singleColumnXIso K p i hi').hom.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

noncomputable def adjacentColumnInclusion (p : ℤ) :
    truncatedBicomplex K (p + 1) ⟶ truncatedBicomplex K p :=
  HomologicalComplex.stupidTruncGEMap K p (p + 1) (by omega)

noncomputable def adjacentColumnProjection (p : ℤ) :
    truncatedBicomplex K p ⟶ singleColumnBicomplex K p where
  f i := if hi : i = p then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
        (i := 0) (by subst i; simp [ComplexShape.embeddingUpIntGE])).hom ≫
          (K.XIsoOfEq hi).hom ≫
          (singleColumnXIso K p i hi).inv
    else 0
  comm' i j hij := by
    by_cases hj : j = p
    · have hip : i < p := by
        have hij' : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        omega
      subst j
      apply IsZero.eq_of_src
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
    · rw [dif_neg hj]
      simp [singleColumnBicomplex]
      symm
      apply comp_zero

noncomputable def adjacentColumnBicomplexShortComplex (p : ℤ) :
    ShortComplex (HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :=
  ShortComplex.mk
    (adjacentColumnInclusion K p)
    (adjacentColumnProjection K p) (by
      apply HomologicalComplex.Hom.ext
      funext i
      rw [HomologicalComplex.comp_f]
      by_cases hi : p + 1 ≤ i
      · have hip : i ≠ p := by omega
        dsimp [adjacentColumnProjection]
        rw [dif_neg hip]
        apply comp_zero
      · apply IsZero.eq_of_src
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega)

noncomputable instance totalFunctor_additive :
    (totalFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).Additive where
  map_add := by
    intro X Y f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro i j h
    dsimp [totalFunctor]
    rw [ιTotal_map, HomologicalComplex.add_f_apply,
      HomologicalComplex.add_f_apply, Preadditive.add_comp,
      ← ιTotal_map X Y f, ← ιTotal_map X Y g]
    exact (Preadditive.comp_add _ _ _ _ _ _).symm

noncomputable def adjacentColumnTotalShortComplex (p : ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{w} ℤ) :=
  ShortComplex.mk
    (total.map (adjacentColumnInclusion K p) (ComplexShape.up ℤ))
    (total.map (adjacentColumnProjection K p) (ComplexShape.up ℤ)) (by
      rw [← total.map_comp]
      change total.map
        ((adjacentColumnBicomplexShortComplex K p).f ≫
          (adjacentColumnBicomplexShortComplex K p).g)
        (ComplexShape.up ℤ) = 0
      rw [(adjacentColumnBicomplexShortComplex K p).zero]
      apply HomologicalComplex.Hom.ext
      funext n
      apply total.hom_ext
      intro i j hij
      rw [ιTotal_map]
      simp)

noncomputable def stupidTruncGEXIso (p i : ℤ) (hi : p ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
    (i := (i - p).toNat) (by
      change p + ((i - p).toNat : ℤ) = i
      rw [Int.toNat_of_nonneg (by omega)]
      omega)

@[simp]
lemma stupidTruncXIso_eq_stupidTruncGEXIso (p i : ℤ) (k : ℕ)
    (h : (ComplexShape.embeddingUpIntGE p).f k = i) :
    K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) h =
      stupidTruncGEXIso K p i (by
        change p + (k : ℤ) = i at h
        omega) := by
  have hk : k = (i - p).toNat := by
    change p + (k : ℤ) = i at h
    rw [show i - p = (k : ℤ) by omega]
    simp
  subst k
  rfl

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_inv_hom_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).inv.f j ≫
      (stupidTruncGEXIso K p i hi').hom.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).inv_hom_id,
    HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_hom_inv_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).hom.f j ≫
      (stupidTruncGEXIso K p i hi').inv.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).hom_inv_id,
    HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma complexIso_inv_hom_f {A B : CochainComplex AddCommGrpCat.{w} ℤ}
    (e : A ≅ B) (j : ℤ) : e.inv.f j ≫ e.hom.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma complexIso_hom_inv_f {A B : CochainComplex AddCommGrpCat.{w} ℤ}
    (e : A ≅ B) (j : ℤ) : e.hom.f j ≫ e.inv.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

noncomputable def adjacentColumnTotalRetraction (p n : ℤ) :
    ((truncatedBicomplex K p).total
      (ComplexShape.up ℤ)).X n ⟶
    ((truncatedBicomplex K (p + 1)).total
      (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : p + 1 ≤ i then
      ((stupidTruncGEXIso K p i (by omega)).hom.f j ≫
        (stupidTruncGEXIso K (p + 1) i hi).inv.f j) ≫
        (truncatedBicomplex K (p + 1)).ιTotal
          (ComplexShape.up ℤ) i j n hij
    else 0)

noncomputable def adjacentColumnTotalSection (p n : ℤ) :
    ((singleColumnBicomplex K p).total (ComplexShape.up ℤ)).X n ⟶
    ((truncatedBicomplex K p).total
      (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : i = p then
      (((singleColumnXIso K p i hi).hom.f j ≫
        (K.XIsoOfEq hi).inv.f j) ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (i := 0) (by subst i; simp [ComplexShape.embeddingUpIntGE])).inv.f j) ≫
        (truncatedBicomplex K p).ιTotal
          (ComplexShape.up ℤ) i j n hij
    else 0)

noncomputable def adjacentColumnTotalDegreewiseSplitting (p n : ℤ) :
    (((adjacentColumnTotalShortComplex K p).map
      (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) n)).Splitting) where
  r := adjacentColumnTotalRetraction K p n
  s := adjacentColumnTotalSection K p n
  f_r := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change (truncatedBicomplex K (p + 1)).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫
          (total.map (adjacentColumnInclusion K p) (ComplexShape.up ℤ)).f n ≫
            adjacentColumnTotalRetraction K p n =
      (truncatedBicomplex K (p + 1)).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ 𝟙 _
    by_cases hi : p + 1 ≤ i
    · rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
      dsimp [adjacentColumnTotalRetraction, truncatedBicomplex]
      rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      simp [adjacentColumnInclusion,
        HomologicalComplex.stupidTruncGEMap, Category.assoc]
      rw [dif_pos hi]
      simp [HomologicalComplex.comp_f, Category.assoc]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
  s_g := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change (singleColumnBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ adjacentColumnTotalSection K p n ≫
          (total.map (adjacentColumnProjection K p) (ComplexShape.up ℤ)).f n =
      (singleColumnBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ 𝟙 _
    by_cases hi : i = p
    · rw [← Category.assoc]
      dsimp [adjacentColumnTotalSection, truncatedBicomplex]
      rw [HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      rw [Category.assoc, Category.assoc, Category.assoc,
        HomologicalComplex₂.ιTotal_map]
      subst i
      simp [adjacentColumnProjection,
        singleColumnBicomplex,
        Category.assoc]
      let e₀ := stupidTruncGEXIso K p p le_rfl
      let e₁ := singleColumnXIso K p p rfl
      change e₁.hom.f j ≫ e₀.inv.f j ≫
        ((e₀.hom.f j ≫ e₁.inv.f j) ≫
          (singleColumnBicomplex K p).ιTotal
            (ComplexShape.up ℤ) p j n hij) = _
      rw [show (e₀.hom.f j ≫ e₁.inv.f j) ≫
          (singleColumnBicomplex K p).ιTotal
            (ComplexShape.up ℤ) p j n hij =
        e₀.hom.f j ≫ e₁.inv.f j ≫
          (singleColumnBicomplex K p).ιTotal
            (ComplexShape.up ℤ) p j n hij by apply Category.assoc,
        stupidTruncGEXIso_inv_hom_f_assoc,
        singleColumnXIso_hom_inv_f_assoc]
      rfl
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi
  id := by
    dsimp [adjacentColumnTotalShortComplex,
      adjacentColumnBicomplexShortComplex, totalFunctor]
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    change (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫
          (adjacentColumnTotalRetraction K p n ≫
              (total.map (adjacentColumnInclusion K p) (ComplexShape.up ℤ)).f n +
            (total.map (adjacentColumnProjection K p) (ComplexShape.up ℤ)).f n ≫
              adjacentColumnTotalSection K p n) =
      (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
        i j n hij ≫ 𝟙 _
    by_cases hpi : p < i
    · have hi : p + 1 ≤ i := by omega
      have hip : i ≠ p := by omega
      rw [show (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
          i j n hij ≫ (_ + _) = _ + _ by
        apply Preadditive.comp_add]
      dsimp [adjacentColumnTotalRetraction,
        adjacentColumnTotalSection]
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [dif_pos hi]
      rw [Category.assoc]
      erw [HomologicalComplex₂.ιTotal_map
        (truncatedBicomplex K (p + 1)) (truncatedBicomplex K p)
        (adjacentColumnInclusion K p) (ComplexShape.up ℤ) i j n hij]
      simp [adjacentColumnInclusion, HomologicalComplex.stupidTruncGEMap,
        adjacentColumnProjection, hip, Category.assoc]
      rw [dif_pos hi]
      let e₀ := stupidTruncGEXIso K p i (by omega)
      let e₁ := stupidTruncGEXIso K (p + 1) i hi
      change e₀.hom.f j ≫ e₁.inv.f j ≫
        ((e₁.hom.f j ≫ e₀.inv.f j) ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij) = _
      rw [show (e₁.hom.f j ≫ e₀.inv.f j) ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij =
        e₁.hom.f j ≫ e₀.inv.f j ≫
          (truncatedBicomplex K p).ιTotal
            (ComplexShape.up ℤ) i j n hij by apply Category.assoc,
        stupidTruncGEXIso_inv_hom_f_assoc,
        stupidTruncGEXIso_hom_inv_f_assoc]
    · by_cases hip : i = p
      · subst i
        rw [show (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ)
            p j n hij ≫ (_ + _) = _ + _ by
          apply Preadditive.comp_add]
        dsimp [adjacentColumnTotalRetraction,
          adjacentColumnTotalSection]
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        rw [dif_neg (show ¬ p + 1 ≤ p by omega)]
        have hz : (0 : ((truncatedBicomplex K p).X p).X j ⟶
            ((truncatedBicomplex K (p + 1)).total
              (ComplexShape.up ℤ)).X n) ≫
              (HomologicalComplex₂.total.map
                (adjacentColumnInclusion K p)
                (ComplexShape.up ℤ)).f n = 0 := zero_comp
        rw [show (0 ≫ _) + _ = _ by rw [hz, zero_add]]
        rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
        dsimp [adjacentColumnProjection]
        rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
        simp [singleColumnBicomplex, Category.assoc]
        let e₀ := stupidTruncGEXIso K p p le_rfl
        change e₀.hom.f j ≫ e₀.inv.f j ≫
            (truncatedBicomplex K p).ιTotal
              (ComplexShape.up ℤ) p j n hij = _
        rw [stupidTruncGEXIso_hom_inv_f_assoc]
      · apply IsZero.eq_of_src
        apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega

end HomologicalComplex₂

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe w

variable (A : CochainComplex AddCommGrpCat.{w} ℤ)

noncomputable def singleZeroBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) 0).obj A

noncomputable def singleZeroXIso (i : ℤ) (hi : i = 0) :
    (singleZeroBicomplex A).X i ≅ A := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A

noncomputable def singleZeroTotalXIso (n : ℤ) :
    ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X n ≅ A.X n where
  hom := HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : i = 0 then
      (singleZeroXIso A i hi).hom.f j ≫
        (A.XIsoOfEq (by dsimp at hij; omega)).hom
    else 0)
  inv := (singleZeroXIso A 0 rfl).inv.f n ≫
    (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi
  inv_hom_id := by
    dsimp
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [singleZeroXIso]

noncomputable def singleZeroTotalIso :
    (singleZeroBicomplex A).total (ComplexShape.up ℤ) ≅ A :=
  HomologicalComplex.Hom.isoOfComponents (singleZeroTotalXIso A) (by
    intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp [singleZeroTotalXIso]
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
      rw [← Category.assoc, HomologicalComplex₂.total_d]
      let ι := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 n n hij
      let d₁ := (singleZeroBicomplex A).D₁ (ComplexShape.up ℤ) n m
      let d₂ := (singleZeroBicomplex A).D₂ (ComplexShape.up ℤ) n m
      let φ : ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m ⟶
          A.X m := (singleZeroBicomplex A).totalDesc (fun i j hij ↦
        if h : i = 0 then
          (singleZeroXIso A i h).hom.f j ≫
            (A.XIsoOfEq (by
              change i + j = m at hij
              omega)).hom
        else 0)
      change ((singleZeroBicomplex A).X 0).d n m ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) 0 A).hom.f m =
        (ι ≫ (d₁ + d₂)) ≫ φ
      have hcomp : ι ≫ (d₁ + d₂) = ι ≫ d₁ + ι ≫ d₂ :=
        Preadditive.comp_add _ _ _ _ _ _
      have hadd : (ι ≫ d₁ + ι ≫ d₂) ≫ φ =
          (ι ≫ d₁) ≫ φ + (ι ≫ d₂) ≫ φ :=
        Preadditive.add_comp _ _ _ _ _ _
      refine Eq.trans ?_ ((congrArg (fun x ↦ x ≫ φ) hcomp).trans hadd).symm
      have ha₁ : (ι ≫ d₁) ≫ φ = ι ≫ d₁ ≫ φ := Category.assoc _ _ _
      have ha₂ : (ι ≫ d₂) ≫ φ = ι ≫ d₂ ≫ φ := Category.assoc _ _ _
      rw [ha₁, ha₂]
      dsimp [ι, d₁, d₂, φ]
      rw [HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc]
      rw [(singleZeroBicomplex A).d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) n m]
      rw [(singleZeroBicomplex A).d₂_eq (ComplexShape.up ℤ)
        0 hnm m (by simp)]
      simp [singleZeroBicomplex]
      let δ := ((singleZeroBicomplex A).X 0).d n m
      let ιm := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 m m (by simp)
      let e := HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 A
      change δ ≫ e.hom.f m =
        (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
        (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ)
      have hzero : (1 : ℤˣ) •
          (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) = 0 :=
        one_smul _ _
      have hvertical : (1 : ℤˣ) • (δ ≫ ιm) = δ ≫ ιm := one_smul _ _
      have hright :
          (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
            (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ) =
          (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) :=
        congrArg₂ (fun x y ↦ x + y)
          (congrArg (fun x ↦ x ≫ φ) hzero)
          (congrArg (fun x ↦ x ≫ φ) hvertical)
      refine Eq.trans ?_ hright.symm
      have hz : (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) ≫ φ = 0 :=
        zero_comp
      rw [show (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) =
          ((δ ≫ ιm) ≫ φ) by rw [hz, zero_add]]
      have hdesc : ιm ≫ φ = e.hom.f m := by
        dsimp [ιm, φ, e]
        rw [HomologicalComplex₂.ι_totalDesc]
        simp [singleZeroXIso]
      exact (congrArg (fun x ↦ δ ≫ x) hdesc.symm).trans
        (Category.assoc δ ιm φ).symm
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi)

noncomputable def singleColumnShiftIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    singleColumnBicomplex K p ≅
      (shiftFunctor₁ AddCommGrpCat.{w} (-p)).obj
        (singleZeroBicomplex (K.X p)) :=
  (((CochainComplex.singleFunctors
    (CochainComplex AddCommGrpCat.{w} ℤ)).shiftIso
      (-p) p 0 (by omega)).app (K.X p)).symm

noncomputable def singleColumnTotalIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (singleColumnBicomplex K p).total (ComplexShape.up ℤ) ≅
      (K.X p)⟦-p⟧ :=
  HomologicalComplex₂.total.mapIso (singleColumnShiftIso K p)
      (ComplexShape.up ℤ) ≪≫
    (singleZeroBicomplex (K.X p)).totalShift₁Iso (-p) ≪≫
    (shiftFunctor (CochainComplex AddCommGrpCat.{w} ℤ) (-p)).mapIso
      (singleZeroTotalIso (K.X p))

noncomputable def adjacentColumnTotalShortExact
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (adjacentColumnTotalShortComplex K p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (adjacentColumnTotalShortComplex K p) (fun n ↦
      let s := adjacentColumnTotalDegreewiseSplitting K p n
      { mono_f := s.mono_f
        epi_g := s.epi_g
        exact := s.exact })

noncomputable def adjacentColumnConeToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f ⟶
      (K.X p)⟦-p⟧ :=
  CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex K p) ≫
    (singleColumnTotalIso K p).hom

noncomputable instance adjacentColumnConeToShift_quasiIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    QuasiIso (adjacentColumnConeToShift K p) := by
  letI : QuasiIso
      (CochainComplex.mappingCone.descShortComplex
        (adjacentColumnTotalShortComplex K p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (adjacentColumnTotalShortExact K p)
  dsimp [adjacentColumnConeToShift]
  infer_instance

/-- The adjacent filtration layer that contributes column `p`: the mapping cone of the map from
filtration stage `-p - 1` to stage `-p`. -/
noncomputable def columnFilteredAdjacentLayerComplex
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    CochainComplex AddCommGrpCat.{w} ℤ :=
  CochainComplex.mappingCone
    ((columnFilteredTotalComplex K).map
      (homOfLE (show columnFiltrationIndex (p + 1) ≤
        columnFiltrationIndex p by simp [columnFiltrationIndex])))

private lemma totalTruncated_eq_of_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b p : ℤ) (h : b = p) :
    (truncatedBicomplex K b).total (ComplexShape.up ℤ) =
      (truncatedBicomplex K p).total (ComplexShape.up ℤ) := by
  subst b
  rfl

/-- A filtration stage indexed by `-p` is canonically the total complex of the stupid
truncation beginning in column `p`. -/
noncomputable def columnFilteredStageIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (columnFilteredTotalComplex K).obj (columnFiltrationIndex p) ≅
      (adjacentColumnTotalShortComplex K p).X₂ :=
  eqToIso (totalTruncated_eq_of_eq K (-columnFiltrationIndex p) p
    (by simp [columnFiltrationIndex]))

private lemma totalStupidTruncGEMap_eqToHom
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b₀ b₁ p : ℤ) (h : b₀ ≤ b₁) (hb₀ : b₀ = p) (hb₁ : b₁ = p + 1) :
    total.map (HomologicalComplex.stupidTruncGEMap K b₀ b₁ h)
          (ComplexShape.up ℤ) ≫
        eqToHom (totalTruncated_eq_of_eq K b₀ p hb₀) =
      eqToHom (totalTruncated_eq_of_eq K b₁ (p + 1) hb₁) ≫
        total.map (HomologicalComplex.stupidTruncGEMap K p (p + 1) (by omega))
          (ComplexShape.up ℤ) := by
  subst b₀
  subst b₁
  rfl

@[reassoc]
lemma columnFilteredStageIso_comm
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])) ≫
      (columnFilteredStageIso K p).hom =
      (columnFilteredStageIso K (p + 1)).hom ≫
      (adjacentColumnTotalShortComplex K p).f := by
  change (columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])) ≫
      (columnFilteredStageIso K p).hom =
    (columnFilteredStageIso K (p + 1)).hom ≫
      total.map (adjacentColumnInclusion K p) (ComplexShape.up ℤ)
  simpa [columnFilteredStageIso, columnFilteredTotalComplex,
    columnFiltrationBicomplex, adjacentColumnTotalShortComplex,
    adjacentColumnBicomplexShortComplex, adjacentColumnInclusion,
    truncatedBicomplex, totalFunctor] using
      totalStupidTruncGEMap_eqToHom K
        (-columnFiltrationIndex p) (-columnFiltrationIndex (p + 1)) p
        (by simp [columnFiltrationIndex])
        (by simp [columnFiltrationIndex]) (by simp [columnFiltrationIndex])

@[reassoc]
lemma columnFilteredStageIso_inv_comm
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    (adjacentColumnTotalShortComplex K p).f ≫
        (columnFilteredStageIso K p).inv =
      (columnFilteredStageIso K (p + 1)).inv ≫
        (columnFilteredTotalComplex K).map
          (homOfLE (show columnFiltrationIndex (p + 1) ≤
            columnFiltrationIndex p by simp [columnFiltrationIndex])) := by
  rw [← cancel_mono (columnFilteredStageIso K p).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    (adjacentColumnTotalShortComplex K p).f =
        (columnFilteredStageIso K (p + 1)).inv ≫
          ((columnFilteredStageIso K (p + 1)).hom ≫
            (adjacentColumnTotalShortComplex K p).f) := by simp
    _ = (columnFilteredStageIso K (p + 1)).inv ≫
        ((columnFilteredTotalComplex K).map
          (homOfLE (show columnFiltrationIndex (p + 1) ≤
            columnFiltrationIndex p by simp [columnFiltrationIndex])) ≫
          (columnFilteredStageIso K p).hom) := by
            rw [columnFilteredStageIso_comm]
    _ = _ := (Category.assoc _ _ _).symm

/-- The adjacent filtration mapping cone is canonically isomorphic to the mapping cone of the
degreewise split adjacent-column short complex. -/
noncomputable def columnFilteredAdjacentLayerIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    columnFilteredAdjacentLayerComplex K p ≅
      CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f where
  hom := CochainComplex.mappingCone.map
    ((columnFilteredTotalComplex K).map
      (homOfLE (show columnFiltrationIndex (p + 1) ≤
        columnFiltrationIndex p by simp [columnFiltrationIndex])))
    (adjacentColumnTotalShortComplex K p).f
    (columnFilteredStageIso K (p + 1)).hom
    (columnFilteredStageIso K p).hom
    (columnFilteredStageIso_comm K p)
  inv := CochainComplex.mappingCone.map
    (adjacentColumnTotalShortComplex K p).f
    ((columnFilteredTotalComplex K).map
      (homOfLE (show columnFiltrationIndex (p + 1) ≤
        columnFiltrationIndex p by simp [columnFiltrationIndex])))
    (columnFilteredStageIso K (p + 1)).inv
    (columnFilteredStageIso K p).inv
    (columnFilteredStageIso_inv_comm K p)
  hom_inv_id := by
    dsimp only [columnFilteredAdjacentLayerComplex]
    rw [← CochainComplex.mappingCone.map_comp
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))
      (adjacentColumnTotalShortComplex K p).f
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))]
    simpa using CochainComplex.mappingCone.map_id
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))
  inv_hom_id := by
    have h := CochainComplex.mappingCone.map_comp
      (adjacentColumnTotalShortComplex K p).f
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))
      (adjacentColumnTotalShortComplex K p).f
      (columnFilteredStageIso K (p + 1)).inv
      (columnFilteredStageIso K p).inv
      (columnFilteredStageIso_inv_comm K p)
      (columnFilteredStageIso K (p + 1)).hom
      (columnFilteredStageIso K p).hom
      (columnFilteredStageIso_comm K p)
    calc
      _ = CochainComplex.mappingCone.map
          (adjacentColumnTotalShortComplex K p).f
          (adjacentColumnTotalShortComplex K p).f
          ((columnFilteredStageIso K (p + 1)).inv ≫
            (columnFilteredStageIso K (p + 1)).hom)
          ((columnFilteredStageIso K p).inv ≫
            (columnFilteredStageIso K p).hom) _ := h.symm
      _ = CochainComplex.mappingCone.map
          (adjacentColumnTotalShortComplex K p).f
          (adjacentColumnTotalShortComplex K p).f
          (𝟙 _) (𝟙 _) _ := by simp
      _ = _ := CochainComplex.mappingCone.map_id _

private lemma mappingConeTotalStupidTruncGEMap_eq_of_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b₀ b₁ p : ℤ) (h : b₀ ≤ b₁) (hb₀ : b₀ = p) (hb₁ : b₁ = p + 1) :
    CochainComplex.mappingCone
      (total.map (HomologicalComplex.stupidTruncGEMap K b₀ b₁ h)
        (ComplexShape.up ℤ)) =
      CochainComplex.mappingCone
        (total.map (HomologicalComplex.stupidTruncGEMap K p (p + 1) (by omega))
          (ComplexShape.up ℤ)) := by
  subst b₀
  subst b₁
  rfl

/-- The filtration's adjacent mapping cone is the canonical adjacent-column mapping cone. -/
lemma columnFilteredAdjacentLayerComplex_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    columnFilteredAdjacentLayerComplex K p =
      CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f := by
  simp [columnFilteredAdjacentLayerComplex,
    columnFilteredTotalComplex, columnFiltrationBicomplex,
    adjacentColumnTotalShortComplex, adjacentColumnBicomplexShortComplex,
    adjacentColumnInclusion, truncatedBicomplex]
  exact mappingConeTotalStupidTruncGEMap_eq_of_eq K
    (-columnFiltrationIndex p) (-columnFiltrationIndex (p + 1)) p
      (by simp [columnFiltrationIndex])
      (by simp [columnFiltrationIndex])
      (by simp [columnFiltrationIndex])

/-- The adjacent column-filtration layer maps quasi-isomorphically to the newly added column,
shifted so that total degree `p + q` corresponds to vertical degree `q`. -/
noncomputable def columnFilteredAdjacentLayerConeToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    columnFilteredAdjacentLayerComplex K p ⟶ (K.X p)⟦-p⟧ :=
  (columnFilteredAdjacentLayerIso K p).hom ≫
    adjacentColumnConeToShift K p

noncomputable instance columnFilteredAdjacentLayerConeToShift_quasiIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    QuasiIso (columnFilteredAdjacentLayerConeToShift K p) := by
  dsimp [columnFilteredAdjacentLayerConeToShift]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical adjacent-layer comparison, the inclusion of the middle filtration stage
becomes the quotient map in the adjacent-column short exact sequence. -/
lemma columnFilteredInr_comp_adjacentLayerConeToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ) :
    CochainComplex.mappingCone.inr
        ((columnFilteredTotalComplex K).map
          (homOfLE (show columnFiltrationIndex (p + 1) ≤
            columnFiltrationIndex p by simp [columnFiltrationIndex]))) ≫
      columnFilteredAdjacentLayerConeToShift K p =
    (columnFilteredStageIso K p).hom ≫
      (adjacentColumnTotalShortComplex K p).g ≫
      (singleColumnTotalIso K p).hom := by
  dsimp [columnFilteredAdjacentLayerConeToShift, columnFilteredAdjacentLayerIso,
    adjacentColumnConeToShift]
  have h := (CochainComplex.mappingCone.triangleMap
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))
      (adjacentColumnTotalShortComplex K p).f
      (columnFilteredStageIso K (p + 1)).hom
      (columnFilteredStageIso K p).hom
      (columnFilteredStageIso_comm K p)).comm₂_assoc
      (CochainComplex.mappingCone.descShortComplex
          (adjacentColumnTotalShortComplex K p) ≫
            (singleColumnTotalIso K p).hom)
  simp only [CochainComplex.mappingCone.triangleMap_hom₂,
    CochainComplex.mappingCone.triangleMap_hom₃,
    CochainComplex.mappingCone.triangle_mor₂] at h
  exact h.trans (by
    rw [← Category.assoc
      (CochainComplex.mappingCone.inr (adjacentColumnTotalShortComplex K p).f)
      (CochainComplex.mappingCone.descShortComplex
        (adjacentColumnTotalShortComplex K p))
      (singleColumnTotalIso K p).hom,
      CochainComplex.mappingCone.inr_descShortComplex])

attribute [local simp] ComposableArrows.Precomp.map ComposableArrows.Precomp.obj
  CategoryTheory.Triangulated.SpectralObject.δ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

/-- The triangle constructed after precomposing a spectral object by a filtered complex is
canonically isomorphic to the triangle obtained from the two mapped filtration morphisms. -/
noncomputable def filteredComplexPrecompTriangleIso
    (X : CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory AddCommGrpCat.{w} (ComplexShape.up ℤ))
      (CochainComplex AddCommGrpCat.{w} ℤ))
    (F : ℤ ⥤ CochainComplex AddCommGrpCat.{w} ℤ)
    {i j k : ℤ} (f : i ⟶ j) (g : j ⟶ k) :
    (X.precomp F).triangle f g ≅ X.triangle (F.map f) (F.map g) := by
  let ef : (F.mapComposableArrows 1).obj (ComposableArrows.mk₁ f) ≅
      ComposableArrows.mk₁ (F.map f) :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)
  let eg : (F.mapComposableArrows 1).obj (ComposableArrows.mk₁ g) ≅
      ComposableArrows.mk₁ (F.map g) :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)
  let efg : (F.mapComposableArrows 1).obj (ComposableArrows.mk₁ (f ≫ g)) ≅
      ComposableArrows.mk₁ (F.map f ≫ F.map g) :=
    ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change F.map (f ≫ g) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f ≫ F.map g
      simpa only [Category.comp_id, Category.id_comp] using F.map_comp f g)
  refine Pretriangulated.Triangle.isoMk _ _
    (X.ω₁.mapIso ef) (X.ω₁.mapIso efg) (X.ω₁.mapIso eg) ?_ ?_ ?_
  · dsimp [CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.triangle]
    simp only [← Functor.map_comp]
    congr 1
    cat_disch
  · dsimp [CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.triangle]
    simp only [← Functor.map_comp]
    congr 1
    cat_disch
  · have h := X.δ'.naturality (F.mapComposableArrowsObjMk₂Iso f g).hom
    dsimp [CategoryTheory.Triangulated.SpectralObject.precomp,
      CategoryTheory.Triangulated.SpectralObject.triangle,
      CategoryTheory.Triangulated.SpectralObject.δ] at h ⊢
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id] at h ⊢
    convert h.symm using 1
    · rw [X.ω₁.map_id, Category.id_comp]
      have hc : (F.mapComposableArrowsObjMk₁Iso f).inv ≫ ef.hom =
          𝟙 (ComposableArrows.mk₁ (F.map f)) := by
        apply ComposableArrows.hom_ext₁ <;> rfl
      have hid :
          (ComposableArrows.homMk₁ (𝟙 (F.obj i)) (𝟙 (F.obj j)) (by cat_disch) :
            ComposableArrows.mk₁ (F.map f) ⟶
              ComposableArrows.mk₁ (F.map f)) = 𝟙 _ := by
        apply ComposableArrows.hom_ext₁ <;> rfl
      rw [hc, hid, X.ω₁.map_id]
    · have hc : (F.mapComposableArrowsObjMk₁Iso g).inv ≫ eg.hom =
          𝟙 (ComposableArrows.mk₁ (F.map g)) := by
        apply ComposableArrows.hom_ext₁ <;> rfl
      have hid :
          (ComposableArrows.homMk₁ (𝟙 (F.obj j)) (𝟙 (F.obj k)) (by cat_disch) :
            ComposableArrows.mk₁ (F.map g) ⟶
              ComposableArrows.mk₁ (F.map g)) = 𝟙 _ := by
        apply ComposableArrows.hom_ext₁ <;> rfl
      rw [hc, hid, X.ω₁.map_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The connecting morphism of the column-filtered spectral object, transported from the
precomposed spectral-object triangle to the ordinary mapping-cone triangle. -/
lemma columnFilteredConnecting_comp_homologyFactor
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    (columnFilteredTotalSpectralObject K).δ
        (homOfLE (show columnFiltrationIndex (p + 1 + 1) ≤
          columnFiltrationIndex (p + 1) by
            dsimp [columnFiltrationIndex]
            omega))
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex]))
        (p + q) (p + 1 + q) (by omega) ≫
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).app
          (columnFilteredAdjacentLayerComplex K (p + 1))).hom =
    ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).app
          (columnFilteredAdjacentLayerComplex K p)).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle
            ((columnFilteredTotalComplex K).map
              (homOfLE (show columnFiltrationIndex (p + 1 + 1) ≤
                columnFiltrationIndex (p + 1) by
                  dsimp [columnFiltrationIndex]
                  omega)))
            ((columnFilteredTotalComplex K).map
              (homOfLE (show columnFiltrationIndex (p + 1) ≤
                columnFiltrationIndex p by simp [columnFiltrationIndex])))).mor₃
          (p + q) (p + 1 + q) (by omega) := by
  let F := columnFilteredTotalComplex K
  let X := HomotopyCategory.spectralObjectMappingCone AddCommGrpCat.{w}
  let H := HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
    (ComplexShape.up ℤ) 0
  let f : columnFiltrationIndex (p + 1 + 1) ⟶
      columnFiltrationIndex (p + 1) := homOfLE (by
        dsimp [columnFiltrationIndex]
        omega)
  let g : columnFiltrationIndex (p + 1) ⟶
      columnFiltrationIndex p := homOfLE (by simp [columnFiltrationIndex])
  let e := filteredComplexPrecompTriangleIso X F f g
  have h := H.homologySequenceδ_naturality
    ((X.precomp F).triangle f g)
    (X.triangle (F.map f) (F.map g)) e.hom
    (p + q) (p + 1 + q) (by omega)
  have he3 : (H.shift (p + q)).map e.hom.hom₃ ≫
        (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
          (ComplexShape.up ℤ) (p + q)).hom.app
            (CochainComplex.mappingCone (F.map g)) =
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).hom.app
          (columnFilteredAdjacentLayerComplex K p) := by
    dsimp [e, filteredComplexPrecompTriangleIso, H, X, F,
      columnFilteredAdjacentLayerComplex, g]
    change (HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (p + q)).map _ ≫ _ = _
    change ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).map _) ≫ _ = _
    change ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).map
          (CochainComplex.mappingCone.map (F.map g) (F.map g)
            (𝟙 _) (𝟙 _) _)) ≫ _ = _
    rw [CochainComplex.mappingCone.map_id]
    calc
      _ = 𝟙 _ ≫ _ := congrArg (· ≫ _)
        ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
            (ComplexShape.up ℤ) (p + q)).map_id _)
      _ = _ := Category.id_comp _
  have he1 : (H.shift (p + 1 + q)).map e.hom.hom₁ ≫
        (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
          (ComplexShape.up ℤ) (p + 1 + q)).hom.app
            (CochainComplex.mappingCone (F.map f)) =
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).hom.app
          (columnFilteredAdjacentLayerComplex K (p + 1)) := by
    dsimp [e, filteredComplexPrecompTriangleIso, H, X, F,
      columnFilteredAdjacentLayerComplex, f]
    change (HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (p + 1 + q)).map _ ≫ _ = _
    change ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).map _) ≫ _ = _
    change ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).map
          (CochainComplex.mappingCone.map (F.map f) (F.map f)
            (𝟙 _) (𝟙 _) _)) ≫ _ = _
    rw [CochainComplex.mappingCone.map_id]
    calc
      _ = 𝟙 _ ≫ _ := congrArg (· ≫ _)
        ((HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
            (ComplexShape.up ℤ) (p + 1 + q)).map_id _)
      _ = _ := Category.id_comp _
  have hraw' : H.homologySequenceδ (X.triangle (F.map f) (F.map g))
        (p + q) (p + 1 + q) (by omega) ≫
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).hom.app
          (CochainComplex.mappingCone (F.map f)) =
    (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).hom.app
          (CochainComplex.mappingCone (F.map g)) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          (p + q) (p + 1 + q) (by omega) := by
    change (HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).homologySequenceδ
          ((HomotopyCategory.quotient AddCommGrpCat.{w}
            (ComplexShape.up ℤ)).mapTriangle.obj
              (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)))
          (p + q) (p + 1 + q) _ ≫
        (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
          (ComplexShape.up ℤ) (p + 1 + q)).hom.app
            (CochainComplex.mappingCone (F.map f)) = _
    erw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj_assoc
      (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g))
      (p + q) (p + 1 + q) (by omega)]
    simp only [CochainComplex.mappingConeCompTriangle_obj₁,
      CochainComplex.mappingConeCompTriangle_obj₃,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    congr 1
  have hδ : H.homologySequenceδ ((X.precomp F).triangle f g)
        (p + q) (p + 1 + q) (by omega) ≫
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).hom.app
          (columnFilteredAdjacentLayerComplex K (p + 1)) =
    (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).hom.app
          (columnFilteredAdjacentLayerComplex K p) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          (p + q) (p + 1 + q) (by omega) := by
    calc
      _ = H.homologySequenceδ ((X.precomp F).triangle f g)
            (p + q) (p + 1 + q) (by omega) ≫
          (H.shift (p + 1 + q)).map e.hom.hom₁ ≫
          (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
            (ComplexShape.up ℤ) (p + 1 + q)).hom.app
              (CochainComplex.mappingCone (F.map f)) := by
        rw [← he1]
      _ = (H.shift (p + q)).map e.hom.hom₃ ≫
          H.homologySequenceδ (X.triangle (F.map f) (F.map g))
            (p + q) (p + 1 + q) (by omega) ≫
          (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
            (ComplexShape.up ℤ) (p + 1 + q)).hom.app
              (CochainComplex.mappingCone (F.map f)) := by
        rw [← Category.assoc, ← h, Category.assoc]
      _ = (H.shift (p + q)).map e.hom.hom₃ ≫
          (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
            (ComplexShape.up ℤ) (p + q)).hom.app
              (CochainComplex.mappingCone (F.map g)) ≫
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
            (ComplexShape.up ℤ) 0).shiftMap
              (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
              (p + q) (p + 1 + q) (by omega) := by
        rw [hraw']
      _ = _ := by
        rw [← Category.assoc, he3]
  have htriangle : (X.precomp F).triangle f g =
      (X.precomp F).ω₂.obj (ComposableArrows.mk₂ f g) := by
    dsimp [CategoryTheory.Triangulated.SpectralObject.triangle,
      CategoryTheory.Triangulated.SpectralObject.ω₂,
      CategoryTheory.Pretriangulated.Triangle.functorMk]
    congr 1
  have hδ' : H.homologySequenceδ
        ((X.precomp F).ω₂.obj (ComposableArrows.mk₂ f g))
        (p + q) (p + 1 + q) (by omega) ≫
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).hom.app
          (columnFilteredAdjacentLayerComplex K (p + 1)) =
    (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).hom.app
          (columnFilteredAdjacentLayerComplex K p) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          (p + q) (p + 1 + q) (by omega) := by
    cases htriangle
    exact hδ
  change H.homologySequenceδ
        ((X.precomp F).ω₂.obj (ComposableArrows.mk₂ f g))
        (p + q) (p + 1 + q) (by omega) ≫
      (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + 1 + q)).hom.app
          (columnFilteredAdjacentLayerComplex K (p + 1)) =
    (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (p + q)).hom.app
          (columnFilteredAdjacentLayerComplex K p) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingConeCompTriangle (F.map f) (F.map g)).mor₃
          (p + q) (p + 1 + q) (by omega)
  exact hδ'

/-- Homology of an adjacent filtration layer, identified with homology of the shifted new
column. -/
noncomputable def columnFilteredAdjacentLayerHomologyIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p n : ℤ) :
    (columnFilteredAdjacentLayerComplex K p).homology n ≅
      ((K.X p)⟦-p⟧).homology n := by
  letI : QuasiIso (columnFilteredAdjacentLayerConeToShift K p) :=
    columnFilteredAdjacentLayerConeToShift_quasiIso K p
  letI : QuasiIsoAt (columnFilteredAdjacentLayerConeToShift K p) n :=
    QuasiIso.quasiIsoAt n
  exact isoOfQuasiIsoAt (columnFilteredAdjacentLayerConeToShift K p) n

/-- The mapping-cone comparison for a short exact sequence transports the canonical connecting
morphism to the ordinary connecting homomorphism in homology. -/
@[reassoc]
lemma homologyMap_descShortComplex_comp_delta
    (S : ShortComplex (CochainComplex AddCommGrpCat.{w} ℤ))
    (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex S) n₀ ≫
      hS.δ n₀ n₁ (by simpa using h) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle S.f).mor₃ n₀ n₁ (by omega) := by
  have h₁ := CochainComplex.mappingCone.homologySequenceδ_triangleh hS n₀ n₁ h
  have h₂ := CochainComplex.homologySequenceδ_quotient_mapTriangle_obj
    (CochainComplex.mappingCone.triangle S.f) n₀ n₁ h
  rw [h₂] at h₁
  let z := (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
    (ComplexShape.up ℤ) n₀).hom.app (CochainComplex.mappingCone S.f)
  let w := (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
    (ComplexShape.up ℤ) n₁).inv.app S.X₁
  change z ≫ _ = z ≫ _ at h₁
  have h₁' := (cancel_epi z).mp h₁
  have h₁'' := h₁'.trans (Category.assoc _ _ w).symm
  exact ((cancel_mono w).mp h₁'').symm

/-- Naturality of the raw mapping-cone connecting map under the canonical filtration-stage
comparison. -/
@[reassoc]
lemma columnFilteredRawConnecting_comp_stageIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle
          ((columnFilteredTotalComplex K).map
            (homOfLE (show columnFiltrationIndex (p + 1) ≤
              columnFiltrationIndex p by simp [columnFiltrationIndex])))).mor₃
        (p + q) (p + 1 + q) (by omega) ≫
      HomologicalComplex.homologyMap (columnFilteredStageIso K (p + 1)).hom
        (p + 1 + q) =
    HomologicalComplex.homologyMap (columnFilteredAdjacentLayerIso K p).hom
        (p + q) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle
            (adjacentColumnTotalShortComplex K p).f).mor₃
          (p + q) (p + 1 + q) (by omega) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
    (ComplexShape.up ℤ) 0
  let e := CochainComplex.mappingCone.triangleMap
    ((columnFilteredTotalComplex K).map
      (homOfLE (show columnFiltrationIndex (p + 1) ≤
        columnFiltrationIndex p by simp [columnFiltrationIndex])))
    (adjacentColumnTotalShortComplex K p).f
    (columnFilteredStageIso K (p + 1)).hom
    (columnFilteredStageIso K p).hom
    (columnFilteredStageIso_comm K p)
  have h := H.homologySequenceδ_naturality
    (CochainComplex.mappingCone.triangle
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex]))))
    (CochainComplex.mappingCone.triangle
      (adjacentColumnTotalShortComplex K p).f)
    e (p + q) (p + 1 + q) (by omega)
  dsimp only [Functor.homologySequenceδ, e,
    CochainComplex.mappingCone.triangleMap_hom₁,
    CochainComplex.mappingCone.triangleMap_hom₃, H] at h
  change
    HomologicalComplex.homologyMap (columnFilteredAdjacentLayerIso K p).hom
        (p + q) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℤ) 0).shiftMap
          (CochainComplex.mappingCone.triangle
            (adjacentColumnTotalShortComplex K p).f).mor₃
          (p + q) (p + 1 + q) (by omega) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.mappingCone.triangle
          ((columnFilteredTotalComplex K).map
            (homOfLE (show columnFiltrationIndex (p + 1) ≤
              columnFiltrationIndex p by simp [columnFiltrationIndex])))).mor₃
        (p + q) (p + 1 + q) (by omega) ≫
      HomologicalComplex.homologyMap (columnFilteredStageIso K (p + 1)).hom
        (p + 1 + q) at h
  exact h.symm

/-- The inclusion of the middle filtration stage followed by the adjacent-layer comparison, on
homology. -/
@[reassoc]
lemma columnFilteredHomologyMap_inr_comp_coneToShift
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p n : ℤ) :
    HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          ((columnFilteredTotalComplex K).map
            (homOfLE (show columnFiltrationIndex (p + 1) ≤
              columnFiltrationIndex p by simp [columnFiltrationIndex])))) n ≫
      HomologicalComplex.homologyMap
        (columnFilteredAdjacentLayerConeToShift K p) n =
    HomologicalComplex.homologyMap (columnFilteredStageIso K p).hom n ≫
      HomologicalComplex.homologyMap
        (adjacentColumnTotalShortComplex K p).g n ≫
      HomologicalComplex.homologyMap (singleColumnTotalIso K p).hom n := by
  let ι := CochainComplex.mappingCone.inr
    ((columnFilteredTotalComplex K).map
      (homOfLE (show columnFiltrationIndex (p + 1) ≤
        columnFiltrationIndex p by simp [columnFiltrationIndex])))
  let e := (columnFilteredStageIso K p).hom
  let g := (adjacentColumnTotalShortComplex K p).g
  let s := (singleColumnTotalIso K p).hom
  have hι : ι ≫ columnFilteredAdjacentLayerConeToShift K p = e ≫ g ≫ s :=
    columnFilteredInr_comp_adjacentLayerConeToShift K p
  calc
    _ = HomologicalComplex.homologyMap
        (ι ≫ columnFilteredAdjacentLayerConeToShift K p) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
    _ = HomologicalComplex.homologyMap (e ≫ g ≫ s) n := by rw [hι]
    _ = _ := by
      simp only [HomologicalComplex.homologyMap_comp]
      rfl

/-- Cancelling the final single-column isomorphism leaves the short-complex mapping-cone
comparison. -/
@[reassoc]
lemma columnFilteredHomologyMap_coneToShift_comp_singleColumnTotalIso_inv
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p n : ℤ) :
    HomologicalComplex.homologyMap
        (columnFilteredAdjacentLayerConeToShift K p) n ≫
      HomologicalComplex.homologyMap (singleColumnTotalIso K p).inv n =
    HomologicalComplex.homologyMap (columnFilteredAdjacentLayerIso K p).hom n ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex
          (adjacentColumnTotalShortComplex K p)) n := by
  have hc : columnFilteredAdjacentLayerConeToShift K p ≫
        (singleColumnTotalIso K p).inv =
      (columnFilteredAdjacentLayerIso K p).hom ≫
        CochainComplex.mappingCone.descShortComplex
          (adjacentColumnTotalShortComplex K p) := by
    dsimp only [columnFilteredAdjacentLayerConeToShift, adjacentColumnConeToShift]
    rw [← cancel_mono (singleColumnTotalIso K p).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Category.assoc
      (columnFilteredAdjacentLayerIso K p).hom
      (CochainComplex.mappingCone.descShortComplex
        (adjacentColumnTotalShortComplex K p))
      (singleColumnTotalIso K p).hom).symm
  calc
    _ = HomologicalComplex.homologyMap
        (columnFilteredAdjacentLayerConeToShift K p ≫
          (singleColumnTotalIso K p).inv) n :=
      (HomologicalComplex.homologyMap_comp _ _ n).symm
    _ = HomologicalComplex.homologyMap
        ((columnFilteredAdjacentLayerIso K p).hom ≫
          CochainComplex.mappingCone.descShortComplex
            (adjacentColumnTotalShortComplex K p)) n :=
      congrArg (fun f ↦ HomologicalComplex.homologyMap f n) hc
    _ = _ := HomologicalComplex.homologyMap_comp _ _ n

/-- The initial-page object before transporting adjacent-layer homology to column homology. -/
noncomputable def columnFilteredInitialPageXIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    ((columnFilteredTotalSpectralSequence K).page 2).X (p, q) ≅
      ((columnFilteredTotalSpectralObject K).H (p + q)).obj
        (ComposableArrows.mk₁ (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex]))) :=
  (columnFilteredTotalSpectralObject K).spectralSequenceFirstPageXIso
    CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt (p, q)
      (columnFiltrationIndex (p + 1)) (columnFiltrationIndex p)
      (by
        dsimp [CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt,
          columnFiltrationIndex]
        omega)
      (by simp [columnFiltrationIndex]) (p + q) rfl

/-- The spectral object's adjacent-layer term is ordinary homology of the corresponding mapping
cone. -/
noncomputable def columnFilteredAdjacentLayerSpectralHomologyIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    ((columnFilteredTotalSpectralObject K).H (p + q)).obj
        (ComposableArrows.mk₁ (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex]))) ≅
      (columnFilteredAdjacentLayerComplex K p).homology (p + q) := by
  dsimp [columnFilteredTotalSpectralObject,
    HomotopyCategory.filteredComplexSpectralObject,
    CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor,
    HomotopyCategory.spectralObjectMappingCone,
    HomotopyCategory.composableArrowsFunctor,
    columnFilteredAdjacentLayerComplex]
  exact (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
    (ComplexShape.up ℤ) (p + q)).app (columnFilteredAdjacentLayerComplex K p)

/-- Homology of a shifted column in total degree `p + q` is column homology in degree `q`. -/
noncomputable def columnShiftHomologyIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    ((K.X p)⟦-p⟧).homology (p + q) ≅ (K.X p).homology q :=
  (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{w}
    (-p) (p + q) q (by omega)).app (K.X p)

/-- The initial page of the column filtration is vertical column homology. -/
noncomputable def columnFilteredInitialPageColumnHomologyIso
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    ((columnFilteredTotalSpectralSequence K).page 2).X (p, q) ≅
      (K.X p).homology q :=
  columnFilteredInitialPageXIso K p q ≪≫
    columnFilteredAdjacentLayerSpectralHomologyIso K p q ≪≫
    columnFilteredAdjacentLayerHomologyIso K p (p + q) ≪≫
    columnShiftHomologyIso K p q

/-- The raw formula for the horizontal differential on the initial page. -/
lemma columnFilteredFirstPage_d_eq
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    ((columnFilteredTotalSpectralSequence K).page 2).d (p, q) (p + 1, q) =
      (columnFilteredInitialPageXIso K p q).hom ≫
        (columnFilteredTotalSpectralObject K).δ
          (homOfLE (show columnFiltrationIndex (p + 1 + 1) ≤
            columnFiltrationIndex (p + 1) by
              dsimp [columnFiltrationIndex]
              omega))
          (homOfLE (show columnFiltrationIndex (p + 1) ≤
            columnFiltrationIndex p by simp [columnFiltrationIndex]))
          (p + q) (p + 1 + q) (by omega) ≫
        (columnFilteredInitialPageXIso K (p + 1) q).inv := by
  dsimp only [columnFilteredTotalSpectralSequence]
  simpa only [columnFilteredInitialPageXIso] using
    (columnFilteredTotalSpectralObject K).spectralSequence_first_page_d_eq
      CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt
        (p, q) (p + 1, q) (by
          change (p, q) + (1, 0) = (p + 1, q)
          simp)
        (columnFiltrationIndex (p + 1 + 1)) (columnFiltrationIndex (p + 1))
        (columnFiltrationIndex p)
        (by
          dsimp [CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt,
            columnFiltrationIndex]
          omega)
        (by
          dsimp [CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt,
            columnFiltrationIndex]
          omega)
        (by
          dsimp [CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt,
            columnFiltrationIndex])
        (p + q) (p + 1 + q)
        (by dsimp [CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt])
        (by omega)

end HomologicalComplex₂
