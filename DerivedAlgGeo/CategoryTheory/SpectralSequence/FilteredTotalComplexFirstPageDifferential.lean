/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplexAdjacent

/-!
# The first differential of a column-filtered total complex

This file continues the identification of the initial page with column homology by tracking its
horizontal differential.  The spectral-object differential is first expressed as the connecting
morphism for two adjacent columns.  At the chain level, the standard section and retraction show
that this connecting morphism is induced by the horizontal differential of the bicomplex.
-/

universe w

open CategoryTheory Category Limits

namespace HomologicalComplex₂

set_option maxHeartbeats 4000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : HomologicalComplex₂ AddCommGrpCat.{w}
  (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- Under the initial-page column-homology identifications, the first differential is the
connecting morphism of the adjacent-column short exact sequence. -/
lemma columnFilteredInitialPage_d_eq_connecting (p q : ℤ) :
    ((columnFilteredTotalSpectralSequence K).page 2).d (p, q) (p + 1, q) ≫
        (columnFilteredInitialPageColumnHomologyIso K (p + 1) q).hom =
      (columnFilteredInitialPageColumnHomologyIso K p q).hom ≫
        (columnShiftHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap (singleColumnTotalIso K p).inv (p + q) ≫
        (adjacentColumnTotalShortExact K p).δ
          (p + q) (p + 1 + q) (by dsimp; omega) ≫
        HomologicalComplex.homologyMap
          (adjacentColumnTotalShortComplex K (p + 1)).g (p + 1 + q) ≫
        HomologicalComplex.homologyMap
          (singleColumnTotalIso K (p + 1)).hom (p + 1 + q) ≫
        (columnShiftHomologyIso K (p + 1) q).hom := by
  rw [columnFilteredFirstPage_d_eq]
  dsimp [columnFilteredInitialPageColumnHomologyIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [cancel_epi (columnFilteredInitialPageXIso K p q).hom]
  dsimp only [columnFilteredAdjacentLayerSpectralHomologyIso]
  simp only [id_eq]
  rw [← Category.assoc]
  erw [columnFilteredConnecting_comp_homologyFactor K p q]
  dsimp [columnFilteredAdjacentLayerHomologyIso, isoOfQuasiIsoAt]
  let z := (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
    (ComplexShape.up ℤ) (p + q)).hom.app
      (columnFilteredAdjacentLayerComplex K p)
  change (z ≫ _) ≫ _ = z ≫ _
  refine (Category.assoc z _ _).trans ?_
  rw [cancel_epi z]
  erw [Functor.shiftMap_comp
    (F := HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
      (ComplexShape.up ℤ) 0)
    (CochainComplex.mappingCone.triangle
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1) ≤
          columnFiltrationIndex p by simp [columnFiltrationIndex])))).mor₃
    (CochainComplex.mappingCone.inr
      ((columnFilteredTotalComplex K).map
        (homOfLE (show columnFiltrationIndex (p + 1 + 1) ≤
          columnFiltrationIndex (p + 1) by
            dsimp [columnFiltrationIndex]
            omega))))
    (p + q) (p + 1 + q) (by omega)]
  change (_ ≫ HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        ((columnFilteredTotalComplex K).map
          (homOfLE (show columnFiltrationIndex (p + 1 + 1) ≤
            columnFiltrationIndex (p + 1) by
              dsimp [columnFiltrationIndex]
              omega)))) (p + 1 + q)) ≫
    HomologicalComplex.homologyMap
      (columnFilteredAdjacentLayerConeToShift K (p + 1)) (p + 1 + q) ≫ _ = _
  rw [Category.assoc]
  rw [columnFilteredHomologyMap_inr_comp_coneToShift_assoc]
  let t := HomologicalComplex.homologyMap
      (adjacentColumnTotalShortComplex K (p + 1)).g (p + 1 + q) ≫
    HomologicalComplex.homologyMap
      (singleColumnTotalIso K (p + 1)).hom (p + 1 + q) ≫
    (columnShiftHomologyIso K (p + 1) q).hom
  change _ ≫ HomologicalComplex.homologyMap
      (columnFilteredStageIso K (p + 1)).hom (p + 1 + q) ≫ t = _
  calc
    _ = HomologicalComplex.homologyMap
          (columnFilteredAdjacentLayerIso K p).hom (p + q) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
          (ComplexShape.up ℤ) 0).shiftMap
            (CochainComplex.mappingCone.triangle
              (adjacentColumnTotalShortComplex K p).f).mor₃
            (p + q) (p + 1 + q) (by omega) ≫ t :=
      columnFilteredRawConnecting_comp_stageIso_assoc K p q t
    _ = _ := by
      dsimp [t]
      simp only [Iso.hom_inv_id_assoc]
      rw [columnFilteredHomologyMap_coneToShift_comp_singleColumnTotalIso_inv_assoc]
      let e := HomologicalComplex.homologyMap
        (columnFilteredAdjacentLayerIso K p).hom (p + q)
      let d := HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex
          (adjacentColumnTotalShortComplex K p)) (p + q)
      let δ := (adjacentColumnTotalShortExact K p).δ
        (p + q) (p + 1 + q) (by dsimp; omega)
      let t' := HomologicalComplex.homologyMap
          (adjacentColumnTotalShortComplex K (p + 1)).g (p + 1 + q) ≫
        HomologicalComplex.homologyMap
          (singleColumnTotalIso K (p + 1)).hom (p + 1 + q) ≫
        (columnShiftHomologyIso K (p + 1) q).hom
      change e ≫ _ ≫ t' = (e ≫ d) ≫ δ ≫ t'
      have hδ : d ≫ δ ≫ t' =
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
            (ComplexShape.up ℤ) 0).shiftMap
              (CochainComplex.mappingCone.triangle
                (adjacentColumnTotalShortComplex K p).f).mor₃
              (p + q) (p + 1 + q) (by omega) ≫ t' :=
        homologyMap_descShortComplex_comp_delta_assoc
          (adjacentColumnTotalShortComplex K p)
          (adjacentColumnTotalShortExact K p)
          (p + q) (p + 1 + q) (by omega) t'
      calc
        _ = e ≫ (_ ≫ t') := Category.assoc _ _ _
        _ = e ≫ (d ≫ δ ≫ t') := congrArg (fun z ↦ e ≫ z) hδ.symm
        _ = _ := (Category.assoc e d (δ ≫ t')).symm

/-- The inclusion of a bidegree term into the total complex of its single-column bicomplex. -/
noncomputable def singleColumnTotalι (p q n : ℤ) (h : p + q = n) :
    (K.X p).X q ⟶ ((singleColumnBicomplex K p).total (ComplexShape.up ℤ)).X n :=
  (singleColumnXIso K p p rfl).inv.f q ≫
    (singleColumnBicomplex K p).ιTotal (ComplexShape.up ℤ) p q n h

private lemma iota_retraction_projection (p i j n : ℤ) (h : i + j = n) :
    (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ) i j n h ≫
        adjacentColumnTotalRetraction K p n ≫
        (adjacentColumnTotalShortComplex K (p + 1)).g.f n =
      if hi : p + 1 ≤ i then
        (stupidTruncGEXIso K p i (by omega)).hom.f j ≫
          (stupidTruncGEXIso K (p + 1) i hi).inv.f j ≫
          (truncatedBicomplex K (p + 1)).ιTotal
            (ComplexShape.up ℤ) i j n h ≫
          (adjacentColumnTotalShortComplex K (p + 1)).g.f n
      else 0 := by
  dsimp [adjacentColumnTotalRetraction]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  split
  · rfl
  · simp only [zero_comp]

private lemma iota_retraction_projection_precomp₂ {A B : AddCommGrpCat.{w}}
    (p i j n : ℤ) (a : A ⟶ B) (d : B ⟶ ((truncatedBicomplex K p).X i).X j)
    (h : i + j = n) :
    a ≫ ((d ≫ (truncatedBicomplex K p).ιTotal
        (ComplexShape.up ℤ) i j n h) ≫
        adjacentColumnTotalRetraction K p n ≫
        (adjacentColumnTotalShortComplex K (p + 1)).g.f n) =
      a ≫ d ≫ if hi : p + 1 ≤ i then
        (stupidTruncGEXIso K p i (by omega)).hom.f j ≫
          (stupidTruncGEXIso K (p + 1) i hi).inv.f j ≫
          (truncatedBicomplex K (p + 1)).ιTotal
            (ComplexShape.up ℤ) i j n h ≫
          (adjacentColumnTotalShortComplex K (p + 1)).g.f n
      else 0 := by
  simp only [Category.assoc, iota_retraction_projection]

private lemma iota_retraction_projection_smul_precomp {A B : AddCommGrpCat.{w}}
    (p i j n : ℤ) (a : A ⟶ B) (d : B ⟶ ((truncatedBicomplex K p).X i).X j)
    (e : ℤˣ) (h : i + j = n) (hi : ¬ p + 1 ≤ i) :
    a ≫ (e • (d ≫ (truncatedBicomplex K p).ιTotal
        (ComplexShape.up ℤ) i j n h)) ≫
        adjacentColumnTotalRetraction K p n ≫
        (adjacentColumnTotalShortComplex K (p + 1)).g.f n = 0 := by
  simp only [Linear.units_smul_comp, Category.assoc,
    iota_retraction_projection, dif_neg hi]
  rw [← Linear.units_smul_comp, ← Category.assoc]
  exact comp_zero

@[reassoc]
private lemma stupidTruncBoundary (p q : ℤ) :
    (HomologicalComplex.stupidTruncXIso K
      (ComplexShape.embeddingUpIntGE p) (i := 0)
        (by simp [ComplexShape.embeddingUpIntGE])).inv.f q ≫
      ((HomologicalComplex.stupidTrunc K
        (ComplexShape.embeddingUpIntGE p)).d p (p + 1)).f q ≫
      (stupidTruncGEXIso K p (p + 1) (by omega)).hom.f q =
    (K.d p (p + 1)).f q := by
  rw [HomologicalComplex.stupidTrunc_d_eq K p (by omega) (by omega)]
  simp only [stupidTruncXIso_eq_stupidTruncGEXIso,
    HomologicalComplex.comp_f]
  slice_lhs 1 2 => rw [stupidTruncGEXIso_inv_hom_f]
  simp only [Category.id_comp]
  slice_lhs 2 3 => rw [stupidTruncGEXIso_inv_hom_f]
  simp only [Category.comp_id]

@[reassoc]
private lemma adjacentProjectionIota (p q n : ℤ) (h : p + q = n) :
    (stupidTruncGEXIso K p p (by omega)).inv.f q ≫
      (truncatedBicomplex K p).ιTotal
        (ComplexShape.up ℤ) p q n h ≫
      (adjacentColumnTotalShortComplex K p).g.f n =
    (singleColumnXIso K p p rfl).inv.f q ≫
      (singleColumnBicomplex K p).ιTotal
        (ComplexShape.up ℤ) p q n h := by
  dsimp [adjacentColumnTotalShortComplex,
    adjacentColumnBicomplexShortComplex, totalFunctor]
  slice_lhs 2 3 => erw [HomologicalComplex₂.ιTotal_map]
  simp [adjacentColumnProjection, singleColumnBicomplex]

/-- One horizontal step in the adjacent-column connecting construction is the horizontal
differential of the original bicomplex.  The vertical part of the total differential vanishes
after projecting to the newly added next column. -/
lemma singleColumnTotalι_section_d_retraction_projection (p q : ℤ) :
    singleColumnTotalι K p q (p + q) rfl ≫
        adjacentColumnTotalSection K p (p + q) ≫
        ((truncatedBicomplex K p).total (ComplexShape.up ℤ)).d
          (p + q) (p + 1 + q) ≫
        adjacentColumnTotalRetraction K p (p + 1 + q) ≫
        (adjacentColumnTotalShortComplex K (p + 1)).g.f (p + 1 + q) =
      (K.d p (p + 1)).f q ≫
        singleColumnTotalι K (p + 1) q (p + 1 + q) (by omega) := by
  dsimp [singleColumnTotalι, adjacentColumnTotalSection]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  simp only [dif_pos trivial]
  simp only [← Category.assoc]
  rw [singleColumnXIso_inv_hom_f]
  simp only [Category.id_comp]
  rw [HomologicalComplex₂.total_d]
  let u := (HomologicalComplex.XIsoOfEq K (show p = p from rfl)).inv.f q ≫
    (HomologicalComplex.stupidTruncXIso K (ComplexShape.embeddingUpIntGE p)
      (show (ComplexShape.embeddingUpIntGE p).f 0 = p by
        simp [ComplexShape.embeddingUpIntGE])).inv.f q ≫
    (truncatedBicomplex K p).ιTotal (ComplexShape.up ℤ) p q (p + q) rfl
  let d₁ := (truncatedBicomplex K p).D₁ (ComplexShape.up ℤ)
    (p + q) (p + 1 + q)
  let d₂ := (truncatedBicomplex K p).D₂ (ComplexShape.up ℤ)
    (p + q) (p + 1 + q)
  let r := adjacentColumnTotalRetraction K p (p + 1 + q)
  let g := (adjacentColumnTotalShortComplex K (p + 1)).g.f (p + 1 + q)
  change ((u ≫ (d₁ + d₂)) ≫ r) ≫ g = _
  calc
    _ = (((u ≫ d₁) + (u ≫ d₂)) ≫ r) ≫ g :=
      congrArg (fun x ↦ (x ≫ r) ≫ g)
        (Preadditive.comp_add _ _ _ u d₁ d₂)
    _ = (((u ≫ d₁) ≫ r) + ((u ≫ d₂) ≫ r)) ≫ g :=
      congrArg (fun x ↦ x ≫ g)
        (Preadditive.add_comp _ _ _ (u ≫ d₁) (u ≫ d₂) r)
    _ = (((u ≫ d₁) ≫ r) ≫ g) + (((u ≫ d₂) ≫ r) ≫ g) :=
      Preadditive.add_comp _ _ _ ((u ≫ d₁) ≫ r) ((u ≫ d₂) ≫ r) g
    _ = _ := by
      dsimp [u, d₁, d₂, r, g]
      simp only [Category.assoc, Category.id_comp]
      erw [HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
      rw [(truncatedBicomplex K p).d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl) q (p + 1 + q)]
      rw [(truncatedBicomplex K p).d₂_eq (ComplexShape.up ℤ)
        p (show (ComplexShape.up ℤ).Rel q (q + 1) by rfl)
        (p + 1 + q) (by dsimp; omega)]
      rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = 1 by rfl, one_smul]
      rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = p.negOnePow by rfl]
      dsimp [truncatedBicomplex]
      erw [HomologicalComplex₂.ιTotalOrZero_eq
        (truncatedBicomplex K p) (ComplexShape.up ℤ)
        (p + 1) q (p + 1 + q) (by dsimp)]
      erw [iota_retraction_projection_precomp₂ K p (p + 1) q (p + 1 + q)
        ((HomologicalComplex.stupidTruncXIso K
          (ComplexShape.embeddingUpIntGE p) (by simp)).inv.f q)
        (((HomologicalComplex.stupidTrunc K
          (ComplexShape.embeddingUpIntGE p)).d p (p + 1)).f q)]
      erw [iota_retraction_projection_smul_precomp K p p (q + 1) (p + 1 + q)
        ((HomologicalComplex.stupidTruncXIso K
          (ComplexShape.embeddingUpIntGE p) (by simp)).inv.f q)
        (((HomologicalComplex.stupidTrunc K
          (ComplexShape.embeddingUpIntGE p)).X p).d q (q + 1))
        p.negOnePow (by omega) (by omega)]
      simp only [dif_pos (show p + 1 ≤ p + 1 by omega), add_zero]
      erw [stupidTruncBoundary_assoc K p q]
      slice_lhs 2 4 =>
        erw [adjacentProjectionIota K (p + 1) q (p + 1 + q)]

/-- A vertical cocycle gives a cocycle in the total complex of its single-column bicomplex. -/
lemma singleColumnTotalι_cycle {A : AddCommGrpCat.{w}}
    (p q : ℤ) (a : A ⟶ (K.X p).X q)
    (ha : a ≫ (K.X p).d q (q + 1) = 0) :
    a ≫ singleColumnTotalι K p q (p + q) rfl ≫
      ((singleColumnBicomplex K p).total (ComplexShape.up ℤ)).d
        (p + q) (p + 1 + q) = 0 := by
  dsimp [singleColumnTotalι]
  simp only [Category.assoc]
  rw [HomologicalComplex₂.total_d]
  let u := a ≫ (singleColumnXIso K p p rfl).inv.f q ≫
    (singleColumnBicomplex K p).ιTotal
      (ComplexShape.up ℤ) p q (p + q) rfl
  let d₁ := (singleColumnBicomplex K p).D₁
    (ComplexShape.up ℤ) (p + q) (p + 1 + q)
  let d₂ := (singleColumnBicomplex K p).D₂
    (ComplexShape.up ℤ) (p + q) (p + 1 + q)
  change u ≫ (d₁ + d₂) = 0
  calc
    _ = (u ≫ d₁) + (u ≫ d₂) :=
      Preadditive.comp_add _ _ _ u d₁ d₂
    _ = 0 := by
      dsimp [u, d₁, d₂]
      simp only [Category.assoc]
      rw [HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.ι_D₂]
      rw [(singleColumnBicomplex K p).d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl) q (p + 1 + q)]
      rw [(singleColumnBicomplex K p).d₂_eq (ComplexShape.up ℤ)
        p (show (ComplexShape.up ℤ).Rel q (q + 1) by rfl)
        (p + 1 + q) (by dsimp; omega)]
      rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = 1 by rfl, one_smul]
      rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = p.negOnePow by rfl]
      simp [singleColumnBicomplex]
      rw [← Category.assoc, ha, zero_comp, smul_zero]

/-- The connecting morphism for two adjacent columns sends a vertical cocycle to its horizontal
differential, viewed as a cocycle in the next single-column total complex. -/
lemma adjacentColumnConnecting_representative {A : AddCommGrpCat.{w}}
    (p q : ℤ) (a : A ⟶ (K.X p).X q)
    (ha : a ≫ (K.X p).d q (q + 1) = 0) :
    let S := adjacentColumnTotalShortComplex K p
    let hS := adjacentColumnTotalShortExact K p
    let n := p + q
    let n' := p + 1 + q
    S.X₃.liftCycles (a ≫ singleColumnTotalι K p q n rfl) n'
        ((ComplexShape.up ℤ).next_eq' (by dsimp [n, n']; omega))
        (by simpa only [S, n, n', adjacentColumnTotalShortComplex,
          Category.assoc] using singleColumnTotalι_cycle K p q a ha) ≫
      S.X₃.homologyπ n ≫ hS.δ n n' (by dsimp [n, n']; omega) ≫
      HomologicalComplex.homologyMap
        (adjacentColumnTotalShortComplex K (p + 1)).g n' =
    ((singleColumnBicomplex K (p + 1)).total (ComplexShape.up ℤ)).liftCycles
        (a ≫ (K.d p (p + 1)).f q ≫
          singleColumnTotalι K (p + 1) q n' (by omega))
        (p + 1 + 1 + q)
        ((ComplexShape.up ℤ).next_eq' (by dsimp [n']; omega))
        (singleColumnTotalι_cycle K (p + 1) q
          (a ≫ (K.d p (p + 1)).f q) (by
            rw [Category.assoc, K.d_comm, reassoc_of% ha]
            simp)) ≫
      ((singleColumnBicomplex K (p + 1)).total
        (ComplexShape.up ℤ)).homologyπ n' := by
  dsimp only
  let S := adjacentColumnTotalShortComplex K p
  let hS := adjacentColumnTotalShortExact K p
  let n := p + q
  let n' := p + 1 + q
  let x₃ := a ≫ singleColumnTotalι K p q n rfl
  let x₂ := x₃ ≫ adjacentColumnTotalSection K p n
  let x₁ := x₂ ≫ S.X₂.d n n' ≫ adjacentColumnTotalRetraction K p n'
  have hx₃ : x₃ ≫ S.X₃.d n n' = 0 := by
    simpa only [x₃, S, n, n', adjacentColumnTotalShortComplex,
      Category.assoc] using singleColumnTotalι_cycle K p q a ha
  have hx₂ : x₂ ≫ S.g.f n = x₃ := by
    have hs := (adjacentColumnTotalDegreewiseSplitting K p n).s_g
    exact (congrArg (fun z ↦ x₃ ≫ z) hs).trans (Category.comp_id x₃)
  have hy₃ : x₂ ≫ S.X₂.d n n' ≫ S.g.f n' = 0 := by
    calc
      _ = x₂ ≫ (S.g.f n ≫ S.X₃.d n n') :=
        congrArg (fun z ↦ x₂ ≫ z) (S.g.comm n n').symm
      _ = (x₂ ≫ S.g.f n) ≫ S.X₃.d n n' :=
        (Category.assoc x₂ (S.g.f n) (S.X₃.d n n')).symm
      _ = x₃ ≫ S.X₃.d n n' :=
        congrArg (fun z ↦ z ≫ S.X₃.d n n') hx₂
      _ = 0 := hx₃
  have hx₁ : x₁ ≫ S.f.f n' = x₂ ≫ S.X₂.d n n' := by
    let s := adjacentColumnTotalDegreewiseSplitting K p n'
    let y := x₂ ≫ S.X₂.d n n'
    dsimp [x₁]
    have hid := s.id
    have hy : y ≫ S.g.f n' = 0 := hy₃
    have hyg : y ≫ (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
        (ComplexShape.up ℤ) n')).g = 0 := hy
    have hy' : y ≫ ((S.map (HomologicalComplex.eval AddCommGrpCat.{w}
        (ComplexShape.up ℤ) n')).g ≫ s.s) = 0 := by
      rw [← Category.assoc, hyg, zero_comp]
    change y ≫ s.r ≫
      ((S.map (HomologicalComplex.eval AddCommGrpCat.{w}
        (ComplexShape.up ℤ) n')).f) = y
    symm
    calc
      y = y ≫ 𝟙 _ := (Category.comp_id y).symm
      _ = y ≫ (s.r ≫ (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).f +
          (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).g ≫ s.s) :=
        congrArg (fun z ↦ y ≫ z) hid.symm
      _ = y ≫ (s.r ≫ (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).f) +
          y ≫ ((S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).g ≫ s.s) :=
        Preadditive.comp_add _ _ _ y _ _
      _ = y ≫ (s.r ≫ (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).f) + 0 := by
        rw [hy']
      _ = y ≫ s.r ≫ (S.map (HomologicalComplex.eval AddCommGrpCat.{w}
            (ComplexShape.up ℤ) n')).f := by
        rw [add_zero, Category.assoc]
  have hδ := hS.δ_eq n n' (by dsimp [n, n']; omega)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (p + 1 + 1 + q)
      ((ComplexShape.up ℤ).next_eq' (by dsimp [n']; omega))
  have hx₁g : x₁ ≫
      (adjacentColumnTotalShortComplex K (p + 1)).g.f n' =
      a ≫ (K.d p (p + 1)).f q ≫
        singleColumnTotalι K (p + 1) q n' (by dsimp [n']) := by
    dsimp only [x₁, x₂, x₃, n, n', S]
    simpa only [Category.assoc, adjacentColumnTotalShortComplex] using
      congrArg (fun z ↦ a ≫ z)
        (singleColumnTotalι_section_d_retraction_projection K p q)
  let T := (singleColumnBicomplex K (p + 1)).total (ComplexShape.up ℤ)
  let b := a ≫ (K.d p (p + 1)).f q ≫
    singleColumnTotalι K (p + 1) q n' (by dsimp [n'])
  have hb : b ≫ T.d n' (p + 1 + 1 + q) = 0 := by
    simpa only [b, T, n', Category.assoc] using singleColumnTotalι_cycle K (p + 1) q
      (a ≫ (K.d p (p + 1)).f q) (by
        rw [Category.assoc, K.d_comm, reassoc_of% ha]
        simp)
  have hc : (x₁ ≫
      (adjacentColumnTotalShortComplex K (p + 1)).g.f n') ≫
      T.d n' (p + 1 + 1 + q) = 0 := by
    rw [hx₁g]
    exact hb
  change (S.X₃.liftCycles x₃ n' _ hx₃ ≫ S.X₃.homologyπ n ≫
      hS.δ n n' _) ≫ HomologicalComplex.homologyMap
        (adjacentColumnTotalShortComplex K (p + 1)).g n' = _
  rw [hδ]
  rw [Category.assoc]
  erw [HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  have hlift : T.liftCycles
      (x₁ ≫ (adjacentColumnTotalShortComplex K (p + 1)).g.f n')
        (p + 1 + 1 + q) ((ComplexShape.up ℤ).next_eq' (by dsimp [n']; omega)) hc =
      T.liftCycles b (p + 1 + 1 + q)
        ((ComplexShape.up ℤ).next_eq' (by dsimp [n']; omega)) hb := by
    rw [← cancel_mono (T.iCycles n')]
    simp only [HomologicalComplex.liftCycles_i]
    exact hx₁g
  simpa only [T, b, S, adjacentColumnTotalShortComplex] using
    congrArg (fun z ↦ z ≫ T.homologyπ n') hlift

private lemma eqToHom_comp₃ {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ : D} (h₀₁ : X₀ = X₁) (h₁₂ : X₁ = X₂)
    (h₂₃ : X₂ = X₃) (h₀₃ : X₀ = X₃) :
    eqToHom h₀₁ ≫ eqToHom h₁₂ ≫ eqToHom h₂₃ = eqToHom h₀₃ := by
  subst X₁
  subst X₂
  subst X₃
  simp

private lemma singleColumnShift_component (p q : ℤ) :
    (singleColumnXIso K p p rfl).inv.f q ≫
        ((singleColumnShiftIso K p).hom.f p).f q ≫
        ((singleZeroBicomplex (K.X p)).shiftFunctor₁XXIso
          p (-p) 0 (by omega) q).hom =
      (singleZeroXIso (K.X p) 0 rfl).inv.f q := by
  dsimp [singleColumnShiftIso, singleColumnXIso, singleZeroXIso,
    HomologicalComplex₂.shiftFunctor₁XXIso,
    CochainComplex.singleFunctors]
  simp [HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  rfl

private lemma singleZeroTotal_shift_component
    (A : CochainComplex AddCommGrpCat.{w} ℤ) (p q : ℤ) :
    (singleZeroTotalXIso A q).inv ≫
        (((singleZeroBicomplex A).total (ComplexShape.up ℤ)).XIsoOfEq
          (show p + q + -p = q by omega)).inv ≫
        (singleZeroTotalXIso A (p + q + -p)).hom =
      (A.XIsoOfEq (show p + q + -p = q by omega)).inv := by
  let φ := (singleZeroTotalIso A).hom
  have h := HomologicalComplex.XIsoOfEq_inv_naturality φ
    (show p + q + -p = q by omega)
  change (singleZeroTotalXIso A q).inv ≫
      _ ≫ φ.f (p + q + -p) = _
  calc
    _ = (singleZeroTotalXIso A q).inv ≫
        (φ.f q ≫ (A.XIsoOfEq (show p + q + -p = q by omega)).inv) := by
      rw [h]
    _ = _ := by
      dsimp [φ, singleZeroTotalIso]
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The canonical inclusion of a bidegree term into a single-column total complex is the
inverse of the standard shifted-column component isomorphism. -/
lemma singleColumnTotalι_comp_singleColumnTotalIso_hom (p q : ℤ) :
    singleColumnTotalι K p q (p + q) rfl ≫
        (singleColumnTotalIso K p).hom.f (p + q) =
      (CochainComplex.shiftFunctorObjXIso (K.X p) (-p) (p + q) q
        (by omega)).inv := by
  dsimp only [singleColumnTotalι, singleColumnTotalIso, Iso.trans_hom,
    HomologicalComplex.comp_f]
  simp only [Category.assoc]
  erw [HomologicalComplex₂.ιTotal_map_assoc]
  erw [HomologicalComplex₂.ι_totalShift₁Iso_hom_f_assoc
    (singleZeroBicomplex (K.X p)) (-p) p q (p + q) rfl 0 (by omega)
      q (by omega)]
  slice_lhs 1 3 =>
    exact singleColumnShift_component K p q
  dsimp [CochainComplex.shiftFunctorObjXIso]
  change (singleZeroTotalXIso (K.X p) q).inv ≫
      (((singleZeroBicomplex (K.X p)).total
        (ComplexShape.up ℤ)).XIsoOfEq
          (show p + q + -p = q by omega)).inv ≫
      (singleZeroTotalXIso (K.X p) (p + q + -p)).hom =
    ((K.X p).XIsoOfEq (show p + q + -p = q by omega)).inv
  exact singleZeroTotal_shift_component (K.X p) p q

/-- A cocycle representative is unchanged after passing from a single-column total complex to
the shifted column and then to column homology. -/
lemma singleColumnTotal_liftCycles_homologyIso {A : AddCommGrpCat.{w}}
    (p q : ℤ) (a : A ⟶ (K.X p).X q)
    (ha : a ≫ (K.X p).d q (q + 1) = 0) :
    let T := (singleColumnBicomplex K p).total (ComplexShape.up ℤ)
    T.liftCycles (a ≫ singleColumnTotalι K p q (p + q) rfl)
        (p + 1 + q) ((ComplexShape.up ℤ).next_eq' (by dsimp; omega))
        (singleColumnTotalι_cycle K p q a ha) ≫
      T.homologyπ (p + q) ≫
      HomologicalComplex.homologyMap (singleColumnTotalIso K p).hom (p + q) ≫
      (columnShiftHomologyIso K p q).hom =
    (K.X p).liftCycles a (q + 1) ((ComplexShape.up ℤ).next_eq' rfl) ha ≫
      (K.X p).homologyπ q := by
  dsimp only
  let T := (singleColumnBicomplex K p).total (ComplexShape.up ℤ)
  let S := (K.X p)⟦-p⟧
  let f := a ≫ (CochainComplex.shiftFunctorObjXIso
    (K.X p) (-p) (p + q) q (by omega)).inv
  have hmap : a ≫ singleColumnTotalι K p q (p + q) rfl ≫
      (singleColumnTotalIso K p).hom.f (p + q) = f := by
    simpa only [f, Category.assoc] using
      congrArg (fun z ↦ a ≫ z)
        (singleColumnTotalι_comp_singleColumnTotalIso_hom K p q)
  have hf : f ≫ S.d (p + q) (p + 1 + q) = 0 := by
    rw [← hmap]
    let b := a ≫ singleColumnTotalι K p q (p + q) rfl
    let e := (singleColumnTotalIso K p).hom
    have hb : b ≫ T.d (p + q) (p + 1 + q) = 0 := by
      simpa only [b, T, Category.assoc] using singleColumnTotalι_cycle K p q a ha
    change (b ≫ e.f (p + q)) ≫ S.d (p + q) (p + 1 + q) = 0
    calc
      _ = b ≫ (e.f (p + q) ≫ S.d (p + q) (p + 1 + q)) :=
        Category.assoc _ _ _
      _ = b ≫ (T.d (p + q) (p + 1 + q) ≫ e.f (p + 1 + q)) :=
        congrArg (fun z ↦ b ≫ z) (e.comm (p + q) (p + 1 + q))
      _ = (b ≫ T.d (p + q) (p + 1 + q)) ≫ e.f (p + 1 + q) :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hb, zero_comp]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  have hc : (a ≫ singleColumnTotalι K p q (p + q) rfl ≫
      (singleColumnTotalIso K p).hom.f (p + q)) ≫
      S.d (p + q) (p + 1 + q) = 0 := by
    rw [hmap]
    exact hf
  have hlift : S.liftCycles
      (a ≫ singleColumnTotalι K p q (p + q) rfl ≫
        (singleColumnTotalIso K p).hom.f (p + q))
        (p + 1 + q) ((ComplexShape.up ℤ).next_eq' (by dsimp; omega)) hc =
      S.liftCycles f (p + 1 + q)
        ((ComplexShape.up ℤ).next_eq' (by dsimp; omega)) hf := by
    rw [← cancel_mono (S.iCycles (p + q))]
    simp only [HomologicalComplex.liftCycles_i]
    exact hmap
  calc
    _ = S.liftCycles f (p + 1 + q)
          ((ComplexShape.up ℤ).next_eq' (by dsimp; omega)) hf ≫
        S.homologyπ (p + q) ≫ (columnShiftHomologyIso K p q).hom := by
      simpa only [S, Category.assoc] using congrArg
        (fun z ↦ z ≫ S.homologyπ (p + q) ≫
          (columnShiftHomologyIso K p q).hom) hlift
    _ = _ := by
      rw [CochainComplex.liftCycles_shift_homologyπ_assoc (K.X p) f
        (p + 1 + q) ((ComplexShape.up ℤ).next_eq' (by dsimp; omega)) hf
        q (by omega) (q + 1) ((ComplexShape.up ℤ).next_eq' rfl)
        (columnShiftHomologyIso K p q).hom]
      let e := columnShiftHomologyIso K p q
      let xiso := CochainComplex.shiftFunctorObjXIso
        (K.X p) (-p) (p + q) q (by omega)
      change (K.X p).liftCycles (f ≫ xiso.hom) (q + 1) _ _ ≫
        (K.X p).homologyπ q ≫ e.inv ≫ e.hom = _
      slice_lhs 3 4 => rw [e.inv_hom_id]
      simp only [Category.comp_id]
      have hfa : f ≫ xiso.hom = a := by
        dsimp [f, xiso]
        simp
      have hfa_cycle : (f ≫ xiso.hom) ≫
          (K.X p).d q (q + 1) = 0 := by
        rw [hfa]
        exact ha
      have hlift' : (K.X p).liftCycles (f ≫ xiso.hom) (q + 1)
          ((ComplexShape.up ℤ).next_eq' rfl) hfa_cycle =
          (K.X p).liftCycles a (q + 1)
            ((ComplexShape.up ℤ).next_eq' rfl) ha := by
        rw [← cancel_mono ((K.X p).iCycles q)]
        simp only [HomologicalComplex.liftCycles_i]
        exact hfa
      simpa only using congrArg
        (fun z ↦ z ≫ (K.X p).homologyπ q) hlift'

private lemma adjacentColumnConnecting_eq_horizontalHomologyMap (p q : ℤ) :
    (columnShiftHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap (singleColumnTotalIso K p).inv (p + q) ≫
        (adjacentColumnTotalShortExact K p).δ
          (p + q) (p + 1 + q) (by dsimp; omega) ≫
        HomologicalComplex.homologyMap
          (adjacentColumnTotalShortComplex K (p + 1)).g (p + 1 + q) ≫
        HomologicalComplex.homologyMap
          (singleColumnTotalIso K (p + 1)).hom (p + 1 + q) ≫
        (columnShiftHomologyIso K (p + 1) q).hom =
      HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
  let C₀ := K.X p
  let C₁ := K.X (p + 1)
  let a := C₀.iCycles q
  have ha : a ≫ C₀.d q (q + 1) = 0 := C₀.iCycles_d q (q + 1)
  let T₀ := (singleColumnBicomplex K p).total (ComplexShape.up ℤ)
  let T₁ := (singleColumnBicomplex K (p + 1)).total (ComplexShape.up ℤ)
  let r₀ := T₀.liftCycles
    (a ≫ singleColumnTotalι K p q (p + q) rfl)
      (p + 1 + q) ((ComplexShape.up ℤ).next_eq' (by dsimp; omega))
      (singleColumnTotalι_cycle K p q a ha) ≫ T₀.homologyπ (p + q)
  have ha₁ : (a ≫ (K.d p (p + 1)).f q) ≫
      C₁.d q (q + 1) = 0 := by
    dsimp [a, C₀, C₁]
    rw [Category.assoc, K.d_comm]
    rw [← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]
  let r₁ := T₁.liftCycles
    (a ≫ (K.d p (p + 1)).f q ≫
      singleColumnTotalι K (p + 1) q (p + 1 + q) (by omega))
      (p + 1 + 1 + q)
      ((ComplexShape.up ℤ).next_eq' (by dsimp; omega))
      (singleColumnTotalι_cycle K (p + 1) q
        (a ≫ (K.d p (p + 1)).f q) ha₁) ≫
      T₁.homologyπ (p + 1 + q)
  have halift : C₀.liftCycles a (q + 1)
      ((ComplexShape.up ℤ).next_eq' rfl) ha = 𝟙 _ := by
    rw [← cancel_mono (C₀.iCycles q)]
    simpa only [a, HomologicalComplex.liftCycles_i] using
      (Category.id_comp (C₀.iCycles q)).symm
  have hrep₀ : r₀ ≫
      HomologicalComplex.homologyMap (singleColumnTotalIso K p).hom (p + q) ≫
      (columnShiftHomologyIso K p q).hom = C₀.homologyπ q := by
    have h := singleColumnTotal_liftCycles_homologyIso K p q a ha
    rw [halift, Category.id_comp] at h
    simpa only [r₀, T₀, C₀, Category.assoc] using h
  have hsource : C₀.homologyπ q ≫
      (columnShiftHomologyIso K p q).inv ≫
      HomologicalComplex.homologyMap (singleColumnTotalIso K p).inv (p + q) = r₀ := by
    calc
      _ = (r₀ ≫ HomologicalComplex.homologyMap
            (singleColumnTotalIso K p).hom (p + q) ≫
          (columnShiftHomologyIso K p q).hom) ≫
          (columnShiftHomologyIso K p q).inv ≫
          HomologicalComplex.homologyMap
            (singleColumnTotalIso K p).inv (p + q) := by rw [hrep₀]
      _ = r₀ := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        let E := HomologicalComplex.homologyMapIso
          (singleColumnTotalIso K p) (p + q)
        change r₀ ≫ E.hom ≫ E.inv = r₀
        calc
          _ = r₀ ≫ (E.hom ≫ E.inv) := Category.assoc _ _ _
          _ = r₀ ≫ 𝟙 _ := congrArg (fun z ↦ r₀ ≫ z) E.hom_inv_id
          _ = r₀ := Category.comp_id _
  have hconnect : r₀ ≫ (adjacentColumnTotalShortExact K p).δ
        (p + q) (p + 1 + q) (by dsimp; omega) ≫
      HomologicalComplex.homologyMap
        (adjacentColumnTotalShortComplex K (p + 1)).g (p + 1 + q) = r₁ := by
    simpa only [r₀, r₁, T₀, T₁, a, C₀, C₁,
      adjacentColumnTotalShortComplex, Category.assoc] using
      adjacentColumnConnecting_representative K p q a ha
  have hrep₁ : r₁ ≫ HomologicalComplex.homologyMap
        (singleColumnTotalIso K (p + 1)).hom (p + 1 + q) ≫
      (columnShiftHomologyIso K (p + 1) q).hom =
      C₁.liftCycles (a ≫ (K.d p (p + 1)).f q) (q + 1)
        ((ComplexShape.up ℤ).next_eq' rfl) ha₁ ≫ C₁.homologyπ q := by
    simpa only [r₁, T₁, C₁, Category.assoc] using
      singleColumnTotal_liftCycles_homologyIso K (p + 1) q
        (a ≫ (K.d p (p + 1)).f q) ha₁
  have hmap : C₁.liftCycles (a ≫ (K.d p (p + 1)).f q) (q + 1)
        ((ComplexShape.up ℤ).next_eq' rfl) ha₁ ≫ C₁.homologyπ q =
      C₀.homologyπ q ≫
        HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
    rw [HomologicalComplex.homologyπ_naturality]
    have hcycles := HomologicalComplex.liftCycles_comp_cyclesMap
      (K := C₀) (L := C₁) (C₀.iCycles q)
      (q + 1) ((ComplexShape.up ℤ).next_eq' rfl)
      (C₀.iCycles_d q (q + 1)) (K.d p (p + 1))
    rw [halift, Category.id_comp] at hcycles
    simpa only [C₀, C₁, a, HomologicalComplex.liftCycles_i,
      Category.id_comp] using
      congrArg (fun z ↦ z ≫ C₁.homologyπ q) hcycles.symm
  rw [← cancel_epi (C₀.homologyπ q)]
  rw [reassoc_of% hsource, reassoc_of% hconnect]
  exact hrep₁.trans hmap

/-- Under the initial-page column-homology isomorphisms, the first spectral-sequence
differential is the map on vertical homology induced by the horizontal bicomplex differential. -/
lemma columnFilteredInitialPage_d_eq_horizontalHomologyMap (p q : ℤ) :
    ((columnFilteredTotalSpectralSequence K).page 2).d
        (p, q) (p + 1, q) ≫
      (columnFilteredInitialPageColumnHomologyIso K (p + 1) q).hom =
    (columnFilteredInitialPageColumnHomologyIso K p q).hom ≫
      HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
  rw [columnFilteredInitialPage_d_eq_connecting]
  rw [adjacentColumnConnecting_eq_horizontalHomologyMap]

end HomologicalComplex₂
