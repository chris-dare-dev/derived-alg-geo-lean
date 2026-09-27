/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplex
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplexAdjacentCore
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Spectral pages of a column-filtered total complex

The generic adjacent-column construction is in `FilteredTotalComplexAdjacentCore`.
Here it is specialized to `AddCommGrpCat` and compared with the filtered
spectral object's adjacent layers and connecting maps.

## Main definitions and results

* `HomologicalComplex₂.columnFilteredInitialPageColumnHomologyIso` identifies
  the initial-page object with vertical column homology.
* `HomologicalComplex₂.columnFilteredFirstPage_d_eq` computes the initial
  differential from the horizontal bicomplex differential.

## Implementation notes

The comparison transports the generic adjacent cone through filtration-stage
isos, then tracks the signed total convention through connecting morphisms.
The spectral-page statements here specialize to abelian groups.

## References

The proof uses Mathlib's filtered `SpectralObject`, mapping-cone triangles,
and homology connecting maps, together with the generic adjacent-column core.
-/

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe w


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

/-- Reindexing filtration stage `-p` gives precisely the tail beginning at
`p`; the comparison commutes with the adjacent-stage inclusion by the
naturality of nested stupid-truncation maps. -/
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

/-- Invert the preceding adjacent-stage square. Cancellation by the stage
isomorphism turns its commutative square into this inverse orientation. -/
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
    adjacentColumnTotalShortComplex, adjacentColumnInclusion, truncatedBicomplex]
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
      CochainComplex.mappingConeCompTriangle_obj₃, Iso.inv_hom_id_app]
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

/-- Apply the homology functor to the cone-triangle isomorphism induced by
the filtration-stage square. Its third morphism gives the connecting-map
square after the shift-map comparison. -/
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

/-- The adjacent-layer cone comparison factors through the short-complex
cone projection and the single-column total isomorphism. Cancel that final
isomorphism after applying homology to expose the short-complex map. -/
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
