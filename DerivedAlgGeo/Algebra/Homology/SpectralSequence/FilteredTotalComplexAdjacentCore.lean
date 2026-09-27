/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Embedding.StupidTruncGE
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.SingleZeroTotal
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Adjacent columns of a total bicomplex

Column tails and supported single columns exist with zero morphisms and a zero
object. Their total-complex comparisons are independent of spectral pages.

## Main definitions and results

* `HomologicalComplex₂.truncatedBicomplex` and
  `HomologicalComplex₂.singleColumnBicomplex` give the tail and new column;
  `HomologicalComplex₂.singleColumnTotalIso` computes its signed total.
* `HomologicalComplex₂.adjacentColumnTotalShortComplex` is the short complex
  of consecutive tail totals and their newly added single column.
* `HomologicalComplex₂.adjacentColumnConeToShift` maps its cone to the shifted
  column; `adjacentColumnTotalShortExact` proves exactness under an abelian
  hypothesis.
* `HomologicalComplex₂.adjacentColumnConeMap_quasiIso` transports a column
  quasi-isomorphism across the cone comparison.

## Implementation notes

The short complex assumes total existence only for the two neighboring tails;
the supported single-column total is constructed directly. A degreewise
splitting proves exactness in an abelian category. The cone map itself needs
binary biproducts, while its quasi-isomorphism uses the abelian hypothesis.

## References

The proofs use Mathlib's `HomologicalComplex₂.total`,
`CochainComplex.mappingCone`, and
`CochainComplex.mappingCone.quasiIso_descShortComplex`.
-/

namespace HomologicalComplex₂

open CategoryTheory Category Limits
open HomologicalComplex (stupidTruncGEXIso stupidTruncXIso_eq_stupidTruncGEXIso)

universe u v w

section Zero

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

noncomputable def truncatedBicomplex (p : ℤ) :
    HomologicalComplex₂ C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE p)

noncomputable def singleColumnBicomplex (p : ℤ) :
    HomologicalComplex₂ C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) p).obj (K.X p)

noncomputable def singleColumnXIso (p i : ℤ) (hi : i = p) :
    (singleColumnBicomplex K p).X i ≅ K.X p := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (K.X p)

/-- Proof irrelevance for the supported-degree witness permits this cancellation
inside the diagonal splitting. -/
@[reassoc (attr := simp)]
lemma singleColumnXIso_hom_inv_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).hom.f j ≫
      (singleColumnXIso K p i hi').inv.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

/-- The reverse cancellation uses the same proof-irrelevant support witness. -/
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
    ShortComplex (HomologicalComplex₂ C
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

/-- Cancellation is independent of the chosen proof that the index lies in the tail. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_inv_hom_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).inv.f j ≫
      (stupidTruncGEXIso K p i hi').hom.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).inv_hom_id,
    HomologicalComplex.id_f]

/-- The reverse cancellation also ignores the proof of tail membership. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_hom_inv_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).hom.f j ≫
      (stupidTruncGEXIso K p i hi').inv.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).hom_inv_id,
    HomologicalComplex.id_f]

variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- Apply the map on retained degrees and zero elsewhere. This needs no additive structure. -/
noncomputable def truncatedBicomplexMap (f : K ⟶ L) (p : ℤ) :
    truncatedBicomplex K p ⟶ truncatedBicomplex L p :=
  HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE p)

/-- The supported degree carries the original map; zero objects force every other component. -/
noncomputable def singleColumnBicomplexMap (f : K ⟶ L) (p : ℤ) :
    singleColumnBicomplex K p ⟶ singleColumnBicomplex L p :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) p).map (f.f p)

end Zero

section Hom

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Used by diagonal-coproduct splittings before any preadditive structure is available. -/
@[reassoc (attr := simp)]
lemma complexIso_inv_hom_f {A B : CochainComplex C ℤ}
    (e : A ≅ B) (j : ℤ) : e.inv.f j ≫ e.hom.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

/-- This direction is needed when transporting maps across the supported-column equivalence. -/
@[reassoc (attr := simp)]
lemma complexIso_hom_inv_f {A B : CochainComplex C ℤ}
    (e : A ≅ B) (j : ℤ) : e.hom.f j ≫ e.inv.f j = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

end Hom

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- This shift moves the supported degree to zero before applying the signed total comparison. -/
noncomputable def singleColumnShiftIso (p : ℤ) :
    singleColumnBicomplex K p ≅
      (shiftFunctor₁ C (-p)).obj
        (singleZeroBicomplex (K.X p)) :=
  (((CochainComplex.singleFunctors
    (CochainComplex C ℤ)).shiftIso
      (-p) p 0 (by omega)).app (K.X p)).symm

/-- Transporting the degree-zero total across the shift avoids category-wide coproducts. -/
noncomputable instance singleColumnHasTotal (p : ℤ) :
    (singleColumnBicomplex K p).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_iso (singleColumnShiftIso K p).symm (ComplexShape.up ℤ)

/-- The shifted degree-zero model fixes the total differential sign as well as the degree shift. -/
noncomputable def singleColumnTotalIso (p : ℤ) :
    (singleColumnBicomplex K p).total (ComplexShape.up ℤ) ≅
      (K.X p)⟦-p⟧ :=
  HomologicalComplex₂.total.mapIso (singleColumnShiftIso K p)
      (ComplexShape.up ℤ) ≪≫
    (singleZeroBicomplex (K.X p)).totalShift₁Iso (-p) ≪≫
    (shiftFunctor (CochainComplex C ℤ) (-p)).mapIso
      (singleZeroTotalIso (K.X p))

/-- Only neighboring tail totals are assumed; the quotient total comes from
the single-column construction. -/
noncomputable def adjacentColumnTotalShortComplex (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (total.map (adjacentColumnInclusion K p) (ComplexShape.up ℤ))
    (total.map (adjacentColumnProjection K p) (ComplexShape.up ℤ)) (by
      rw [← total.map_comp]
      rw [show adjacentColumnInclusion K p ≫ adjacentColumnProjection K p = 0 from
        (adjacentColumnBicomplexShortComplex K p).zero]
      apply HomologicalComplex.Hom.ext
      funext n
      apply total.hom_ext
      intro i j hij
      rw [ιTotal_map]
      simp)

noncomputable def adjacentColumnTotalRetraction (p n : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)] :
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

noncomputable def adjacentColumnTotalSection (p n : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)] :
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

/-- Diagonal coproduct injections split the sequence degreewise without an
abelian hypothesis. -/
noncomputable def adjacentColumnTotalDegreewiseSplitting (p n : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    (((adjacentColumnTotalShortComplex K p).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) where
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
      apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
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
      simp [adjacentColumnProjection, singleColumnBicomplex]
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
      apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
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
        apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega


variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- Mathlib’s shift isomorphism is natural; its inverse supplies this square without
a component calculation. -/
@[reassoc]
lemma singleColumnShiftIso_naturality (f : K ⟶ L) (p : ℤ) :
    singleColumnBicomplexMap f p ≫ (singleColumnShiftIso L p).hom =
      (singleColumnShiftIso K p).hom ≫
        (shiftFunctor₁ C (-p)).map
          (singleZeroBicomplexMap (f.f p)) := by
  exact ((CochainComplex.singleFunctors
    (CochainComplex C ℤ)).shiftIso
      (-p) p 0 (by omega)).inv.naturality (f.f p)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compose shifted-total naturality with the single-zero comparison. This
compatibility is used in finite-strip induction. -/
@[reassoc]
lemma singleColumnTotalIso_naturality (f : K ⟶ L) (p : ℤ) :
    total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ) ≫
        (singleColumnTotalIso L p).hom =
      (singleColumnTotalIso K p).hom ≫ (f.f p)⟦-p⟧' := by
  dsimp only [singleColumnTotalIso, Iso.trans_hom]
  simp only [HomologicalComplex₂.total.mapIso_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Category.assoc, ← total.map_comp]
  rw [singleColumnShiftIso_naturality]
  rw [total.map_comp]
  rw [Category.assoc]
  rw [HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc]
  rw [← Functor.map_comp]
  rw [singleZeroTotalIso_naturality]
  rw [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The three maps commute using neighboring tail totals on each side; no
exactness premise is needed. -/
noncomputable def adjacentColumnTotalShortComplexMap (f : K ⟶ L) (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    adjacentColumnTotalShortComplex K p ⟶ adjacentColumnTotalShortComplex L p where
  τ₁ := total.map (truncatedBicomplexMap f (p + 1)) (ComplexShape.up ℤ)
  τ₂ := total.map (truncatedBicomplexMap f p) (ComplexShape.up ℤ)
  τ₃ := total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ)
  comm₁₂ := by
    dsimp [adjacentColumnTotalShortComplex, adjacentColumnBicomplexShortComplex]
    rw [← total.map_comp, ← total.map_comp]
    congr 1
    simpa only [adjacentColumnInclusion, truncatedBicomplexMap] using
      (HomologicalComplex.stupidTruncGEMap_naturality f p (p + 1) (by omega))
  comm₂₃ := by
    dsimp [adjacentColumnTotalShortComplex, adjacentColumnBicomplexShortComplex]
    rw [← total.map_comp, ← total.map_comp]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = p
    · subst i
      let eK := K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
        (i := 0) (i' := p) (by simp [ComplexShape.embeddingUpIntGE])
      let eL := L.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
        (i := 0) (i' := p) (by simp [ComplexShape.embeddingUpIntGE])
      let sK := singleColumnXIso K p p rfl
      let sL := singleColumnXIso L p p rfl
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp [adjacentColumnProjection]
      rw [dif_pos rfl, dif_pos rfl]
      simp only [Category.id_comp]
      simp only [Category.assoc]
      change (truncatedBicomplexMap f p).f p ≫ eL.hom ≫ sL.inv =
        eK.hom ≫ sK.inv ≫ (singleColumnBicomplexMap f p).f p
      rw [← cancel_mono sL.hom]
      simp only [Category.assoc, sL.inv_hom_id, Category.comp_id]
      dsimp [truncatedBicomplexMap, truncatedBicomplex, singleColumnBicomplexMap, eK, eL]
      rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
      rw [cancel_epi (K.stupidTruncXIso
        (ComplexShape.embeddingUpIntGE p) (i := 0) (i' := p)
          (by simp [ComplexShape.embeddingUpIntGE])).hom]
      dsimp [sK, sL, singleColumnXIso, singleColumnBicomplex]
      change f.f p =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (K.X p)).inv ≫
          ((HomologicalComplex.single (CochainComplex C ℤ)
            (ComplexShape.up ℤ) p).map (f.f p)).f p ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (L.X p)).hom
      rw [HomologicalComplex.single_map_f_self]
      simp
    · apply IsZero.eq_of_tgt
      apply HomologicalComplex.isZero_single_obj_X
      exact hi

end Preadditive

section ConeMap

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- A homotopy cofiber is needed only for this inclusion; the target uses
the signed single-column total comparison. -/
noncomputable def adjacentColumnConeToShift (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)]
    [HomologicalComplex.HasHomotopyCofiber
      (adjacentColumnTotalShortComplex K p).f] :
    CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f ⟶
      (K.X p)⟦-p⟧ :=
  CochainComplex.mappingCone.desc _ 0
      (adjacentColumnTotalShortComplex K p).g (by simp) ≫
    (singleColumnTotalIso K p).hom

end ConeMap

section ConeMapNaturality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- The natural square for the adjacent-tail inclusions supplies the two
component maps and commutativity witness required by `mappingCone.map`.
This construction needs binary biproducts but no abelian hypothesis. -/
noncomputable def adjacentColumnConeMap (f : K ⟶ L) (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f ⟶
      CochainComplex.mappingCone (adjacentColumnTotalShortComplex L p).f :=
  CochainComplex.mappingCone.map _ _
    (adjacentColumnTotalShortComplexMap f p).τ₁
    (adjacentColumnTotalShortComplexMap f p).τ₂
    (adjacentColumnTotalShortComplexMap f p).comm₁₂.symm

end ConeMapNaturality

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- Degreewise splitting lifts to exactness in an abelian category, with no horizontal bound. -/
theorem adjacentColumnTotalShortExact (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    (adjacentColumnTotalShortComplex K p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact
    (adjacentColumnTotalShortComplex K p) (fun n ↦
      let s := adjacentColumnTotalDegreewiseSplitting K p n
      { mono_f := s.mono_f
        epi_g := s.epi_g
        exact := s.exact })

noncomputable instance adjacentColumnConeToShift_quasiIso (p : ℤ)
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (adjacentColumnConeToShift K p) := by
  letI : QuasiIso
      (CochainComplex.mappingCone.descShortComplex
        (adjacentColumnTotalShortComplex K p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (adjacentColumnTotalShortExact K p)
  change QuasiIso
    (CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex K p) ≫
      (singleColumnTotalIso K p).hom)
  infer_instance

end Abelian

section ConeQuasiIso

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- The shifted single-zero comparison is natural in the vertical column map,
so a column quasi-isomorphism remains one after single-column totalization. -/
lemma singleColumnTotalMap_quasiIso (f : K ⟶ L) (p : ℤ)
    (h : QuasiIso (f.f p)) :
    QuasiIso (total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ)) := by
  letI : QuasiIso (f.f p) := h
  rw [← quasiIso_iff_comp_right _ (singleColumnTotalIso L p).hom]
  rw [singleColumnTotalIso_naturality]
  infer_instance

/-- Compare each cone with its single-column quotient using
`mappingCone.descShortComplex`. Degreewise splitting makes those comparison
maps quasi-isomorphisms; naturality and the given column quasi-isomorphism
then make the induced cone map a quasi-isomorphism. -/
lemma adjacentColumnConeMap_quasiIso (f : K ⟶ L) (p : ℤ)
    (h : QuasiIso (f.f p))
    [(truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex K (p + 1)).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ)]
    [(truncatedBicomplex L (p + 1)).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (adjacentColumnConeMap f p) := by
  have h₃ : QuasiIso (adjacentColumnTotalShortComplexMap f p).τ₃ := by
    exact singleColumnTotalMap_quasiIso f p h
  letI : QuasiIso (adjacentColumnTotalShortComplexMap f p).τ₃ := h₃
  letI : QuasiIso (CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex L p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (adjacentColumnTotalShortExact L p)
  letI : QuasiIso (CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex K p)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (adjacentColumnTotalShortExact K p)
  rw [← quasiIso_iff_comp_right _
    (CochainComplex.mappingCone.descShortComplex
      (adjacentColumnTotalShortComplex L p))]
  dsimp [adjacentColumnConeMap]
  rw [CochainComplex.mappingCone.map_descShortComplex]
  infer_instance

end ConeQuasiIso

end HomologicalComplex₂
