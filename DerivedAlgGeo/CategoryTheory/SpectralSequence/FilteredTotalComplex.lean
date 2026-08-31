/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredComplexSpectralObject
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.SpectralObject.FirstPage
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Column-filtered total complexes

For a cohomological bicomplex, the stupid truncations in the first degree form the usual
decreasing column filtration.  Reindexing the truncation bound by `p ↦ -p` makes this an
increasing filtration indexed by `ℤ`.

The pinned Mathlib revision constructs stupid truncations, but deliberately leaves their
inclusion maps as a TODO.  We first supply the inclusion for the standard embedding of degrees
at least `p`, use its monicity to organize the maps between nested truncations, and then totalize.
-/

open CategoryTheory Category Limits

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The usual `E₂` cohomological spectral-sequence data, with filtration indices in `ℤ`
rather than `EInt`. -/
@[simps!]
def coreE₂CohomologicalInt :
    SpectralSequenceDataCore ℤ
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := pq.2 - r + 2
  i₁ pq := pq.2
  i₂ pq := pq.2 + 1
  i₃ r pq hr := pq.2 + r - 1
  le₀₁ r pq hr := by omega
  le₁₂ pq := by omega
  le₂₃ r pq hr := by omega
  hc := by rintro r pq _ rfl _; dsimp; omega
  hc₀₂ := by rintro r pq _ rfl _; dsimp; omega
  hc₁₃ := by rintro r pq _ rfl _; dsimp; omega
  antitone_i₀ := by intros; omega
  monotone_i₃ := by intros; omega
  i₀_prev := by rintro r r' pq _ rfl _ _; dsimp; omega
  i₃_next := by rintro r r' pq _ rfl _ _; dsimp; omega

instance : coreE₂CohomologicalInt.HasFirstPageComputation where
  hi₀₁ pq := by dsimp [coreE₂CohomologicalInt]; omega
  hi₂₃ pq := by dsimp [coreE₂CohomologicalInt]; omega

instance (E : SpectralObject C ℤ) : E.HasSpectralSequence coreE₂CohomologicalInt where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1 - r)) (by simp)

/-- The cohomological spectral-sequence coordinates for the increasing reindexing of a
decreasing column filtration.  At the initial page, `(p, q)` uses the adjacent filtration
stages `-p-1 ≤ -p`; their quotient is column `p`, and total degree `p+q` leaves vertical
degree `q`. -/
@[simps!]
def coreE₂ColumnFilteredCohomologicalInt :
    SpectralSequenceDataCore ℤ
      (fun r ↦ ComplexShape.up' (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := -pq.1 - r + 1
  i₁ pq := -pq.1 - 1
  i₂ pq := -pq.1
  i₃ r pq hr := -pq.1 + r - 2
  le₀₁ r pq hr := by omega
  le₁₂ pq := by omega
  le₂₃ r pq hr := by omega
  hc := by rintro r pq _ rfl _; dsimp; omega
  hc₀₂ := by rintro r pq _ rfl _; dsimp; omega
  hc₁₃ := by rintro r pq _ rfl _; dsimp; omega
  antitone_i₀ := by intros; omega
  monotone_i₃ := by intros; omega
  i₀_prev := by rintro r r' pq _ rfl _ _; dsimp; omega
  i₃_next := by rintro r r' pq _ rfl _ _; dsimp; omega

instance : coreE₂ColumnFilteredCohomologicalInt.HasFirstPageComputation where
  hi₀₁ pq := by dsimp [coreE₂ColumnFilteredCohomologicalInt]; omega
  hi₂₃ pq := by dsimp [coreE₂ColumnFilteredCohomologicalInt]; omega

instance (E : SpectralObject C ℤ) :
    E.HasSpectralSequence coreE₂ColumnFilteredCohomologicalInt where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r - 1, 2 - r)) (by simp)

end CategoryTheory.Abelian.SpectralObject

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

private noncomputable def geIndex (p i : ℤ) : ℕ := (i - p).toNat

private lemma geIndex_spec (p i : ℤ) (h : p ≤ i) :
    (ComplexShape.embeddingUpIntGE p).f (geIndex p i) = i := by
  change p + ((i - p).toNat : ℤ) = i
  rw [Int.toNat_of_nonneg (by omega)]
  omega

lemma stupidTrunc_d_eq (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ)
    {i j : ℤ} (hi : p ≤ i) (hj : p ≤ j) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).d i j =
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi)).hom ≫
        K.d i j ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (geIndex_spec p j hj)).inv := by
  change (((K.restriction (ComplexShape.embeddingUpIntGE p)).extend
    (ComplexShape.embeddingUpIntGE p)).d i j) = _
  rw [(K.restriction (ComplexShape.embeddingUpIntGE p)).extend_d_eq
      (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi) (geIndex_spec p j hj),
    K.restriction_d_eq (ComplexShape.embeddingUpIntGE p)
      (geIndex_spec p i hi) (geIndex_spec p j hj)]
  simp [stupidTruncXIso, restrictionXIso, Category.assoc]
  all_goals aesop

/-- The inclusion of the stupid truncation in degrees at least `p` into the original complex. -/
noncomputable def stupidTruncGEι (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE p) ⟶ K where
  f i := if hi : p ≤ i then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi)).hom
    else 0
  comm' i j hij := by
    by_cases hi : p ≤ i
    · have hj : p ≤ j := by
        have hij' : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        omega
      rw [dif_pos hi, dif_pos hj, stupidTrunc_d_eq K p hi hj]
      simp
    · apply IsZero.eq_of_src
      apply isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega

noncomputable instance stupidTruncGEι_f_mono
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p i : ℤ) :
    Mono ((stupidTruncGEι K p).f i) := by
  dsimp [stupidTruncGEι]
  split_ifs with hi
  · infer_instance
  · apply IsZero.mono
    apply isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

noncomputable instance stupidTruncGEι_mono
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    Mono (stupidTruncGEι K p) :=
  mono_of_mono_f _ (fun _ ↦ inferInstance)

/-- Inclusion between nested stupid truncations.  If `p ≤ q`, the terms in degrees at
least `q` form a subcomplex of the terms in degrees at least `p`. -/
noncomputable def stupidTruncGEMap (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q : ℤ) (hpq : p ≤ q) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE q) ⟶
      K.stupidTrunc (ComplexShape.embeddingUpIntGE p) where
  f i := if hi : q ≤ i then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE q) (geIndex_spec q i hi)).hom ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (geIndex_spec p i (hpq.trans hi))).inv
    else 0
  comm' i j hij := by
    by_cases hi : q ≤ i
    · have hj : q ≤ j := by
        have hij' : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        omega
      rw [dif_pos hi, dif_pos hj, stupidTrunc_d_eq K q hi hj,
        stupidTrunc_d_eq K p (hpq.trans hi) (hpq.trans hj)]
      simp
    · apply IsZero.eq_of_src
      apply isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega

@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp_ι (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q : ℤ) (hpq : p ≤ q) :
    stupidTruncGEMap K p q hpq ≫ stupidTruncGEι K p = stupidTruncGEι K q := by
  ext i
  by_cases hi : q ≤ i
  · rw [comp_f]
    simp [stupidTruncGEMap, stupidTruncGEι, hi, hpq.trans hi]
  · apply IsZero.eq_of_src
    apply isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

@[simp]
lemma stupidTruncGEMap_self (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    stupidTruncGEMap K p p le_rfl = 𝟙 _ := by
  rw [← cancel_mono (stupidTruncGEι K p)]
  simp

@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) :
    stupidTruncGEMap K q r hqr ≫ stupidTruncGEMap K p q hpq =
      stupidTruncGEMap K p r (hpq.trans hqr) := by
  rw [← cancel_mono (stupidTruncGEι K p), Category.assoc]
  simp

end HomologicalComplex

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- Filtration index at which column `p` is added in the increasing reindexing of the decreasing
column filtration. -/
def columnFiltrationIndex (p : ℤ) : ℤ := -p

/-- The increasing `ℤ`-filtration of a cohomological bicomplex obtained by retaining the
columns in first degrees at least `-p` at filtration index `p`. -/
noncomputable def columnFiltrationBicomplex
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    ℤ ⥤ HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  obj p := K.stupidTrunc (ComplexShape.embeddingUpIntGE (-p))
  map {p q} f := HomologicalComplex.stupidTruncGEMap K (-q) (-p)
    (neg_le_neg (leOfHom f))
  map_id p := by simp
  map_comp {p q r} f g := by simp

/-- Totalize the column filtration of a cohomological bicomplex. -/
noncomputable def columnFilteredTotalComplex
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)] :
    ℤ ⥤ CochainComplex C ℤ where
  obj p := ((columnFiltrationBicomplex K).obj p).total (ComplexShape.up ℤ)
  map f := total.map ((columnFiltrationBicomplex K).map f) (ComplexShape.up ℤ)
  map_id p := by simp
  map_comp f g := by simp

/-- The canonical map from a stage of the column-filtered total complex to the total complex of
the whole bicomplex.  These maps name the intended abutment target even though the pinned
`SpectralSequence` structure itself has no convergence or abutment field. -/
noncomputable def columnFilteredTotalι
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)]
    (p : ℤ) :
    (columnFilteredTotalComplex K).obj p ⟶ K.total (ComplexShape.up ℤ) := by
  letI : HomologicalComplex₂.HasTotal
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-p))) (ComplexShape.up ℤ) :=
    inferInstanceAs (((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ))
  exact total.map (HomologicalComplex.stupidTruncGEι K (-p)) (ComplexShape.up ℤ)

/-- The filtration-stage maps to the total complex are compatible with the filtration maps. -/
@[reassoc]
lemma columnFilteredTotal_map_comp_ι
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)]
    {p q : ℤ} (f : p ⟶ q) :
    (columnFilteredTotalComplex K).map f ≫ columnFilteredTotalι K q =
      columnFilteredTotalι K p := by
  change total.map _ (ComplexShape.up ℤ) ≫ total.map _ (ComplexShape.up ℤ) =
    total.map _ (ComplexShape.up ℤ)
  rw [← total.map_comp]
  congr 1
  exact HomologicalComplex.stupidTruncGEMap_comp_ι K (-q) (-p)
    (neg_le_neg (leOfHom f))

/-- The compatible filtration-stage maps as a natural transformation to the constant total
complex. -/
noncomputable def columnFilteredTotalιNat
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)] :
    columnFilteredTotalComplex K ⟶
      (Functor.const ℤ).obj (K.total (ComplexShape.up ℤ)) where
  app p := columnFilteredTotalι K p
  naturality := by
    intro p q f
    change _ = columnFilteredTotalι K p ≫ 𝟙 _
    rw [Category.comp_id]
    exact columnFilteredTotal_map_comp_ι K f

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]

/-- The abelian spectral object associated to the column-filtered total complex of a
cohomological bicomplex. -/
noncomputable def columnFilteredTotalSpectralObject
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)] :
    CategoryTheory.Abelian.SpectralObject C ℤ :=
  HomotopyCategory.filteredComplexSpectralObject (columnFilteredTotalComplex K)

/-- The `E₂` cohomological spectral sequence of the column-filtered total complex. -/
noncomputable def columnFilteredTotalSpectralSequence
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [∀ p : ℤ, ((columnFiltrationBicomplex K).obj p).HasTotal (ComplexShape.up ℤ)] :
    CategoryTheory.SpectralSequence C
      (fun r ↦ ComplexShape.up' (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2 :=
  (columnFilteredTotalSpectralObject K).spectralSequence
    CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt

end HomologicalComplex₂
