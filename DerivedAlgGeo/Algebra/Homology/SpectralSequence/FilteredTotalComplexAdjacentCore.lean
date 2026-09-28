/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Embedding.StupidTruncGE
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.SingleZeroTotal
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexShift

/-!
# Adjacent-column short complexes of total complexes

For a cohomological bicomplex in a preadditive category with a zero object, the totals of two
consecutive stupid column truncations form a degreewise split short complex, provided diagonal
coproducts exist in every degree for both truncated bicomplexes. Its quotient is the newly added
column, whose total is canonically that column shifted by its horizontal degree. These
constructions are natural in the bicomplex.
In an abelian category the short complex is short exact. `FiniteStripTotal` consumes its
natural map downstream, using the derived-category triangle of a short exact sequence.

## Main definitions and results

* `HomologicalComplex₂.truncatedBicomplex` and
  `HomologicalComplex₂.singleColumnBicomplex` use Mathlib's stupid truncation and
  single-object functor to select a tail and one column.
* `HomologicalComplex₂.singleColumnTotalIso` identifies the signed total of one column
  with its shifted vertical complex.
* `HomologicalComplex₂.totalMap_quasiIso_of_singleColumn` transfers a quasi-isomorphism of
  columns to the literal map between their single-column totals.
* `HomologicalComplex₂.adjacentColumnTotalShortComplex` and
  `HomologicalComplex₂.adjacentColumnTotalDegreewiseSplitting` exhibit consecutive tail
  totals and their one-column quotient as degreewise split.
* `HomologicalComplex₂.adjacentColumnTotalShortComplexMap` is the natural map of these
  short complexes; `HomologicalComplex₂.adjacentColumnTotalShortExact` proves exactness
  when the target category is abelian.

## Implementation notes

The maps in the adjacent short complex are the literal maps induced by Mathlib's
`HomologicalComplex₂.total.map`. The splitting is constructed separately in each total
degree; no chain-level splitting is asserted. Existence of adjacent total objects is an
explicit premise until a downstream theorem supplies it.

## References

This extends Mathlib's `HomologicalComplex.stupidTrunc`,
`HomologicalComplex.single`, and `HomologicalComplex₂.total` APIs.
-/

namespace HomologicalComplex₂

open CategoryTheory Category Limits

universe u v w

-- Internal projection of the ordinary iso identities, for the splitting calculation only.
@[reassoc]
private lemma localIso_inv_hom_f
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {I : Type w} {c : ComplexShape I}
    {A B : HomologicalComplex D c} (e : A ≅ B) (i : I) :
    e.inv.f i ≫ e.hom.f i = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

@[reassoc]
private lemma localIso_hom_inv_f
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {I : Type w} {c : ComplexShape I}
    {A B : HomologicalComplex D c} (e : A ≅ B) (i : I) :
    e.hom.f i ≫ e.inv.f i = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

section Zero

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The column tail beginning at `p`, definitionally Mathlib's stupid truncation along
`ComplexShape.embeddingUpIntGE p`. -/
noncomputable def truncatedBicomplex (p : ℤ) :
    HomologicalComplex₂ C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE p)

/-- The column at `p`, obtained from Mathlib's canonical `HomologicalComplex.single`
functor; no second bicomplex carrier is introduced. -/
noncomputable def singleColumnBicomplex (p : ℤ) :
    HomologicalComplex₂ C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) p).obj (K.X p)

noncomputable def singleColumnXIso (p i : ℤ) (hi : i = p) :
    (singleColumnBicomplex K p).X i ≅ K.X p := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (K.X p)

/-- At the retained column, the canonical component comparison and its inverse cancel;
this form places the forward comparison first in degreewise splitting calculations. -/
@[reassoc (attr := simp)]
lemma singleColumnXIso_hom_inv_f (p i j : ℤ) (hi hi' : i = p) :
    (singleColumnXIso K p i hi).hom.f j ≫
      (singleColumnXIso K p i hi').inv.f j = 𝟙 _ := by
  subst i
  simp [singleColumnXIso, ← HomologicalComplex.comp_f]

/-- At the retained column, the inverse component comparison followed by the forward
comparison is the identity, as used in the opposite splitting composite. -/
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

variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- Stupid column truncation is natural in the bicomplex. This is Mathlib's
`HomologicalComplex.stupidTruncMap` at the standard degree-at-least embedding. -/
noncomputable def truncatedBicomplexMap (f : K ⟶ L) (p : ℤ) :
    truncatedBicomplex K p ⟶ truncatedBicomplex L p :=
  HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE p)

/-- The single-column construction is natural in the bicomplex. It is Mathlib's
`HomologicalComplex.single` functor applied to the actual column map `f.f p`. -/
noncomputable def singleColumnBicomplexMap (f : K ⟶ L) (p : ℤ) :
    singleColumnBicomplex K p ⟶ singleColumnBicomplex L p :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) p).map (f.f p)

end Zero

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- A column in horizontal degree `p` is its degree-zero model shifted by `-p`.
The negative sign matches the cohomological shift convention: horizontal degree `p`
contributes in total degree `p + q`. -/
noncomputable def singleColumnShiftIso (p : ℤ) :
    singleColumnBicomplex K p ≅
      (shiftFunctor₁ C (-p)).obj
        (singleZeroBicomplex (K.X p)) :=
  (((CochainComplex.singleFunctors
    (CochainComplex C ℤ)).shiftIso
      (-p) p 0 (by omega)).app (K.X p)).symm

/-- A single column has a total using only the zero object, via its shifted degree-zero model. -/
noncomputable instance singleColumnHasTotal (p : ℤ) :
    (singleColumnBicomplex K p).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_iso (singleColumnShiftIso K p).symm (ComplexShape.up ℤ)

/-- The signed total of one column is the vertical complex shifted by `-p`.
This factors through `singleColumnShiftIso`, Mathlib's total/shift comparison, and
the degree-zero-column total iso; the factorization retains the signed total map. -/
noncomputable def singleColumnTotalIso (p : ℤ) :
    (singleColumnBicomplex K p).total (ComplexShape.up ℤ) ≅
      (K.X p)⟦-p⟧ :=
  HomologicalComplex₂.total.mapIso (singleColumnShiftIso K p)
      (ComplexShape.up ℤ) ≪≫
    (singleZeroBicomplex (K.X p)).totalShift₁Iso (-p) ≪≫
    (shiftFunctor (CochainComplex C ℤ) (-p)).mapIso
      (singleZeroTotalIso (K.X p))

/-- The short complex of the `p + 1` tail total, `p` tail total, and column-`p`
total. Both arrows are the literal maps induced by Mathlib's `total.map`; its
zero-composite property is proved before any exactness assumption. -/
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Split the adjacent-column total short complex in each total degree using an
explicit retraction and section of the diagonal coproduct maps. The degreewise
splitting does not assert a splitting by chain maps. -/
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
      rw [HomologicalComplex.comp_f, Category.assoc,
        localIso_inv_hom_f_assoc, localIso_hom_inv_f_assoc]
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
      rw [HomologicalComplex.comp_f, Category.assoc,
        localIso_inv_hom_f_assoc, localIso_hom_inv_f_assoc]
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
      · apply IsZero.eq_of_src
        apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega


variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- The canonical single-column shift comparison commutes with a bicomplex morphism
because it is the inverse component of Mathlib's natural shift isomorphism for
the single-object functor. -/
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
/-- The total map of a single column is conjugate to the shifted vertical map.
This combines naturality of the single-object shift comparison, Mathlib's total/shift
comparison, and the degree-zero-column total iso; it is the bridge used to transfer
quasi-isomorphisms to literal total maps. -/
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
/-- A bicomplex morphism gives a map between adjacent-column total short complexes.
Its three components are the literal `total.map` maps on the deeper tail, shallower
tail, and single column; the commutative squares prove their naturality. -/
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
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : p + 1 ≤ i
    · dsimp [adjacentColumnInclusion, HomologicalComplex.stupidTruncGEMap]
      rw [dif_pos hi, dif_pos hi]
      let eK₀ := stupidTruncGEXIso K (p + 1) i hi
      let eK₁ := stupidTruncGEXIso K p i (by omega)
      let eL₀ := stupidTruncGEXIso L (p + 1) i hi
      let eL₁ := stupidTruncGEXIso L p i (by omega)
      simp only [Category.assoc]
      change (truncatedBicomplexMap f (p + 1)).f i ≫ eL₀.hom ≫ eL₁.inv =
        eK₀.hom ≫ eK₁.inv ≫ (truncatedBicomplexMap f p).f i
      dsimp [truncatedBicomplexMap, truncatedBicomplex]
      rw [← cancel_mono eL₁.hom]
      simp only [Category.assoc, eL₁.inv_hom_id, Category.comp_id]
      rw [← Category.assoc, ← Category.assoc]
      dsimp [eK₀, eK₁, eL₀, eL₁, stupidTruncGEXIso,
        HomologicalComplex.stupidTruncGEXIso]
      rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
      simp only [Category.assoc]
      rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
      simp
    · apply IsZero.eq_of_src
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
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
section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- A quasi-isomorphism on a vertical column induces a quasi-isomorphism on the literal
total map of its canonical single-column bicomplexes. The natural total comparison
identifies that map with the shifted column map, and shifts preserve quasi-isomorphisms. -/
lemma totalMap_quasiIso_of_singleColumn
    (f : K ⟶ L) (p : ℤ) (h : QuasiIso (f.f p)) :
    QuasiIso (total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ)) := by
  letI : QuasiIso (f.f p) := h
  rw [← quasiIso_iff_comp_right _ (singleColumnTotalIso L p).hom]
  rw [singleColumnTotalIso_naturality]
  infer_instance

variable
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- Adjacent column tails form a short exact sequence after totalization in an
abelian category. Exactness follows from the separately constructed degreewise
splitting; no chain-level retraction or section is used. -/
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

end Abelian

end HomologicalComplex₂
