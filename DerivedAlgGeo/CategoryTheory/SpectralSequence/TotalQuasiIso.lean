/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SpectralSequence.FilteredTotalComplexAdjacent
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms and filtered total complexes

This file supplies two naturality lemmas missing from the upstream homology-sequence and total-
complex APIs.  They are the comparison-theorem plumbing needed for the Cech bicomplex:

* in a morphism of short exact cochain-complex sequences, quasi-isomorphisms on the outer terms
  imply a quasi-isomorphism on the middle term; and
* a bicomplex morphism induces a morphism between its adjacent-column total short exact
  sequences.

Both statements are general and independent of sheaves.
-/

open CategoryTheory Category Limits
open CategoryTheory.Pretriangulated

universe w

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex.mappingCone

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CochainComplex AddCommGrpCat.{w} ℤ}
  {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {f' : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃}
  (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : X₃ ⟶ Y₃)
  (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism between the mapping-cone composition triangles induced by a morphism of
composable pairs. -/
private noncomputable def compTriangleMapC :
    CochainComplex.mappingConeCompTriangle f g ⟶
      CochainComplex.mappingConeCompTriangle f' g' :=
  Triangle.homMk _ _
    (map f f' a b hf)
    (map (f ≫ g) (f' ≫ g') a c
      (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
    (map g g' b c hg)
    (by
      simp only [CochainComplex.mappingConeCompTriangle_mor₁]
      rw [← map_comp, ← map_comp]
      simp only [Category.id_comp, Category.comp_id, hg])
    (by
      simp only [CochainComplex.mappingConeCompTriangle_mor₂]
      rw [← map_comp, ← map_comp]
      simp only [Category.id_comp, Category.comp_id, hf])
    (by
      let φ : ComposableArrows.mk₂ f g ⟶ ComposableArrows.mk₂ f' g' :=
        ComposableArrows.homMk₂ a b c hf hg
      exact (CochainComplex.mappingConeCompTriangle_mor₃_naturality
        f g f' g' φ).symm)

/-- The morphism between mapping-cone composition triangles in the homotopy category induced
by a morphism of composable pairs. -/
private noncomputable def compTriangleMap :
    CochainComplex.mappingConeCompTriangleh f g ⟶
      CochainComplex.mappingConeCompTriangleh f' g' :=
  (HomotopyCategory.quotient AddCommGrpCat.{w}
    (ComplexShape.up ℤ)).mapTriangle.map (compTriangleMapC a b c hf hg)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a morphism between two composable pairs of cochain-complex maps, quasi-isomorphisms on
the mapping cones of the two individual maps imply a quasi-isomorphism on the mapping cone of
their composites.  This is the octahedral analogue of the five lemma. -/
lemma quasiIso_compMap
    [QuasiIso (map f f' a b hf)] [QuasiIso (map g g' b c hg)] :
    QuasiIso (map (f ≫ g) (f' ≫ g') a c
      (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc])) := by
  let ψ := compTriangleMap a b c hf hg
  let Qh := (DerivedCategory.Qh :
    HomotopyCategory AddCommGrpCat.{w} (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{w})
  let Ψ := Qh.mapTriangle.map ψ
  have hT : Qh.mapTriangle.obj
      (CochainComplex.mappingConeCompTriangleh f g) ∈
      distTriang (DerivedCategory AddCommGrpCat.{w}) :=
    Qh.map_distinguished _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished f g)
  have hT' : Qh.mapTriangle.obj
      (CochainComplex.mappingConeCompTriangleh f' g') ∈
      distTriang (DerivedCategory AddCommGrpCat.{w}) :=
    Qh.map_distinguished _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished f' g')
  haveI h₁ : IsIso Ψ.hom₁ := by
    change IsIso (DerivedCategory.Q.map (map f f' a b hf))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  haveI h₃ : IsIso Ψ.hom₃ := by
    change IsIso (DerivedCategory.Q.map (map g g' b c hg))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  haveI h₂ : IsIso Ψ.hom₂ :=
    Pretriangulated.isIso₂_of_isIso₁₃ Ψ hT hT' h₁ h₃
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  change IsIso Ψ.hom₂
  infer_instance

/-- Quasi-isomorphism of a mapping-cone map is invariant under replacing its source and target
arrows by equal arrows.  This small transport lemma avoids exposing the dependent
`HasHomotopyCofiber` instances carried by `mappingCone`. -/
private lemma quasiIso_map_of_eq
    {X₁ X₂ Y₁ Y₂ : CochainComplex AddCommGrpCat.{w} ℤ}
    {u u' : X₁ ⟶ X₂} {v v' : Y₁ ⟶ Y₂}
    (hu : u = u') (hv : v = v') (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (h : u ≫ b = a ≫ v) (h' : u' ≫ b = a ≫ v')
    (q : QuasiIso (map u v a b h)) : QuasiIso (map u' v' a b h') := by
  subst u'
  subst v'
  exact q

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the source complex vanishes in two adjacent degrees, the canonical inclusion into the
mapping cone is a quasi-isomorphism in the lower degree. -/
lemma quasiIsoAt_inr_of_isZero_X
    {A B : CochainComplex AddCommGrpCat.{w} ℤ} (f : A ⟶ B) (n : ℤ)
    (hn : IsZero (A.X n)) (hn₁ : IsZero (A.X (n + 1))) :
    QuasiIsoAt (inr f) n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let Q := HomotopyCategory.quotient AddCommGrpCat.{w} (ComplexShape.up ℤ)
  let F := HomotopyCategory.homologyFunctor AddCommGrpCat.{w}
    (ComplexShape.up ℤ) 0
  let T := triangleh f
  have hT : T ∈ distTriang
      (HomotopyCategory AddCommGrpCat.{w} (ComplexShape.up ℤ)) :=
    HomotopyCategory.mappingCone_triangleh_distinguished f
  have hHn : IsZero (A.homology n) := by
    exact ShortComplex.isZero_homology_of_isZero_X₂ (A.sc n) hn
  have hHn₁ : IsZero (A.homology (n + 1)) := by
    exact ShortComplex.isZero_homology_of_isZero_X₂ (A.sc (n + 1)) hn₁
  have hHhn : IsZero ((F.shift n).obj (Q.obj A)) :=
    hHn.of_iso
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) n).app A)
  have hHhn₁ : IsZero ((F.shift (n + 1)).obj (Q.obj A)) :=
    hHn₁.of_iso
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
        (ComplexShape.up ℤ) (n + 1)).app A)
  haveI hmono : Mono ((F.shift n).map T.mor₂) := by
    rw [F.homologySequence_mono_shift_map_mor₂_iff T hT n]
    exact hHhn.eq_of_src _ _
  haveI hepi : Epi ((F.shift n).map T.mor₂) := by
    rw [F.homologySequence_epi_shift_map_mor₂_iff T hT n (n + 1) rfl]
    exact hHhn₁.eq_of_tgt _ _
  change IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
    (ComplexShape.up ℤ) n).map (inr f))
  rw [← NatIso.isIso_map_iff
    (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{w}
      (ComplexShape.up ℤ) n) (inr f)]
  change IsIso ((F.shift n).map T.mor₂)
  exact isIso_of_mono_of_epi _

end CochainComplex.mappingCone

namespace HomologicalComplex

variable {S₁ S₂ : ShortComplex (CochainComplex AddCommGrpCat.{w} ℤ)}
  (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a morphism of short exact sequences of integer-graded cochain complexes, if the maps on
the outer terms are quasi-isomorphisms, then so is the map on the middle term.

This is the missing `τ₂` companion to Mathlib's `HomologySequence.quasiIso_τ₃`.  The proof
uses the two four lemmas on consecutive pieces of the long exact homology sequence. -/
lemma HomologySequence.quasiIso_τ₂
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    have hi : (ComplexShape.up ℤ).Rel (i - 1) i := by simp
    apply Abelian.mono_of_epi_of_mono_of_mono'' (n := 5) (k := 2) (by omega)
      (HomologySequence.composableArrows₅_exact hS₁ (i - 1) i hi)
      (HomologySequence.composableArrows₅_exact hS₂ (i - 1) i hi)
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i hi)
      2 3 4 5 rfl rfl rfl rfl
    all_goals dsimp
    all_goals infer_instance
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    have hi : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
    apply Abelian.epi_of_epi_of_epi_of_mono'' (n := 5) (k := 0) (by omega)
      (HomologySequence.composableArrows₅_exact hS₁ i (i + 1) hi)
      (HomologySequence.composableArrows₅_exact hS₂ i (i + 1) hi)
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) hi)
      0 1 2 3 rfl rfl rfl rfl
    all_goals dsimp
    all_goals infer_instance
  exact isIso_of_mono_of_epi _

end HomologicalComplex

namespace HomologicalComplex₂

variable {K L : HomologicalComplex₂ AddCommGrpCat.{w}
  (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- A bicomplex is vertically connective when every term in negative vertical degree is zero. -/
def IsVerticallyConnective
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) : Prop :=
  ∀ p q : ℤ, q < 0 → IsZero ((K.X p).X q)

/-- A bicomplex is horizontally connective when every term in negative horizontal degree is
zero. -/
def IsHorizontallyConnective
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) : Prop :=
  ∀ p q : ℤ, p < 0 → IsZero ((K.X p).X q)

/-- Stupid column truncation is natural in the bicomplex. -/
private noncomputable def truncatedBicomplexMap (f : K ⟶ L) (p : ℤ) :
    truncatedBicomplex K p ⟶ truncatedBicomplex L p :=
  HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE p)

/-- The single-column construction is natural in the bicomplex. -/
private noncomputable def singleColumnBicomplexMap (f : K ⟶ L) (p : ℤ) :
    singleColumnBicomplex K p ⟶ singleColumnBicomplex L p :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) p).map (f.f p)

variable {A B : CochainComplex AddCommGrpCat.{w} ℤ}

/-- Naturality map for a bicomplex supported in horizontal degree zero. -/
noncomputable def singleZeroBicomplexMap (f : A ⟶ B) :
    singleZeroBicomplex A ⟶ singleZeroBicomplex B :=
  (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{w} ℤ) 0).map f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The total-complex identification for a bicomplex supported in horizontal degree zero is
natural. -/
@[reassoc]
lemma singleZeroTotalIso_naturality (f : A ⟶ B) :
    total.map (singleZeroBicomplexMap f) (ComplexShape.up ℤ) ≫
        (singleZeroTotalIso B).hom =
      (singleZeroTotalIso A).hom ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [← cancel_epi (singleZeroTotalXIso A n).inv]
  dsimp [singleZeroTotalIso]
  simp [singleZeroTotalXIso, singleZeroBicomplexMap, singleZeroBicomplex,
    singleZeroXIso]
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv.f n ≫
      (((HomologicalComplex.single (CochainComplex AddCommGrpCat.{w} ℤ)
        (ComplexShape.up ℤ) 0).map f).f 0).f n ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).hom.f n = f.f n
  rw [HomologicalComplex.single_map_f_self]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identification of a single column with a shifted degree-zero column is natural. -/
@[reassoc]
private lemma singleColumnShiftIso_naturality (f : K ⟶ L) (p : ℤ) :
    singleColumnBicomplexMap f p ≫ (singleColumnShiftIso L p).hom =
      (singleColumnShiftIso K p).hom ≫
        (shiftFunctor₁ AddCommGrpCat.{w} (-p)).map
          (singleZeroBicomplexMap (f.f p)) := by
  exact ((CochainComplex.singleFunctors
    (CochainComplex AddCommGrpCat.{w} ℤ)).shiftIso
      (-p) p 0 (by omega)).inv.naturality (f.f p)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard identification of a single-column total complex with the shifted column is
natural. -/
@[reassoc]
private lemma singleColumnTotalIso_naturality (f : K ⟶ L) (p : ℤ) :
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

/-- A quasi-isomorphism on one vertical column induces a quasi-isomorphism on its single-column
total complex. -/
private lemma singleColumnTotalMap_quasiIso (f : K ⟶ L) (p : ℤ)
    (h : QuasiIso (f.f p)) :
    QuasiIso (total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ)) := by
  letI : QuasiIso (f.f p) := h
  rw [← quasiIso_iff_comp_right _ (singleColumnTotalIso L p).hom]
  rw [singleColumnTotalIso_naturality]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A bicomplex morphism maps the adjacent-column short exact sequence of its source to that of
its target. -/
private noncomputable def adjacentColumnTotalShortComplexMap (f : K ⟶ L) (p : ℤ) :
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
      change (truncatedBicomplexMap f (p + 1)).f i ≫ eL₀.hom ≫ eL₁.inv =
        eK₀.hom ≫ eK₁.inv ≫ (truncatedBicomplexMap f p).f i
      dsimp [truncatedBicomplexMap, truncatedBicomplex]
      rw [← cancel_mono eL₁.hom]
      simp only [Category.assoc, eL₁.inv_hom_id, Category.comp_id]
      rw [← Category.assoc, ← Category.assoc]
      dsimp [eK₀, eK₁, eL₀, eL₁, stupidTruncGEXIso]
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
          ((HomologicalComplex.single (CochainComplex AddCommGrpCat.{w} ℤ)
            (ComplexShape.up ℤ) p).map (f.f p)).f p ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p (L.X p)).hom
      rw [HomologicalComplex.single_map_f_self]
      simp
    · apply IsZero.eq_of_tgt
      apply HomologicalComplex.isZero_single_obj_X
      exact hi

/-- The morphism between the mapping cones of two adjacent-column inclusions induced by a
bicomplex morphism. -/
private noncomputable def adjacentColumnConeMap (f : K ⟶ L) (p : ℤ) :
    CochainComplex.mappingCone (adjacentColumnTotalShortComplex K p).f ⟶
      CochainComplex.mappingCone (adjacentColumnTotalShortComplex L p).f :=
  CochainComplex.mappingCone.map _ _
    (adjacentColumnTotalShortComplexMap f p).τ₁
    (adjacentColumnTotalShortComplexMap f p).τ₂
    (adjacentColumnTotalShortComplexMap f p).comm₁₂.symm

/-- A quasi-isomorphism on one vertical column induces a quasi-isomorphism on the mapping cone
of the corresponding adjacent-column inclusion. -/
private lemma adjacentColumnConeMap_quasiIso (f : K ⟶ L) (p : ℤ)
    (h : QuasiIso (f.f p)) : QuasiIso (adjacentColumnConeMap f p) := by
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

/-- The inclusion of the tail beginning in column `n + 1` into the tail beginning in column
zero.  Its cone is the finite quotient containing columns `0, …, n`. -/
private noncomputable def tailToZero
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (n : ℕ) :
    (truncatedBicomplex K ((n : ℤ) + 1)).total (ComplexShape.up ℤ) ⟶
      (truncatedBicomplex K 0).total (ComplexShape.up ℤ) :=
  total.map (HomologicalComplex.stupidTruncGEMap K 0 ((n : ℤ) + 1) (by omega))
    (ComplexShape.up ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Adding the next adjacent column and then including the existing tail is the direct tail
inclusion. -/
private lemma adjacent_comp_tailToZero (K : HomologicalComplex₂ AddCommGrpCat.{w}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (n : ℕ) :
    (adjacentColumnTotalShortComplex K ((n : ℤ) + 1)).f ≫ tailToZero K n =
      tailToZero K (n + 1) := by
  dsimp [adjacentColumnTotalShortComplex, adjacentColumnBicomplexShortComplex,
    adjacentColumnInclusion, tailToZero]
  rw [← total.map_comp]
  congr 1
  exact HomologicalComplex.stupidTruncGEMap_comp K 0 ((n : ℤ) + 1)
    ((n : ℤ) + 2) (by omega) (by omega)

/-- The map induced by a bicomplex morphism on the total complex of a column tail. -/
private noncomputable def truncatedTotalMap (f : K ⟶ L) (p : ℤ) :
    (truncatedBicomplex K p).total (ComplexShape.up ℤ) ⟶
      (truncatedBicomplex L p).total (ComplexShape.up ℤ) :=
  total.map (truncatedBicomplexMap f p) (ComplexShape.up ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Maps on column tails commute with the inclusions between two truncation levels. -/
private lemma truncatedBicomplexMap_naturality_inclusion (f : K ⟶ L)
    (p q : ℤ) (hpq : p ≤ q) :
    truncatedTotalMap f q ≫
        total.map (HomologicalComplex.stupidTruncGEMap L p q hpq)
          (ComplexShape.up ℤ) =
      total.map (HomologicalComplex.stupidTruncGEMap K p q hpq)
          (ComplexShape.up ℤ) ≫ truncatedTotalMap f p := by
  dsimp [truncatedTotalMap]
  rw [← total.map_comp, ← total.map_comp]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : q ≤ i
  · dsimp [HomologicalComplex.stupidTruncGEMap]
    rw [dif_pos hi, dif_pos hi]
    let eK₀ := stupidTruncGEXIso K q i hi
    let eK₁ := stupidTruncGEXIso K p i (hpq.trans hi)
    let eL₀ := stupidTruncGEXIso L q i hi
    let eL₁ := stupidTruncGEXIso L p i (hpq.trans hi)
    change (truncatedBicomplexMap f q).f i ≫ eL₀.hom ≫ eL₁.inv =
      eK₀.hom ≫ eK₁.inv ≫ (truncatedBicomplexMap f p).f i
    dsimp [truncatedBicomplexMap, truncatedBicomplex]
    rw [← cancel_mono eL₁.hom]
    simp only [Category.assoc, eL₁.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Category.assoc]
    dsimp [eK₀, eK₁, eL₀, eL₁, stupidTruncGEXIso]
    rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
    simp only [Category.assoc]
    rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
    simp
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

/-- The direct inclusion of a column tail is natural in the bicomplex. -/
private lemma tailToZero_naturality (f : K ⟶ L) (n : ℕ) :
    tailToZero K n ≫ truncatedTotalMap f 0 =
      truncatedTotalMap f ((n : ℤ) + 1) ≫ tailToZero L n :=
  (truncatedBicomplexMap_naturality_inclusion f 0 ((n : ℤ) + 1)
    (by omega)).symm

/-- The finite quotient of the nonnegative column tail containing columns `0, …, n`, represented
by the mapping cone of the tail beginning in column `n + 1`. -/
private noncomputable def finiteColumnCone
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (n : ℕ) :
    CochainComplex AddCommGrpCat.{w} ℤ :=
  CochainComplex.mappingCone (tailToZero K n)

/-- The map on finite column quotients induced by a bicomplex morphism. -/
private noncomputable def finiteColumnConeMap (f : K ⟶ L) (n : ℕ) :
    finiteColumnCone K n ⟶ finiteColumnCone L n :=
  CochainComplex.mappingCone.map _ _
    (truncatedTotalMap f ((n : ℤ) + 1)) (truncatedTotalMap f 0)
    (tailToZero_naturality f n)

set_option maxHeartbeats 1600000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map of first-quadrant bicomplexes that is a quasi-isomorphism on every nonnegative
vertical column induces a quasi-isomorphism on every finite column quotient. -/
private lemma finiteColumnConeMap_quasiIso (f : K ⟶ L)
    (h : ∀ n : ℕ, QuasiIso (f.f (n : ℤ))) (n : ℕ) :
    QuasiIso (finiteColumnConeMap f n) := by
  induction n with
  | zero =>
      change QuasiIso (adjacentColumnConeMap f 0)
      exact adjacentColumnConeMap_quasiIso f 0 (h 0)
  | succ n ih =>
      have hfK := adjacent_comp_tailToZero K n
      have hfL := adjacent_comp_tailToZero L n
      dsimp [finiteColumnConeMap, finiteColumnCone]
      let φ := adjacentColumnTotalShortComplexMap f ((n : ℤ) + 1)
      let a := φ.τ₁
      let b := φ.τ₂
      let c := truncatedTotalMap f 0
      have hsquare₁ :
          (adjacentColumnTotalShortComplex K ((n : ℤ) + 1)).f ≫ b =
            a ≫ (adjacentColumnTotalShortComplex L ((n : ℤ) + 1)).f :=
        φ.comm₁₂.symm
      have hsquare₂ : tailToZero K n ≫ c = b ≫ tailToZero L n := by
        exact tailToZero_naturality f n
      letI : QuasiIso (CochainComplex.mappingCone.map
          (adjacentColumnTotalShortComplex K ((n : ℤ) + 1)).f
          (adjacentColumnTotalShortComplex L ((n : ℤ) + 1)).f
          a b hsquare₁) :=
        adjacentColumnConeMap_quasiIso f ((n : ℤ) + 1) (h (n + 1))
      letI : QuasiIso (CochainComplex.mappingCone.map
          (tailToZero K n) (tailToZero L n) b c hsquare₂) := ih
      have hcomp :=
        CochainComplex.mappingCone.quasiIso_compMap a b c hsquare₁ hsquare₂
      refine CochainComplex.mappingCone.quasiIso_map_of_eq hfK hfL a c ?_
        (tailToZero_naturality f (n + 1)) ?_
      · rw [Category.assoc, hsquare₂, ← Category.assoc, hsquare₁,
          Category.assoc]
      · simpa only [Nat.cast_add, Nat.cast_one, a, b, c, φ,
          adjacentColumnTotalShortComplexMap, truncatedTotalMap] using hcomp

/-- A sufficiently far column tail has a zero term in a prescribed total degree when the
bicomplex is vertically connective. -/
private lemma isZero_total_truncatedBicomplex_X (hK : IsVerticallyConnective K)
    (N k : ℤ) (hk : k < N) :
    IsZero (((truncatedBicomplex K N).total (ComplexShape.up ℤ)).X k) := by
  rw [IsZero.iff_id_eq_zero]
  apply total.hom_ext
  intro p q hpq
  by_cases hp : N ≤ p
  · have hq : q < 0 := by
      dsimp at hpq
      omega
    let r : ℕ := (p - N).natAbs
    have hr : (ComplexShape.embeddingUpIntGE N).f r = p := by
      change N + (((p - N).natAbs : ℕ) : ℤ) = p
      rw [Int.natAbs_of_nonneg (by omega)]
      omega
    let e : (truncatedBicomplex K N).X p ≅ K.X p := by
      dsimp [truncatedBicomplex]
      exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE N) hr
    have hz : IsZero (((truncatedBicomplex K N).X p).X q) :=
      (hK p q hq).of_iso
        ((HomologicalComplex.eval AddCommGrpCat.{w}
          (ComplexShape.up ℤ) q).mapIso e)
    exact hz.eq_of_src _ _
  · have hz₀ : IsZero ((truncatedBicomplex K N).X p) := by
      dsimp [truncatedBicomplex]
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
    have hz := (HomologicalComplex.eval AddCommGrpCat.{w}
      (ComplexShape.up ℤ) q).map_isZero hz₀
    exact hz.eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Degreewise form of the first-quadrant total comparison theorem. -/
private lemma truncatedTotalMap_zero_quasiIsoAt (f : K ⟶ L)
    (hK : IsVerticallyConnective K) (hL : IsVerticallyConnective L)
    (hcol : ∀ n : ℕ, QuasiIso (f.f (n : ℤ))) (k : ℤ) :
    QuasiIsoAt (truncatedTotalMap f 0) k := by
  let n : ℕ := (k + 1).toNat + 1
  have hn : k + 1 < (n : ℤ) + 1 := by
    dsimp [n]
    by_cases hk : 0 ≤ k + 1
    · rw [Int.toNat_of_nonneg hk]
      omega
    · rw [Int.toNat_of_nonpos (by omega)]
      omega
  have hKk := isZero_total_truncatedBicomplex_X hK ((n : ℤ) + 1) k (by omega)
  have hKk₁ := isZero_total_truncatedBicomplex_X hK ((n : ℤ) + 1)
    (k + 1) hn
  have hLk := isZero_total_truncatedBicomplex_X hL ((n : ℤ) + 1) k (by omega)
  have hLk₁ := isZero_total_truncatedBicomplex_X hL ((n : ℤ) + 1)
    (k + 1) hn
  let iK := CochainComplex.mappingCone.inr (tailToZero K n)
  let iL := CochainComplex.mappingCone.inr (tailToZero L n)
  let q := finiteColumnConeMap f n
  have qiK : QuasiIsoAt iK k :=
    CochainComplex.mappingCone.quasiIsoAt_inr_of_isZero_X
      (tailToZero K n) k hKk hKk₁
  have qiL : QuasiIsoAt iL k :=
    CochainComplex.mappingCone.quasiIsoAt_inr_of_isZero_X
      (tailToZero L n) k hLk hLk₁
  have qq : QuasiIso q := finiteColumnConeMap_quasiIso f hcol n
  letI : QuasiIsoAt iK k := qiK
  letI : QuasiIsoAt iL k := qiL
  letI : QuasiIso q := qq
  have hsquare : iK ≫ q = truncatedTotalMap f 0 ≫ iL := by
    exact (CochainComplex.mappingCone.triangleMap
      (tailToZero K n) (tailToZero L n)
      (truncatedTotalMap f ((n : ℤ) + 1)) (truncatedTotalMap f 0)
      (tailToZero_naturality f n)).comm₂
  rw [← quasiIsoAt_iff_comp_right (truncatedTotalMap f 0) iL k]
  rw [← hsquare]
  infer_instance

/-- A columnwise quasi-isomorphism between vertically connective bicomplexes induces a
quasi-isomorphism on the totals of their nonnegative column tails. -/
private lemma truncatedTotalMap_zero_quasiIso (f : K ⟶ L)
    (hK : IsVerticallyConnective K) (hL : IsVerticallyConnective L)
    (hcol : ∀ n : ℕ, QuasiIso (f.f (n : ℤ))) :
    QuasiIso (truncatedTotalMap f 0) := by
  rw [quasiIso_iff]
  exact truncatedTotalMap_zero_quasiIsoAt f hK hL hcol

/-- The canonical inclusion from the total of the nonnegative column tail into the full total. -/
private noncomputable def tailZeroToTotal
    (K : HomologicalComplex₂ AddCommGrpCat.{w}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (truncatedBicomplex K 0).total (ComplexShape.up ℤ) ⟶
      K.total (ComplexShape.up ℤ) :=
  total.map (HomologicalComplex.stupidTruncGEι K 0) (ComplexShape.up ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a horizontally connective bicomplex, the nonnegative column truncation is isomorphic to
the original bicomplex. -/
private lemma stupidTruncGEι_zero_isIso (K : HomologicalComplex₂ AddCommGrpCat.{w}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (hK : IsHorizontallyConnective K) :
    IsIso (HomologicalComplex.stupidTruncGEι K 0) := by
  letI componentIso (p q : ℤ) :
      IsIso (((HomologicalComplex.stupidTruncGEι K 0).f p).f q) := by
    dsimp [HomologicalComplex.stupidTruncGEι]
    split_ifs with hp
    · infer_instance
    · apply IsZero.isIso
      · apply (HomologicalComplex.eval AddCommGrpCat.{w}
          (ComplexShape.up ℤ) q).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega
      · exact hK p q (by omega)
  letI rowIso (p : ℤ) : IsIso ((HomologicalComplex.stupidTruncGEι K 0).f p) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The inclusion of the nonnegative column tail induces an isomorphism on total complexes for
a horizontally connective bicomplex. -/
private lemma tailZeroToTotal_isIso (K : HomologicalComplex₂ AddCommGrpCat.{w}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (hK : IsHorizontallyConnective K) :
    IsIso (tailZeroToTotal K) := by
  letI : IsIso (HomologicalComplex.stupidTruncGEι K 0) :=
    stupidTruncGEι_zero_isIso K hK
  dsimp [tailZeroToTotal]
  change IsIso ((totalFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (HomologicalComplex.stupidTruncGEι K 0))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The column-truncation map followed by the truncation inclusion equals the original
bicomplex map followed by the source inclusion. -/
private lemma truncatedBicomplexMap_comp_stupidTruncGEι (f : K ⟶ L) :
    truncatedBicomplexMap f 0 ≫ HomologicalComplex.stupidTruncGEι L 0 =
      HomologicalComplex.stupidTruncGEι K 0 ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext p
  by_cases hp : 0 ≤ p
  · dsimp [truncatedBicomplexMap, truncatedBicomplex,
      HomologicalComplex.stupidTruncGEι]
    rw [dif_pos hp, dif_pos hp]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom f _ _
  · apply IsZero.eq_of_src
    dsimp [truncatedBicomplex]
    apply HomologicalComplex.isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inclusion from the nonnegative column tail into the full total. -/
private lemma tailZeroToTotal_naturality (f : K ⟶ L) :
    truncatedTotalMap f 0 ≫ tailZeroToTotal L =
      tailZeroToTotal K ≫ total.map f (ComplexShape.up ℤ) := by
  dsimp [truncatedTotalMap, tailZeroToTotal, truncatedBicomplex]
  rw [← total.map_comp, ← total.map_comp,
    truncatedBicomplexMap_comp_stupidTruncGEι]

/-- A columnwise quasi-isomorphism between first-quadrant bicomplexes of abelian groups induces
a quasi-isomorphism on their total complexes. -/
lemma totalMap_quasiIso (f : K ⟶ L)
    (hKv : IsVerticallyConnective K) (hLv : IsVerticallyConnective L)
    (hKh : IsHorizontallyConnective K) (hLh : IsHorizontallyConnective L)
    (hcol : ∀ n : ℕ, QuasiIso (f.f (n : ℤ))) :
    QuasiIso (total.map f (ComplexShape.up ℤ)) := by
  letI : QuasiIso (truncatedTotalMap f 0) :=
    truncatedTotalMap_zero_quasiIso f hKv hLv hcol
  letI : IsIso (tailZeroToTotal K) := tailZeroToTotal_isIso K hKh
  letI : IsIso (tailZeroToTotal L) := tailZeroToTotal_isIso L hLh
  rw [← quasiIso_iff_comp_left (tailZeroToTotal K)
    (total.map f (ComplexShape.up ℤ))]
  rw [← tailZeroToTotal_naturality]
  infer_instance

end HomologicalComplex₂
