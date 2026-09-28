/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplexAdjacentCore
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Data.Int.Interval

/-!
# Finite-strip comparison for total complexes

A columnwise quasi-isomorphism of bicomplexes supported on a finite horizontal interval
induces a quasi-isomorphism of their actual signed total complexes. Total objects are
constructed from finite diagonal support; no infinite coproduct assumption is needed.
The adjacent-tail induction uses derived-category triangles of short exact sequences.
-/

open CategoryTheory Category Limits

universe u v w

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

/-- A quasi-isomorphism on a vertical column gives one on its total. -/
private lemma singleColumnTotalMap_quasiIso_generic (f : K ⟶ L) (p : ℤ)
    (h : QuasiIso (f.f p)) :
    QuasiIso (total.map (singleColumnBicomplexMap f p) (ComplexShape.up ℤ)) := by
  letI : QuasiIso (f.f p) := h
  rw [← quasiIso_iff_comp_right _ (singleColumnTotalIso L p).hom]
  rw [singleColumnTotalIso_naturality]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma truncatedMap_inclusion_naturality (f : K ⟶ L) (a : ℤ) :
    truncatedBicomplexMap f a ≫ HomologicalComplex.stupidTruncGEι L a =
      HomologicalComplex.stupidTruncGEι K a ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext p
  by_cases hp : a ≤ p
  · dsimp [truncatedBicomplexMap, truncatedBicomplex, HomologicalComplex.stupidTruncGEι]
    rw [dif_pos hp, dif_pos hp]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom f _ _
  · apply IsZero.eq_of_src
    dsimp [truncatedBicomplex]
    apply HomologicalComplex.isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega


variable [∀ p : ℤ, (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
  [∀ p : ℤ, (truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ)]

private lemma upperTail_total_isZero (K : HomologicalComplex₂ C
    (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [∀ p : ℤ, (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ)]
    (b : ℤ) (hK : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q)) :
    IsZero ((truncatedBicomplex K (b + 1)).total (ComplexShape.up ℤ)) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q hpq
  by_cases hp : b + 1 ≤ p
  · have hz : IsZero (((truncatedBicomplex K (b + 1)).X p).X q) :=
      (hK p q (by omega)).of_iso
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapIso
          (stupidTruncGEXIso K (b + 1) p hp))
    exact hz.eq_of_src _ _
  · have hz : IsZero ((truncatedBicomplex K (b + 1)).X p) := by
      apply HomologicalComplex.isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega
    exact ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero hz).eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteTailMap_quasiIso (f : K ⟶ L) (b : ℤ)
    (hK : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℤ, b < p → IsZero ((L.X p).X q))
    (hcol : ∀ p : ℤ, QuasiIso (f.f p)) (r : ℕ) :
    QuasiIso (total.map (truncatedBicomplexMap f (b + 1 - (r : ℤ)))
      (ComplexShape.up ℤ)) := by
  induction r with
  | zero =>
    have hi : IsIso (total.map (truncatedBicomplexMap f (b + 1 - (0 : ℤ)))
        (ComplexShape.up ℤ)) := by
      apply IsZero.isIso
      · simpa using upperTail_total_isZero K b hK
      · simpa using upperTail_total_isZero L b hL
    infer_instance
  | succ r ih =>
    rw [show b + 1 - ((r + 1 : ℕ) : ℤ) = b - (r : ℤ) by omega]
    let φ := adjacentColumnTotalShortComplexMap f (b - (r : ℤ))
    have hprev : QuasiIso φ.τ₁ := by
      dsimp [φ, adjacentColumnTotalShortComplexMap]
      have heq : b + 1 - (r : ℤ) = b - (r : ℤ) + 1 := by omega
      exact (congrArg (fun p : ℤ => QuasiIso
        (total.map (truncatedBicomplexMap f p) (ComplexShape.up ℤ))) heq).mp ih
    let hS₁ := adjacentColumnTotalShortExact K (b - (r : ℤ))
    let hS₂ := adjacentColumnTotalShortExact L (b - (r : ℤ))
    letI : HasDerivedCategory C := HasDerivedCategory.standard C
    have hq₁ : IsIso (DerivedCategory.Q.map φ.τ₁) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₁).2 hprev
    have hq₃ : IsIso (DerivedCategory.Q.map φ.τ₃) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₃).2
        (singleColumnTotalMap_quasiIso_generic f _ (hcol _))
    have hq₂ : IsIso (DerivedCategory.Q.map φ.τ₂) := by
      let ψ := DerivedCategory.triangleOfSES.map hS₁ hS₂ φ
      exact Pretriangulated.isIso₂_of_isIso₁₃ ψ
        (DerivedCategory.triangleOfSES_distinguished hS₁)
        (DerivedCategory.triangleOfSES_distinguished hS₂) hq₁ hq₃
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₂).1 hq₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma lowerTail_inclusion_isIso (K : HomologicalComplex₂ C
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a : ℤ)
    (hK : ∀ p q : ℤ, p < a → IsZero ((K.X p).X q)) :
    IsIso (HomologicalComplex.stupidTruncGEι K a) := by
  letI componentIso (p q : ℤ) :
      IsIso (((HomologicalComplex.stupidTruncGEι K a).f p).f q) := by
    dsimp [HomologicalComplex.stupidTruncGEι]
    split_ifs with hp
    · infer_instance
    · apply IsZero.isIso
      · apply (HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero
        apply HomologicalComplex.isZero_stupidTrunc_X
        rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
        omega
      · exact hK p q (by omega)
  letI rowIso (p : ℤ) : IsIso ((HomologicalComplex.stupidTruncGEι K a).f p) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteStrip_totalMap_quasiIso_of_hasTotal
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (f : K ⟶ L) (a b : ℤ) (hab : a ≤ b + 1)
    (hKlo : ∀ p q : ℤ, p < a → IsZero ((K.X p).X q))
    (hLlo : ∀ p q : ℤ, p < a → IsZero ((L.X p).X q))
    (hKhi : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hLhi : ∀ p q : ℤ, b < p → IsZero ((L.X p).X q))
    (hcol : ∀ p : ℤ, QuasiIso (f.f p)) :
    QuasiIso (total.map f (ComplexShape.up ℤ)) := by
  have htail : QuasiIso (total.map (truncatedBicomplexMap f a) (ComplexShape.up ℤ)) := by
    have h := finiteTailMap_quasiIso f b hKhi hLhi hcol (b + 1 - a).toNat
    have heq : b + 1 - ((b + 1 - a).toNat : ℤ) = a := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    exact (congrArg (fun p : ℤ => QuasiIso
      (total.map (truncatedBicomplexMap f p) (ComplexShape.up ℤ))) heq).mp h
  letI : IsIso (HomologicalComplex.stupidTruncGEι K a) := lowerTail_inclusion_isIso K a hKlo
  letI : IsIso (HomologicalComplex.stupidTruncGEι L a) := lowerTail_inclusion_isIso L a hLlo
  letI : HomologicalComplex₂.HasTotal (K.stupidTrunc (ComplexShape.embeddingUpIntGE a))
      (ComplexShape.up ℤ) := inferInstanceAs ((truncatedBicomplex K a).HasTotal (ComplexShape.up ℤ))
  letI : HomologicalComplex₂.HasTotal (L.stupidTrunc (ComplexShape.embeddingUpIntGE a))
      (ComplexShape.up ℤ) := inferInstanceAs ((truncatedBicomplex L a).HasTotal (ComplexShape.up ℤ))
  let iK := total.map (HomologicalComplex.stupidTruncGEι K a) (ComplexShape.up ℤ)
  let iL := total.map (HomologicalComplex.stupidTruncGEι L a) (ComplexShape.up ℤ)
  letI : IsIso iK := (total.mapIso (asIso (HomologicalComplex.stupidTruncGEι K a))
    (ComplexShape.up ℤ)).isIso_hom
  letI : IsIso iL := (total.mapIso (asIso (HomologicalComplex.stupidTruncGEι L a))
    (ComplexShape.up ℤ)).isIso_hom
  have hsquare : total.map (truncatedBicomplexMap f a) (ComplexShape.up ℤ) ≫ iL =
      iK ≫ total.map f (ComplexShape.up ℤ) := by
    dsimp [iK, iL]
    rw [← total.map_comp, ← total.map_comp, truncatedMap_inclusion_naturality]
  rw [← quasiIso_iff_comp_left iK (total.map f (ComplexShape.up ℤ)), ← hsquare]
  letI := htail
  infer_instance

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C]

section Coproduct
variable [HasZeroMorphisms C]

private noncomputable def supportCofan {I : Type w} (X : I → C) (s : Finset I)
    [HasCoproduct (fun i : s => X i)] : Cofan X := by
  classical
  exact Cofan.mk (∐ fun i : s => X i)
    (fun i => if hi : i ∈ s then Sigma.ι (fun i : s => X i) ⟨i, hi⟩ else 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def supportCofanIsColimit {I : Type w} (X : I → C) (s : Finset I)
    [HasCoproduct (fun i : s => X i)]
    (hzero : ∀ i, i ∉ s → IsZero (X i)) : IsColimit (supportCofan X s) := by
  classical
  refine Cofan.IsColimit.mk _ (fun t => Sigma.desc (fun i : s => t.inj i)) ?_ ?_
  · intro t i
    by_cases hi : i ∈ s
    · simp [supportCofan, hi]
    · exact (hzero i hi).eq_of_src _ _
  · intro t m hm
    apply Sigma.hom_ext m (Sigma.desc (fun i : s => t.inj i))
    intro i
    rw [Sigma.ι_desc]
    simpa [supportCofan, i.property] using hm i

private lemma hasCoproduct_of_finite_support [HasFiniteCoproducts C]
    {I : Type w} (X : I → C) (s : Finset I)
    (hzero : ∀ i, i ∉ s → IsZero (X i)) : HasCoproduct X :=
  ⟨⟨supportCofan X s, supportCofanIsColimit X s hzero⟩⟩

end Coproduct
end HomologicalComplex₂

namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]

private lemma hasTotal_of_finite_columns
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (a b : ℤ)
    (hK : ∀ p q : ℤ, p < a ∨ b < p → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  classical
  intro n
  let idx : ℤ → ((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) ⁻¹' {n}) := fun p => ⟨(p, n - p), by simp⟩
  let s := (Finset.Icc a b).image idx
  apply hasCoproduct_of_finite_support _ s
  rintro ⟨⟨p, q⟩, hpq⟩ hnot
  have hpq' : p + q = n := hpq
  apply hK p q
  by_contra! h
  apply hnot
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_Icc.mpr h, ?_⟩
  apply Subtype.ext
  dsimp [idx]
  congr 1
  omega

private lemma tailHasTotal_of_upper_bound
    [HasZeroObject C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b : ℤ) (hK : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q)) (a : ℤ) :
    (truncatedBicomplex K a).HasTotal (ComplexShape.up ℤ) := by
  apply hasTotal_of_finite_columns _ a b
  intro p q hp
  by_cases ha : a ≤ p
  · have hb : b < p := hp.resolve_left (by omega)
    exact (hK p q hb).of_iso
      ((HomologicalComplex.eval C (ComplexShape.up ℤ) q).mapIso
        (stupidTruncGEXIso K a p ha))
  · apply (HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero
    apply HomologicalComplex.isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A columnwise quasi-isomorphism on a finite horizontal strip induces a quasi-isomorphism
of total complexes. Vertical columns may be unbounded, and the strip may be empty. -/
lemma finiteStrip_totalMap_quasiIso
    {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : K ⟶ L) (a b : ℤ)
    (hK : ∀ p q : ℤ, p < a ∨ b < p → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℤ, p < a ∨ b < p → IsZero ((L.X p).X q))
    (hcol : ∀ p : ℤ, a ≤ p → p ≤ b → QuasiIso (f.f p)) :
    letI := hasTotal_of_finite_columns K a b hK
    letI := hasTotal_of_finite_columns L a b hL
    QuasiIso (total.map f (ComplexShape.up ℤ)) := by
  letI := hasTotal_of_finite_columns K a b hK
  letI := hasTotal_of_finite_columns L a b hL
  letI : ∀ p : ℤ, (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ) :=
    tailHasTotal_of_upper_bound K b (fun p q hp => hK p q (Or.inr hp))
  letI : ∀ p : ℤ, (truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ) :=
    tailHasTotal_of_upper_bound L b (fun p q hp => hL p q (Or.inr hp))
  have hcol' (p : ℤ) : QuasiIso (f.f p) := by
    by_cases hp : a ≤ p ∧ p ≤ b
    · exact hcol p hp.1 hp.2
    · have hp' : p < a ∨ b < p := by omega
      have hzK : IsZero (K.X p) := by
        rw [IsZero.iff_id_eq_zero]
        apply HomologicalComplex.Hom.ext
        funext q
        exact (hK p q hp').eq_of_src _ _
      have hzL : IsZero (L.X p) := by
        rw [IsZero.iff_id_eq_zero]
        apply HomologicalComplex.Hom.ext
        funext q
        exact (hL p q hp').eq_of_src _ _
      letI : IsIso (f.f p) := IsZero.isIso hzK hzL _
      infer_instance
  apply finiteStrip_totalMap_quasiIso_of_hasTotal f (min a (b + 1)) b (by omega)
  · intro p q hp
    exact hK p q (Or.inl (by omega))
  · intro p q hp
    exact hL p q (Or.inl (by omega))
  · intro p q hp
    exact hK p q (Or.inr hp)
  · intro p q hp
    exact hL p q (Or.inr hp)
  · exact hcol'

end HomologicalComplex₂
