/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplexAdjacentCore
import DerivedAlgGeo.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Data.Int.Interval

/-!
# Finite horizontal-strip comparison for total complexes

A columnwise quasi-isomorphism of bicomplexes supported on a finite horizontal interval
induces a quasi-isomorphism of their actual signed total complexes. Total objects are
constructed from finite diagonal support; no infinite coproduct assumption is needed.

## Main result

`HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip` identifies the actual total map as
a quasi-isomorphism from quasi-isomorphisms on the finitely many supported columns. The
vertical direction may be unbounded, and the horizontal interval may be empty.

## Implementation notes

The adjacent-tail induction applies derived-category triangles of short exact sequences
to literal total maps. The single-column quotient is the shifted original column; the
outer tails vanish by the support conditions.

## References

The adjacent-column short exact sequence is in `FilteredTotalComplexAdjacentCore`.
-/

open CategoryTheory Category Limits

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C]

/-- The tail beginning strictly above a supported upper bound has zero total complex.
Only this tail's total is required; no other truncation is constructed. -/
private lemma upperTail_total_isZero [Preadditive C] [HasZeroObject C]
    (K : HomologicalComplex₂ C
    (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (b : ℤ) [(truncatedBicomplex K (b + 1)).HasTotal (ComplexShape.up ℤ)]
    (hK : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q)) :
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

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteTailMap_quasiIso (f : K ⟶ L) (b : ℤ)
    (hK : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℤ, b < p → IsZero ((L.X p).X q))
    (hKT : ∀ p : ℤ, p ≤ b + 1 →
      (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ))
    (hLT : ∀ p : ℤ, p ≤ b + 1 →
      (truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ))
    (hcol : ∀ p : ℤ, p ≤ b → QuasiIso (f.f p))
    (p : ℤ) (hp : p ≤ b + 1) (r : ℕ) (hpr : p = b + 1 - (r : ℤ)) :
    letI := hKT p hp
    letI := hLT p hp
    QuasiIso (total.map (truncatedBicomplexMap f p)
      (ComplexShape.up ℤ)) := by
  induction r generalizing p with
  | zero =>
    have heq : p = b + 1 := by omega
    cases heq
    letI := hKT (b + 1) (by omega)
    letI := hLT (b + 1) (by omega)
    have hi : IsIso (total.map (truncatedBicomplexMap f (b + 1))
        (ComplexShape.up ℤ)) := by
      apply IsZero.isIso
      · exact upperTail_total_isZero K b hK
      · exact upperTail_total_isZero L b hL
    infer_instance
  | succ r ih =>
    letI := hKT p hp
    letI := hLT p hp
    have hp' : p + 1 ≤ b + 1 := by omega
    letI := hKT (p + 1) hp'
    letI := hLT (p + 1) hp'
    let φ := adjacentColumnTotalShortComplexMap f p
    have hprev : QuasiIso φ.τ₁ := by
      dsimp [φ, adjacentColumnTotalShortComplexMap]
      exact ih (p + 1) hp' (by omega)
    let hS₁ := adjacentColumnTotalShortExact K p
    let hS₂ := adjacentColumnTotalShortExact L p
    letI : HasDerivedCategory C := HasDerivedCategory.standard C
    have hq₁ : IsIso (DerivedCategory.Q.map φ.τ₁) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₁).2 hprev
    have hq₃ : IsIso (DerivedCategory.Q.map φ.τ₃) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₃).2
        (singleColumnTotalMap_quasiIso f p (hcol p (by omega)))
    have hq₂ : IsIso (DerivedCategory.Q.map φ.τ₂) := by
      let ψ := DerivedCategory.triangleOfSES.map hS₁ hS₂ φ
      exact Pretriangulated.isIso₂_of_isIso₁₃ ψ
        (DerivedCategory.triangleOfSES_distinguished hS₁)
        (DerivedCategory.triangleOfSES_distinguished hS₂) hq₁ hq₃
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.τ₂).1 hq₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma finiteStrip_totalMap_quasiIso_of_hasTotal
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (f : K ⟶ L) (a b : ℤ) (hab : a ≤ b + 1)
    (hKT : ∀ p : ℤ, p ≤ b + 1 →
      (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ))
    (hLT : ∀ p : ℤ, p ≤ b + 1 →
      (truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ))
    (hKlo : ∀ p q : ℤ, p < a → IsZero ((K.X p).X q))
    (hLlo : ∀ p q : ℤ, p < a → IsZero ((L.X p).X q))
    (hKhi : ∀ p q : ℤ, b < p → IsZero ((K.X p).X q))
    (hLhi : ∀ p q : ℤ, b < p → IsZero ((L.X p).X q))
    (hcol : ∀ p : ℤ, p ≤ b → QuasiIso (f.f p)) :
    QuasiIso (total.map f (ComplexShape.up ℤ)) := by
  letI := hKT a hab
  letI := hLT a hab
  have htail : QuasiIso (total.map (truncatedBicomplexMap f a) (ComplexShape.up ℤ)) := by
    have heq : a = b + 1 - ((b + 1 - a).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    exact finiteTailMap_quasiIso f b hKhi hLhi hKT hLT hcol a hab
      (b + 1 - a).toNat heq
  letI : IsIso (HomologicalComplex.stupidTruncGEι K a) :=
    HomologicalComplex.stupidTruncGEι_isIso_of_isZero K a (by
      intro p hp
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext q
      exact (hKlo p q hp).eq_of_src _ _)
  letI : IsIso (HomologicalComplex.stupidTruncGEι L a) :=
    HomologicalComplex.stupidTruncGEι_isIso_of_isZero L a (by
      intro p hp
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext q
      exact (hLlo p q hp).eq_of_src _ _)
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
    rw [← total.map_comp, ← total.map_comp]
    exact congrArg (fun g => total.map g (ComplexShape.up ℤ))
      (HomologicalComplex.stupidTruncMap_comp_stupidTruncGEι f a)
  rw [← quasiIso_iff_comp_left iK (total.map f (ComplexShape.up ℤ)), ← hsquare]
  letI := htail
  infer_instance

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

/-- The literal total map of a finite horizontal-strip bicomplex morphism is a
quasi-isomorphism when each retained vertical column map is one. The vertical columns
may be unbounded, and the horizontal strip may be empty; finite diagonal support
constructs the total complexes in an arbitrary abelian category. -/
lemma totalMap_quasiIso_of_finiteStrip
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
  have hKT (p : ℤ) (_ : p ≤ b + 1) :
      (truncatedBicomplex K p).HasTotal (ComplexShape.up ℤ) :=
    tailHasTotal_of_upper_bound K b (fun p q hp => hK p q (Or.inr hp)) p
  have hLT (p : ℤ) (_ : p ≤ b + 1) :
      (truncatedBicomplex L p).HasTotal (ComplexShape.up ℤ) :=
    tailHasTotal_of_upper_bound L b (fun p q hp => hL p q (Or.inr hp)) p
  have hcol' (p : ℤ) (hpb : p ≤ b) : QuasiIso (f.f p) := by
    by_cases hpa : a ≤ p
    · exact hcol p hpa hpb
    · have hp' : p < a := by omega
      have hzK : IsZero (K.X p) := by
        rw [IsZero.iff_id_eq_zero]
        apply HomologicalComplex.Hom.ext
        funext q
        exact (hK p q (Or.inl hp')).eq_of_src _ _
      have hzL : IsZero (L.X p) := by
        rw [IsZero.iff_id_eq_zero]
        apply HomologicalComplex.Hom.ext
        funext q
        exact (hL p q (Or.inl hp')).eq_of_src _ _
      letI : IsIso (f.f p) := IsZero.isIso hzK hzL _
      infer_instance
  apply finiteStrip_totalMap_quasiIso_of_hasTotal f (min a (b + 1)) b (by omega)
    hKT hLT
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
