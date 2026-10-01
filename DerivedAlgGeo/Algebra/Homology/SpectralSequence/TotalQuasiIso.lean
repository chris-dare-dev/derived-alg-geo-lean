/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplexAdjacentCore
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FilteredTotalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms for mapping cones and first-quadrant totals

This file proves quasi-isomorphism criteria for mapping-cone maps and
first-quadrant total complexes of abelian groups.

## Main definitions

* `HomologicalComplex₂.IsVerticallyConnective` records vanishing in negative
  vertical degrees.
* `HomologicalComplex₂.IsHorizontallyConnective` records vanishing in negative
  horizontal degrees.

## Main results

* `CochainComplex.mappingCone.quasiIso_compMap` deduces a quasi-isomorphism
  for the cone map of a composite from quasi-isomorphisms for the two
  constituent cone maps.
* `CochainComplex.mappingCone.quasiIsoAt_inr_of_isZero_X` gives a
  quasi-isomorphism at the cone inclusion in degree `n` when the source `A`
  of the arrow `f : A ⟶ B` vanishes in degrees `n` and `n + 1`.
* `HomologicalComplex₂.totalMap_quasiIso` turns a columnwise
  quasi-isomorphism of first-quadrant bicomplexes of abelian groups into a
  quasi-isomorphism of their totals.

## Implementation notes

The composition result uses the octahedral mapping-cone triangle in the
derived category. The total result compares finite-column cones through
adjacent-column maps, then identifies the connective tail with the full
total. The generic adjacent-column maps and their cone quasi-isomorphism are
in `FilteredTotalComplexAdjacentCore`. The middle-term short-exact comparison
lives at the separate generic homology-sequence owner.
The downstream finite-strip comparison in `FiniteStripTotal` uses derived
short-exact triangles directly.

## References

These proofs use Mathlib's mapping-cone composition triangle, derived-category
localization, and homological-complex totalization.
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
  simpa only [truncatedBicomplexMap] using
    (HomologicalComplex.stupidTruncGEMap_naturality f p q hpq)

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
  apply HomologicalComplex.stupidTruncGEι_isIso_of_isZero
  intro p hp
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext q
  exact (hK p q hp).eq_of_src _ _

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
  exact HomologicalComplex.stupidTruncMap_comp_stupidTruncGEι f 0

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
