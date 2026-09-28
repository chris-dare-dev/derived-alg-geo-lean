/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Canonical good-truncation towers

Mathlib's good truncations assemble into a natural ℕ-indexed tower. Under
local homology hypotheses, their inclusion cocone is colimiting.

## Main definitions

`CochainComplex.truncLEToTruncLE` gives the transitions;
`CochainComplex.truncLETower` and `CochainComplex.truncLETowerCocone`
assemble the diagram and its inclusions; `CochainComplex.truncLETowerMap`
acts on morphisms.

## Main results

`CochainComplex.isColimitTruncLETowerCocone` proves the colimit property.

## Implementation notes

At degree `p`, the inclusion is an isomorphism when the cutoff is strictly
greater than `p`; at the cutoff the truncation contains cycles. Evaluation
is eventually constant, and degreewise colimits assemble into a colimit of
complexes.

## References

This extends Mathlib's `CochainComplex.truncLE`, `CochainComplex.ιTruncLE`,
and `CochainComplex.truncLEMap`.

## Tags

good truncation, cochain complexes, colimits
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The transition is characterized by its composite with the monic inclusion into `K`:
that composite is the inclusion at the earlier cutoff. -/
noncomputable def truncLEToTruncLE (K : CochainComplex C ℤ) [∀ i, K.HasHomology i]
    {n m : ℤ} (h : n ≤ m) : K.truncLE n ⟶ K.truncLE m := by
  letI : (K.truncLE n).IsStrictlyLE m :=
    (K.truncLE n).isStrictlyLE_of_le n m h
  exact (asIso ((K.truncLE n).ιTruncLE m)).inv ≫
    CochainComplex.truncLEMap (K.ιTruncLE n) m

/-- Monicity of the later inclusion makes this equation the uniqueness principle used to
prove the tower's functor laws. -/
@[reassoc]
lemma truncLEToTruncLE_comp_ιTruncLE (K : CochainComplex C ℤ) [∀ i, K.HasHomology i]
    {n m : ℤ} (h : n ≤ m) :
    truncLEToTruncLE K h ≫ K.ιTruncLE m = K.ιTruncLE n := by
  letI : (K.truncLE n).IsStrictlyLE m :=
    (K.truncLE n).isStrictlyLE_of_le n m h
  dsimp [truncLEToTruncLE]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality]
  simp

/-- Natural-number cutoffs are cofinal among integer cutoffs; at each fixed degree,
components stabilize once the cutoff is strictly above that degree. -/
noncomputable def truncLETower (K : CochainComplex C ℤ) [∀ i, K.HasHomology i] :
    ℕ ⥤ CochainComplex C ℤ where
  obj n := K.truncLE (n : ℤ)
  map {n m} f := truncLEToTruncLE K (by exact_mod_cast leOfHom f)
  map_id n := by
    haveI : Mono (K.ιTruncLE (n : ℤ)) := by
      dsimp [CochainComplex.ιTruncLE]
      infer_instance
    apply (cancel_mono (K.ιTruncLE (n : ℤ))).mp
    simpa using truncLEToTruncLE_comp_ιTruncLE K (le_refl (n : ℤ))
  map_comp {n m l} f g := by
    haveI : Mono (K.ιTruncLE (l : ℤ)) := by
      dsimp [CochainComplex.ιTruncLE]
      infer_instance
    apply (cancel_mono (K.ιTruncLE (l : ℤ))).mp
    simp only [Category.assoc, truncLEToTruncLE_comp_ιTruncLE]

private lemma inclusionComponentIsIso (K : CochainComplex C ℤ) [∀ i, K.HasHomology i]
    (n p : ℤ) (hp : p < n) : IsIso ((K.ιTruncLE n).f p) := by
  dsimp [CochainComplex.ιTruncLE, HomologicalComplex.ιTruncLE]
  change IsIso (((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f p).unop)
  have hcomponent : IsIso ((K.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f p) := by
    let e := (ComplexShape.embeddingUpIntLE n).op
    let m := (n - p).natAbs
    have hi : e.f m = p := by
      change n - ((n - p).natAbs : ℤ) = p
      rw [Int.natAbs_of_nonneg (by omega)]
      omega
    have hnb : ¬ e.BoundaryGE m := by
      change ¬ (ComplexShape.embeddingUpIntLE n).BoundaryLE m
      rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
      dsimp [m]
      omega
    change IsIso ((e.liftExtend (K.op.restrictionToTruncGE' e)
      (K.op.restrictionToTruncGE'_hasLift e)).f p)
    apply (e.isIso_liftExtend_f_iff _ _ hi).2
    exact K.op.isIso_restrictionToTruncGE' e m hnb
  infer_instance

/-- The inclusion cocone on the canonical good-truncation tower. Its point is the
original complex and its legs are the canonical inclusions. -/
noncomputable def truncLETowerCocone (K : CochainComplex C ℤ) [∀ i, K.HasHomology i] :
    Cocone (truncLETower K) where
  pt := K
  ι := {
    app n := K.ιTruncLE (n : ℤ)
    naturality := by
      intro n m f
      change truncLEToTruncLE K (by exact_mod_cast leOfHom f) ≫ K.ιTruncLE (m : ℤ) =
        K.ιTruncLE (n : ℤ) ≫ 𝟙 K
      simp [truncLEToTruncLE_comp_ιTruncLE]
  }

private noncomputable def towerEvalIsColimit (K : CochainComplex C ℤ)
    [∀ i, K.HasHomology i] (p : ℤ) :
    IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone
      (truncLETowerCocone K)) := by
  let n : ℕ := p.toNat + 1
  have hp : p < (n : ℤ) := by dsimp [n]; omega
  let F := truncLETower K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p
  have hF : F.IsEventuallyConstantFrom n := by
    intro m f
    have hnm : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast leOfHom f
    haveI : IsIso ((K.ιTruncLE (n : ℤ)).f p) :=
      inclusionComponentIsIso K (n : ℤ) p hp
    haveI : IsIso ((K.ιTruncLE (m : ℤ)).f p) :=
      inclusionComponentIsIso K (m : ℤ) p (by omega)
    have heq := congrArg (fun z => z.f p) (truncLEToTruncLE_comp_ιTruncLE K hnm)
    change IsIso ((truncLEToTruncLE K hnm).f p)
    exact IsIso.of_isIso_fac_right heq
  let c := (HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone
    (truncLETowerCocone K)
  haveI : IsIso (c.ι.app n) := inclusionComponentIsIso K (n : ℤ) p hp
  exact hF.isColimitOfIsIso c

/-- Every cochain complex is the colimit of its canonical increasing good-truncation
tower. This uses local homology assumptions needed to form the good truncations. -/
noncomputable def isColimitTruncLETowerCocone (K : CochainComplex C ℤ)
    [∀ i, K.HasHomology i] : IsColimit (truncLETowerCocone K) :=
  HomologicalComplex.isColimitOfEval _ _ (towerEvalIsColimit K)

/-- Composing both sides with the monic later inclusion reduces this compatibility to
naturality of Mathlib's truncation inclusions. -/
lemma truncLEToTruncLE_naturality {K L : CochainComplex C ℤ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    (f : K ⟶ L) {n m : ℤ} (h : n ≤ m) :
    CochainComplex.truncLEMap f n ≫ truncLEToTruncLE L h =
      truncLEToTruncLE K h ≫ CochainComplex.truncLEMap f m := by
  haveI : Mono (L.ιTruncLE m) := by dsimp [CochainComplex.ιTruncLE]; infer_instance
  apply (cancel_mono (L.ιTruncLE m)).mp
  simp only [Category.assoc, truncLEToTruncLE_comp_ιTruncLE,
    CochainComplex.ιTruncLE_naturality, truncLEToTruncLE_comp_ιTruncLE_assoc]

/-- A morphism of complexes induces a map between their canonical good-truncation
towers, degreewise by Mathlib's `CochainComplex.truncLEMap`. -/
noncomputable def truncLETowerMap {K L : CochainComplex C ℤ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    (f : K ⟶ L) : truncLETower K ⟶ truncLETower L where
  app n := CochainComplex.truncLEMap f (n : ℤ)
  naturality {n m} g :=
    (truncLEToTruncLE_naturality f (by exact_mod_cast leOfHom g)).symm

/-- Together with the colimit theorem, this identifies the map induced on colimit
points by `truncLETowerMap f` with `f`. -/
lemma truncLETowerMap_ι {K L : CochainComplex C ℤ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    (f : K ⟶ L) (n : ℕ) :
    (truncLETowerMap f).app n ≫ (truncLETowerCocone L).ι.app n =
      (truncLETowerCocone K).ι.app n ≫ f :=
  CochainComplex.ιTruncLE_naturality f (n : ℤ)

/-- The identity law follows stagewise from Mathlib's fixed-cutoff truncation map law. -/
lemma truncLETowerMap_id (K : CochainComplex C ℤ) [∀ i, K.HasHomology i] :
    truncLETowerMap (𝟙 K) = 𝟙 (truncLETower K) := by
  apply NatTrans.ext
  funext n
  exact HomologicalComplex.truncLEMap_id K (ComplexShape.embeddingUpIntLE (n : ℤ))

/-- The composition law follows stagewise from Mathlib's fixed-cutoff truncation map law. -/
lemma truncLETowerMap_comp {K L M : CochainComplex C ℤ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] [∀ i, M.HasHomology i]
    (f : K ⟶ L) (g : L ⟶ M) :
    truncLETowerMap (f ≫ g) = truncLETowerMap f ≫ truncLETowerMap g := by
  apply NatTrans.ext
  funext n
  exact HomologicalComplex.truncLEMap_comp f g (ComplexShape.embeddingUpIntLE (n : ℤ))

end CochainComplex
