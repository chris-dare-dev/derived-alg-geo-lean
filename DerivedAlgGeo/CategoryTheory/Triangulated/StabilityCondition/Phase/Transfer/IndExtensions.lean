/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.TwoHeartEmbedding

/-!
# Ind-extensions of the dual t-structures of a slicing

Definition A.22 of arXiv:2607.28411v1 attaches to a slicing `𝒫` of `Dᵇ(X)` two
families of compactly generated t-structures on `Dqc(X)`: the Ind-extensions,
in the sense of Lemma A.14, of `τ_φ = (𝒫(> φ), 𝒫(≤ φ + 1))` and of
`τ'_φ = (𝒫(≥ φ), 𝒫(< φ + 1))`.  Corollary A.23 uses the primed family.  This
file packages that family for a slicing on a full triangulated subcategory `Q`
of an ambient category, as `TStructure.IndExtensionData` (Lemma A.14) at every
phase, and records what the restriction clause of Lemma A.14(iii) says when it
is read through the slicing.

## Main definitions

* `Slicing.IndExtensions`: the primed half of Definition A.22.
* `Slicing.IndExtensions.MapsSemistableAisle`: assumption (v') of Corollary
  A.23 for an endofunctor `G` of the ambient category, `G 𝒫(φ) ⊆ τ̂'_φ^{≤ 0}`.
* `Slicing.IndExtensions.ofCompactGenerators` and `ofBrown`: the two
  constructors, from Neeman-style compact generators at every phase through the
  owned Lemma A.14 and Theorem A.13.

## Main results

* `Slicing.IndExtensions.isLE_zero_iff_geProp` and `isGE_one_iff_ltProp`:
  Lemma A.14(iii) through the slicing, the two halves of the recognition
  formula (A.8) on the target.
* `Slicing.IndExtensions.tStructure_isBounded`: the restriction of `τ̂'_φ`
  to `Q` is bounded.
* `Slicing.IndExtensions.le_zero_anti`: the aisles `τ̂'_φ^{≤ 0}` decrease in
  `φ`.

## Implementation notes

The family is bundled rather than passed as a function plus a hypothesis,
because the family of large t-structures is data while
`TStructure.IndExtensionData` is a `Prop`; bundling also gives
`Slicing.IndExtensions.instHasInducedTStructure` a projection to key on.

`w` is the coproduct-size universe and is the first universe parameter of
every declaration here, which is what `.{w}` binds.

The consumers, the monad hypothesis and Corollary A.23, are in
`Phase/Transfer/Inducing.lean`; a realization of Definition A.22 needs only
this file.

## References

* arXiv:2607.28411v1, Lemma A.14 and Definition A.22.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] {Q : ObjectProperty D} [Q.IsTriangulated]

/-- The primed half of Definition A.22 of arXiv:2607.28411v1: the
Ind-extensions, in the sense of Lemma A.14, of the dual t-structures
`τ'_φ = (𝒫(≥ φ), 𝒫(< φ + 1))` of a slicing on the full subcategory `Q`, one
large t-structure `τ̂'_φ` on the ambient category at every phase.

Bundled rather than passed as a function plus a hypothesis because the family
of large t-structures is data while `TStructure.IndExtensionData` is a `Prop`;
bundling also gives `Slicing.IndExtensions.instHasInducedTStructure` a
projection to key on. -/
structure Slicing.IndExtensions (s : Slicing Q.FullSubcategory) where
  /-- The large t-structure `τ̂'_φ` at the phase `φ`. -/
  tStructure : ℝ → TStructure D
  /-- Lemma A.14 at `τ'_φ`: boundedness of `τ'_φ`, the aisle formula
  `τ̂'_φ^{≤ 0} = Coprod(𝒫(≥ φ))`, compact generation, the induced restriction,
  and the degreewise restriction equivalences.  Boundedness is the only clause
  about the slicing rather than about the extension;
  `Slicing.toDualTStructure_isBounded` supplies it. -/
  indExtensionData (φ : ℝ) :
    TStructure.IndExtensionData.{w} Q ((s.phaseShift _ φ).toDualTStructure _) (tStructure φ)

namespace Slicing.IndExtensions

variable {s : Slicing Q.FullSubcategory}

/-- Definition A.22 from compact generators at every phase: a family `G φ` of
compact objects with the approximation triangles of Theorem A.13, whose
coproduct-and-extension closure is that of `𝒫(≥ φ)`.  This is the Neeman-style
boundary of `TStructure.IndExtensionData.ofCompactGenerators`, phase by phase;
boundedness of `τ'_φ` is `Slicing.toDualTStructure_isBounded`. -/
def ofCompactGenerators (G : ℝ → ObjectProperty D)
    (happrox : ∀ φ : ℝ, TStructure.CompactGeneratorApproximation.{w} (G φ))
    (hcompact : ∀ φ : ℝ, G φ ≤ ObjectProperty.compactObjects.{w} (C := D))
    (hclosure : ∀ φ : ℝ, (G φ).coprodClosure.{w} =
      (TStructure.boundedAisle Q ((s.phaseShift _ φ).toDualTStructure _)).coprodClosure.{w}) :
    s.IndExtensions.{w} where
  tStructure φ := (happrox φ).tStructure
  indExtensionData φ :=
    TStructure.IndExtensionData.ofCompactGenerators Q _
      ((s.phaseShift _ φ).toDualTStructure_isBounded _) (happrox φ) (hcompact φ) (hclosure φ)

/-- Definition A.22 through the owned Brown tower: the approximation triangles
of Theorem A.13 are constructed, so the only inputs are shift-closed families
of compact generators with the right closure at every phase, as in
`TStructure.IndExtensionData.ofBrown`. -/
def ofBrown (G : ℝ → ObjectProperty D) [∀ φ : ℝ, ObjectProperty.Small.{0} (G φ)]
    [LocallySmall.{0} D] [HasCoproducts.{0} D]
    (hshift : ∀ φ : ℝ, G φ ≤ (G φ).shift (1 : ℤ))
    (hcompact : ∀ φ : ℝ, G φ ≤ ObjectProperty.compactObjects.{0} (C := D))
    (hclosure : ∀ φ : ℝ, (G φ).coprodClosure.{0} =
      (TStructure.boundedAisle Q ((s.phaseShift _ φ).toDualTStructure _)).coprodClosure.{0}) :
    s.IndExtensions.{0} where
  tStructure φ := TStructure.CompactGeneratorBrown.tStructure (G := G φ) (hshift φ) (hcompact φ)
  indExtensionData φ :=
    TStructure.IndExtensionData.ofBrown Q _
      ((s.phaseShift _ φ).toDualTStructure_isBounded _) (hshift φ) (hcompact φ) (hclosure φ)

variable (ind : s.IndExtensions.{w})

instance instHasInducedTStructure (φ : ℝ) : Q.HasInducedTStructure (ind.tStructure φ) :=
  (ind.indExtensionData φ).hasInduced

/-- Clause (iii) of Lemma A.14 at degree zero, composed with the phase
dictionary: `τ̂'_φ` restricts to `τ'_φ` on `Q`, and the aisle of `τ'_φ` is
`𝒫(≥ φ)`.  This is the left half of the recognition formula (A.8), and it is
why the induced source t-structures can be read phase-wise rather than
degree-wise. -/
theorem isLE_zero_iff_geProp (φ : ℝ) (X : Q.FullSubcategory) :
    (ind.tStructure φ).IsLE X.obj 0 ↔ s.geProp _ φ X :=
  ((ind.indExtensionData φ).isLE_iff X 0).trans
    (s.phaseShift_toDualTStructure_isLE_zero_iff _ φ X)

/-- The same at degree one.  Degree one and not zero because
`τ'_φ = (𝒫(≥ φ), 𝒫(< φ + 1))`: its degree-zero coaisle is `𝒫(< φ + 1)`, and
one shift lands on the cut `𝒫(< φ)` that (A.8) uses. -/
theorem isGE_one_iff_ltProp (φ : ℝ) (X : Q.FullSubcategory) :
    (ind.tStructure φ).IsGE X.obj 1 ↔ s.ltProp _ φ X :=
  ((ind.indExtensionData φ).isGE_iff X 1).trans
    (s.phaseShift_toDualTStructure_isGE_one_iff _ φ X)

/-- The restriction of `τ̂'_φ` to `Q` is bounded, since `τ'_φ` is. -/
theorem tStructure_isBounded (φ : ℝ) : (Q.tStructure (ind.tStructure φ)).IsBounded := by
  intro X
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (ind.indExtensionData φ).small_isBounded X
  exact ⟨⟨a, (Q.tStructure_isGE_iff (ind.tStructure φ) X a).2
      (((ind.indExtensionData φ).isGE_iff X a).2 ha)⟩,
    ⟨b, (Q.tStructure_isLE_iff (ind.tStructure φ) X b).2
      (((ind.indExtensionData φ).isLE_iff X b).2 hb)⟩⟩

/-- The aisles `τ̂'_φ^{≤ 0}` decrease in `φ`, as the cuts `𝒫(≥ φ)` do. -/
theorem le_zero_anti {φ ψ : ℝ} (h : φ ≤ ψ) :
    (ind.tStructure ψ).le 0 ≤ (ind.tStructure φ).le 0 := by
  rw [(ind.indExtensionData ψ).largeAisle, (ind.indExtensionData φ).largeAisle]
  refine ObjectProperty.coprodClosure_le _
    (le_trans ?_ (ObjectProperty.le_coprodClosure.{w} _))
  rintro Z ⟨X, hX, ⟨e⟩⟩
  refine ⟨X, ?_, ⟨e⟩⟩
  exact ((s.phaseShift_toDualTStructure_isLE_zero_iff _ φ X).2
    (s.geProp_anti _ h X ((s.phaseShift_toDualTStructure_isLE_zero_iff _ ψ X).1 ⟨hX⟩))).le

/-- Assumption (v') of Corollary A.23 of arXiv:2607.28411v1 for an
endofunctor `G` of the ambient category: `G` sends every semistable object of
phase `φ` into the aisle `τ̂'_φ^{≤ 0} = 𝒫̂(≥ φ)`.  At the monad `G = Φ Φ_L`
this is the paper's `Φ Φ_L 𝒫(φ) ⊆ 𝒫̂(≥ φ)`.  It is stated on semistable
objects, as the paper states it; `Slicing.IndExtensions.monad_isLE_zero_of_geProp`
extends it to `𝒫(≥ φ)`. -/
def MapsSemistableAisle (G : D ⥤ D) : Prop :=
  ∀ (φ : ℝ) (E : Q.FullSubcategory), s.P φ E → (ind.tStructure φ).IsLE (G.obj E.obj) 0

end Slicing.IndExtensions

end CategoryTheory.Triangulated
