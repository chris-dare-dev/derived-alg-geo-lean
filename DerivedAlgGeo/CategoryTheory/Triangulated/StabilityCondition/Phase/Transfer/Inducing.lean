/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Adjoint
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.HN
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.IndExtensions
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Polishchuk

/-!
# Corollary A.23: inducing a slicing through Theorem A.17

Corollary A.23 of arXiv:2607.28411v1 produces a slicing on the source of a
functor `Φ` from a slicing on its target.  Its proof applies Theorem A.17 at
every real phase `φ`, to the Ind-extension `τ̂'_φ` (Definition A.22) of the
dual t-structure `τ'_φ = (𝒫(≥ φ), 𝒫(< φ + 1))` of the target slicing, and
then reads the resulting family of bounded t-structures through the
recognition formulas (A.8).  The repository already owns both ends of that
argument: `Polishchuk.induce` is Theorem A.17, and
`Slicing.InducedTStructures.preimageData` is the finite phase-truncation
argument that turns (A.8) into slicing data.  This file is the joint between
them; the Definition A.22 input is `Slicing.IndExtensions`.

## Main definitions

* `Slicing.IndExtensions.InducedTStructuresLarge`: the large-target twin of
  `Slicing.InducedTStructures`, with (A.8) read against the Ind-extensions
  themselves and no target subcategory; `ofIso` transports it along a natural
  isomorphism of the detecting functor, and `toInducedTStructures` /
  `ofInducedTStructures` identify it with the bounded shape whenever the
  detecting functor factors through `Q`.
* `Slicing.IndExtensions.largePreimagePhase`: the phase collection
  `Slicing.IndExtensions.largePhase` pulls back to along the detecting
  functor, the large-target analogue of `Slicing.preimagePhase`.

## Main results

* `Slicing.IndExtensions.monad_isRightTExact`: assumption (v') of Corollary
  A.23, stated on semistable objects, implies assumption (v) of Theorem A.17
  at every phase: the monad is right t-exact for `τ̂'_φ`.  This is the step
  the paper summarizes as "(v') precisely corresponds to (v)".
* `Slicing.IndExtensions.nonempty_inducedTStructures`: Theorem A.17 at every
  phase assembles into the phase-indexed recognition formulas (A.8).
* `Slicing.IndExtensions.preimageData`: **Corollary A.23, without the
  S-local half**: the preimage collection (A.7) is a slicing.
* `Slicing.IndExtensions.mapsSemistableGE_iff`: assumption (v') is the
  bounded predicate `Slicing.MapsSemistableGE` of the monad restricted to
  `Q`, which `Slicing.MapsSemistableGE.of_mapsSemistableLE` produces from
  condition (3.2) of Proposition 3.8.
* `Slicing.IndExtensions.preimageData_of_le`: Corollary A.23 on a triangulated
  source subcategory `P ≤ F⁻¹ Q` with truncation stability supplied; the
  detecting functor is `ObjectProperty.liftOfLE F hle`.
* `Slicing.IndExtensions.preimageData_of_coproduct`: Corollary A.23 when the
  monad is a coproduct of identities, the categorical shape of Theorem 2.8(1)
  on `F⁻¹ Q`, and `preimageData_of_coproduct_of_le`, the same on a chosen
  `P ≤ F⁻¹ Q`.
* `Slicing.IndExtensions.preimageData_of_mapsSemistableLE`: **Proposition
  3.8**, categorically: condition (3.2) on the restricted comonad, through the
  adjunctions restricted to `Q` and `F⁻¹ Q`, gives the preimage slicing.
* `Slicing.IndExtensions.InducedTStructuresLarge.hom_vanishing`: the first
  non-formal `Slicing` axiom for `largePreimagePhase`.
* `Slicing.IndExtensions.nonempty_inducedTStructuresLarge`: Corollary A.23 in
  that shape, the categorical half of Theorem 2.8(1) for an arbitrary field
  extension at the level of the phase-indexed t-structures.

## Implementation notes

The large categories are `C` and `D`; the bounded ones are the full
subcategories `Q ⊆ D` and either its inverse image `F⁻¹ Q ⊆ C`, so that
hypothesis (iv) of Theorem A.17 holds by construction, as in
`Polishchuk.induce`, or a chosen triangulated `P ≤ F⁻¹ Q` with truncation
stability supplied, as in `Polishchuk.induceOfLE`.  The slicing lives on
`Q`, and the detecting functor of the output is the restriction of `F`,
`ObjectProperty.inverseImageLift F Q` or `ObjectProperty.liftOfLE F hle`.
Theorem 2.8 for an infinite extension is in neither shape: it recognizes the
base-changed slicing against the Ind-extensions on the large `D`, with no `Q`.
That is the third shape, `InducedTStructuresLarge` and
`nonempty_inducedTStructuresLarge`, on `Polishchuk.induceLarge`; its phase
collection is `Slicing.IndExtensions.largePreimagePhase`, built from
`largePhase`, which `largePhase_iff_semistable` identifies with `s.P` on `Q`.

Assembling those into a `Slicing` is the accounting of `Slicing.PreimageData`
with one entry moved.  Closure under isomorphisms and zero membership still
follow formally, from the iso- and zero-invariance of `IsLE` and `IsGE`.  The
shift law no longer does: there is no slicing on `D` to borrow `shift_iff`
from, and `Slicing.IndExtensions` relates the aisles at two phases only by
inclusion (`le_zero_anti`), never by the shift, so `𝒫̂(φ)⟦1⟧ = 𝒫̂(φ + 1)` has
to be proved from `largeAisle` and a shift equality for
`ObjectProperty.coprodClosure` that the repository does not have.  HN
existence is the other open half: the bounded twin lifts a target HN
filtration (`Slicing.InducedTStructures.hn_exists`), and the ambient category
carries no slicing to lift one from, so it needs the finite phase-truncation
argument run on the source -- which is why `InducedTStructuresLarge` keeps
Step 4's boundedness that the bounded twin can afford to drop.

Assumption (v') is `Slicing.IndExtensions.MapsSemistableAisle`, stated as the
paper states it, on semistable objects and in the large category.  Extending
it to `𝒫(≥ φ)` uses that the aisles `τ̂'_φ^{≤ 0}` decrease in `φ` and are
closed under extensions, and then right t-exactness follows because the aisle
is the coproduct-and-extension closure of `𝒫(≥ φ)` (Lemma A.14(i)) and the
monad preserves coproducts and triangles.

The source-side existence input of Theorem A.17, a t-structure on `C`
compactly generated by the left-adjoint image of some generators of `τ̂'_φ`,
is taken as the hypothesis `hsrc`, in the shape `Polishchuk.induce` consumes;
`Polishchuk.induceOfApproximation` and `induceOfBrown` show how the owned
Theorem A.13 constructions discharge it.  The `_of_le` theorems take the same
input as the families `G`, `tC` with `hG`, `htC` rather than as a single
existential, because `htrunc` must name `tC φ`.

Assumption (i) of Theorem A.17, S-linearity of `Φ`, and the S-locality of the
input and output slicings are outside the categorical layer, as in
`Polishchuk.lean`; what is proved here is Corollary A.23 at `S = Spec ℤ`.

`w` is the coproduct-size universe and is the first universe parameter of
every declaration here, which is what `.{w}` binds.  Both categories share one
hom universe `v`, as `Polishchuk.induce` requires.

Nothing here is geometric.  Realizing `Slicing.IndExtensions` for the
standard slicings of `Dᵇ(Coh)` inside `Dqc`, the adjunctions `f_! ⊣ f^* ⊣ f_*`
on `Dqc`, the preservation of `Dᵇ(Coh)` by `f^* f_!` and `f^* f_*`, and
conservativity of `f^*` on bounded objects, which the paper gets from faithful
flatness, are the remaining inputs of Proposition 3.8;
`preimageData_of_mapsSemistableLE` states exactly what they must supply.

## References

* arXiv:2607.28411v1, Theorem 2.8, Definition A.22, Corollary A.23, and the proof of
  Proposition 3.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u₁ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v} C]
  {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
  {Q : ObjectProperty D} [Q.IsTriangulated]

namespace Slicing.IndExtensions

variable {s : Slicing Q.FullSubcategory} (ind : s.IndExtensions.{w})

/-- Assumption (v') of Corollary A.23 is the bounded predicate
`Slicing.MapsSemistableGE` of the monad restricted to `Q`, whenever the
monad preserves `Q`.  For `f^* f_!` this is the reading of Proposition 3.8:
`f_!` preserves `Dᵇ(Coh)` when the relative dualizing complex is perfect, and
then `f^* f_! 𝒫(φ) ⊆ 𝒫̂(≥ φ)` is `f^* f_! 𝒫(φ) ⊆ 𝒫(≥ φ)`. -/
theorem mapsSemistableGE_iff {L : D ⥤ C} {F : C ⥤ D}
    (hQL : ∀ E : D, Q E → Q (F.obj (L.obj E))) :
    s.MapsSemistableGE (ObjectProperty.liftToInverseImage F Q L hQL ⋙
        ObjectProperty.inverseImageLift F Q) ↔
      ind.MapsSemistableAisle (L ⋙ F) :=
  forall_congr' fun φ => forall_congr' fun _ => imp_congr_right fun _ =>
    (ind.isLE_zero_iff_geProp φ _).symm

section Monad

variable {L : D ⥤ C} {F : C ⥤ D}
  [(L ⋙ F).Additive] [(L ⋙ F).CommShift ℤ] [(L ⋙ F).IsTriangulated]

/-- Assumption (v') of Corollary A.23 extends from semistable objects of
phase `φ` to all of `𝒫(≥ φ)`: the monad carries the HN filtration to a
Postnikov tower whose factors lie in aisles `τ̂'_ψ^{≤ 0} ⊆ τ̂'_φ^{≤ 0}` for
`ψ ≥ φ`, and aisles are closed under extensions. -/
theorem monad_isLE_zero_of_geProp (hv : ind.MapsSemistableAisle (L ⋙ F))
    {φ : ℝ} {E : Q.FullSubcategory} (hE : s.geProp _ φ E) :
    (ind.tStructure φ).IsLE ((L ⋙ F).obj E.obj) 0 := by
  rcases hE with hz | ⟨Fil, hn, hge⟩
  · exact (ind.tStructure φ).isLE_of_isZero ((L ⋙ F).map_isZero (Q.ι.map_isZero hz)) 0
  · have hfac : ∀ i, (ind.tStructure φ).le 0
        ((PostnikovTower.mapF Fil.toPostnikovTower (Q.ι ⋙ L ⋙ F)).factor i) := by
      intro i
      exact ind.le_zero_anti (hge.trans (Fil.phase_mem_range _ hn i).1) _
        (hv (Fil.φ i) (Fil.factor i) (Fil.semistable i)).le
    refine ⟨ExtensionClosure.le_of_closed (fun hz => ((ind.tStructure φ).isLE_of_isZero hz 0).le)
      le_rfl (fun hT hX hY => ((ind.tStructure φ).isLE₂ _ hT 0 ⟨hX⟩ ⟨hY⟩).le) _
      (ExtensionClosure.ofPostnikovTower _ hfac)⟩

/-- **Assumption (v') implies assumption (v).**  If the monad `L ⋙ F`
preserves coproducts and sends `𝒫(φ)` into `τ̂'_φ^{≤ 0}` for every `φ`, then
it is right t-exact for `τ̂'_φ`: the aisle is the coproduct-and-extension
closure of `𝒫(≥ φ)` by Lemma A.14(i), the monad carries that closure into
the closure of its image, and the image lies in the aisle by
`Slicing.IndExtensions.monad_isLE_zero_of_geProp`. -/
theorem monad_isRightTExact (hLF : (L ⋙ F).PreservesSmallCoproducts.{w})
    (hv : ind.MapsSemistableAisle (L ⋙ F)) (φ : ℝ) :
    (L ⋙ F).IsRightTExact (ind.tStructure φ) (ind.tStructure φ) :=
  (L ⋙ F).isRightTExact_of_isLE_zero fun X hX => by
    have hX' : (TStructure.boundedAisle Q
        ((s.phaseShift _ φ).toDualTStructure _)).coprodClosure.{w} X := by
      rw [← (ind.indExtensionData φ).largeAisle]
      exact hX.le
    have hmap := (TStructure.boundedAisle Q
      ((s.phaseShift _ φ).toDualTStructure _)).coprodClosure_map_obj (L ⋙ F) hLF hX'
    have hgen : (TStructure.boundedAisle Q
        ((s.phaseShift _ φ).toDualTStructure _)).map (L ⋙ F) ≤ (ind.tStructure φ).le 0 := by
      rintro Z ⟨Y, ⟨X', hX', ⟨eι⟩⟩, ⟨eLF⟩⟩
      haveI : (ind.tStructure φ).IsLE ((L ⋙ F).obj (Q.ι.obj X')) 0 :=
        ind.monad_isLE_zero_of_geProp hv
          ((s.phaseShift_toDualTStructure_isLE_zero_iff _ φ X').1 ⟨hX'⟩)
      exact ((ind.tStructure φ).isLE_of_iso (((L ⋙ F).mapIso eι).trans eLF) 0).le
    rw [(ind.indExtensionData φ).largeAisle] at hgen
    refine ⟨?_⟩
    rw [(ind.indExtensionData φ).largeAisle]
    exact ObjectProperty.coprodClosure_le _ hgen _ hmap

end Monad

section Large

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The phase collection `largePhase` pulls back to along `F`: the large-target analogue of
`Slicing.preimagePhase`, which cannot be used here because it needs a slicing on the target.
This is the collection the eventual slicing `𝒫_ℓ` carries; `InducedTStructuresLarge.hom_vanishing`
is one of its `Slicing` axioms. -/
def largePreimagePhase (F : C ⥤ D) (φ : ℝ) : ObjectProperty C :=
  fun E => ind.largePhase φ (F.obj E)

/-- The large-target twin of `Slicing.InducedTStructures`: the bounded output of Theorem A.17
at every phase, with the recognition formulas (A.8) read against the Ind-extensions on the
ambient category rather than against the slicing on `Q`.

This is the shape Theorem 2.8(1) of arXiv:2607.28411v1 needs for an arbitrary field extension
`ℓ/k`.  There `F = π_*` sends no nonzero object of `Dᵇ(Coh X_ℓ)` into `Q = Dᵇ(Coh X)`, so
`s.geProp` and `s.ltProp` are not defined at `F.obj E` and `Slicing.InducedTStructures` cannot
be stated; the cuts of `τ̂'_φ` on the ambient `Dqc(X)` still are.  `toInducedTStructures` and
`ofInducedTStructures` show the two structures agree whenever `F` does land in `Q`, so this is
a genuine extension of the bounded shape and not a second notion. -/
structure InducedTStructuresLarge (F : C ⥤ D) where
  /-- The source t-structure induced at the phase `φ`. -/
  tStructure : ℝ → TStructure C
  /-- Formula (A.8), connective half, against `τ̂'_φ`. -/
  le_zero_iff (φ : ℝ) (E : C) :
    (tStructure φ).IsLE E 0 ↔ (ind.tStructure φ).IsLE (F.obj E) 0
  /-- Formula (A.8), coconnective half, against `τ̂'_φ`. -/
  ge_one_iff (φ : ℝ) (E : C) :
    (tStructure φ).IsGE E 1 ↔ (ind.tStructure φ).IsGE (F.obj E) 1
  /-- Step 4 of Theorem A.17: each induced source t-structure is bounded.  The bounded twin
  has no such field because it never truncates on the source -- it lifts a target HN
  filtration -- whereas the finite phase-truncation argument this shape needs does. -/
  isBounded (φ : ℝ) : TStructure.IsBounded (tStructure φ)

namespace InducedTStructuresLarge

/-- Hom-vanishing for the large phase collection, the first non-formal slicing axiom.

Shorter than its bounded twin: `largePhase` already carries the coaisle membership at every
`ψ > φ₁`, so no HN filtration of the target is needed to move from phase `φ₂` up to `φ₁` --
which is what makes this provable at all when the target has no slicing. -/
theorem hom_vanishing {F : C ⥤ D} (h : ind.InducedTStructuresLarge F) :
    ∀ (φ₁ φ₂ : ℝ) (A B : C), φ₂ < φ₁ →
      ind.largePreimagePhase F φ₁ A → ind.largePreimagePhase F φ₂ B →
        ∀ g : A ⟶ B, g = 0 := fun φ₁ φ₂ A B hφ hA hB g =>
  (h.tStructure φ₁).zero_of_isLE_of_isGE g 0 1 (by omega)
    ((h.le_zero_iff φ₁ A).2 hA.1) ((h.ge_one_iff φ₁ B).2 (hB.2 φ₁ hφ))

/-- The recognition formulas are invariant under a natural isomorphism of the detecting
functor, as in `Slicing.InducedTStructures.ofIso`; here the transport is through the aisle
and coaisle of `τ̂'_φ` rather than through the phase cuts. -/
def ofIso {F G : C ⥤ D} (h : ind.InducedTStructuresLarge F) (e : F ≅ G) :
    ind.InducedTStructuresLarge G where
  tStructure := h.tStructure
  le_zero_iff φ E := (h.le_zero_iff φ E).trans
    ⟨fun hE => letI := hE; (ind.tStructure φ).isLE_of_iso (e.app E) 0,
      fun hE => letI := hE; (ind.tStructure φ).isLE_of_iso (e.app E).symm 0⟩
  ge_one_iff φ E := (h.ge_one_iff φ E).trans
    ⟨fun hE => letI := hE; (ind.tStructure φ).isGE_of_iso (e.app E) 1,
      fun hE => letI := hE; (ind.tStructure φ).isGE_of_iso (e.app E).symm 1⟩
  isBounded := h.isBounded

/-- When the detecting functor lands in `Q`, the large twin is the bounded structure: both
recognition formulas are Lemma A.14(iii). -/
def toInducedTStructures {G : C ⥤ Q.FullSubcategory}
    (h : ind.InducedTStructuresLarge (G ⋙ Q.ι)) : s.InducedTStructures G where
  tStructure := h.tStructure
  le_zero_iff φ E := (h.le_zero_iff φ E).trans (ind.isLE_zero_iff_geProp φ (G.obj E))
  ge_one_iff φ E := (h.ge_one_iff φ E).trans (ind.isGE_one_iff_ltProp φ (G.obj E))

/-- The converse: a bounded structure is a large one along the inclusion of `Q`.  With
`toInducedTStructures` this makes the two structures interderivable whenever `F` factors
through `Q`, which is the sense in which the bounded shape is the special case.

Boundedness has to be supplied: `Slicing.InducedTStructures` carries no such field, because
its own consumer never needs it.  Where the source t-structures come from Theorem A.17 it is
`Polishchuk.InducedTStructureDataLarge.isBounded`. -/
def ofInducedTStructures {G : C ⥤ Q.FullSubcategory} (h : s.InducedTStructures G)
    (hb : ∀ φ : ℝ, TStructure.IsBounded (h.tStructure φ)) :
    ind.InducedTStructuresLarge (G ⋙ Q.ι) where
  tStructure := h.tStructure
  le_zero_iff φ E := (h.le_zero_iff φ E).trans (ind.isLE_zero_iff_geProp φ (G.obj E)).symm
  ge_one_iff φ E := (h.ge_one_iff φ E).trans (ind.isGE_one_iff_ltProp φ (G.obj E)).symm
  isBounded := hb

end InducedTStructuresLarge

end Large

section Induce

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Q.IsClosedUnderIsomorphisms]
  {L : D ⥤ C} {F : C ⥤ D} [L.CommShift ℤ] [L.IsTriangulated]
  [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

/-- **Theorem A.17 at every phase.**  Under the hypotheses of Theorem A.17
with `Φ = F`, hypothesis (iv) built in as `P = F⁻¹ Q`, and assumption (v')
of Corollary A.23 in place of (v), the induced bounded t-structures on
`F⁻¹ Q` satisfy the recognition formulas (A.8) for the slicing on `Q`.  The
source-side input `hsrc` is Theorem A.13 on `C` for the left-adjoint image of
one generating family of each `τ̂'_φ`, the shape `Polishchuk.induce`
consumes. -/
theorem nonempty_inducedTStructures (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (hsrc : ∀ φ : ℝ, ∃ (G : ObjectProperty D) (tC : TStructure C),
      (ind.tStructure φ).IsCompactlyGeneratedBy.{w} G ∧
        tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hv : ind.MapsSemistableAisle (L ⋙ F)) :
    Nonempty (s.InducedTStructures (ObjectProperty.inverseImageLift F Q)) := by
  have hL : L.PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI : PreservesColimitsOfShape (Discrete ι) L :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    infer_instance
  have hLF : (L ⋙ F).PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI := hL ι
    haveI := hF ι
    infer_instance
  have hdata : ∀ φ : ℝ, Nonempty (Polishchuk.InducedTStructureData F (Q.inverseImage F) Q
      (ind.tStructure φ) le_rfl) := by
    intro φ
    obtain ⟨G, tC, hG, htC⟩ := hsrc φ
    exact ⟨Polishchuk.induce adj hF hG htC (ind.monad_isRightTExact hLF hv φ) hzero
      (ind.tStructure_isBounded φ)⟩
  refine ⟨{ tStructure := fun φ => (hdata φ).some.tStructure
            le_zero_iff := fun φ E => ?_
            ge_one_iff := fun φ E => ?_ }⟩
  · exact ((hdata φ).some.isLE_iff E 0).trans
      ((Q.tStructure_isLE_iff (ind.tStructure φ) _ 0).trans (ind.isLE_zero_iff_geProp φ _))
  · exact ((hdata φ).some.isGE_iff E 1).trans
      ((Q.tStructure_isGE_iff (ind.tStructure φ) _ 1).trans (ind.isGE_one_iff_ltProp φ _))

/-- **Corollary A.23 of arXiv:2607.28411v1, without the S-local half.**  The
preimage collection (A.7), `𝒫_X(φ) = {E | F E ∈ 𝒫(φ)}` on `F⁻¹ Q`, is a
slicing: the phase-indexed t-structures of
`Slicing.IndExtensions.nonempty_inducedTStructures` supply Hom-vanishing and,
through the finite phase-truncation argument
`Slicing.InducedTStructures.preimageData`, HN filtrations.  The slicing itself
is `s.preimage (ObjectProperty.inverseImageLift F Q)` at this witness. -/
theorem preimageData [IsTriangulated C] (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (hsrc : ∀ φ : ℝ, ∃ (G : ObjectProperty D) (tC : TStructure C),
      (ind.tStructure φ).IsCompactlyGeneratedBy.{w} G ∧
        tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hv : ind.MapsSemistableAisle (L ⋙ F)) :
    s.PreimageData (ObjectProperty.inverseImageLift F Q) :=
  (ind.nonempty_inducedTStructures adj hF hsrc hzero hv).elim fun h => h.preimageData

omit [Q.IsClosedUnderIsomorphisms] in
/-- **Theorem A.17 at every phase, on a chosen source subcategory.**  As
`nonempty_inducedTStructures`, but on a triangulated `P ≤ F⁻¹ Q` with truncation stability
under the source t-structures `tC φ` supplied (`htrunc`), with zero reflection required only
on `P`.  The output is the family of recognition formulas (A.8) for the restriction
`ObjectProperty.liftOfLE F hle`.  The source data is given as families rather than
existentially, since the stability hypothesis refers to the chosen `tC φ`. -/
theorem nonempty_inducedTStructures_of_le (P : ObjectProperty C) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (hle : P ≤ Q.inverseImage F)
    (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (G : ℝ → ObjectProperty D) (tC : ℝ → TStructure C)
    (hG : ∀ φ : ℝ, (ind.tStructure φ).IsCompactlyGeneratedBy.{w} (G φ))
    (htC : ∀ φ : ℝ, (tC φ).IsCompactlyGeneratedBy.{w} ((G φ).map L))
    (htrunc : ∀ φ : ℝ, P.HasInducedTStructure (tC φ))
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hv : ind.MapsSemistableAisle (L ⋙ F)) :
    Nonempty (s.InducedTStructures (ObjectProperty.liftOfLE F hle)) := by
  have hL : L.PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI : PreservesColimitsOfShape (Discrete ι) L :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    infer_instance
  have hLF : (L ⋙ F).PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI := hL ι
    haveI := hF ι
    infer_instance
  have hdata : ∀ φ : ℝ, Nonempty (Polishchuk.InducedTStructureData F P Q
      (ind.tStructure φ) hle) := by
    intro φ
    exact ⟨Polishchuk.induceOfLE adj P hle (htrunc φ) hF (hG φ) (htC φ)
      (ind.monad_isRightTExact hLF hv φ) hzero (ind.tStructure_isBounded φ)⟩
  refine ⟨{ tStructure := fun φ => (hdata φ).some.tStructure
            le_zero_iff := fun φ E => ?_
            ge_one_iff := fun φ E => ?_ }⟩
  · exact ((hdata φ).some.isLE_iff E 0).trans
      ((Q.tStructure_isLE_iff (ind.tStructure φ) _ 0).trans (ind.isLE_zero_iff_geProp φ _))
  · exact ((hdata φ).some.isGE_iff E 1).trans
      ((Q.tStructure_isGE_iff (ind.tStructure φ) _ 1).trans (ind.isGE_one_iff_ltProp φ _))

omit [Q.IsClosedUnderIsomorphisms] in
/-- **Corollary A.23 on a chosen source subcategory, without the S-local half.**  The
preimage collection (A.7) on a triangulated `P ≤ F⁻¹ Q` is a slicing, provided `P` is stable
under the truncations of the source t-structures.  At `P = F⁻¹ Q`, with the stability from
`ObjectProperty.hasInducedTStructure_of_preimage`, this is `preimageData`.  It is not the
statement Theorem 2.8 needs for an infinite extension `ℓ/k`, where `π_* Dᵇ(Coh X_ℓ)` meets
`Dᵇ(Coh X)` only in zero; see `preimageData_of_coproduct`. -/
theorem preimageData_of_le [IsTriangulated C] (P : ObjectProperty C) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (hle : P ≤ Q.inverseImage F)
    (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (G : ℝ → ObjectProperty D) (tC : ℝ → TStructure C)
    (hG : ∀ φ : ℝ, (ind.tStructure φ).IsCompactlyGeneratedBy.{w} (G φ))
    (htC : ∀ φ : ℝ, (tC φ).IsCompactlyGeneratedBy.{w} ((G φ).map L))
    (htrunc : ∀ φ : ℝ, P.HasInducedTStructure (tC φ))
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hv : ind.MapsSemistableAisle (L ⋙ F)) :
    s.PreimageData (ObjectProperty.liftOfLE F hle) :=
  (ind.nonempty_inducedTStructures_of_le P hle adj hF G tC hG htC htrunc hzero hv).elim
    fun h => h.preimageData

omit [Q.IsClosedUnderIsomorphisms] in
/-- **Corollary A.23 with recognition against the large target.**  Theorem A.17 at every phase
on a triangulated `P` with truncation stability supplied, recognized against the Ind-extensions
themselves: no target subcategory appears, and `P` is not required to sit inside `F⁻¹ Q`.

This is the categorical half of Theorem 2.8(1) of arXiv:2607.28411v1 for an arbitrary field
extension, at the level of the phase-indexed t-structures.  `Polishchuk.induceLarge` supplies
each phase.  `hbdd` is the hypothesis that `F` sends `P` into the `τ̂'_φ`-bounded objects,
which for `F = π_*` is the descent-to-a-finite-subextension argument of Remark A.12(3); it is
the one hypothesis this shape adds over `nonempty_inducedTStructures_of_le`, which bought it
from `hle`.  It joins `hzero`, `hG`/`htC` and `htrunc` on the list of geometric inputs still to
be supplied for `π : X_ℓ → X`.

Two things still separate this from the slicing `𝒫_ℓ` itself, and both are open: the phase
shift `𝒫̂(φ)⟦1⟧ = 𝒫̂(φ + 1)`, which `Slicing.IndExtensions` relates across phases only by the
aisle inclusion `le_zero_anti`, and HN existence for `largePreimagePhase`.  See the
implementation notes for the full accounting against `Slicing`'s fields. -/
theorem nonempty_inducedTStructuresLarge (P : ObjectProperty C) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (G : ℝ → ObjectProperty D) (tC : ℝ → TStructure C)
    (hG : ∀ φ : ℝ, (ind.tStructure φ).IsCompactlyGeneratedBy.{w} (G φ))
    (htC : ∀ φ : ℝ, (tC φ).IsCompactlyGeneratedBy.{w} ((G φ).map L))
    (htrunc : ∀ φ : ℝ, P.HasInducedTStructure (tC φ))
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hbdd : ∀ φ : ℝ, P ≤ (ind.tStructure φ).bounded.inverseImage F)
    (hv : ind.MapsSemistableAisle (L ⋙ F)) :
    Nonempty (ind.InducedTStructuresLarge (P.ι ⋙ F)) := by
  have hL : L.PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI : PreservesColimitsOfShape (Discrete ι) L :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    infer_instance
  have hLF : (L ⋙ F).PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI := hL ι
    haveI := hF ι
    infer_instance
  have hdata : ∀ φ : ℝ,
      Nonempty (Polishchuk.InducedTStructureDataLarge F P (ind.tStructure φ)) := fun φ =>
    ⟨Polishchuk.induceLarge adj P (htrunc φ) hF (hG φ) (htC φ)
      (ind.monad_isRightTExact hLF hv φ) hzero (hbdd φ)⟩
  exact ⟨{ tStructure := fun φ => (hdata φ).some.tStructure
           le_zero_iff := fun φ E => (hdata φ).some.isLE_iff E 0
           ge_one_iff := fun φ E => (hdata φ).some.isGE_iff E 1
           isBounded := fun φ => (hdata φ).some.isBounded }⟩

/-- **Corollary A.23 for a monad that is a coproduct of identities**: when `F L` sends each
semistable object to a small coproduct of copies of itself, assumption (v') is automatic
(`Slicing.IndExtensions.mapsSemistableAisle_of_coproduct`) and the preimage collection (A.7)
is a slicing on `F⁻¹ Q`.  The motivating monad is `π_* π^* = - ⊗_k ℓ` for the base change
`π : X_ℓ → X` along a field extension `k ⊂ ℓ`, with `F = π_*`, `L = π^*`, `Q = Dᵇ(Coh X)`.
This is not yet Theorem 2.8(1) of arXiv:2607.28411v1.  For finite `ℓ/k` the output lives on
`F⁻¹ Q = Dᵇ(Coh X_ℓ)` and the coproduct is finite; for infinite `ℓ/k` no nonzero coherent
object of `X_ℓ` has coherent direct image, so `F⁻¹ Q` meets `Dᵇ(Coh X_ℓ)` only in zero, and
the paper's slicing on `Dᵇ(X_ℓ)` needs Corollary A.23 with the source subcategory chosen
independently of `F` and the slicing recognized against the Ind-extensions on `Dqc(X)`
rather than on `Q`; `preimageData_of_le` keeps `P ≤ F⁻¹ Q` and does not reach it, and
`Polishchuk.induceLarge` is the Theorem A.17 half of what does. -/
theorem preimageData_of_coproduct [IsTriangulated C] (adj : L ⊣ F)
    (hF : F.PreservesSmallCoproducts.{w})
    (hsrc : ∀ φ : ℝ, ∃ (G : ObjectProperty D) (tC : TStructure C),
      (ind.tStructure φ).IsCompactlyGeneratedBy.{w} G ∧
        tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (h : ∀ (φ : ℝ) (E : Q.FullSubcategory), s.P φ E →
      ∃ (ι : Type w) (f : ι → (E.obj ⟶ F.obj (L.obj E.obj))),
        Nonempty (IsColimit (Cofan.mk (F.obj (L.obj E.obj)) f))) :
    s.PreimageData (ObjectProperty.inverseImageLift F Q) :=
  ind.preimageData adj hF hsrc hzero (ind.mapsSemistableAisle_of_coproduct (L ⋙ F) h)

omit [Q.IsClosedUnderIsomorphisms] in
/-- **Corollary A.23 for a coproduct-of-identities monad on a chosen source subcategory**:
`preimageData_of_coproduct` on a triangulated `P ≤ F⁻¹ Q` with truncation stability supplied.
For a finite extension `ℓ/k` this is `preimageData_of_coproduct` at
`P = F⁻¹ Q = Dᵇ(Coh X_ℓ)`; for an infinite one `hle` fails and the statement Theorem 2.8(1)
needs recognizes against `Dqc(X)` (see `preimageData_of_coproduct`). -/
theorem preimageData_of_coproduct_of_le [IsTriangulated C] (P : ObjectProperty C)
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (hle : P ≤ Q.inverseImage F)
    (adj : L ⊣ F) (hF : F.PreservesSmallCoproducts.{w})
    (G : ℝ → ObjectProperty D) (tC : ℝ → TStructure C)
    (hG : ∀ φ : ℝ, (ind.tStructure φ).IsCompactlyGeneratedBy.{w} (G φ))
    (htC : ∀ φ : ℝ, (tC φ).IsCompactlyGeneratedBy.{w} ((G φ).map L))
    (htrunc : ∀ φ : ℝ, P.HasInducedTStructure (tC φ))
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (h : ∀ (φ : ℝ) (E : Q.FullSubcategory), s.P φ E →
      ∃ (ι : Type w) (f : ι → (E.obj ⟶ F.obj (L.obj E.obj))),
        Nonempty (IsColimit (Cofan.mk (F.obj (L.obj E.obj)) f))) :
    s.PreimageData (ObjectProperty.liftOfLE F hle) :=
  ind.preimageData_of_le P hle adj hF G tC hG htC htrunc hzero
    (ind.mapsSemistableAisle_of_coproduct (L ⋙ F) h)

/-- **Proposition 3.8 of arXiv:2607.28411v1, the slicing half at `S = Spec ℤ`.**
Let `F` have
a left adjoint `L` and a right adjoint `R`, both of whose composites with
`F` preserve `Q`, so that both adjunctions restrict to `Q` and `F⁻¹ Q`.  If
the restricted comonad `F R` satisfies condition (3.2), sending `𝒫(φ)` into
`𝒫(≤ φ)`, then under the Theorem A.17 hypotheses the preimage collection
(A.7) is a slicing on `F⁻¹ Q`.  The proof is the paper's: (3.2) transposes
through `Slicing.MapsSemistableGE.of_mapsSemistableLE` into the bounded
Corollary A.23 hypothesis, `mapsSemistableGE_iff` reads it as assumption
(v'), and `preimageData` is the corollary.  The S-local statement and the
`f_♯σ` clause, which Proposition 3.8 derives from Remark 3.7, are outside the
categorical layer and are not proved here.  Geometrically, `F = f^*`,
`L = f_!`, `R = f_*`, and the slicing is `f_♯𝒫`. -/
theorem preimageData_of_mapsSemistableLE [IsTriangulated C] {R : D ⥤ C}
    [R.CommShift ℤ] [R.IsTriangulated]
    (adj : L ⊣ F) (adjR : F ⊣ R) (hF : F.PreservesSmallCoproducts.{w})
    (hsrc : ∀ φ : ℝ, ∃ (G : ObjectProperty D) (tC : TStructure C),
      (ind.tStructure φ).IsCompactlyGeneratedBy.{w} G ∧
        tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hQL : ∀ E : D, Q E → Q (F.obj (L.obj E))) (hQR : ∀ E : D, Q E → Q (F.obj (R.obj E)))
    (h32 : s.MapsSemistableLE (ObjectProperty.liftToInverseImage F Q R hQR ⋙
      ObjectProperty.inverseImageLift F Q)) :
    s.PreimageData (ObjectProperty.inverseImageLift F Q) :=
  ind.preimageData adj hF hsrc hzero ((ind.mapsSemistableGE_iff hQL).1
    (Slicing.MapsSemistableGE.of_mapsSemistableLE (adj.restrictInverseImageLeft Q hQL)
      (adjR.restrictInverseImageRight Q hQR) h32))

end Induce

end Slicing.IndExtensions

end CategoryTheory.Triangulated
