/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences
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
* `Slicing.IndExtensions.largePhase`: the semistable objects of phase `φ` of
  the Ind-slicing `𝒫̂`, in the ambient category.
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
* `Slicing.IndExtensions.isLE_zero_of_semistable`: a semistable object lies in
  the aisle of its phase.
* `Slicing.IndExtensions.largePhase_iff_semistable`: on `Q` the Ind-slicing's
  phase collection is the slicing's own, so `largePhase` extends `s.P`.
* `Slicing.IndExtensions.isLE_zero_shift` and `isGE_one_shift`: the aisles and
  coaisles of the Ind-extensions shift with the phase.  Definition A.22 relates
  no two phases; this is a theorem, from clause (i) of Lemma A.14 and the
  shift-compatibility of `𝒫(≥ φ)` and of `ObjectProperty.coprodClosure`.
* `Slicing.IndExtensions.largePhase_shift` and `largePhase_shift_iff`: the
  phase shift `𝒫̂(φ)⟦1⟧ = 𝒫̂(φ + 1)`, which with
  `largePhase_isClosedUnderIsomorphisms` and `largePhase_of_isZero` gives the
  three formal `Slicing` axioms for `largePhase`.
* `Slicing.IndExtensions.mapsSemistableAisle_of_coproduct`: assumption (v')
  holds for an endofunctor that sends each semistable object to a coproduct of
  copies of itself, the base-change mechanism of Theorem 2.8(1).

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

* arXiv:2607.28411v1, Lemma A.14, Definition A.22, Theorem 2.8, and Corollary A.23.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] {Q : ObjectProperty D} [Q.IsTriangulated]

/-- The bounded aisle of `τ'_φ` shifts with the phase, because the cut `𝒫(≥ φ)` does
(`Slicing.geProp_shift`) and `Q` is closed under the shift.  This is the phase-dictionary
input of `Slicing.IndExtensions.isLE_zero_shift`; it mentions no Ind-extension data. -/
theorem Slicing.boundedAisle_shift (s : Slicing Q.FullSubcategory) (φ : ℝ) (a : ℤ) (Y : D)
    (h : TStructure.boundedAisle Q ((s.phaseShift _ φ).toDualTStructure _) Y) :
    TStructure.boundedAisle Q ((s.phaseShift _ (φ + a)).toDualTStructure _) (Y⟦a⟧) := by
  obtain ⟨X, hX, ⟨e⟩⟩ := h
  refine ⟨X⟦a⟧, ?_, ⟨(Q.ι.commShiftIso a).app X ≪≫ (shiftFunctor D a).mapIso e⟩⟩
  exact ((s.phaseShift_toDualTStructure_isLE_zero_iff _ (φ + a) _).2
    (s.geProp_shift _ φ X a ((s.phaseShift_toDualTStructure_isLE_zero_iff _ φ X).1 ⟨hX⟩))).le

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

/-- A semistable object of phase `φ` lies in the aisle `τ̂'_φ^{≤ 0} = 𝒫̂(≥ φ)`: it lies in
`𝒫(≥ φ)`, and Lemma A.14(iii) reads the large aisle on `Q` as the small one. -/
theorem isLE_zero_of_semistable (φ : ℝ) (E : Q.FullSubcategory) (hE : s.P φ E) :
    (ind.tStructure φ).IsLE E.obj 0 :=
  (ind.isLE_zero_iff_geProp φ E).2 (geProp_of_semistable _ s hE)

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

/-- The semistable objects of phase `φ` of the Ind-slicing `𝒫̂`, in the ambient category:
the aisle of `τ̂'_φ` cut against the coaisles of `τ̂'_ψ` for every `ψ > φ`.  This is the phase
collection Corollary A.23 recognizes the base-changed slicing against for an arbitrary field
extension, where the direct image leaves `Q` and `s.P` is unavailable.  Theorem 2.8(1) states
the recognition on the cuts `𝒫̂(> φ)` and `𝒫̂(≤ φ + 1)` of the unprimed family `τ_φ`; this
file carries the primed family, of whose cuts the phase collection is the intersection.

Written as `𝒫̂(≥ φ) ∩ ⋂_{ψ > φ} 𝒫̂(< ψ)` rather than `𝒫̂(≥ φ) ∩ 𝒫̂(≤ φ)` because the
Ind-extensions supply the half-open cuts and not `𝒫̂(≤ φ)`; `largePhase_iff_semistable` shows
the two agree on `Q`. -/
def largePhase (φ : ℝ) : ObjectProperty D :=
  fun Y => (ind.tStructure φ).IsLE Y 0 ∧ ∀ ψ, φ < ψ → (ind.tStructure ψ).IsGE Y 1

/-- On `Q` the Ind-slicing's phase collection is the slicing's own, so `largePhase` extends
`s.P` rather than competing with it.  Both halves are Lemma A.14(iii) read through the phase
dictionary, and the reassembly is `Slicing.semistable_iff_geProp_ltProp`. -/
theorem largePhase_iff_semistable (φ : ℝ) (X : Q.FullSubcategory) :
    ind.largePhase φ X.obj ↔ s.P φ X := by
  rw [s.semistable_iff_geProp_ltProp _ φ X]
  exact and_congr (ind.isLE_zero_iff_geProp φ X)
    (forall_congr' fun ψ => imp_congr_right fun _ => ind.isGE_one_iff_ltProp ψ X)

/-- **The aisles of the Ind-extensions shift with the phase**: `τ̂'_{φ+a}` is the `a`-shift of
`τ̂'_φ`.  This is not part of Definition A.22 -- `Slicing.IndExtensions` asserts nothing relating
two phases beyond the inclusion `le_zero_anti` -- but it is a theorem, because clause (i) of
Lemma A.14 pins each aisle to `Coprod(𝒫(≥ φ))` and both `𝒫(≥ φ)` and `Coprod` commute with the
shift (`boundedAisle_shift`, `ObjectProperty.coprodClosure_le_shift_of_le_shift`). -/
theorem isLE_zero_shift (φ : ℝ) (a : ℤ) (Y : D) (h : (ind.tStructure φ).IsLE Y 0) :
    (ind.tStructure (φ + a)).IsLE (Y⟦a⟧) 0 := by
  refine ⟨?_⟩
  rw [(ind.indExtensionData (φ + a)).largeAisle]
  refine ObjectProperty.coprodClosure_le_shift_of_le_shift
    (TStructure.boundedAisle Q ((s.phaseShift _ φ).toDualTStructure _)) a
    (R := (TStructure.boundedAisle Q
      ((s.phaseShift _ (φ + a)).toDualTStructure _)).coprodClosure.{w})
    (fun Z hZ => ObjectProperty.le_coprodClosure _ _ (s.boundedAisle_shift φ a Z hZ)) Y ?_
  · rw [← (ind.indExtensionData φ).largeAisle]; exact h.le

/-- The coaisles shift too.  Not a second argument: the coaisle is the right orthogonal of the
aisle (`isGE_iff_orthogonal`), so `isLE_zero_shift` at `-a` transports a test object back and
the shift is fully faithful. -/
theorem isGE_one_shift (φ : ℝ) (a : ℤ) (Y : D) (h : (ind.tStructure φ).IsGE Y 1) :
    (ind.tStructure (φ + a)).IsGE (Y⟦a⟧) 1 := by
  -- at `(𝟭 D).obj Y`, not `Y`: that is the codomain of `shiftFunctorCompIsoId`, and
  -- instance search does not unfold it.
  haveI : (ind.tStructure φ).IsGE ((𝟭 D).obj Y) 1 := h
  rw [(ind.tStructure (φ + a)).isGE_iff_orthogonal 0 1 rfl]
  intro Z f hZ
  haveI : (ind.tStructure φ).IsLE (Z⟦(-a : ℤ)⟧) 0 := by
    have := ind.isLE_zero_shift (φ + a) (-a) Z hZ
    rwa [show φ + (a : ℝ) + ((-a : ℤ) : ℝ) = φ by push_cast; ring] at this
  haveI : (ind.tStructure φ).IsGE ((Y⟦a⟧)⟦(-a : ℤ)⟧) 1 :=
    (ind.tStructure φ).isGE_of_iso
      ((shiftFunctorCompIsoId D a (-a) (by ring)).app Y).symm 1
  exact (shiftFunctor D (-a)).map_injective
    (by simpa using (ind.tStructure φ).zero ((shiftFunctor D (-a)).map f) 0 1 (by omega))

instance largePhase_isClosedUnderIsomorphisms (φ : ℝ) :
    (ind.largePhase φ).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨?_, fun ψ hψ => ?_⟩
    · haveI := h.1; exact (ind.tStructure φ).isLE_of_iso e 0
    · haveI := h.2 ψ hψ; exact (ind.tStructure ψ).isGE_of_iso e 1

/-- The zero object is semistable of every phase for the Ind-slicing.  Stated at an arbitrary
zero object, not at `(0 : D)`, because `largePreimage` needs it at `F.obj 0`, which is only *a*
zero object; this is the `largePhase` analogue of `Slicing.zero_mem_of_isZero`, which exists
beside the `zero_mem` field for the same reason. -/
theorem largePhase_of_isZero (φ : ℝ) {Y : D} (hY : IsZero Y) : ind.largePhase φ Y :=
  ⟨(ind.tStructure φ).isLE_of_isZero hY 0,
    fun ψ _ => (ind.tStructure ψ).isGE_of_isZero hY 1⟩

/-- **The phase shift for the Ind-slicing**: `𝒫̂(φ)⟦a⟧ = 𝒫̂(φ + a)`, from the aisle and coaisle
shifts.  With `largePhase_isClosedUnderIsomorphisms` and `largePhase_of_isZero` this is the
third of the three formal `Slicing` axioms for `largePhase`. -/
theorem largePhase_shift (φ : ℝ) (a : ℤ) (Y : D) (h : ind.largePhase φ Y) :
    ind.largePhase (φ + a) (Y⟦a⟧) := by
  refine ⟨ind.isLE_zero_shift φ a Y h.1, fun ψ hψ => ?_⟩
  have := ind.isGE_one_shift (ψ - a) a Y (h.2 _ (by linarith))
  rwa [show ψ - (a : ℝ) + (a : ℝ) = ψ by ring] at this

/-- The shift law as an equivalence, at every integer shift.  Only `→` is proved directly;
`←` is the same statement at `-a`, transported back along `shiftFunctorCompIsoId`, which is
why `largePhase_shift` is stated as an implication and this as the `Iff`. -/
theorem largePhase_shift_int (φ : ℝ) (a : ℤ) (Y : D) :
    ind.largePhase φ Y ↔ ind.largePhase (φ + a) (Y⟦a⟧) := by
  refine ⟨ind.largePhase_shift φ a Y, fun h => ?_⟩
  have h2 := ind.largePhase_shift (φ + a) (-a) _ h
  rw [show φ + (a : ℝ) + ((-a : ℤ) : ℝ) = φ by push_cast; ring] at h2
  exact (ind.largePhase φ).prop_of_iso
    ((shiftFunctorCompIsoId D a (-a) (by ring)).app Y) h2

/-- The shift law in the form `Slicing.shift_iff` takes it. -/
theorem largePhase_shift_iff (φ : ℝ) (Y : D) :
    ind.largePhase φ Y ↔ ind.largePhase (φ + 1) (Y⟦(1 : ℤ)⟧) := by
  simpa using ind.largePhase_shift_int φ 1 Y

/-- Assumption (v') of Corollary A.23 of arXiv:2607.28411v1 for an
endofunctor `G` of the ambient category: `G` sends every semistable object of
phase `φ` into the aisle `τ̂'_φ^{≤ 0} = 𝒫̂(≥ φ)`.  At the monad `G = Φ Φ_L`
this is the paper's `Φ Φ_L 𝒫(φ) ⊆ 𝒫̂(≥ φ)`.  It is stated on semistable
objects, as the paper states it; `Slicing.IndExtensions.monad_isLE_zero_of_geProp`
extends it to `𝒫(≥ φ)`. -/
def MapsSemistableAisle (G : D ⥤ D) : Prop :=
  ∀ (φ : ℝ) (E : Q.FullSubcategory), s.P φ E → (ind.tStructure φ).IsLE (G.obj E.obj) 0

/-- Assumption (v') holds for any endofunctor that sends each semistable object to a small
coproduct of copies of itself, because the aisle `τ̂'_φ^{≤ 0} = Coprod(𝒫(≥ φ))` is closed under
coproducts and contains the semistable objects of phase `φ`.  This is the mechanism of base
change along a field extension `k ⊂ ℓ` in Theorem 2.8(1) of arXiv:2607.28411v1: the monad
`π_* π^*` of `π : X_ℓ → X` sends `E` to `E ⊗_k ℓ`, a coproduct of copies of `E` indexed by a
`k`-basis of `ℓ`, so (v') costs nothing there; the coproduct is infinite exactly when `ℓ/k`
is, which is why the Ind-extension in `Dqc` is needed at all. -/
theorem mapsSemistableAisle_of_coproduct (G : D ⥤ D)
    (h : ∀ (φ : ℝ) (E : Q.FullSubcategory), s.P φ E →
      ∃ (ι : Type w) (f : ι → (E.obj ⟶ G.obj E.obj)),
        Nonempty (IsColimit (Cofan.mk (G.obj E.obj) f))) :
    ind.MapsSemistableAisle G := by
  intro φ E hE
  obtain ⟨ι, f, ⟨hc⟩⟩ := h φ E hE
  refine ⟨?_⟩
  have hgen := (ind.isLE_zero_of_semistable φ E hE).le
  rw [(ind.indExtensionData φ).largeAisle] at hgen ⊢
  exact ObjectProperty.coprodClosure.of_coproduct (Cofan.mk (G.obj E.obj) f) hc fun _ => hgen

end Slicing.IndExtensions

end CategoryTheory.Triangulated
