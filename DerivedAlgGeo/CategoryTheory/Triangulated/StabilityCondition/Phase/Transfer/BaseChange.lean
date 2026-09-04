/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Coaisle
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Inducing
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Retracts

/-!
# Semistability under base change: Theorem 2.8(3), categorically

Theorem 2.8(3) of arXiv:2607.28411v1 says that an object `E` of `Dᵇ(X)` is semistable of
phase `φ` if and only if its base change `π^* E` is, for the base-changed slicing of Theorem
2.8(1).  Since `π_* π^* E ≅ E ⊗_k ℓ` is a nonempty coproduct of copies of `E`, and the
base-changed slicing recognizes `π^* E` through `π_* π^* E`, the statement reduces to: `E` is
semistable of phase `φ` if and only if a nonempty coproduct of copies of `E` lies in the aisle
of `τ̂'_φ` and in the coaisles of `τ̂'_ψ` for every `ψ > φ`.

That reduction is `semistable_iff_largePhase_of_iso_coproduct`, and it constrains
the coproduct only as an object of the large category `D`.  It holds because the aisle is
closed under coproducts by Lemma A.14(i), the coaisle is closed under coproducts because the
t-structure is compactly generated
(`TStructure.IsCompactlyGeneratedBy.isGE_one_coproduct`), and both are closed under retracts,
`E` being a retract of the coproduct.

When the coproduct itself lies in `Q`, the two one-sided conditions reassemble into
semistability there (`semistable_iff_semistable_of_iso_coproduct`), and Theorem 2.8(3) follows
for the preimage slicing on `F⁻¹ Q`.  That is the **finite** extension: for an infinite `ℓ/k`
the object `E ⊗_k ℓ` is not coherent, so no such object of `Q` exists and both `Q`-level
statements are vacuous.  The large-target form of Theorem 2.8(1) is
`Slicing.IndExtensions.largePreimage`, which is built from the aisle and coaisle shifts rather
than from these; the `D`-level reduction and the two closure lemmas here are what a
large-target Theorem 2.8(3) will consume.

## Main results

* `Slicing.IndExtensions.semistable_iff_largePhase_of_iso_coproduct`: the reduction of
  semistability to semistability of a coproduct of copies for the Ind-slicing, with no
  `Q`-membership of the coproduct required.
* `Slicing.IndExtensions.isLE_zero_coproduct` and `isGE_one_coproduct`: the aisle and the
  coaisle of `τ̂'_φ` are closed under coproducts, the two closure facts that reduction rests on.
* `Slicing.IndExtensions.semistable_iff_semistable_of_iso_coproduct`: its restatement when the
  coproduct lies in `Q`.
* `Slicing.IndExtensions.semistable_iff_preimage_of_coproduct`: Theorem 2.8(3) for the preimage
  slicing on `F⁻¹ Q`, the finite-extension case, when `F L E` is a nonempty coproduct of copies
  of `E`.

## Implementation notes

Coproducts are indexed by `Type` because `IsCompactObject.exists_finite_sum` is; the
Ind-extension data is correspondingly `IndExtensions.{0}`.  `isLE_zero_coproduct` holds at any
`w` and is pinned here only by that shared binder.  The coproduct of copies of `E` is assumed
to exist in the large category; nothing here needs coproducts in `D` in general.

## References

* arXiv:2607.28411v1, Theorem 2.8(3), with Lemma A.14, Definition A.22 and Corollary A.23.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u₁ u₂

namespace CategoryTheory.Triangulated.Slicing.IndExtensions

variable {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
  {Q : ObjectProperty D} [Q.IsTriangulated]
  {s : Slicing Q.FullSubcategory} (ind : s.IndExtensions.{0})

/-- The coaisle of `τ̂'_φ` is closed under coproducts, since `τ̂'_φ` is compactly generated. -/
theorem isGE_one_coproduct (φ : ℝ) {ι : Type} (X : ι → D) [HasCoproduct X]
    (hX : ∀ i, (ind.tStructure φ).IsGE (X i) 1) : (ind.tStructure φ).IsGE (∐ X) 1 := by
  obtain ⟨G, hG⟩ := (ind.indExtensionData φ).compactlyGenerated
  exact hG.isGE_one_coproduct X hX

/-- The aisle of `τ̂'_φ` is closed under coproducts, by Lemma A.14(i). -/
theorem isLE_zero_coproduct (φ : ℝ) {ι : Type} (X : ι → D) [HasCoproduct X]
    (hX : ∀ i, (ind.tStructure φ).IsLE (X i) 0) : (ind.tStructure φ).IsLE (∐ X) 0 := by
  refine ⟨?_⟩
  rw [(ind.indExtensionData φ).largeAisle]
  refine ObjectProperty.coprodClosure.of_coproduct (colimit.cocone (Discrete.functor X))
    (colimit.isColimit _) fun i => ?_
  rw [← (ind.indExtensionData φ).largeAisle]
  exact (hX i.as).le

include ind in
/-- **The reduction behind Theorem 2.8(3).**  `E` is semistable of phase `φ` exactly when a
nonempty coproduct of copies of it is semistable of phase `φ` for the Ind-slicing
(`Slicing.IndExtensions.largePhase`, which unfolds to membership in the aisle of `τ̂'_φ` and in
the coaisles of `τ̂'_ψ` for every `ψ > φ`).  Both directions are closure properties: `→` because
aisle and coaisle are closed under coproducts (`isLE_zero_coproduct`, `isGE_one_coproduct`),
`←` because they are closed under retracts and `E` is a retract of the coproduct, `ι` being
nonempty.  The coproduct is constrained only as an object of `D`, which is what makes this the
form the large-target Theorem 2.8(1) can consume: there `π_* π^* E = E ⊗_k ℓ` is not coherent,
so no statement asking for it in `Q` applies. -/
theorem semistable_iff_largePhase_of_iso_coproduct (φ : ℝ) (E : Q.FullSubcategory)
    {ι : Type} [Nonempty ι] [HasCoproduct fun _ : ι => E.obj] (Y : D)
    (e : Y ≅ ∐ fun _ : ι => E.obj) : s.P φ E ↔ ind.largePhase φ Y := by
  show s.P φ E ↔
    ((ind.tStructure φ).IsLE Y 0 ∧ ∀ ψ, φ < ψ → (ind.tStructure ψ).IsGE Y 1)
  let r : Retract E.obj (∐ fun _ : ι => E.obj) :=
    { i := Sigma.ι (fun _ : ι => E.obj) (Classical.arbitrary ι)
      r := Sigma.desc fun _ => 𝟙 E.obj
      retract := Sigma.ι_desc _ _ }
  have hLE : ∀ ψ, (ind.tStructure ψ).IsLE E.obj 0 ↔ (ind.tStructure ψ).IsLE Y 0 := by
    intro ψ
    constructor
    · intro h
      haveI : (ind.tStructure ψ).IsLE (∐ fun _ : ι => E.obj) 0 :=
        ind.isLE_zero_coproduct ψ _ fun _ => h
      exact (ind.tStructure ψ).isLE_of_iso e.symm 0
    · intro h
      haveI := h
      exact tStructureIsLE_of_retract _ r 0 ((ind.tStructure ψ).isLE_of_iso e 0)
  have hGE : ∀ ψ, (ind.tStructure ψ).IsGE E.obj 1 ↔ (ind.tStructure ψ).IsGE Y 1 := by
    intro ψ
    constructor
    · intro h
      haveI : (ind.tStructure ψ).IsGE (∐ fun _ : ι => E.obj) 1 :=
        ind.isGE_one_coproduct ψ _ fun _ => h
      exact (ind.tStructure ψ).isGE_of_iso e.symm 1
    · intro h
      haveI := h
      exact tStructureIsGE_of_retract _ r 1 ((ind.tStructure ψ).isGE_of_iso e 1)
  rw [s.semistable_iff_geProp_ltProp _ φ E]
  refine and_congr ?_ (forall_congr' fun ψ => imp_congr_right fun _ => ?_)
  · rw [← ind.isLE_zero_iff_geProp]; exact hLE φ
  · rw [← ind.isGE_one_iff_ltProp]; exact hGE ψ

include ind in
/-- **Theorem 2.8(3), categorical core.**  An object of `Q` is semistable of phase `φ` if and
only if a nonempty coproduct of copies of it, *lying in `Q`*, is: the previous theorem read
back through `semistable_iff_geProp_ltProp` at `Y`.  The `Q`-membership is the whole content of
the restriction to a finite extension; without it only the two one-sided conditions survive. -/
theorem semistable_iff_semistable_of_iso_coproduct (φ : ℝ) (E : Q.FullSubcategory) {ι : Type}
    [Nonempty ι] [HasCoproduct fun _ : ι => E.obj] (Y : Q.FullSubcategory)
    (e : Y.obj ≅ ∐ fun _ : ι => E.obj) : s.P φ E ↔ s.P φ Y :=
  (ind.semistable_iff_largePhase_of_iso_coproduct φ E Y.obj e).trans
    (ind.largePhase_iff_semistable φ Y)

variable {C : Type u₁} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {L : D ⥤ C} {F : C ⥤ D} [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

include ind in
/-- **Theorem 2.8(3) of arXiv:2607.28411v1 for a finite extension, categorically.**  This is
`semistable_iff_semistable_of_iso_coproduct` at `Y = F (L E)` and nothing more: `Slicing.preimage`
ignores its `PreimageData` witness (`@[nolint unusedArguments]`) and its phase collection is
`s.preimagePhase F` by definition, so the right-hand side unfolds to `s.P φ (F (L E))` by
`Iff.rfl` for any `hd`.  The witness is carried only so that the statement can be *read* as
semistability in the preimage slicing along `F` on `F⁻¹ Q` (Corollary A.23,
`preimageData_of_coproduct`).

Geometrically `F = π_*`, `L = π^*` for the base change `π : X_ℓ → X` along a finite extension
`k ⊂ ℓ`, and `π_* π^* E ≅ E ⊗_k ℓ`; no adjunction between `L` and `F` is used, only the
isomorphism `e`.  For an infinite extension `F (L E) = E ⊗_k ℓ` is not coherent, so `hQL`
cannot hold at `E`, the hypotheses are unsatisfiable, and the preimage slicing is not the
paper's `𝒫_ℓ` (see `preimageData_of_coproduct`); what the large-target statement consumes there
is `semistable_iff_largePhase_of_iso_coproduct`, which constrains the coproduct only as an
object of `D`. -/
theorem semistable_iff_preimage_of_coproduct [Q.IsClosedUnderIsomorphisms]
    (hd : s.PreimageData (ObjectProperty.inverseImageLift F Q))
    (hQL : ∀ X : D, Q X → Q (F.obj (L.obj X))) (φ : ℝ) (E : Q.FullSubcategory) {ι : Type}
    [Nonempty ι] [HasCoproduct fun _ : ι => E.obj]
    (e : F.obj (L.obj E.obj) ≅ ∐ fun _ : ι => E.obj) :
    s.P φ E ↔
      (s.preimage (ObjectProperty.inverseImageLift F Q) hd).P φ ⟨L.obj E.obj, hQL _ E.property⟩ :=
  ind.semistable_iff_semistable_of_iso_coproduct φ E ⟨F.obj (L.obj E.obj), hQL _ E.property⟩ e

end CategoryTheory.Triangulated.Slicing.IndExtensions
