/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Restricting t-structures detected by a t-exact functor

This file formalizes Steps 2--4 of Polishchuk's Theorem A.17 from
arXiv:2607.28411v1. If a t-exact functor detects membership in chosen bounded
subcategories, then restriction of the target t-structure forces restriction
of the source t-structure. If the functor also reflects zero objects, the two
halves of the restricted source t-structure are recognized exactly on the
target; these are formulas (A.3) and (A.4). Boundedness of the restricted
source t-structure then follows from boundedness of the images, which is
Step 4.

The theorem is independent of schemes and of the compact-generation argument
that constructs the large source t-structure in Step 1.

The same file owns the restriction of an adjunction on either side of `F` to
`Q` and `F⁻¹ Q`, which Proposition 3.8 transposes condition (3.2) through;
these six `ObjectProperty` declarations need no t-structure and are recorded
in `docs/architecture/cutover-ledger.md` as a block to move to
`CategoryTheory/ObjectProperty/`.

## Main definitions

* `ObjectProperty.liftOfLE`: the restriction of `F` to a subcategory
  `P ≤ F⁻¹ Q`, landing in `Q`, with the `Additive`, `CommShift ℤ`, and
  `IsTriangulated` instances a slicing consumer needs of a detecting functor;
  `ObjectProperty.preimageLift` is its case of a two-way detection, and
  `ObjectProperty.inverseImageLift` its `P = F⁻¹ Q` case, the shape
  hypothesis (iv) of A.17 produces.
* `ObjectProperty.liftToInverseImage`: the restriction of a functor in the
  other direction whose composite with `F` preserves `Q`.
* `Adjunction.restrictInverseImageLeft` and `restrictInverseImageRight`: an
  adjunction on either side of `F` restricted to those subcategories, through
  Mathlib's `Adjunction.restrictFullyFaithful`; the suffix names which adjoint
  of `F` is restricted.

## Main results

* `ObjectProperty.hasInducedTStructure_of_preimage`: Step 2, restriction of
  the source t-structure from detection of the two subcategories.
* `ObjectProperty.isLE_iff_isLE_map`, `isGE_iff_isGE_map`: Step 3, formulas
  (A.3) and (A.4) against the large target t-structure, with no target
  subcategory, the shape Theorem 2.8(1) recognizes the base-changed slicing
  in.  `tStructure_isLE_iff_map_of_le` and `tStructure_isGE_iff_map_of_le`
  restate them inside `Q` for `P ≤ F⁻¹ Q`, and `tStructure_isLE_iff_map`,
  `tStructure_isGE_iff_map` are their two-way detection cases.
* `ObjectProperty.tStructure_isBounded_of_le_bounded_inverseImage`: Step 4 in
  that shape, together with `tStructure_isBounded_iff_le_bounded`, the form in
  which a bounded target subcategory supplies its hypothesis.

## References

* arXiv:2607.28411v1, Theorem A.17 (Steps 2--4) and Proposition 3.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : Functor C D} {t : TStructure C} {t' : TStructure D}
  {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Step 2 of A.17: restriction of the target t-structure and detection of
the two bounded subcategories imply restriction of the source t-structure.

The proof compares truncations using `Functor.mapTruncLEIso` and
`Functor.mapTruncGEIso`. Thus the conclusion is derived from t-exactness and
bounded-subcategory detection; it is not included among the premises. -/
theorem hasInducedTStructure_of_preimage
    [P.IsTriangulated] [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    P.HasInducedTStructure t := by
  apply HasInducedTStructure.mk'
  intro X hX n
  have hFX : Q (F.obj X) := (hmem X).1 hX
  let TD := (t'.triangleLEGE n (n + 1) rfl).obj (F.obj X)
  have hTD : TD ∈ distTriang D :=
    t'.triangleLEGE_distinguished n (n + 1) rfl (F.obj X)
  have hQ := Q.mem_of_hasInductedTStructure t' TD hTD n (n + 1) rfl
    (by simpa only [TD, TStructure.triangleLEGE_obj_obj₁] using
      t'.isLE_truncLE_obj (F.obj X) n n)
    hFX
    (by simpa only [TD, TStructure.triangleLEGE_obj_obj₃] using
      t'.isGE_truncGE_obj (F.obj X) (n + 1) (n + 1))
  let TD' := (t'.triangleLEGE (n - 1) n (by omega)).obj (F.obj X)
  have hTD' : TD' ∈ distTriang D :=
    t'.triangleLEGE_distinguished (n - 1) n (by omega) (F.obj X)
  have hQ' := Q.mem_of_hasInductedTStructure t' TD' hTD' (n - 1) n (by omega)
    (by simpa only [TD', TStructure.triangleLEGE_obj_obj₁] using
      t'.isLE_truncLE_obj (F.obj X) (n - 1) (n - 1))
    hFX
    (by simpa only [TD', TStructure.triangleLEGE_obj_obj₃] using
      t'.isGE_truncGE_obj (F.obj X) n n)
  constructor
  · apply (hmem _).2
    exact Q.prop_of_iso (F.mapTruncLEIso t t' n X).symm
      (by simpa only [TD, TStructure.triangleLEGE_obj_obj₁] using hQ.1)
  · apply (hmem _).2
    exact Q.prop_of_iso (F.mapTruncGEIso t t' n X).symm
      (by simpa only [TD', TStructure.triangleLEGE_obj_obj₃] using hQ'.2)

/-- The restriction of `F` to a full subcategory `P ≤ F⁻¹ Q`, landing in `Q`.
Definitionally `ObjectProperty.ιOfLE hle ⋙ inverseImageLift F Q`, but defined
as `Q.lift (P.ι ⋙ F) _` because Mathlib's `ιOfLE` carries no `Additive`,
`CommShift`, or `IsTriangulated` instance while `lift` carries all three; the
instances below are those, transported.  Its `F = 𝟭` case is `ιOfLE`. -/
def liftOfLE (F : Functor C D) (hle : P ≤ Q.inverseImage F) :
    Functor P.FullSubcategory Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun X ↦ hle X.obj X.property)

instance instAdditiveLiftOfLE [F.Additive] (hle : P ≤ Q.inverseImage F) :
    (liftOfLE F hle).Additive :=
  inferInstanceAs (Q.lift (P.ι ⋙ F) (fun X ↦ hle X.obj X.property)).Additive

instance instCommShiftLiftOfLE [P.IsTriangulated] [Q.IsTriangulated]
    [F.CommShift ℤ] (hle : P ≤ Q.inverseImage F) :
    (liftOfLE F hle).CommShift ℤ :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) (fun X ↦ hle X.obj X.property)).CommShift ℤ)

instance instIsTriangulatedLiftOfLE [P.IsTriangulated] [Q.IsTriangulated] [F.CommShift ℤ]
    [F.IsTriangulated] (hle : P ≤ Q.inverseImage F) :
    (liftOfLE F hle).IsTriangulated :=
  inferInstanceAs (Q.lift (P.ι ⋙ F) (fun X ↦ hle X.obj X.property)).IsTriangulated

/-- The functor between the two full subcategories selected by a detection
equivalence: `liftOfLE` along its forward direction, by definition. -/
def preimageLift (F : Functor C D) (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    Functor P.FullSubcategory Q.FullSubcategory :=
  liftOfLE F (fun X ↦ (hmem X).1)

instance instAdditivePreimageLift [F.Additive] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).Additive :=
  inferInstanceAs (liftOfLE F (fun X ↦ (hmem X).1)).Additive

instance instCommShiftPreimageLift [P.IsTriangulated] [Q.IsTriangulated]
    [F.CommShift ℤ] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).CommShift ℤ :=
  inferInstanceAs ((liftOfLE F (fun X ↦ (hmem X).1)).CommShift ℤ)

instance instIsTriangulatedPreimageLift [P.IsTriangulated] [Q.IsTriangulated] [F.CommShift ℤ]
    [F.IsTriangulated] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).IsTriangulated :=
  inferInstanceAs (liftOfLE F (fun X ↦ (hmem X).1)).IsTriangulated

/-- The restriction of `F` to the objects whose image lies in `Q`, landing
in `Q`.  This is the functor between the selected subcategories under
hypothesis (iv) of Theorem A.17 of arXiv:2607.28411v1, `P = F⁻¹ Q`, the
form `Polishchuk.induce` produces.

Kept an `abbrev`, hence reducible, so that a `Polishchuk.InducedTStructureData`
field stated with `liftOfLE F le_rfl` (`Polishchuk.induce`) is definitionally
this functor; `Slicing.IndExtensions.nonempty_inducedTStructures` relies on
that. -/
abbrev inverseImageLift (F : Functor C D) (Q : ObjectProperty D) :
    Functor (Q.inverseImage F).FullSubcategory Q.FullSubcategory :=
  liftOfLE F (P := Q.inverseImage F) (Q := Q) le_rfl

/-- The restriction of `L : D ⥤ C` to `Q`, landing in `F⁻¹ Q`, when `F ∘ L`
preserves `Q`.  For `L` a left adjoint of `F` this is the bounded left
adjoint of `inverseImageLift F Q`; geometrically, `f_!` on `Dᵇ(Coh)` when it
preserves bounded coherent complexes. -/
abbrev liftToInverseImage (F : Functor C D) (Q : ObjectProperty D) (L : Functor D C)
    (hL : ∀ E : D, Q E → Q (F.obj (L.obj E))) :
    Functor Q.FullSubcategory (Q.inverseImage F).FullSubcategory :=
  (Q.inverseImage F).lift (Q.ι ⋙ L) fun E ↦ hL E.obj E.property

/-- An adjunction `L ⊣ F` restricts to `Q ⊆ D` and `F⁻¹ Q ⊆ C` when the monad
`F L` preserves `Q`; the restricted functors are `liftToInverseImage` and
`inverseImageLift`, and the comparison isomorphisms are `liftCompιIso`, so
nothing is transported.  Geometrically this is `f_! ⊣ f^*` on `Dᵇ(Coh)`, under
the hypothesis that the monad `f^* f_!` preserves bounded coherent complexes,
which Proposition 3.8 of arXiv:2607.28411v1 obtains from `f_!(Dᵇ) ⊆ Dᵇ`,
itself a consequence of perfectness of the relative dualizing complex. -/
def _root_.CategoryTheory.Adjunction.restrictInverseImageLeft
    {L : Functor D C} (adj : L ⊣ F) (Q : ObjectProperty D)
    (hL : ∀ E : D, Q E → Q (F.obj (L.obj E))) :
    liftToInverseImage F Q L hL ⊣ inverseImageLift F Q :=
  adj.restrictFullyFaithful Q.fullyFaithfulι (Q.inverseImage F).fullyFaithfulι
    ((Q.inverseImage F).liftCompιIso _ _).symm (Q.liftCompιIso _ _).symm

/-- An adjunction `F ⊣ R` restricts to `F⁻¹ Q ⊆ C` and `Q ⊆ D` when the comonad
`F R` preserves `Q`; the restricted functors are `inverseImageLift` and
`liftToInverseImage`, and the comparison isomorphisms are `liftCompιIso`, so
nothing is transported.  Geometrically this is `f^* ⊣ f_*` on `Dᵇ(Coh)`, under
the hypothesis that the comonad `f^* f_*` preserves bounded coherent
complexes, exactly what condition (3.2) of arXiv:2607.28411v1 needs in order
to be stated there. -/
def _root_.CategoryTheory.Adjunction.restrictInverseImageRight
    {R : Functor D C} (adj : F ⊣ R) (Q : ObjectProperty D)
    (hR : ∀ E : D, Q E → Q (F.obj (R.obj E))) :
    inverseImageLift F Q ⊣ liftToInverseImage F Q R hR :=
  adj.restrictFullyFaithful (Q.inverseImage F).fullyFaithfulι Q.fullyFaithfulι
    (Q.liftCompιIso _ _).symm ((Q.inverseImage F).liftCompιIso _ _).symm

/-- Formula (A.3) against the large target t-structure, with no target
subcategory: the content of Step 3 of Theorem A.17, in the shape Theorem 2.8(1)
of arXiv:2607.28411v1 recognizes the base-changed slicing.  Right t-exactness
gives `→`; for `←`, `F (τ^{≥ n+1} X) ≅ τ'^{≥ n+1} (F X) = 0` by t-exactness,
`τ^{≥ n+1} X ∈ P` by `P.HasInducedTStructure t`, and zero reflection at that
truncation finishes.  That is why truncation stability of `P` and zero
reflection on `P` are exactly the hypotheses. -/
theorem isLE_iff_isLE_map
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    {X : C} (hX : P X) (n : ℤ) :
    t.IsLE X n ↔ t'.IsLE (F.obj X) n := by
  constructor
  · exact Functor.IsRightTExact.isLE_map X n
  · intro hX'
    haveI : t'.IsLE (F.obj X) n := hX'
    have hTarget : IsZero ((t'.truncGE (n + 1)).obj (F.obj X)) :=
      t'.isZero_truncGE_obj_of_isLE n (n + 1) rfl (F.obj X)
    have hMapped : IsZero (F.obj ((t.truncGE (n + 1)).obj X)) :=
      hTarget.of_iso (F.mapTruncGEIso t t' (n + 1) X)
    have hP : P ((t.truncGE (n + 1)).obj X) := by
      simpa only [TStructure.triangleLEGE_obj_obj₃] using
        (P.mem_of_hasInductedTStructure t _
          (t.triangleLEGE_distinguished n (n + 1) rfl X) n (n + 1) rfl
          (by simpa only [TStructure.triangleLEGE_obj_obj₁] using
            t.isLE_truncLE_obj X n n)
          hX
          (by simpa only [TStructure.triangleLEGE_obj_obj₃] using
            t.isGE_truncGE_obj X (n + 1) (n + 1))).2
    exact (t.isLE_iff_isZero_truncGE_obj n (n + 1) rfl X).2 (hzero _ hP hMapped)

/-- Formula (A.3) on the restricted categories, for `P ≤ F⁻¹ Q`: the large
target statement `isLE_iff_isLE_map`, restated inside `Q`.  `hle` enters only
in that restatement. -/
theorem tStructure_isLE_iff_map_of_le
    [P.IsTriangulated] [Q.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hle : P ≤ Q.inverseImage F)
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsLE X n ↔
      (Q.tStructure t').IsLE ((liftOfLE F hle).obj X) n := by
  rw [P.tStructure_isLE_iff, Q.tStructure_isLE_iff]
  exact isLE_iff_isLE_map hzero X.property n

/-- Formula (A.3) on the restricted categories.

Zero reflection is required only on objects of `P`, matching A.17's
conservativity-on-bounded-objects hypothesis: the proof applies `hzero` at a
truncation of an object of `P`, and truncations stay in `P` by the induced
t-structure. A caller with global conservativity weakens it pointwise. -/
theorem tStructure_isLE_iff_map
    [P.IsTriangulated] [Q.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hmem : ∀ X : C, P X ↔ Q (F.obj X))
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsLE X n ↔
      (Q.tStructure t').IsLE ((preimageLift F hmem).obj X) n :=
  tStructure_isLE_iff_map_of_le hzero (fun X ↦ (hmem X).1) X n

/-- Formula (A.4) against the large target t-structure, as
`isLE_iff_isLE_map`. -/
theorem isGE_iff_isGE_map
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    {X : C} (hX : P X) (n : ℤ) :
    t.IsGE X n ↔ t'.IsGE (F.obj X) n := by
  constructor
  · exact Functor.IsLeftTExact.isGE_map X n
  · intro hX'
    haveI : t'.IsGE (F.obj X) n := hX'
    have hTarget : IsZero ((t'.truncLT n).obj (F.obj X)) :=
      t'.isZero_truncLT_obj_of_isGE n (F.obj X)
    let e : F.obj ((t.truncLT n).obj X) ≅ (t'.truncLT n).obj (F.obj X) := by
      simpa only [TStructure.truncLE, sub_add_cancel] using F.mapTruncLEIso t t' (n - 1) X
    have hMapped : IsZero (F.obj ((t.truncLT n).obj X)) := hTarget.of_iso e
    have hP : P ((t.truncLT n).obj X) := by
      have h₁ := (P.mem_of_hasInductedTStructure t _
        (t.triangleLEGE_distinguished (n - 1) n (by omega) X) (n - 1) n (by omega)
        (by simpa only [TStructure.triangleLEGE_obj_obj₁] using
          t.isLE_truncLE_obj X (n - 1) (n - 1))
        hX
        (by simpa only [TStructure.triangleLEGE_obj_obj₃] using t.isGE_truncGE_obj X n n)).1
      simpa only [TStructure.triangleLEGE_obj_obj₁, TStructure.truncLE, sub_add_cancel] using h₁
    exact (t.isGE_iff_isZero_truncLT_obj n X).2 (hzero _ hP hMapped)

/-- The induced t-structure on `Q` is bounded exactly when `Q` consists of
`t'`-bounded objects, the form in which Step 4 of Theorem A.17 consumes a
bounded target subcategory. -/
theorem tStructure_isBounded_iff_le_bounded [Q.IsTriangulated]
    [Q.HasInducedTStructure t'] :
    TStructure.IsBounded (Q.tStructure t') ↔ Q ≤ t'.bounded := by
  constructor
  · intro h X hX
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h ⟨X, hX⟩
    exact ⟨⟨a, (Q.tStructure_isGE_iff t' _ a).1 ha⟩, ⟨b, (Q.tStructure_isLE_iff t' _ b).1 hb⟩⟩
  · intro h X
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h X.obj X.property
    exact ⟨⟨a, (Q.tStructure_isGE_iff t' _ a).2 ha⟩, ⟨b, (Q.tStructure_isLE_iff t' _ b).2 hb⟩⟩

/-- Step 4 of Theorem A.17 with no target subcategory: if `F` sends `P` into
the `t'`-bounded objects, the induced t-structure on `P` is bounded. -/
theorem tStructure_isBounded_of_le_bounded_inverseImage
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hbdd : P ≤ t'.bounded.inverseImage F) :
    TStructure.IsBounded (P.tStructure t) := by
  intro X
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hbdd X.obj X.property
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · rw [P.tStructure_isGE_iff]
    exact (isGE_iff_isGE_map hzero X.property a).2 ha
  · rw [P.tStructure_isLE_iff]
    exact (isLE_iff_isLE_map hzero X.property b).2 hb

/-- Formula (A.4) on the restricted categories, for `P ≤ F⁻¹ Q`, as
`tStructure_isLE_iff_map_of_le`. -/
theorem tStructure_isGE_iff_map_of_le
    [P.IsTriangulated] [Q.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hle : P ≤ Q.inverseImage F)
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsGE X n ↔
      (Q.tStructure t').IsGE ((liftOfLE F hle).obj X) n := by
  rw [P.tStructure_isGE_iff, Q.tStructure_isGE_iff]
  exact isGE_iff_isGE_map hzero X.property n

/-- Formula (A.4) on the restricted categories.

As in `tStructure_isLE_iff_map`, zero reflection is required only on objects
of `P`. -/
theorem tStructure_isGE_iff_map
    [P.IsTriangulated] [Q.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hmem : ∀ X : C, P X ↔ Q (F.obj X))
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsGE X n ↔
      (Q.tStructure t').IsGE ((preimageLift F hmem).obj X) n :=
  tStructure_isGE_iff_map_of_le hzero (fun X ↦ (hmem X).1) X n

end CategoryTheory.ObjectProperty
