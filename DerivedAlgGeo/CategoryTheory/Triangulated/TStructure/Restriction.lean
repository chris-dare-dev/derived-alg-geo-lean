/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Restricting t-structures detected by a t-exact functor

This file formalizes Steps 2 and 3 of Polishchuk's Theorem A.17 from
arXiv:2607.28411v1. If a t-exact functor detects membership in chosen bounded
subcategories, then restriction of the target t-structure forces restriction
of the source t-structure. If the functor also reflects zero objects, the two
halves of the restricted source t-structure are recognized exactly on the
target; these are formulas (A.3) and (A.4).

The theorem is independent of schemes and of the compact-generation argument
that constructs the large source t-structure in Step 1.

## Main definitions

* `ObjectProperty.preimageLift`: the functor between the two selected full
  subcategories, with the `Additive`, `CommShift ℤ`, and `IsTriangulated`
  instances a slicing consumer needs of a detecting functor.
* `ObjectProperty.inverseImageLift`: its `P = F⁻¹ Q` special case, the shape
  hypothesis (iv) of A.17 produces, and `ObjectProperty.liftToInverseImage`,
  the restriction of a functor in the other direction whose composite with
  `F` preserves `Q`.
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

/-- The functor between the two full subcategories selected by a detection
equivalence. -/
def preimageLift (F : Functor C D) (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    Functor P.FullSubcategory Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun X ↦ (hmem X.obj).1 X.property)

instance instAdditivePreimageLift [F.Additive] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).Additive :=
  inferInstanceAs (Q.lift (P.ι ⋙ F) (fun X ↦ (hmem X.obj).1 X.property)).Additive

noncomputable instance instCommShiftPreimageLift [P.IsTriangulated] [Q.IsTriangulated]
    [F.CommShift ℤ] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).CommShift ℤ :=
  inferInstanceAs ((Q.lift (P.ι ⋙ F) (fun X ↦ (hmem X.obj).1 X.property)).CommShift ℤ)

instance instIsTriangulatedPreimageLift [P.IsTriangulated] [Q.IsTriangulated] [F.CommShift ℤ]
    [F.IsTriangulated] (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    (preimageLift F hmem).IsTriangulated :=
  inferInstanceAs (Q.lift (P.ι ⋙ F) (fun X ↦ (hmem X.obj).1 X.property)).IsTriangulated

/-- The restriction of `F` to the objects whose image lies in `Q`, landing
in `Q`.  This is the functor between the selected subcategories under
hypothesis (iv) of Theorem A.17 of arXiv:2607.28411v1, `P = F⁻¹ Q`, the
form `Polishchuk.induce` produces.

Kept an `abbrev`, hence reducible, so that a `Polishchuk.InducedTStructureData`
field stated with `preimageLift F (fun _ ↦ Iff.rfl)` is definitionally the
same functor; `Slicing.IndExtensions.nonempty_inducedTStructures` relies on
that. -/
abbrev inverseImageLift (F : Functor C D) (Q : ObjectProperty D) :
    Functor (Q.inverseImage F).FullSubcategory Q.FullSubcategory :=
  preimageLift F (P := Q.inverseImage F) (Q := Q) fun _ ↦ Iff.rfl

/-- The restriction of `L : D ⥤ C` to `Q`, landing in `F⁻¹ Q`, when `F ∘ L`
preserves `Q`.  For `L` a left adjoint of `F` this is the bounded left
adjoint of `inverseImageLift F Q`; geometrically, `f_!` on `Dᵇ(Coh)` when it
preserves bounded coherent complexes. -/
abbrev liftToInverseImage (F : Functor C D) (Q : ObjectProperty D) (L : Functor D C)
    (hL : ∀ E : D, Q E → Q (F.obj (L.obj E))) :
    Functor Q.FullSubcategory (Q.inverseImage F).FullSubcategory :=
  (Q.inverseImage F).lift (Q.ι ⋙ L) fun E ↦ hL E.obj E.property

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
      (Q.tStructure t').IsLE ((preimageLift F hmem).obj X) n := by
  rw [P.tStructure_isLE_iff, Q.tStructure_isLE_iff]
  have key : t.IsLE X.obj n ↔ t'.IsLE (F.obj X.obj) n := by
    constructor
    · exact Functor.IsRightTExact.isLE_map X.obj n
    · intro hX
      haveI : t'.IsLE (F.obj X.obj) n := hX
      have hTarget : IsZero ((t'.truncGE (n + 1)).obj (F.obj X.obj)) :=
        t'.isZero_truncGE_obj_of_isLE n (n + 1) rfl (F.obj X.obj)
      have hMapped : IsZero (F.obj ((t.truncGE (n + 1)).obj X.obj)) :=
        hTarget.of_iso (F.mapTruncGEIso t t' (n + 1) X.obj)
      have hP : P ((t.truncGE (n + 1)).obj X.obj) := by
        simpa only [TStructure.triangleLEGE_obj_obj₃] using
          (P.mem_of_hasInductedTStructure t _
            (t.triangleLEGE_distinguished n (n + 1) rfl X.obj) n (n + 1) rfl
            (by simpa only [TStructure.triangleLEGE_obj_obj₁] using
              t.isLE_truncLE_obj X.obj n n)
            X.property
            (by simpa only [TStructure.triangleLEGE_obj_obj₃] using
              t.isGE_truncGE_obj X.obj (n + 1) (n + 1))).2
      exact (t.isLE_iff_isZero_truncGE_obj n (n + 1) rfl X.obj).2
        (hzero _ hP hMapped)
  exact key

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
      (Q.tStructure t').IsGE ((preimageLift F hmem).obj X) n := by
  rw [P.tStructure_isGE_iff, Q.tStructure_isGE_iff]
  have key : t.IsGE X.obj n ↔ t'.IsGE (F.obj X.obj) n := by
    constructor
    · exact Functor.IsLeftTExact.isGE_map X.obj n
    · intro hX
      haveI : t'.IsGE (F.obj X.obj) n := hX
      have hTarget : IsZero ((t'.truncLT n).obj (F.obj X.obj)) :=
        t'.isZero_truncLT_obj_of_isGE n (F.obj X.obj)
      let e : F.obj ((t.truncLT n).obj X.obj) ≅
          (t'.truncLT n).obj (F.obj X.obj) := by
        simpa only [TStructure.truncLE, sub_add_cancel] using
          F.mapTruncLEIso t t' (n - 1) X.obj
      have hMapped : IsZero (F.obj ((t.truncLT n).obj X.obj)) :=
        hTarget.of_iso e
      have hP : P ((t.truncLT n).obj X.obj) := by
        have h₁ := (P.mem_of_hasInductedTStructure t _
          (t.triangleLEGE_distinguished (n - 1) n (by omega) X.obj)
          (n - 1) n (by omega)
          (by simpa only [TStructure.triangleLEGE_obj_obj₁] using
            t.isLE_truncLE_obj X.obj (n - 1) (n - 1))
          X.property
          (by simpa only [TStructure.triangleLEGE_obj_obj₃] using
            t.isGE_truncGE_obj X.obj n n)).1
        simpa only [TStructure.triangleLEGE_obj_obj₁, TStructure.truncLE,
          sub_add_cancel] using h₁
      exact (t.isGE_iff_isZero_truncLT_obj n X.obj).2 (hzero _ hP hMapped)
  exact key

end CategoryTheory.ObjectProperty
