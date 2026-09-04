/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Lifting a functor to full subcategories cut out by object properties

Mathlib's `ObjectProperty.lift` restricts a functor to the full subcategory a property cuts out,
and `ObjectProperty.inverseImage` pulls a property back along a functor. This file combines the
two: given `F : C ⥤ D` and properties `P` on `C` and `Q` on `D` with `P ≤ F⁻¹ Q`, it names the
restriction `P.FullSubcategory ⥤ Q.FullSubcategory`, transports the `Additive`, `CommShift ℤ`, and
`IsTriangulated` instances `lift` already carries, and restricts an adjunction on either side of
`F` to those subcategories.

Nothing here mentions a t-structure, a slicing, or a stability condition. The declarations lived in
`CategoryTheory/Triangulated/TStructure/Restriction.lean` until this cutover because that is where
Theorem A.17 of arXiv:2607.28411v1 first needed them; their carrier is `ObjectProperty`, whose
`lift`, `ι`, `ιOfLE`, `liftCompιIso`, and `fullyFaithfulι` Mathlib defines in
`Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`, so this file mirrors that directory.
It is named for the operation it adds rather than for Mathlib's file because
`ObjectProperty/FullSubcategory.lean` is one of the two paths `scripts/check_source_independence.py`
keeps retired -- a verbatim copy from the retired stability source once lived there and was replaced
by an owner-native proof, and that gate has no allowlist. The consumers now import this file
directly. That the block is not t-structure theory is settled by its own import list: it needs
Mathlib alone, and nothing from `DerivedAlgGeo`.

## Main definitions

* `ObjectProperty.liftOfLE`: the restriction of `F` to a subcategory `P ≤ F⁻¹ Q`, landing in `Q`,
  with the `Additive`, `CommShift ℤ`, and `IsTriangulated` instances a triangulated consumer needs.
* `ObjectProperty.preimageLift`: its case of a two-way detection `P X ↔ Q (F.obj X)`.
* `ObjectProperty.inverseImageLift`: its `P = F⁻¹ Q` case.
* `ObjectProperty.liftToInverseImage`: the restriction of a functor in the other direction whose
  composite with `F` preserves `Q`.
* `Adjunction.restrictInverseImageLeft` and `Adjunction.restrictInverseImageRight`: an adjunction
  on either side of `F` restricted to those subcategories, through Mathlib's
  `Adjunction.restrictFullyFaithful`; the suffix names which adjoint of `F` is restricted.

## References

* arXiv:2607.28411v1, Theorem A.17 and Proposition 3.8, where these restrictions are used.
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
  {F : Functor C D} {P : ObjectProperty C} {Q : ObjectProperty D}

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

end CategoryTheory.ObjectProperty
