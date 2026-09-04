/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.IndExtension

/-!
# The categorical core of Polishchuk's inducing theorem

This file assembles Steps 1--4 of Theorem A.17 in arXiv:2607.28411v1 after
the compactly generated large t-structures have been constructed.

The result constructs a bounded t-structure on the selected source
subcategory and proves the recognition formulas (A.3) and (A.4). It does not
assume those formulas or boundedness. The only large-category t-structure
input on the source is the concrete output of Theorem A.13: a `TStructure`
together with its proved compact-generation formula.

The selected source subcategory comes in three shapes.  `induce` takes the
preimage `F⁻¹ Q` of a bounded target subcategory, hypothesis (iv) of Theorem
A.17 built in, and proves truncation stability from (iv).  `induceLarge`
takes any triangulated `P` with truncation stability supplied (Definition
A.7) and recognizes (A.3) and (A.4) against the large target t-structure
itself, with no target subcategory; boundedness comes from
`P ⊆ F⁻¹(tD-bounded)`.  `induceOfLE` is `induceLarge` read inside a bounded
`Q` with `P ⊆ F⁻¹ Q`, the shape `Slicing.InducedTStructures` consumes, and
`induce` is its case `P = F⁻¹ Q`; conversely, once `D` is triangulated,
`induceLarge` is `induceOfLE` at `Q = tD.bounded` through Mathlib's instances
on `TStructure.bounded`.  No geometric instance of `induceOfLE` with
`P ≠ F⁻¹ Q` is claimed.

Theorem 2.8 of arXiv:2607.28411v1 for an infinite extension `ℓ/k` is in the
large shape: `π_*` sends no nonzero coherent object into `Dᵇ(Coh X)`, so
`P ⊆ F⁻¹ Q` fails for `Q = Dᵇ(Coh X)`, and the paper recognizes `𝒫_ℓ`
against the Ind-extension on `Dqc(X)`.  `induceLarge` is the Theorem A.17
half of that, one phase at a time; reading the phases into a slicing, the
Corollary A.23 half, is the open item in `Phase/Transfer/Inducing.lean`.

Scheme realization, bounded-coherent/perfect identification, and S-locality
are intentionally absent. They are the geometric layer of SF7.3.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u₁ u₂

namespace CategoryTheory.Triangulated.Polishchuk

variable {C : Type u₁} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- The bounded categorical output of A.17 on a source subcategory `P`, with
formulas (A.3) and (A.4) stated against the large target t-structure: the
shape in which Theorem 2.8(1) of arXiv:2607.28411v1 recognizes the
base-changed slicing, where `F = π_*` lands in `Dqc(X)`.  The `tD`-bounded
objects do form a bounded target subcategory (Mathlib's
`TStructure.onBounded`); what is unavailable there is one carrying the
slicing that contains the image of `Dᵇ(Coh X_ℓ)`. -/
structure InducedTStructureDataLarge
    (F : Functor C D) (P : ObjectProperty C) [P.IsTriangulated]
    (tD : TStructure D) where
  /-- The induced t-structure on the selected source subcategory. -/
  tStructure : TStructure P.FullSubcategory
  /-- Step 4: the induced t-structure is bounded. -/
  isBounded : TStructure.IsBounded tStructure
  /-- Formula (A.3), in every degree, against the large target. -/
  isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    tStructure.IsLE X n ↔ tD.IsLE (F.obj X.obj) n
  /-- Formula (A.4), in every degree, against the large target. -/
  isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    tStructure.IsGE X n ↔ tD.IsGE (F.obj X.obj) n

/-- The bounded categorical output of A.17 on a source subcategory `P ≤ F⁻¹ Q`,
with formulas (A.3) and (A.4) stated against the restricted target
t-structure. -/
structure InducedTStructureData
    (F : Functor C D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsTriangulated] [Q.IsTriangulated]
    (tD : TStructure D) [Q.HasInducedTStructure tD]
    (hle : P ≤ Q.inverseImage F) where
  /-- The induced t-structure on the selected source subcategory. -/
  tStructure : TStructure P.FullSubcategory
  /-- Step 4: the induced t-structure is bounded. -/
  isBounded : TStructure.IsBounded tStructure
  /-- Formula (A.3), in every degree. -/
  isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    tStructure.IsLE X n ↔
      (Q.tStructure tD).IsLE
        ((ObjectProperty.liftOfLE F hle).obj X) n
  /-- Formula (A.4), in every degree. -/
  isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    tStructure.IsGE X n ↔
      (Q.tStructure tD).IsGE
        ((ObjectProperty.liftOfLE F hle).obj X) n

/-- `InducedTStructureDataLarge` read inside a bounded target subcategory
`Q ⊇ F(P)`: the recognition formulas restated through `Q.tStructure_isLE_iff`
and `isGE_iff`.  The converse restatement holds too, so the two structures
carry the same content once `hle` is available. -/
def InducedTStructureDataLarge.toInducedTStructureData {F : Functor C D}
    {P : ObjectProperty C} [P.IsTriangulated] {Q : ObjectProperty D} [Q.IsTriangulated]
    {tD : TStructure D} [Q.HasInducedTStructure tD]
    (d : InducedTStructureDataLarge F P tD) (hle : P ≤ Q.inverseImage F) :
    InducedTStructureData F P Q tD hle where
  tStructure := d.tStructure
  isBounded := d.isBounded
  isLE_iff X n := (d.isLE_iff X n).trans
    (Q.tStructure_isLE_iff tD ((ObjectProperty.liftOfLE F hle).obj X) n).symm
  isGE_iff X n := (d.isGE_iff X n).trans
    (Q.tStructure_isGE_iff tD ((ObjectProperty.liftOfLE F hle).obj X) n).symm

/-- Theorem A.17, categorical Steps 1--4, with recognition against the large
target t-structure and no target subcategory.  Hypothesis (iv) of A.17 is
replaced by truncation stability of `P` (`htrunc`, Definition A.7 and Remark
A.8 of arXiv:2607.28411v1) and by `hbdd`, that `F` sends `P` into the
`tD`-bounded objects; zero reflection is needed on `P` only.  This is the
shape Theorem 2.8(1) needs for the base change `π : X_ℓ → X` along an
arbitrary field extension: `P = Dᵇ(Coh X_ℓ)`, `F = π_*` into `Dqc(X)`, `tD`
the Ind-extension `τ̂'_φ` -- the Theorem A.17 half of 2.8(1), one phase at a
time.  The Corollary A.23 half, reading the phases into a slicing, is open
(`Phase/Transfer/Inducing.lean`). -/
noncomputable def induceLarge
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tC : TStructure C} {tD : TStructure D} {G : ObjectProperty D}
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (htrunc : P.HasInducedTStructure tC)
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (hC : tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hbdd : P ≤ tD.bounded.inverseImage F) :
    InducedTStructureDataLarge F P tD := by
  letI : F.IsTExact tC tD :=
    adj.isTExact_of_compactlyGenerated hF hD hC hmonad
  letI := htrunc
  exact
    { tStructure := P.tStructure tC
      isBounded := ObjectProperty.tStructure_isBounded_of_le_bounded_inverseImage
        (P := P) (F := F) (t := tC) (t' := tD) hzero hbdd
      isLE_iff := fun X n => (P.tStructure_isLE_iff tC X n).trans
        (ObjectProperty.isLE_iff_isLE_map (P := P) (F := F) (t := tC) (t' := tD)
          hzero X.property n)
      isGE_iff := fun X n => (P.tStructure_isGE_iff tC X n).trans
        (ObjectProperty.isGE_iff_isGE_map (P := P) (F := F) (t := tC) (t' := tD)
          hzero X.property n) }

/-- Theorem A.17, categorical Steps 1--4, on a triangulated `P ≤ F⁻¹ Q`:
`induceLarge` restated inside `Q`, boundedness of `Q` supplying the
bounded-image containment through `hle`.  Hypothesis (iv) of A.17 is used by
the paper only to show the source t-structure restricts to the selected
subcategory; here that conclusion is the hypothesis `htrunc`, which for
`P = F⁻¹ Q` is `ObjectProperty.hasInducedTStructure_of_preimage` (`induce`).
Zero reflection is needed on `P` only.  This is the shape
`Slicing.InducedTStructures` consumes, with the slicing on `Q`; it is not the
shape of Theorem 2.8 for an infinite extension `ℓ/k`, where `hle` fails for
`Q = Dᵇ(Coh X)` and `induceLarge` applies instead. -/
noncomputable def induceOfLE
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tC : TStructure C} {tD : TStructure D}
    {G : ObjectProperty D} {Q : ObjectProperty D}
    [Q.IsTriangulated] [Q.HasInducedTStructure tD]
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hle : P ≤ Q.inverseImage F)
    (htrunc : P.HasInducedTStructure tC)
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (hC : tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, P E → IsZero (F.obj E) → IsZero E)
    (hbounded : TStructure.IsBounded (Q.tStructure tD)) :
    InducedTStructureData F P Q tD hle :=
  (induceLarge adj P htrunc hF hD hC hmonad hzero
    (fun X hX =>
      (ObjectProperty.tStructure_isBounded_iff_le_bounded.1 hbounded) _
        (hle X hX))).toInducedTStructureData hle

/-- Theorem A.17, categorical Steps 1--4, on the preimage `F⁻¹ Q`.

The target large t-structure is compactly generated by `G`; the source large
t-structure is the A.13 output generated by the left-adjoint image of `G`.
The monad hypothesis proves t-exactness. Detection of the selected
subcategories proves truncation stability, zero reflection proves both
recognition formulas, and boundedness descends from the restricted target.

Zero reflection is assumed only on objects whose image lies in the selected
target subcategory `Q` -- the object-property form of A.17's
conservativity-on-bounded-objects hypothesis. Until 2026-08-18 it was
demanded on the whole source category, which was sound but strictly stronger
than the source theorem and a materially harder obligation for the scheme
realization (adversarial review, finding P2-11). -/
noncomputable def induce
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tC : TStructure C} {tD : TStructure D}
    {G : ObjectProperty D} {Q : ObjectProperty D}
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    [Q.HasInducedTStructure tD]
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (hC : tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hbounded : TStructure.IsBounded (Q.tStructure tD)) :
    InducedTStructureData F (Q.inverseImage F) Q tD le_rfl := by
  letI : F.IsTExact tC tD :=
    adj.isTExact_of_compactlyGenerated hF hD hC hmonad
  exact induceOfLE adj (Q.inverseImage F) le_rfl
    (ObjectProperty.hasInducedTStructure_of_preimage
      (P := Q.inverseImage F) (Q := Q) (F := F) (t := tC) (t' := tD) (fun _ ↦ Iff.rfl))
    hF hD hC hmonad hzero hbounded

/-- The categorical A.17 constructor with the source t-structure assembled
directly from the A.13 approximation triangles.

Compactness of the source generators is derived from the adjunction and target
compactness. Thus the only source existence input is the honest Brown-
representability approximation output, not a pre-existing t-structure or its
compact-generation equality. -/
noncomputable def induceOfApproximation
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tD : TStructure D} {G : ObjectProperty D} {Q : ObjectProperty D}
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    [Q.HasInducedTStructure tD]
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (happrox : TStructure.CompactGeneratorApproximation.{w} (G.map L))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hbounded : TStructure.IsBounded (Q.tStructure tD)) :
    InducedTStructureData F (Q.inverseImage F) Q tD le_rfl :=
  induce adj hF hD
    (happrox.isCompactlyGeneratedBy
      (adj.compactObjects_map_leftAdjoint hF hD.compact))
    hmonad hzero hbounded

/-- The categorical A.17 constructor using the repository-owned Brown tower.

The source compact generators are the left-adjoint images of the target
generators. Their compactness follows from the adjunction and coproduct
preservation. The remaining size and shift-closure assumptions are stated
explicitly, so no approximation-map or global inducing theorem is accepted
from the caller. -/
noncomputable def induceOfBrown
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tD : TStructure D} {G : ObjectProperty D} {Q : ObjectProperty D}
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    [Q.HasInducedTStructure tD]
    [ObjectProperty.Small.{0} (G.map L)] [LocallySmall.{0} C]
    [HasCoproducts.{0} C]
    (hF : F.PreservesSmallCoproducts.{0})
    (hD : tD.IsCompactlyGeneratedBy.{0} G)
    (hshift : G.map L ≤ (G.map L).shift (1 : ℤ))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hbounded : TStructure.IsBounded (Q.tStructure tD)) :
    InducedTStructureData F (Q.inverseImage F) Q tD le_rfl :=
  induceOfApproximation adj hF hD
    (TStructure.CompactGeneratorBrown.compactGeneratorApproximation
      (G := G.map L) hshift
      (adj.compactObjects_map_leftAdjoint hF hD.compact))
    hmonad hzero hbounded

/-- The categorical A.17 constructor from Brown-style universal maps.

The source approximation triangles and the proof that their cones are right
orthogonal are both constructed internally.  The remaining representability
input is precisely the existence of universal maps with the two Hom controls
recorded by `TStructure.ApproximationMap`. -/
noncomputable def induceOfApproximationMaps
    {L : Functor D C} {F : Functor C D}
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (adj : L ⊣ F)
    {tD : TStructure D} {G : ObjectProperty D} {Q : ObjectProperty D}
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    [Q.HasInducedTStructure tD]
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (hshift : G.map L ≤ (G.map L).shift (1 : ℤ))
    (happrox : ∀ A : C,
      Nonempty (TStructure.ApproximationMap (G.map L).coprodClosure.{w} A))
    (hmonad : (L ⋙ F).IsRightTExact tD tD)
    (hzero : ∀ E : C, Q (F.obj E) → IsZero (F.obj E) → IsZero E)
    (hbounded : TStructure.IsBounded (Q.tStructure tD)) :
    InducedTStructureData F (Q.inverseImage F) Q tD le_rfl :=
  induceOfApproximation adj hF hD
    (TStructure.CompactGeneratorApproximation.ofApproximationMaps hshift happrox)
    hmonad hzero hbounded

end CategoryTheory.Triangulated.Polishchuk
