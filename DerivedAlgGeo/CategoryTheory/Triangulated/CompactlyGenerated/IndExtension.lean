/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Brown
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Orthogonal
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Restriction

/-!
# Ind-extended t-structures

This file proves the categorical restriction argument in Lemma A.14 of
arXiv:2607.28411v1. An Ind-extension has a compactly generated large
t-structure, aisle `Coprod(Dᵇ≤0)`, and restriction equal to the original
bounded t-structure.

The record is theorem output data, not a replacement for Neeman's theorem.
`IndExtensionData.ofApproximation` derives the large t-structure, aisle
formula, and compact generation from the A.13 output.  The orthogonality
argument below proves the restriction statements internally; callers do not
supply them.  A separate constructor allows a compact generating property
whose coproduct-and-extension closure agrees with `Coprod(Dᵇ≤0)`, avoiding the
false assertion that every bounded coherent complex is compact.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The large-category image of the nonpositive objects in a t-structure on
a full subcategory. -/
def boundedAisle (P : ObjectProperty C) [P.IsTriangulated]
    (t : TStructure P.FullSubcategory) : ObjectProperty C :=
  (t.le 0).map P.ι

/-- An object in the degree-one coaisle of the small t-structure is right
orthogonal, in the ambient category, to the coproduct-and-extension closure of
the mapped small aisle.  This is the orthogonality observation in the proof of
Lemma A.14.

Only the generator case is proved here: the three closure cases are
`ObjectProperty.coprodClosure_le`'s hypotheses, and each is an instance on
`ObjectProperty.leftOrthogonal`. -/
theorem coprodBoundedAisle_rightOrthogonal_of_isGE
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory)
    (Y : P.FullSubcategory) (hY : small.IsGE Y 1) :
    (boundedAisle P small).coprodClosure.{w}.rightOrthogonal Y.obj := by
  intro Z f hZ
  refine (boundedAisle P small).coprodClosure_le
    (Q := ObjectProperty.leftOrthogonal (fun W => W = Y.obj))
    (fun W hW => ?_) Z hZ f rfl
  obtain ⟨X, hX, ⟨e⟩⟩ := hW
  rintro _ g rfl
  rw [← cancel_epi e.hom, comp_zero]
  have hzero : P.fullyFaithfulι.preimage (e.hom ≫ g) = 0 :=
    small.zero_of_isLE_of_isGE _ 0 1 (by omega) ⟨hX⟩ hY
  change ObjectProperty.homMk (e.hom ≫ g) = 0 at hzero
  exact congrArg (fun q => q.hom) hzero

/-- The mapped small aisle is contained in any large aisle whose degree-zero
part is its coproduct-and-extension closure. -/
theorem boundedAisle_le_large
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w}) :
    boundedAisle P small ≤ large.le 0 := by
  rw [hlarge]
  exact (boundedAisle P small).le_coprodClosure.{w}

/-- Degree zero of the large t-structure restricts to degree zero of the
small t-structure. -/
theorem large_isLE_zero_iff
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w})
    (X : P.FullSubcategory) :
    large.IsLE X.obj 0 ↔ small.IsLE X 0 := by
  constructor
  · intro hX
    rw [small.isLE_iff_orthogonal 0 1 rfl]
    intro Y f hY
    apply P.ι.map_injective
    have hYlarge : large.IsGE Y.obj 1 := by
      rw [large.isGE_iff_orthogonal 0 1 rfl]
      intro Z g hZ
      have hZ' : (boundedAisle P small).coprodClosure.{w} Z := by
        rw [← hlarge]
        exact hZ.le
      exact coprodBoundedAisle_rightOrthogonal_of_isGE P small Y hY g hZ'
    exact large.zero_of_isLE_of_isGE (P.ι.map f) 0 1 (by omega) hX hYlarge
  · intro hX
    exact ⟨boundedAisle_le_large P small large hlarge X.obj
      ((small.le 0).prop_map_obj P.ι hX.le)⟩

/-- Degree one of the large t-structure restricts to degree one of the small
t-structure. -/
theorem large_isGE_one_iff
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w})
    (X : P.FullSubcategory) :
    large.IsGE X.obj 1 ↔ small.IsGE X 1 := by
  constructor
  · intro hX
    rw [small.isGE_iff_orthogonal 0 1 rfl]
    intro Y f hY
    apply P.ι.map_injective
    exact large.zero_of_isLE_of_isGE (P.ι.map f) 0 1 (by omega)
      ((large_isLE_zero_iff P small large hlarge Y).2 hY) hX
  · intro hX
    rw [large.isGE_iff_orthogonal 0 1 rfl]
    intro Z f hZ
    have hZ' : (boundedAisle P small).coprodClosure.{w} Z := by
      rw [← hlarge]
      exact hZ.le
    exact coprodBoundedAisle_rightOrthogonal_of_isGE P small X hX f hZ'

/-- The image of a small aisle is closed under the shift required by the
compact-generator Brown construction. -/
theorem boundedAisle_le_shift
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) :
    boundedAisle P small ≤ (boundedAisle P small).shift (1 : ℤ) := by
  rintro Z ⟨X, hX, ⟨e⟩⟩
  letI : small.IsLE X 0 := ⟨hX⟩
  have hshiftNeg : small.IsLE (X⟦(1 : ℤ)⟧) (-1) :=
    small.isLE_shift X 0 1 (-1) (by omega)
  letI : small.IsLE (X⟦(1 : ℤ)⟧) (-1) := hshiftNeg
  have hshift : small.IsLE (X⟦(1 : ℤ)⟧) 0 :=
    small.isLE_of_le _ (-1) 0 (by omega)
  exact ⟨X⟦(1 : ℤ)⟧, hshift.le,
    ⟨(P.ι.commShiftIso (1 : ℤ)).app X ≪≫
      (shiftFunctor C (1 : ℤ)).mapIso e⟩⟩

/-- The degree-zero restriction equality propagates to every coconnective
degree by shifting. -/
theorem large_isLE_iff
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w})
    (X : P.FullSubcategory) (n : ℤ) :
    large.IsLE X.obj n ↔ small.IsLE X n := by
  let e : (X⟦n⟧).obj ≅ X.obj⟦n⟧ := (P.ι.commShiftIso n).app X
  constructor
  · intro hX
    have hLargeShift : large.IsLE (X.obj⟦n⟧) 0 :=
      (large.isLE_shift_iff X.obj n n 0 (by omega)).2 hX
    letI : large.IsLE (X.obj⟦n⟧) 0 := hLargeShift
    have hLargeSmallShift : large.IsLE (X⟦n⟧).obj 0 :=
      large.isLE_of_iso e.symm 0
    have hSmallShift : small.IsLE (X⟦n⟧) 0 :=
      (large_isLE_zero_iff P small large hlarge (X⟦n⟧)).1
        hLargeSmallShift
    exact (small.isLE_shift_iff X n n 0 (by omega)).1 hSmallShift
  · intro hX
    have hSmallShift : small.IsLE (X⟦n⟧) 0 :=
      (small.isLE_shift_iff X n n 0 (by omega)).2 hX
    have hLargeSmallShift : large.IsLE (X⟦n⟧).obj 0 :=
      (large_isLE_zero_iff P small large hlarge (X⟦n⟧)).2 hSmallShift
    letI : large.IsLE (X⟦n⟧).obj 0 := hLargeSmallShift
    have hLargeShift : large.IsLE (X.obj⟦n⟧) 0 :=
      large.isLE_of_iso e 0
    exact (large.isLE_shift_iff X.obj n n 0 (by omega)).1 hLargeShift

/-- The degree-one restriction equality propagates to every connective
degree by shifting. -/
theorem large_isGE_iff
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w})
    (X : P.FullSubcategory) (n : ℤ) :
    large.IsGE X.obj n ↔ small.IsGE X n := by
  let a := n - 1
  let e : (X⟦a⟧).obj ≅ X.obj⟦a⟧ := (P.ι.commShiftIso a).app X
  constructor
  · intro hX
    have hLargeShift : large.IsGE (X.obj⟦a⟧) 1 :=
      (large.isGE_shift_iff X.obj n a 1 (by omega)).2 hX
    letI : large.IsGE (X.obj⟦a⟧) 1 := hLargeShift
    have hLargeSmallShift : large.IsGE (X⟦a⟧).obj 1 :=
      large.isGE_of_iso e.symm 1
    have hSmallShift : small.IsGE (X⟦a⟧) 1 :=
      (large_isGE_one_iff P small large hlarge (X⟦a⟧)).1
        hLargeSmallShift
    exact (small.isGE_shift_iff X n a 1 (by omega)).1 hSmallShift
  · intro hX
    have hSmallShift : small.IsGE (X⟦a⟧) 1 :=
      (small.isGE_shift_iff X n a 1 (by omega)).2 hX
    have hLargeSmallShift : large.IsGE (X⟦a⟧).obj 1 :=
      (large_isGE_one_iff P small large hlarge (X⟦a⟧)).2 hSmallShift
    letI : large.IsGE (X⟦a⟧).obj 1 := hLargeSmallShift
    have hLargeShift : large.IsGE (X.obj⟦a⟧) 1 :=
      large.isGE_of_iso e 1
    exact (large.isGE_shift_iff X.obj n a 1 (by omega)).1 hLargeShift

/-- The aisle equality constructs the induced t-structure on the selected
full subcategory; truncation stability is a theorem, not caller data. -/
theorem hasInducedTStructure_of_largeAisle
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C)
    (hlarge : large.le 0 = (boundedAisle P small).coprodClosure.{w}) :
    P.HasInducedTStructure large := by
  constructor
  intro A hA
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
    small.exists_triangle_zero_one ⟨A, hA⟩
  let T := P.ι.mapTriangle.obj (Triangle.mk f g h)
  refine ⟨T.obj₁, T.obj₃,
    (large_isLE_zero_iff P small large hlarge X).2 ⟨hX⟩,
    (large_isGE_one_iff P small large hlarge Y).2 ⟨hY⟩,
    T.mor₁, T.mor₂, T.mor₃, P.ι.map_distinguished _ hT, ?_, ?_⟩
  · exact P.le_isoClosure _ X.property
  · exact P.le_isoClosure _ Y.property

/-- The precise output package of Lemma A.14.

`largeAisle` is clause (i), `compactlyGenerated` is clause (ii), and the two
restriction equivalences are clause (iii). -/
structure IndExtensionData (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C) : Prop where
  /-- The original t-structure is bounded. -/
  small_isBounded : small.IsBounded
  /-- Clause (i): the large aisle is `Coprod` of the bounded aisle. -/
  largeAisle : large.le 0 = (boundedAisle P small).coprodClosure.{w}
  /-- Clause (ii): the large t-structure is compactly generated. -/
  compactlyGenerated : ∃ G : ObjectProperty C,
    large.IsCompactlyGeneratedBy.{w} G
  /-- The large t-structure restricts to the selected full subcategory. -/
  hasInduced : P.HasInducedTStructure large
  /-- Clause (iii), coconnective half, in every degree. -/
  isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    large.IsLE X.obj n ↔ small.IsLE X n
  /-- Clause (iii), connective half, in every degree. -/
  isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    large.IsGE X.obj n ↔ small.IsGE X n

namespace IndExtensionData

/-- Assemble A.14 from a compact generating property whose `Coprod` closure
is the closure of the mapped bounded aisle.

This is the correct Neeman-style boundary: `G` consists of compact objects,
but the objects of `Dᵇ≤0` themselves need not be compact.  The A.13
approximation supplies the large t-structure.  The aisle equality then proves
truncation stability and both restriction equivalences internally. -/
theorem ofCompactGenerators
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory)
    (hsmall : small.IsBounded)
    {G : ObjectProperty C}
    (happrox : CompactGeneratorApproximation.{w} G)
    (hcompact : G ≤ ObjectProperty.compactObjects.{w} (C := C))
    (hclosure : G.coprodClosure.{w} =
      (boundedAisle P small).coprodClosure.{w}) :
    IndExtensionData.{w} P small happrox.tStructure := by
  have hlarge : happrox.tStructure.le 0 =
      (boundedAisle P small).coprodClosure.{w} := by
    rw [happrox.tStructure_le_zero, hclosure]
  let hInduced : P.HasInducedTStructure happrox.tStructure :=
    hasInducedTStructure_of_largeAisle P small happrox.tStructure hlarge
  letI : P.HasInducedTStructure happrox.tStructure := hInduced
  exact
    { small_isBounded := hsmall
      largeAisle := hlarge
      compactlyGenerated :=
        ⟨G, happrox.isCompactlyGeneratedBy hcompact⟩
      hasInduced := hInduced
      isLE_iff := large_isLE_iff P small happrox.tStructure hlarge
      isGE_iff := large_isGE_iff P small happrox.tStructure hlarge }

/-- Specialization of `ofCompactGenerators` in which the mapped bounded
aisle itself consists of compact objects.  This stronger hypothesis is useful
categorically, but is not imposed by the scheme-level A.14 constructor. -/
theorem ofApproximation
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory)
    (hsmall : small.IsBounded)
    (happrox : CompactGeneratorApproximation.{w} (boundedAisle P small))
    (hcompact : boundedAisle P small ≤
      ObjectProperty.compactObjects.{w} (C := C)) :
    IndExtensionData.{w} P small happrox.tStructure :=
  ofCompactGenerators P small hsmall happrox hcompact rfl

/-- Construct the full A.14 output directly from the owned Brown tower and a
Neeman-style compact generating property.

The only comparison input is the honest geometric statement that the compact
generators and the mapped bounded aisle have the same coproduct-and-extension
closure.  Restriction is no longer supplied by the caller. -/
theorem ofBrown
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory)
    (hsmall : small.IsBounded)
    {G : ObjectProperty C}
    [ObjectProperty.Small.{0} G] [LocallySmall.{0} C]
    [HasCoproducts.{0} C]
    (hshift : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C))
    (hclosure : G.coprodClosure.{0} =
      (boundedAisle P small).coprodClosure.{0}) :
    IndExtensionData.{0} P small
      (CompactGeneratorBrown.tStructure (G := G) hshift hcompact) :=
  ofCompactGenerators P small hsmall
    (CompactGeneratorBrown.compactGeneratorApproximation
      (G := G) hshift hcompact)
    hcompact hclosure

end IndExtensionData

end CategoryTheory.Triangulated.TStructure
