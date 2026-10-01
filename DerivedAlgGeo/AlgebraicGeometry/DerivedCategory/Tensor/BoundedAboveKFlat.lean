/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Embedding.StupidTruncGE
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.FiniteKFlat
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.ComplexColimits

/-!
# Bounded-above flat complexes are K-flat for scheme-module tensor

The increasing lower stupid-truncation tower of a strictly bounded-above
complex has finite term support at every stage. When all terms of the input
are flat over the identity, the finite K-flat theorem applies stagewise.
Sequential colimits then recover the original complex and preserve K-flatness.

## Main definitions

This module introduces no new definitions. It uses the existing
`CategoryTheory.CochainComplex.IsKFlat` predicate and literal
`AlgebraicGeometry.Scheme.Modules.totalTensor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isKFlat_totalTensor_of_boundedAbove_flatTerms`
  proves two-slot K-flatness for a strictly bounded-above complex whose every
  term is flat over the identity.

## Implementation notes

Each lower stupid tail is supported in a finite interval. Flatness transfers
across its component isomorphism to the input; the finite-support theorem
proves K-flatness of that stage. The generic K-flat colimit theorem applies
using sequential-colimit preservation of total tensor in both slots and
the AB5 property of scheme-module sheaves. An isomorphism from the input to
the tower's colimit transports the two localization clauses back to the input.
This theorem does not assert an arbitrary unbounded flat-term complex is K-flat.

## References

The ingredients are the lower stupid-tower colimit theorem in
`HomologicalComplex.isColimitStupidTruncGETowerCocone`,
`AlgebraicGeometry.Scheme.Modules.isKFlat_totalTensor_of_finiteFlatTerms`,
`CategoryTheory.CochainComplex.IsKFlat.colimit`, and the sequential
total-tensor colimit results in `Modules/Tensor/ComplexColimits.lean`.

## Tags

scheme-module sheaf, flatness, bounded-above complex, K-flat complex, colimit
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory ComplexShape

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- A strictly bounded-above complex with every term flat over the identity
is K-flat for the literal scheme-module total tensor. The upper bound concerns
terms, not merely cohomology; no claim about arbitrary unbounded complexes is
made. -/
theorem isKFlat_totalTensor_of_boundedAbove_flatTerms
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (c : ℤ)
    [K.IsStrictlyLE c] (hFlat : ∀ p, IsFlatOver (𝟙 X) (K.X p)) :
    CochainComplex.IsKFlat (totalTensor X) K := by
  letI : AB5OfSize.{0,0} X.Modules := AB5OfSize_of_univLE X.Modules
  letI (L : CochainComplex X.Modules ℤ) :
      PreservesColimitsOfShape ℕ ((totalTensor X).obj L) :=
    preservesColimitsOfShape_totalTensor_obj_nat X L
  letI (L : CochainComplex X.Modules ℤ) :
      PreservesColimitsOfShape ℕ ((totalTensor X).flip.obj L) :=
    preservesColimitsOfShape_totalTensor_flip_obj_nat X L
  let T := HomologicalComplex.stupidTruncGETower K c
  have hStage : ∀ n, CochainComplex.IsKFlat (totalTensor X) (T.obj n) := by
    intro n
    let S := K.stupidTrunc (embeddingUpIntGE (c - n))
    apply isKFlat_totalTensor_of_finiteFlatTerms X S (c - n) c
    · exact fun p hp => CochainComplex.isZero_of_isStrictlyGE S (c - n) p hp
    · exact fun p hp => CochainComplex.isZero_of_isStrictlyLE S c p hp
    · intro p hp _
      let e : K.X p ≅ S.X p :=
        (HomologicalComplex.stupidTruncGEXIso K (c - n) p hp).symm
      apply (isFlatOverId_iff_stalkwiseFlat X (S.X p)).2
      intro x
      have h := ((isFlatOverId_iff_stalkwiseFlat X (K.X p)).1 (hFlat p)) x
      letI : Module.Flat (X.presheaf.stalk x)
          ((moduleStalkFunctor X x).obj (K.X p)) := h
      exact Module.Flat.of_linearEquiv
        ((moduleStalkFunctor X x).mapIso e).symm.toLinearEquiv
  have hCol := CochainComplex.IsKFlat.colimit T hStage
  let e : K ≅ colimit T := IsColimit.coconePointUniqueUpToIso
    (HomologicalComplex.isColimitStupidTruncGETowerCocone K c) (colimit.isColimit T)
  constructor
  · exact (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight ((totalTensor X).mapIso e) DerivedCategory.Q)).mpr hCol.1
  · exact (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight ((totalTensor X).flip.mapIso e) DerivedCategory.Q)).mpr hCol.2

end

end AlgebraicGeometry.Scheme.Modules
