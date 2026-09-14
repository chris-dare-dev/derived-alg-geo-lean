/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KFlatResolution
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex

/-!
# K-flat derived tensor products on schemes

This file specializes the generic K-flat localization construction to the total tensor product of
unbounded complexes of `𝒪_X`-modules. A `SchemeKFlatResolution X` is therefore concrete data for
the actual sheafified tensor bifunctor, rather than an arbitrary derived-category operation.

Constructing these resolutions, proving that the result preserves quasicoherent cohomology, and
then restricting it to `Dqc X` are the remaining geometric steps.
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- A functorial K-flat resolution for the total tensor product of complexes of
`𝒪_X`-modules. -/
abbrev SchemeKFlatResolution (X : Scheme.{u}) :=
  KFlatResolution X.Modules (Scheme.Modules.totalTensor X)

namespace SchemeKFlatResolution

variable {X : Scheme.{u}}

/-- The honest unbounded derived tensor bifunctor supplied by a K-flat resolution. -/
def derivedTensor (R : SchemeKFlatResolution X) :
    SchemeDerivedCategory X ⥤ SchemeDerivedCategory X ⥤ SchemeDerivedCategory X :=
  CategoryTheory.KFlatResolution.derivedTensor R

/-- On localized complexes, the scheme derived tensor is represented by total tensor after K-flat
replacement in both variables. -/
def derivedTensorFactors (R : SchemeKFlatResolution X) :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
          R.derivedTensor ≅
      CategoryTheory.KFlatResolution.resolvedTensor R :=
  CategoryTheory.KFlatResolution.derivedTensorFactors R

end SchemeKFlatResolution

end

end AlgebraicGeometry.DerivedCategory
