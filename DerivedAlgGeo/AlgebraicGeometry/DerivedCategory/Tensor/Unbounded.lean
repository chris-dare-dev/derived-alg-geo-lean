/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KFlatResolution
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex

/-!
# The unbounded derived tensor product on schemes

This file specializes the generic K-flat localization construction to the total tensor product of
unbounded complexes of `𝒪_X`-modules. A `SchemeKFlatResolution X` is therefore concrete data for
the actual sheafified tensor bifunctor, rather than an arbitrary derived-category operation.

Constructing these resolutions, proving that the result preserves quasicoherent cohomology, and
then restricting it to `Dqc X` are the remaining geometric steps.

## Which tensor product this is

This is the **unbounded** tier of the `Tensor/` owner, and it is the only tier that
constructs anything: the bifunctor here is built from a supplied K-flat resolution on
complexes of module sheaves. The other two tiers are contracts rather than constructions.

* `Tensor/BoundedCoherent.lean` supplies a derived tensor on the bounded coherent derived
  category as a named capability. It is not obtained from this file by restriction, and
  must not be read as one: the bounded coherent derived category of a singular scheme is
  not closed under arbitrary derived tensor, so no such restriction map exists in that
  generality.
* `Tensor/Coherent.lean` adds monoidal coherence to that capability, and
  `Tensor/Relative.lean` carries the relative tier -- compatibility of a coherent tensor
  with derived pullback along a morphism of scheme base changes.

MO1.10 (#1321) moved this file from `DerivedCategory/KFlatTensor.lean` so that the three
tiers sit under one owner; the declaration names are unchanged. The `Dqc`-level K-flat
tensor stays with its own owner at `DerivedCategory/Dqc/KFlatTensor.lean`.
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
