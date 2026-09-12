/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Bifunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.KFlatTensor

/-!
# K-flat derived tensor on `Dqc`

A scheme K-flat resolution already constructs an honest derived tensor on the ambient derived
category of all module sheaves. This file isolates the remaining geometric preservation statement
and, from that evidence, restricts the bifunctor to the full subcategory with quasicoherent
cohomology.

No unrelated tensor operation can inhabit this interface: the restricted bifunctor is built by
`ObjectProperty.lift₂` from `SchemeKFlatResolution.derivedTensor`, and forgetting the property
witnesses recovers that ambient bifunctor definitionally.
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SchemeKFlatResolution

variable {X : Scheme.{u}}

/-- The geometric condition needed for a K-flat derived tensor to restrict to `Dqc(X)`. -/
def PreservesQuasicoherentCohomology (R : SchemeKFlatResolution X) : Prop :=
  ∀ E F : SchemeDerivedCategory X,
    Dqc.schemeQuasicoherentCohomology X E →
      Dqc.schemeQuasicoherentCohomology X F →
        Dqc.schemeQuasicoherentCohomology X
          (((R.derivedTensor.obj E).obj F))

/-- Restrict the K-flat derived tensor to the honest quasicoherent-cohomology locus. -/
def derivedTensorToDqc (R : SchemeKFlatResolution X)
    (hR : R.PreservesQuasicoherentCohomology) :
    Dqc.SchemeQuasicoherentDerivedCategory X ⥤
      Dqc.SchemeQuasicoherentDerivedCategory X ⥤
        Dqc.SchemeQuasicoherentDerivedCategory X :=
  (Dqc.schemeQuasicoherentCohomology X).lift₂ R.derivedTensor hR

@[simp]
theorem derivedTensorToDqc_obj_obj_obj (R : SchemeKFlatResolution X)
    (hR : R.PreservesQuasicoherentCohomology)
    (E F : Dqc.SchemeQuasicoherentDerivedCategory X) :
    (((R.derivedTensorToDqc hR).obj E).obj F).obj =
      ((R.derivedTensor.obj E.obj).obj F.obj) :=
  rfl

/-- The compactness condition needed in base-change constructions: the restricted K-flat tensor
of two compact `Dqc(X)` objects is compact. -/
def PreservesCompactObjects (R : SchemeKFlatResolution X)
    (hR : R.PreservesQuasicoherentCohomology) : Prop :=
  ∀ E F : Dqc.SchemeQuasicoherentDerivedCategory X,
    IsCompactObject.{u} E → IsCompactObject.{u} F →
      IsCompactObject.{u} (((R.derivedTensorToDqc hR).obj E).obj F)

/-- Forgetting the `Dqc` witnesses recovers the ambient K-flat derived tensor restricted along the
two inclusions. -/
def derivedTensorToDqcCompInclusion (R : SchemeKFlatResolution X)
    (hR : R.PreservesQuasicoherentCohomology) :
    R.derivedTensorToDqc hR ⋙
        (Functor.whiskeringRight _ _ _).obj
          (Dqc.SchemeQuasicoherentDerivedCategory.ι X) ≅
      Dqc.SchemeQuasicoherentDerivedCategory.ι X ⋙ R.derivedTensor ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Dqc.SchemeQuasicoherentDerivedCategory.ι X) :=
  (Dqc.schemeQuasicoherentCohomology X).lift₂CompιIso R.derivedTensor hR

end SchemeKFlatResolution

end

end AlgebraicGeometry.DerivedCategory
