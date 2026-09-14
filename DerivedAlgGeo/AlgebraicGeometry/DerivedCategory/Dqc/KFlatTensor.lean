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

/-- A representative-level criterion for quasicoherence preservation. It asks only about the
actual total tensor of the functorial K-flat replacements of two complexes. -/
def ResolvedTensorPreservesQuasicoherentCohomology (R : SchemeKFlatResolution X) : Prop :=
  ∀ K L : CochainComplex X.Modules ℤ,
    Dqc.schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj K) →
      Dqc.schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj L) →
        Dqc.schemeQuasicoherentCohomology X
          (((CategoryTheory.KFlatResolution.resolvedTensor R).obj K).obj L)

/-- Quasicoherence preservation for the derived tensor follows from the corresponding claim on
resolved complex representatives. Essential surjectivity of derived localization supplies the
representatives, and `derivedTensorFactors` identifies their derived tensor with resolved total
tensor. -/
theorem preservesQuasicoherentCohomology_of_resolvedTensor
    (R : SchemeKFlatResolution X)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    R.PreservesQuasicoherentCohomology :=
  (Dqc.schemeQuasicoherentCohomology X).maps₂_of_comp_of_essSurj
    (SchemeDerivedCategory.Q X) R.derivedTensor
    (CategoryTheory.KFlatResolution.resolvedTensor R) R.derivedTensorFactors hR

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

/-- A representative-level compactness criterion. The quasicoherence hypothesis gives the
resolved total tensor an object of `Dqc(X)`; compactness then only has to be checked on such
objects coming directly from complexes. -/
def ResolvedTensorPreservesCompactObjects (R : SchemeKFlatResolution X)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) : Prop :=
  ∀ (K L : CochainComplex X.Modules ℤ)
    (hK : Dqc.schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj K))
    (hL : Dqc.schemeQuasicoherentCohomology X ((SchemeDerivedCategory.Q X).obj L)),
    IsCompactObject.{u}
        (⟨(SchemeDerivedCategory.Q X).obj K, hK⟩ :
          Dqc.SchemeQuasicoherentDerivedCategory X) →
      IsCompactObject.{u}
          (⟨(SchemeDerivedCategory.Q X).obj L, hL⟩ :
            Dqc.SchemeQuasicoherentDerivedCategory X) →
        IsCompactObject.{u}
          (⟨((CategoryTheory.KFlatResolution.resolvedTensor R).obj K).obj L,
              hR K L hK hL⟩ : Dqc.SchemeQuasicoherentDerivedCategory X)

/-- Compactness preservation for the restricted derived tensor follows from the corresponding
claim on resolved complex representatives. -/
theorem preservesCompactObjects_of_resolvedTensor
    (R : SchemeKFlatResolution X)
    (hqc : R.ResolvedTensorPreservesQuasicoherentCohomology)
    (hcompact : R.ResolvedTensorPreservesCompactObjects hqc) :
    R.PreservesCompactObjects
      (R.preservesQuasicoherentCohomology_of_resolvedTensor hqc) := by
  intro E F hE hF
  let K := (SchemeDerivedCategory.Q X).objPreimage E.obj
  let L := (SchemeDerivedCategory.Q X).objPreimage F.obj
  let eK : (SchemeDerivedCategory.Q X).obj K ≅ E.obj :=
    (SchemeDerivedCategory.Q X).objObjPreimageIso E.obj
  let eL : (SchemeDerivedCategory.Q X).obj L ≅ F.obj :=
    (SchemeDerivedCategory.Q X).objObjPreimageIso F.obj
  have hK : Dqc.schemeQuasicoherentCohomology X
      ((SchemeDerivedCategory.Q X).obj K) :=
    (Dqc.schemeQuasicoherentCohomology X).prop_of_iso eK.symm E.property
  have hL : Dqc.schemeQuasicoherentCohomology X
      ((SchemeDerivedCategory.Q X).obj L) :=
    (Dqc.schemeQuasicoherentCohomology X).prop_of_iso eL.symm F.property
  let EK : Dqc.SchemeQuasicoherentDerivedCategory X := ⟨_, hK⟩
  let EL : Dqc.SchemeQuasicoherentDerivedCategory X := ⟨_, hL⟩
  have hEK : IsCompactObject.{u} EK :=
    ObjectProperty.isCompactObject_of_iso
      ((Dqc.schemeQuasicoherentCohomology X).isoMk eK).symm hE
  have hEL : IsCompactObject.{u} EL :=
    ObjectProperty.isCompactObject_of_iso
      ((Dqc.schemeQuasicoherentCohomology X).isoMk eL).symm hF
  let resolved : Dqc.SchemeQuasicoherentDerivedCategory X :=
    ⟨((CategoryTheory.KFlatResolution.resolvedTensor R).obj K).obj L,
      hqc K L hK hL⟩
  have hresolved : IsCompactObject.{u} resolved :=
    hcompact K L hK hL hEK hEL
  exact ObjectProperty.isCompactObject_of_iso
    ((Dqc.schemeQuasicoherentCohomology X).isoMk
      (((R.derivedTensorFactors.app K).app L).symm ≪≫
        (R.derivedTensor.mapIso eK).app ((SchemeDerivedCategory.Q X).obj L) ≪≫
        (R.derivedTensor.obj E.obj).mapIso eL)) hresolved

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
