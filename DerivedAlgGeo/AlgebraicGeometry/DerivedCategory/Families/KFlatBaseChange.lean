/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.KFlatTensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeCategory

/-!
# Base-change categories from K-flat derived tensor

This file specializes the generic external-product construction in `BaseChangeCategory.lean` to
the actual derived tensor obtained from a K-flat resolution of complexes of module sheaves on the
fibre product. Its parameters are geometric evidence about that construction—preservation of
quasicoherent cohomology and compact objects—rather than an arbitrary bifunctor on `Dqc`.

The resulting aliases are the K-flat forms of the paper's `(Dqc)_T` and `D_T`. Constructing the
resolution and proving quasicoherence and compactness for its resolved complex-level tensors
remains explicit in their signatures; the corresponding facts for arbitrary derived objects are
then theorems.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} (X T : SchemeBaseChange S)

/-- The base-change external product formed with the derived tensor constructed from a K-flat
resolution of complexes of module sheaves on `X_T`. -/
noncomputable def kFlatBaseChangeExternalProduct
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  baseChangeExternalProduct X T P pullX pullT
    (R.derivedTensorToDqc (R.preservesQuasicoherentCohomology_of_resolvedTensor hR))

/-- After forgetting quasicoherence witnesses, the K-flat external product is the ambient K-flat
derived tensor of the two derived pullbacks. -/
@[simp]
theorem kFlatBaseChangeExternalProduct_obj_obj_obj
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    (((kFlatBaseChangeExternalProduct X T P pullX pullT R hR).obj F).obj G).obj =
      ((R.derivedTensor.obj (pullX.functor.obj F.obj).obj).obj
        (pullT.functor.obj G.obj).obj) :=
  rfl

/-- K-flat external products of compact factors are compact when the two pullbacks and the
restricted K-flat tensor preserve compact objects. -/
theorem kFlatBaseChangeExternalProduct_obj_isCompact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology)
    (hpullX : pullX.PreservesCompactObjects)
    (hpullT : pullT.PreservesCompactObjects)
    (htensor : R.ResolvedTensorPreservesCompactObjects hR)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    IsCompactObject.{u}
      (((kFlatBaseChangeExternalProduct X T P pullX pullT R hR).obj F).obj G) :=
  baseChangeExternalProduct_obj_isCompact X T P pullX pullT
    (R.derivedTensorToDqc (R.preservesQuasicoherentCohomology_of_resolvedTensor hR))
    hpullX hpullT (R.preservesCompactObjects_of_resolvedTensor hR htensor) F G

/-- The external-product generators obtained from K-flat derived tensor. -/
def kFlatPerfectBaseChangeGenerators
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  perfectBaseChangeGenerators X T P
    (kFlatBaseChangeExternalProduct X T P pullX pullT R hR)

/-- The perfect base-change envelope generated using K-flat derived tensor. -/
def kFlatPerfectBaseChangeEnvelope
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  perfectBaseChangeEnvelope X T P
    (kFlatBaseChangeExternalProduct X T P pullX pullT R hR)

/-- The full perfect base-change envelope constructed from K-flat derived tensor. -/
abbrev KFlatPerfectBaseChangeEnvelopeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :=
  (kFlatPerfectBaseChangeEnvelope X T P pullX pullT R hR).FullSubcategory

/-- The quasicoherent base-change component `(Dqc)_T` constructed from K-flat derived tensor. -/
def kFlatQuasicoherentBaseChangeComponent
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  quasicoherentBaseChangeComponent X T P
    (kFlatBaseChangeExternalProduct X T P pullX pullT R hR)

/-- The full K-flat quasicoherent base-change category `(Dqc)_T`. -/
abbrev KFlatQuasicoherentBaseChangeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :=
  (kFlatQuasicoherentBaseChangeComponent X T P pullX pullT R hR).FullSubcategory

/-- The bounded base-change component `D_T` constructed from K-flat derived tensor. -/
def kFlatBoundedBaseChangeComponent
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :
    ObjectProperty (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :=
  boundedBaseChangeComponent X T P
    (kFlatBaseChangeExternalProduct X T P pullX pullT R hR)

/-- The full K-flat bounded base-change category `D_T`. -/
abbrev KFlatBoundedBaseChangeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology) :=
  (kFlatBoundedBaseChangeComponent X T P pullX pullT R hR).FullSubcategory

/-- The whole perfect envelope built from K-flat tensor lies in the compact objects when the
geometric operations preserve compactness. -/
theorem kFlatPerfectBaseChangeEnvelope_le_compact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (R : SchemeKFlatResolution (X ⨯ T).left)
    (hR : R.ResolvedTensorPreservesQuasicoherentCohomology)
    (hpullX : pullX.PreservesCompactObjects)
    (hpullT : pullT.PreservesCompactObjects)
    (htensor : R.ResolvedTensorPreservesCompactObjects hR) :
    kFlatPerfectBaseChangeEnvelope X T P pullX pullT R hR ≤
      ObjectProperty.compactObjects.{u} :=
  perfectBaseChangeEnvelope_externalProduct_le_compact X T P pullX pullT
    (R.derivedTensorToDqc (R.preservesQuasicoherentCohomology_of_resolvedTensor hR))
    hpullX hpullT (R.preservesCompactObjects_of_resolvedTensor hR htensor)

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
