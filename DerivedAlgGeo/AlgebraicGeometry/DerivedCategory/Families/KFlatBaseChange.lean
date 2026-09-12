/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.KFlatTensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeCategory
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback

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

/-- The K-flat resolutions and resolved representative-level facts needed to construct all three
operations in the base-change external product. In particular, the two derived pullbacks are not
supplied as independent functors: they are constructed from `fstResolution` and `sndResolution`. -/
structure KFlatBaseChangeData where
  /-- A K-flat replacement on `X`, used to derive pullback along `X_T ⟶ X`. -/
  fstResolution : SchemeKFlatResolution X.left
  /-- Pullback along `X_T ⟶ X` is acyclic on the chosen replacements. -/
  fstAcyclic : KFlatPullbackAcyclic fstResolution (baseChangeFst X T)
  /-- Resolved pullback along `X_T ⟶ X` preserves quasicoherent cohomology. -/
  fstQuasicoherent :
    KFlatResolvedPullbackPreservesQuasicoherentCohomology fstResolution (baseChangeFst X T)
  /-- A K-flat replacement on `T`, used to derive pullback along `X_T ⟶ T`. -/
  sndResolution : SchemeKFlatResolution T.left
  /-- Pullback along `X_T ⟶ T` is acyclic on the chosen replacements. -/
  sndAcyclic : KFlatPullbackAcyclic sndResolution (baseChangeSnd X T)
  /-- Resolved pullback along `X_T ⟶ T` preserves quasicoherent cohomology. -/
  sndQuasicoherent :
    KFlatResolvedPullbackPreservesQuasicoherentCohomology sndResolution (baseChangeSnd X T)
  /-- A K-flat replacement on the fibre product, used to derive tensor there. -/
  tensorResolution : SchemeKFlatResolution (X ⨯ T).left
  /-- Resolved tensor on the fibre product preserves quasicoherent cohomology. -/
  tensorQuasicoherent : tensorResolution.ResolvedTensorPreservesQuasicoherentCohomology

namespace KFlatBaseChangeData

variable {X T : SchemeBaseChange S}

/-- The `Dqc` pullback along `X_T ⟶ X` constructed from the first K-flat resolution. -/
def pullFst (D : KFlatBaseChangeData X T) :
    DqcLeftDerivedPullback (baseChangeFst X T) :=
  kFlatDqcLeftDerivedPullback D.fstResolution (baseChangeFst X T)
    D.fstAcyclic D.fstQuasicoherent

/-- The `Dqc` pullback along `X_T ⟶ T` constructed from the second K-flat resolution. -/
def pullSnd (D : KFlatBaseChangeData X T) :
    DqcLeftDerivedPullback (baseChangeSnd X T) :=
  kFlatDqcLeftDerivedPullback D.sndResolution (baseChangeSnd X T)
    D.sndAcyclic D.sndQuasicoherent

/-- The base-change external product with both pullbacks and tensor constructed from the bundled
K-flat resolutions. -/
noncomputable def externalProduct (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  kFlatBaseChangeExternalProduct X T P D.pullFst D.pullSnd
    D.tensorResolution D.tensorQuasicoherent

/-- The perfect base-change envelope obtained entirely from the bundled K-flat resolutions. -/
def perfectEnvelope (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  perfectBaseChangeEnvelope X T P (D.externalProduct P)

/-- The quasicoherent base-change component `(Dqc)_T` obtained entirely from the bundled K-flat
resolutions. -/
def quasicoherentComponent (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  quasicoherentBaseChangeComponent X T P (D.externalProduct P)

/-- The full quasicoherent base-change category `(Dqc)_T` constructed from the bundled K-flat
resolutions. -/
abbrev QuasicoherentCategory (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :=
  (D.quasicoherentComponent P).FullSubcategory

/-- The bounded base-change component `D_T` obtained entirely from the bundled K-flat
resolutions. -/
def boundedComponent (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :=
  boundedBaseChangeComponent X T P (D.externalProduct P)

/-- The full bounded base-change category `D_T` constructed from the bundled K-flat
resolutions. -/
abbrev BoundedCategory (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :=
  (D.boundedComponent P).FullSubcategory

/-- Representative-level compactness conditions for the three K-flat operations bundled in
`KFlatBaseChangeData`. -/
structure PreservesCompactObjects (D : KFlatBaseChangeData X T) : Prop where
  fst : KFlatResolvedPullbackPreservesCompactObjects
    D.fstResolution (baseChangeFst X T) D.fstQuasicoherent
  snd : KFlatResolvedPullbackPreservesCompactObjects
    D.sndResolution (baseChangeSnd X T) D.sndQuasicoherent
  tensor : D.tensorResolution.ResolvedTensorPreservesCompactObjects D.tensorQuasicoherent

/-- Under representative-level compactness for the three resolutions, every external-product
generator produced by the fully K-flat construction is compact. -/
theorem externalProduct_obj_isCompact (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (hD : D.PreservesCompactObjects)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    IsCompactObject.{u} (((D.externalProduct P).obj F).obj G) :=
  kFlatBaseChangeExternalProduct_obj_isCompact X T P D.pullFst D.pullSnd
    D.tensorResolution D.tensorQuasicoherent
    (kFlatDqcLeftDerivedPullback_preservesCompactObjects D.fstResolution
      (baseChangeFst X T) D.fstAcyclic D.fstQuasicoherent hD.fst)
    (kFlatDqcLeftDerivedPullback_preservesCompactObjects D.sndResolution
      (baseChangeSnd X T) D.sndAcyclic D.sndQuasicoherent hD.snd)
    hD.tensor F G

/-- Under representative-level compactness for the three resolutions, the whole fully K-flat
perfect envelope consists of compact objects. -/
theorem perfectEnvelope_le_compact (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (hD : D.PreservesCompactObjects) :
    D.perfectEnvelope P ≤ ObjectProperty.compactObjects.{u} :=
  kFlatPerfectBaseChangeEnvelope_le_compact X T P D.pullFst D.pullSnd
    D.tensorResolution D.tensorQuasicoherent
    (kFlatDqcLeftDerivedPullback_preservesCompactObjects D.fstResolution
      (baseChangeFst X T) D.fstAcyclic D.fstQuasicoherent hD.fst)
    (kFlatDqcLeftDerivedPullback_preservesCompactObjects D.sndResolution
      (baseChangeSnd X T) D.sndAcyclic D.sndQuasicoherent hD.snd)
    hD.tensor

end KFlatBaseChangeData

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
