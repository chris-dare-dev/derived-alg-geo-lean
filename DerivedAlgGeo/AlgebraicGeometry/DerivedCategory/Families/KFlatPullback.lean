/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.KFlatTensor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeCategory
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpenImmersionPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.PullbackAcyclicResolution
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.KFlatQuasiIso

/-!
# Derived pullback from K-flat resolutions

A K-flat resolution on the source of pullback already supplies the functorial replacement,
comparison, and quasi-isomorphism required by
`AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.PullbackAcyclicResolution`.
This file isolates the two remaining operational facts about pullback of those
replacements and constructs the genuine left-derived pullback universal property
from them.

Quasicoherence and compactness are reduced to the resolved complex-level pullback. Thus the
base-change construction no longer needs independently supplied functors on derived categories:
all categorical structure descends from one K-flat replacement and explicit geometric evidence.

## Main definitions

* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.KFlatPullbackAcyclic`
  records the two pullback-acyclicity fields.
* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.arbitraryLeftDerivedPullback`
  uses the canonical free-Yoneda resolution.

## Main results

* `AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.kFlatPullbackAcyclic`
  proves both fields for any K-flat resolution and morphism.
* The right-tensor comparison identifies canonical derived pullback with
  ordinary pullback on a supplied tensor-acyclic complex. Its K-flat
  specialization supplies the inversion premise.

## Implementation notes

The caller-free constructor applies the existing left-derived universal-property
construction to the canonical resolution and the acyclicity theorem.

## References

The resolution and derived functor constructions are in the repository's
`DerivedCategory/Tensor/FreeYonedaKFlat.lean` and
`DerivedCategory/Families/PullbackAcyclicResolution.lean` modules.

## Tags

scheme pullback, derived category, K-flat resolution
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {T U : SchemeBaseChange S}

/-- Resolve a complex by a K-flat replacement on `U`, pull it back to `T`, and localize. -/
def kFlatResolvedPullback (R : SchemeKFlatResolution U.left) (f : T ⟶ U) :
    CochainComplex U.left.Modules ℤ ⥤ T.DerivedFiber :=
  R.resolution ⋙ complexPullback f ⋙ SchemeDerivedCategory.Q T.left

/-- The exact geometric conditions under which a K-flat replacement is acyclic for pullback.

The first field lets resolved pullback descend through source localization. The second says that
the comparison is invertible after pulling back an already resolved complex; this is the
idempotence input used by the left-derived universal property. -/
structure KFlatPullbackAcyclic (R : SchemeKFlatResolution U.left) (f : T ⟶ U) : Prop where
  pullback_inverts :
    (HomologicalComplex.quasiIso U.left.Modules
      (ComplexShape.up ℤ)).IsInvertedBy (kFlatResolvedPullback R f)
  resolved_comparison_isIso (K : CochainComplex U.left.Modules ℤ) :
    IsIso ((complexPullback f ⋙ SchemeDerivedCategory.Q T.left).map
      (R.comparison.app (R.resolution.obj K)))

/-- Along an exact pullback, every K-flat replacement is automatically pullback-acyclic. Exactness
preserves the quasi-isomorphisms produced by the replacement, including its comparison on an
already resolved complex. -/
theorem kFlatPullbackAcyclic_ofExact (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    [IsExactPullback f] : KFlatPullbackAcyclic R f where
  pullback_inverts := by
    intro K L g hg
    change IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.resolution.map g)))
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    have hRg := R.map_quasiIso g hg
    change HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)
      (R.resolution.map g) at hRg
    rw [HomologicalComplex.mem_quasiIso_iff] at hRg ⊢
    letI := hRg
    infer_instance
  resolved_comparison_isIso K := by
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    rw [HomologicalComplex.mem_quasiIso_iff]
    have hcomparison := R.comparison_quasiIso (R.resolution.obj K)
    rw [HomologicalComplex.mem_quasiIso_iff] at hcomparison
    letI := hcomparison
    infer_instance

/-- Flat scheme pullback is an unconditional geometric case of K-flat pullback acyclicity. -/
theorem kFlatPullbackAcyclic_ofFlat (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    [Flat f.left] : KFlatPullbackAcyclic R f :=
  kFlatPullbackAcyclic_ofExact R f

/-- Every K-flat resolution is acyclic for pullback along an arbitrary scheme
morphism. Both fields follow by applying pullback preservation to
quasi-isomorphisms between resolved complexes; for the second field these are
the once- and twice-resolved complexes. -/
theorem kFlatPullbackAcyclic (R : SchemeKFlatResolution U.left) (f : T ⟶ U) :
    KFlatPullbackAcyclic R f where
  pullback_inverts := by
    intro K L g hg
    change IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.resolution.map g)))
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    exact Scheme.Modules.quasiIso_pullback_of_isKFlat f.left (R.resolution.map g)
      (R.map_quasiIso g hg) (R.isKFlat K) (R.isKFlat L)
  resolved_comparison_isIso K := by
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    exact Scheme.Modules.quasiIso_pullback_of_isKFlat f.left
      (R.comparison.app (R.resolution.obj K))
      (R.comparison_quasiIso (R.resolution.obj K))
      (R.isKFlat (R.resolution.obj K)) (R.isKFlat K)

/-- A K-flat resolution satisfying the pullback-acyclicity conditions constructs the existing
functorial pullback-acyclic resolution interface. -/
def kFlatPullbackAcyclicResolution (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hR : KFlatPullbackAcyclic R f) : PullbackAcyclicResolution f where
  resolution := R.resolution
  comparison := R.comparison
  comparison_quasiIso := R.comparison_quasiIso
  pullback_inverts := hR.pullback_inverts
  resolved_comparison_isIso := hR.resolved_comparison_isIso

/-- The genuine left-derived pullback constructed from a pullback-acyclic K-flat replacement. -/
def kFlatLeftDerivedPullback (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hR : KFlatPullbackAcyclic R f) : LeftDerivedPullback f :=
  (kFlatPullbackAcyclicResolution R f hR).toLeftDerivedPullback

/-- The left-derived pullback for any morphism in `Over S`, constructed using
the canonical free-Yoneda K-flat resolution and its proved pullback acyclicity.
No preservation assertion or resolution is supplied by the caller. -/
def arbitraryLeftDerivedPullback (f : T ⟶ U) : LeftDerivedPullback f :=
  kFlatLeftDerivedPullback (freeYonedaSchemeKFlatResolution U.left) f
    (kFlatPullbackAcyclic _ f)

/-- On an input whose right tensor functor inverts quasi-isomorphisms, ordinary
pullback computes the canonical arbitrary left-derived pullback. The comparison
uses the canonical free-Yoneda resolution but does not require its terms to be
quasi-coherent. -/
def derivedPullbackObjIsoOfTensorRightInverts (f : T ⟶ U)
    (K : CochainComplex U.left.Modules ℤ)
    (hRight :
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ)).IsInvertedBy
        ((Scheme.Modules.totalTensor U.left).flip.obj K ⋙ DerivedCategory.Q)) :
    (arbitraryLeftDerivedPullback f).functor.obj
      ((SchemeDerivedCategory.Q U.left).obj K) ≅
      (SchemeDerivedCategory.Q T.left).obj ((complexPullback f).obj K) := by
  let R := freeYonedaSchemeKFlatResolution U.left
  let hR := kFlatPullbackAcyclic R f
  have hcomp : IsIso ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.comparison.app K))) := by
    apply Localization.inverts (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    exact Scheme.Modules.quasiIso_pullback_of_tensorRight_inverts f.left
      (R.comparison.app K) (R.comparison_quasiIso K) (R.isKFlat K).2 hRight
  exact (kFlatPullbackAcyclicResolution R f hR).derivedFactors.app K ≪≫
    @asIso _ _ _ _ ((SchemeDerivedCategory.Q T.left).map
      ((complexPullback f).map (R.comparison.app K))) hcomp

/-- Ambient K-flatness supplies the right-tensor inversion premise for the
objectwise comparison with ordinary pullback. -/
def derivedPullbackObjIsoOfKFlat (f : T ⟶ U)
    (K : CochainComplex U.left.Modules ℤ)
    (hK : CochainComplex.IsKFlat (Scheme.Modules.totalTensor U.left) K) :
    (arbitraryLeftDerivedPullback f).functor.obj
      ((SchemeDerivedCategory.Q U.left).obj K) ≅
      (SchemeDerivedCategory.Q T.left).obj ((complexPullback f).obj K) :=
  derivedPullbackObjIsoOfTensorRightInverts f K hK.2

/-- For exact pullback, the K-flat construction agrees canonically with the existing exact
derived pullback. -/
def kFlatExactPullbackComparison (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    [IsExactPullback f] :
    (kFlatLeftDerivedPullback R f (kFlatPullbackAcyclic_ofExact R f)).functor ≅
      derivedPullback f :=
  (kFlatLeftDerivedPullback R f
    (kFlatPullbackAcyclic_ofExact R f)).exactComparison

/-- The exact comparison specialized to a flat scheme morphism. -/
def kFlatFlatPullbackComparison (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    [Flat f.left] :
    (kFlatLeftDerivedPullback R f (kFlatPullbackAcyclic_ofFlat R f)).functor ≅
      derivedPullback f :=
  kFlatExactPullbackComparison R f

/-- Quasicoherence preservation stated only on resolved complex representatives. -/
def KFlatResolvedPullbackPreservesQuasicoherentCohomology
    (R : SchemeKFlatResolution U.left) (f : T ⟶ U) : Prop :=
  ∀ K : CochainComplex U.left.Modules ℤ,
    Dqc.schemeQuasicoherentCohomology U.left ((SchemeDerivedCategory.Q U.left).obj K) →
      Dqc.schemeQuasicoherentCohomology T.left ((kFlatResolvedPullback R f).obj K)

/-- Quasicoherence preservation for K-flat derived pullback follows from the resolved
complex-level claim. -/
theorem kFlatLeftDerivedPullback_preservesQuasicoherentCohomology
    (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hR : KFlatPullbackAcyclic R f)
    (hqc : KFlatResolvedPullbackPreservesQuasicoherentCohomology R f) :
    ∀ E : U.DerivedFiber,
      Dqc.schemeQuasicoherentCohomology U.left E →
        Dqc.schemeQuasicoherentCohomology T.left
          ((kFlatLeftDerivedPullback R f hR).functor.obj E) := by
  intro E hE
  let K := (SchemeDerivedCategory.Q U.left).objPreimage E
  let eK : (SchemeDerivedCategory.Q U.left).obj K ≅ E :=
    (SchemeDerivedCategory.Q U.left).objObjPreimageIso E
  exact (Dqc.schemeQuasicoherentCohomology T.left).prop_of_iso
    (((kFlatPullbackAcyclicResolution R f hR).derivedFactors.app K).symm ≪≫
      (kFlatPullbackAcyclicResolution R f hR).derivedFunctor.mapIso eK)
    (hqc K ((Dqc.schemeQuasicoherentCohomology U.left).prop_of_iso eK.symm hE))

/-- A pullback-acyclic K-flat replacement whose resolved pullback preserves quasicoherence
constructs the actual `Dqc` left-derived pullback used by base change. -/
def kFlatDqcLeftDerivedPullback (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hR : KFlatPullbackAcyclic R f)
    (hqc : KFlatResolvedPullbackPreservesQuasicoherentCohomology R f) :
    DqcLeftDerivedPullback f where
  ambient := kFlatLeftDerivedPullback R f hR
  mapsQuasicoherent E :=
    kFlatLeftDerivedPullback_preservesQuasicoherentCohomology R f hR hqc E.obj E.property

/-- Compactness preservation stated only for resolved representatives of compact `Dqc(U)`
objects. -/
def KFlatResolvedPullbackPreservesCompactObjects
    (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hqc : KFlatResolvedPullbackPreservesQuasicoherentCohomology R f) : Prop :=
  ∀ (K : CochainComplex U.left.Modules ℤ)
    (hK : Dqc.schemeQuasicoherentCohomology U.left
      ((SchemeDerivedCategory.Q U.left).obj K)),
    IsCompactObject.{u}
        (⟨(SchemeDerivedCategory.Q U.left).obj K, hK⟩ :
          Dqc.SchemeQuasicoherentDerivedCategory U.left) →
      IsCompactObject.{u}
        (⟨(kFlatResolvedPullback R f).obj K, hqc K hK⟩ :
          Dqc.SchemeQuasicoherentDerivedCategory T.left)

/-- Compactness preservation for the constructed `Dqc` left-derived pullback follows from its
resolved representative-level form. -/
theorem kFlatDqcLeftDerivedPullback_preservesCompactObjects
    (R : SchemeKFlatResolution U.left) (f : T ⟶ U)
    (hR : KFlatPullbackAcyclic R f)
    (hqc : KFlatResolvedPullbackPreservesQuasicoherentCohomology R f)
    (hcompact : KFlatResolvedPullbackPreservesCompactObjects R f hqc) :
    (kFlatDqcLeftDerivedPullback R f hR hqc).PreservesCompactObjects := by
  intro E hE
  let K := (SchemeDerivedCategory.Q U.left).objPreimage E.obj
  let eK : (SchemeDerivedCategory.Q U.left).obj K ≅ E.obj :=
    (SchemeDerivedCategory.Q U.left).objObjPreimageIso E.obj
  have hK : Dqc.schemeQuasicoherentCohomology U.left
      ((SchemeDerivedCategory.Q U.left).obj K) :=
    (Dqc.schemeQuasicoherentCohomology U.left).prop_of_iso eK.symm E.property
  let EK : Dqc.SchemeQuasicoherentDerivedCategory U.left := ⟨_, hK⟩
  have hEK : IsCompactObject.{u} EK :=
    ObjectProperty.isCompactObject_of_iso
      ((Dqc.schemeQuasicoherentCohomology U.left).isoMk eK).symm hE
  let resolved : Dqc.SchemeQuasicoherentDerivedCategory T.left :=
    ⟨(kFlatResolvedPullback R f).obj K, hqc K hK⟩
  have hresolved : IsCompactObject.{u} resolved := hcompact K hK hEK
  exact ObjectProperty.isCompactObject_of_iso
    ((Dqc.schemeQuasicoherentCohomology T.left).isoMk
      (((kFlatPullbackAcyclicResolution R f hR).derivedFactors.app K).symm ≪≫
        (kFlatPullbackAcyclicResolution R f hR).derivedFunctor.mapIso eK)) hresolved

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
