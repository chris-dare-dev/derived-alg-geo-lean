/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeCategory

/-!
# Derived base-change data, independent of how it is constructed

`BaseChangeCategory.lean` builds the base-change categories of §3 of
arXiv:1902.08184 from three supplied operations: a derived pullback along each
projection off the fibre product, and a derived tensor on it. Every construction
there -- the external product, the perfect generators and their envelope, the
quasicoherent component `(Dqc)_T`, the bounded component `D_T` -- takes those
three as separate arguments.

This file bundles them. `DerivedBaseChangeData` is that bundle and nothing more:
two `DqcLeftDerivedPullback`s and an operation-level tensor bifunctor. It says
how base change is consumed, not how it was produced. In particular,
`derivedTensor` is deliberately not presented as a universal-property
construction of the unbounded derived tensor on `Dqc`; exactness, monoidal
coherence, and geometric existence must be supplied by a producer or by the
theorem using the operation. A field of this type is therefore an interface,
not a proof of the corresponding geometric fact.

**Why the bundle is the root and not the K-flat one.** K-flat resolutions are a
*model*: one way to produce these three operations, and the one
`KFlatBaseChange.lean` uses. They are not what base change is. Stating the
downstream API on the model means a second construction -- pullback along an
open immersion, which `OpenImmersionPullback.lean` already proves exact and so
needs no resolution at all; a flat base; an eventual `∞`-categorical tensor --
cannot reuse any of it. `abstraction-tree.md` names that failure directly: a
leaf must not copy the carrier or fields of its root, and until this file there
was no root for a leaf to reach.

So `KFlatBaseChangeData` keeps its resolutions and becomes a producer of this
structure rather than a rival carrier, through
`KFlatBaseChangeData.toDerivedBaseChangeData`.

Nothing here is inhabited, and nothing here is new mathematics: every
declaration is the corresponding one from `KFlatBaseChange.lean` with the model
projected away.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}}

/-- The derived operations base change is built from: a derived pullback along
each projection off the fibre product, and a derived tensor on it.

This is the model-free root. `KFlatBaseChangeData` produces one of these from
K-flat resolutions; any other construction of the same three operations
produces one too, and reaches the whole API below by doing so. -/
structure DerivedBaseChangeData (X T : SchemeBaseChange S) where
  /-- Derived pullback along `X_T ⟶ X`. -/
  pullFst : DqcLeftDerivedPullback (baseChangeFst X T)
  /-- Derived pullback along `X_T ⟶ T`. -/
  pullSnd : DqcLeftDerivedPullback (baseChangeSnd X T)
  /-- A derived tensor on the fibre product. It stays explicit because the
  repository does not yet construct the unbounded derived tensor on `Dqc`. -/
  derivedTensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
    Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left

namespace DerivedBaseChangeData

variable {X T : SchemeBaseChange S}

/-- Assemble the model-free root from exact geometric pullbacks.

This is a second producer for `DerivedBaseChangeData`: exact or flat/open
base-change morphisms can use the canonical derived pullback without choosing
K-flat resolutions.  The tensor and the two `Dqc` preservation statements
remain explicit because this file does not claim a general unbounded tensor
or a general-scheme quasi-coherence theorem. -/
noncomputable def ofExactPullbacks
    [IsExactPullback (baseChangeFst X T)]
    [IsExactPullback (baseChangeSnd X T)]
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hFst : ∀ E : Dqc.SchemeQuasicoherentDerivedCategory X.left,
      Dqc.schemeQuasicoherentCohomology (X ⨯ T).left
        ((derivedPullback (baseChangeFst X T)).obj E.obj))
    (hSnd : ∀ E : Dqc.SchemeQuasicoherentDerivedCategory T.left,
      Dqc.schemeQuasicoherentCohomology (X ⨯ T).left
        ((derivedPullback (baseChangeSnd X T)).obj E.obj)) :
    DerivedBaseChangeData X T where
  pullFst := DqcLeftDerivedPullback.ofExact hFst
  pullSnd := DqcLeftDerivedPullback.ofExact hSnd
  derivedTensor := tensor

/-- The base-change external product of the bundled operations. -/
noncomputable def externalProduct (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  baseChangeExternalProduct X T P D.pullFst D.pullSnd D.derivedTensor

/-- The external-product generators of the bundled operations. -/
def perfectGenerators (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  perfectBaseChangeGenerators X T P (D.externalProduct P)

/-- Every concrete external product belongs to the generator property. -/
theorem externalProduct_mem_perfectGenerators (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    D.perfectGenerators P (((D.externalProduct P).obj F).obj G) :=
  ⟨F, G, ⟨Iso.refl _⟩⟩

/-- The external-product generators with all their shifts and isomorphic
copies. -/
def shiftedPerfectGenerators (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  (D.perfectGenerators P).shiftClosure ℤ

/-- Every shift of a concrete external product belongs to the shifted generator
property. -/
theorem externalProduct_shift_mem_shiftedPerfectGenerators
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) (n : ℤ) :
    D.shiftedPerfectGenerators P
      ((((D.externalProduct P).obj F).obj G)⟦n⟧) :=
  ⟨((D.externalProduct P).obj F).obj G, n, Iso.refl _,
    D.externalProduct_mem_perfectGenerators P F G⟩

instance shiftedPerfectGenerators_isStableUnderShift
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    (D.shiftedPerfectGenerators P).IsStableUnderShift ℤ := by
  dsimp [shiftedPerfectGenerators]
  infer_instance

/-- The perfect base-change envelope of the bundled operations. -/
def perfectEnvelope (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  perfectBaseChangeEnvelope X T P (D.externalProduct P)

/-- The quasicoherent base-change component `(Dqc)_T`. -/
def quasicoherentComponent (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  quasicoherentBaseChangeComponent X T P (D.externalProduct P)

/-- The full quasicoherent base-change category `(Dqc)_T`. -/
abbrev QuasicoherentCategory (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :=
  (D.quasicoherentComponent P).FullSubcategory

/-- The bounded base-change component `D_T`. -/
def boundedComponent (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :=
  boundedBaseChangeComponent X T P (D.externalProduct P)

/-- The full bounded base-change category `D_T`. -/
abbrev BoundedCategory (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :=
  (D.boundedComponent P).FullSubcategory

instance perfectEnvelope_isClosedUnderIsomorphisms
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    (D.perfectEnvelope P).IsClosedUnderIsomorphisms := by
  dsimp [perfectEnvelope]
  infer_instance

instance perfectEnvelope_isTriangulated
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    [P.ContainsZero] : (D.perfectEnvelope P).IsTriangulated := by
  dsimp [perfectEnvelope]
  infer_instance

instance quasicoherentComponent_isTriangulated
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    [P.ContainsZero] : (D.quasicoherentComponent P).IsTriangulated := by
  dsimp [quasicoherentComponent]
  infer_instance

instance quasicoherentComponent_isClosedUnderIsomorphisms
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    (D.quasicoherentComponent P).IsClosedUnderIsomorphisms := by
  dsimp [quasicoherentComponent, quasicoherentBaseChangeComponent]
  infer_instance

instance boundedComponent_isClosedUnderIsomorphisms
    (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    (D.boundedComponent P).IsClosedUnderIsomorphisms where
  of_iso e hE :=
    (D.quasicoherentComponent P).prop_of_iso
      ((boundedCoherentFiberToDqc X T).mapIso e) hE

/-- The compactness obligations on the three bundled operations, stated on the
operations rather than on whatever produced them. -/
structure PreservesCompactObjects (D : DerivedBaseChangeData X T) : Prop where
  /-- Pullback along `X_T ⟶ X` preserves compact objects. -/
  fst : D.pullFst.PreservesCompactObjects
  /-- Pullback along `X_T ⟶ T` preserves compact objects. -/
  snd : D.pullSnd.PreservesCompactObjects
  /-- The derived tensor preserves compact objects. -/
  tensor : TensorPreservesCompactObjects X T D.derivedTensor

/-- Under those obligations every external-product generator is compact. -/
theorem externalProduct_obj_isCompact (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (hD : D.PreservesCompactObjects)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    IsCompactObject.{u} (((D.externalProduct P).obj F).obj G) :=
  baseChangeExternalProduct_obj_isCompact X T P D.pullFst D.pullSnd
    D.derivedTensor hD.fst hD.snd hD.tensor F G

/-- Under those obligations the whole perfect envelope consists of compact
objects. -/
theorem perfectEnvelope_le_compact (D : DerivedBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (hD : D.PreservesCompactObjects) :
    D.perfectEnvelope P ≤ ObjectProperty.compactObjects.{u} :=
  perfectBaseChangeEnvelope_externalProduct_le_compact X T P D.pullFst D.pullSnd
    D.derivedTensor hD.fst hD.snd hD.tensor

end DerivedBaseChangeData

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
