/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.LeftDerivedPullback
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated

/-!
# Base-change components of scheme-derived categories

This file starts the construction of the categories `D_T` and `(Dqc)_T` from
Section 3 of arXiv:1902.08184v4 without imposing a Noetherian hypothesis on
`T` or on the fibre product `X_T`.

If `X` and `T` are schemes over `S`, their product in `Over S` is the ordinary
fibre product `X_T`.  A source component is represented by an object property
`P` in `Dqc(X)`.  Its perfect part is the intersection with the canonical
compact-object property.  Given the geometric external-product functor on
those compact factors, the paper's construction is then expressed by the
existing object-property closure operators:

1. take the triangulated envelope of the external products in `Dqc(X_T)`;
2. take its coproduct-and-extension closure to obtain `(Dqc)_T`;
3. restrict `(Dqc)_T` to the intrinsic bounded-coherent cohomology locus to
   obtain `D_T`.

The use of compact objects is deliberate.  Under the quasi-compact affine-
diagonal hypotheses of Proposition 3.15 they are the perfect complexes, while
the repository's current `SchemePerfectDerivedCategory` is built from
`D(Coh -)` and therefore requires local Noetherianity.  Using it for `T` would
silently strengthen Theorem 3.17.  The eventual compact-equals-perfect theorem
will identify this construction with the paper's notation rather than change
its carrier.

No new category hierarchy is introduced: every category below is an
abbreviation for `ObjectProperty.FullSubcategory`.  A
`DqcLeftDerivedPullback` refines the repository's existing universal-property
object `LeftDerivedPullback` by proving that its functor preserves
quasi-coherent cohomology.  The external product is assembled from those
lifts along the two fibre-product projections and a supplied tensor
bifunctor on `Dqc(X_T)`.  The compactness layer below isolates the exact
preservation statements needed to put the resulting generators, and hence
their thick envelope, inside the compact objects of `Dqc(X_T)`.  Constructing
the unbounded derived tensor and proving those preservation statements,
constructing the source `Dqc` component from a strong semiorthogonal component
of `Dᵇ(X)`, and proving pullback/pushforward functoriality are the next layers
of Theorem 3.17.

## Main definitions

* `SchemeBaseChange.CompactDqcFiber`: compact objects of `Dqc` on a base
  change;
* `SchemeBaseChange.DqcLeftDerivedPullback`: an actual left-derived pullback
  which preserves the `Dqc` locus;
* `SchemeBaseChange.baseChangeExternalProduct`: the functor
  `(F, G) ↦ Lφ'^*F ⊗ Lg'^*G`;
* `SchemeBaseChange.DqcLeftDerivedPullback.PreservesCompactObjects` and
  `SchemeBaseChange.TensorPreservesCompactObjects`: the exact compactness
  obligations on the supplied geometric operations;
* `SchemeBaseChange.sourcePerfectPart`: the compact part of a source
  component;
* `SchemeBaseChange.perfectBaseChangeGenerators` and
  `perfectBaseChangeEnvelope`: the external-product construction;
* `SchemeBaseChange.quasicoherentBaseChangeComponent` and
  `QuasicoherentBaseChangeCategory`: `(Dqc)_T`;
* `SchemeBaseChange.boundedBaseChangeComponent` and
  `BoundedBaseChangeCategory`: `D_T`.

## Reference

* arXiv:1902.08184v4, Proposition 3.15, Theorem 3.17, and Lemma 3.18.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- An actual left-derived pullback whose ambient functor preserves
quasi-coherent cohomology.

The `ambient` field is the existing universal-property object, so this
structure cannot be inhabited by merely choosing an unrelated functor between
the two `Dqc` categories.  The additional field is exactly what is needed to
lift that functor to the quasi-coherent-cohomology loci. -/
structure DqcLeftDerivedPullback {T U : SchemeBaseChange S} (f : T ⟶ U) where
  /-- The left-derived pullback on the ambient derived categories of module
  sheaves. -/
  ambient : LeftDerivedPullback f
  /-- The ambient left-derived pullback preserves quasi-coherent cohomology. -/
  mapsQuasicoherent (E : Dqc.SchemeQuasicoherentDerivedCategory U.left) :
    Dqc.schemeQuasicoherentCohomology T.left
      (ambient.functor.obj E.obj)

namespace DqcLeftDerivedPullback

variable {T U : SchemeBaseChange S} {f : T ⟶ U}

/-- The lift of an actual left-derived pullback to the honest `Dqc` loci. -/
noncomputable def functor (P : DqcLeftDerivedPullback f) :
    Dqc.SchemeQuasicoherentDerivedCategory U.left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory T.left :=
  (Dqc.schemeQuasicoherentCohomology T.left).lift
    (Dqc.SchemeQuasicoherentDerivedCategory.ι U.left ⋙ P.ambient.functor)
    P.mapsQuasicoherent

/-- Forgetting the quasi-coherence witness recovers the ambient
left-derived pullback on the nose. -/
noncomputable def functorCompInclusion (P : DqcLeftDerivedPullback f) :
    P.functor ⋙ Dqc.SchemeQuasicoherentDerivedCategory.ι T.left ≅
      Dqc.SchemeQuasicoherentDerivedCategory.ι U.left ⋙ P.ambient.functor :=
  (Dqc.schemeQuasicoherentCohomology T.left).liftCompιIso
    (Dqc.SchemeQuasicoherentDerivedCategory.ι U.left ⋙ P.ambient.functor)
    P.mapsQuasicoherent

@[simp]
theorem functor_obj_obj (P : DqcLeftDerivedPullback f)
    (E : Dqc.SchemeQuasicoherentDerivedCategory U.left) :
    (P.functor.obj E).obj = P.ambient.functor.obj E.obj :=
  rfl

/-- The exact compactness obligation on a `Dqc` left-derived pullback.

This is kept as a property of the already constructed universal-property
object rather than as a second pullback structure.  In geometric applications
it is discharged by the perfect-pullback theorem. -/
def PreservesCompactObjects (P : DqcLeftDerivedPullback f) : Prop :=
  ∀ E : Dqc.SchemeQuasicoherentDerivedCategory U.left,
    IsCompactObject.{u} E → IsCompactObject.{u} (P.functor.obj E)

end DqcLeftDerivedPullback

/-- The compact objects of `Dqc(T)`.  Under the quasi-compact affine-diagonal
hypotheses in Section 3 these are the perfect complexes.  This formulation is
available without assuming that `T` is locally Noetherian. -/
abbrev CompactDqcFiber (T : SchemeBaseChange S) :=
  (ObjectProperty.compactObjects.{u}
    (C := Dqc.SchemeQuasicoherentDerivedCategory T.left)).FullSubcategory

/-- The perfect part of a source quasi-coherent component: its intersection
with the compact objects of `Dqc(X)`. -/
def sourcePerfectPart (X : SchemeBaseChange S)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left) :=
  P ⊓ ObjectProperty.compactObjects.{u}

/-- The full compact part of a source quasi-coherent component. -/
abbrev SourcePerfectPartCategory (X : SchemeBaseChange S)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :=
  (sourcePerfectPart X P).FullSubcategory

variable (X T : SchemeBaseChange S)

/-- The projection `φ' : X_T ⟶ X` from the fibre product in `Over S`. -/
abbrev baseChangeFst : X ⨯ T ⟶ X :=
  Limits.prod.fst

/-- The projection `g' : X_T ⟶ T` from the fibre product in `Over S`. -/
abbrev baseChangeSnd : X ⨯ T ⟶ T :=
  Limits.prod.snd

/-- Pull the compact part of the source component to `Dqc(X_T)` along
`φ' : X_T ⟶ X`. -/
noncomputable def sourcePerfectPullback
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T)) :
    SourcePerfectPartCategory X P ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left :=
  (sourcePerfectPart X P).ι ⋙ pullX.functor

/-- Pull compact objects of `Dqc(T)` to `Dqc(X_T)` along
`g' : X_T ⟶ T`. -/
noncomputable def compactFiberPullback
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T)) :
    CompactDqcFiber T ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left :=
  (ObjectProperty.compactObjects.{u}
    (C := Dqc.SchemeQuasicoherentDerivedCategory T.left)).ι ⋙ pullT.functor

/-- The geometric external-product functor
`(F, G) ↦ Lφ'^*F ⊗ Lg'^*G` used in Proposition 3.15.

The two pullbacks are actual left-derived pullbacks which preserve `Dqc`.
The tensor bifunctor remains explicit because the repository does not yet
construct the unbounded derived tensor product on `Dqc`. -/
noncomputable def baseChangeExternalProduct
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :
    SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  sourcePerfectPullback X T P pullX ⋙ tensor ⋙
    (Functor.whiskeringLeft _ _ _).obj (compactFiberPullback X T pullT)

/-- The exact compactness obligation on the supplied tensor bifunctor: the
tensor product of two compact objects is compact. -/
def TensorPreservesCompactObjects
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) : Prop :=
  ∀ E F : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left,
    IsCompactObject.{u} E → IsCompactObject.{u} F →
      IsCompactObject.{u} ((tensor.obj E).obj F)

@[simp]
theorem baseChangeExternalProduct_obj_obj
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    ((baseChangeExternalProduct X T P pullX pullT tensor).obj F).obj G =
      (tensor.obj (pullX.functor.obj F.obj)).obj
        (pullT.functor.obj G.obj) :=
  rfl

/-- Every geometric external product is compact when both derived pullbacks
preserve compact objects and tensor preserves compactness in two compact
arguments. -/
theorem baseChangeExternalProduct_obj_isCompact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hpullX : pullX.PreservesCompactObjects)
    (hpullT : pullT.PreservesCompactObjects)
    (htensor : TensorPreservesCompactObjects X T tensor)
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) :
    IsCompactObject.{u}
      (((baseChangeExternalProduct X T P pullX pullT tensor).obj F).obj G) :=
  htensor _ _ (hpullX F.obj F.property.2) (hpullT G.obj G.property)

/-- The objects `φ'^* F ⊗ g'^* G` which generate the perfect base-change
component in Proposition 3.15.  The curried functor is the geometric external
product on the compact part of the source component and the compact objects
of `Dqc(T)`. -/
def perfectBaseChangeGenerators
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  fun E ↦ ∃ (F : SourcePerfectPartCategory X P),
    ∃ (G : CompactDqcFiber T), Nonempty ((externalProduct.obj F).obj G ≅ E)

/-- Membership in the generator property after assembling the external
product from the two `Dqc` pullbacks and tensor is exactly the formula in
Proposition 3.15. -/
theorem mem_perfectBaseChangeGenerators_externalProduct_iff
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (E : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :
    perfectBaseChangeGenerators X T P
        (baseChangeExternalProduct X T P pullX pullT tensor) E ↔
      ∃ (F : SourcePerfectPartCategory X P), ∃ (G : CompactDqcFiber T),
        Nonempty
          ((tensor.obj (pullX.functor.obj F.obj)).obj
            (pullT.functor.obj G.obj) ≅ E) :=
  Iff.rfl

/-- The triangulated envelope generated by the perfect external products in
`Dqc(X_T)`.  The later compactness theorem identifies this envelope with the
paper's subcategory of `Perf(X_T)`. -/
def perfectBaseChangeEnvelope
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  (perfectBaseChangeGenerators X T P externalProduct).triangEnvelope

/-- The full subcategory cut out by `perfectBaseChangeEnvelope`. -/
abbrev PerfectBaseChangeEnvelopeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :=
  (perfectBaseChangeEnvelope X T P externalProduct).FullSubcategory

/-- The quasi-coherent base-change component `(Dqc)_T`: the
coproduct-and-extension closure of the perfect base-change envelope. -/
def quasicoherentBaseChangeComponent
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :=
  (perfectBaseChangeEnvelope X T P externalProduct).coprodClosure.{u}

/-- The full quasi-coherent base-change category `(Dqc)_T`. -/
abbrev QuasicoherentBaseChangeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :=
  (quasicoherentBaseChangeComponent X T P externalProduct).FullSubcategory

/-- The intrinsic bounded-coherent locus on `X_T`, included in `Dqc(X_T)`.
Unlike `Dᵇ(Coh X_T)`, this category is defined without assuming `X_T`
locally Noetherian. -/
abbrev boundedCoherentFiberToDqc :
    Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left :=
  Dqc.SchemeBoundedCoherentDqcCategory.ι (X ⨯ T).left

/-- The bounded base-change component `D_T`, defined as the inverse image of
`(Dqc)_T` in the intrinsic bounded-coherent locus of `Dqc(X_T)`. -/
def boundedBaseChangeComponent
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    ObjectProperty (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :=
  (quasicoherentBaseChangeComponent X T P externalProduct).inverseImage
    (boundedCoherentFiberToDqc X T)

/-- The full bounded base-change category `D_T`. -/
abbrev BoundedBaseChangeCategory
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :=
  (boundedBaseChangeComponent X T P externalProduct).FullSubcategory

/-- The perfect part is contained in the source quasi-coherent component. -/
theorem sourcePerfectPart_le
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    sourcePerfectPart X P ≤ P :=
  inf_le_left

/-- The perfect part consists of compact objects. -/
theorem sourcePerfectPart_le_compact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left)) :
    sourcePerfectPart X P ≤ ObjectProperty.compactObjects.{u} :=
  inf_le_right

/-- Every external-product generator belongs to the perfect base-change
envelope. -/
theorem perfectBaseChangeGenerators_le_envelope
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    perfectBaseChangeGenerators X T P externalProduct ≤
      perfectBaseChangeEnvelope X T P externalProduct :=
  ObjectProperty.le_triangEnvelope _

/-- Under compact-preserving pullback and tensor, every geometric generator
of Proposition 3.15 is a compact object of `Dqc(X_T)`. -/
theorem perfectBaseChangeGenerators_externalProduct_le_compact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hpullX : pullX.PreservesCompactObjects)
    (hpullT : pullT.PreservesCompactObjects)
    (htensor : TensorPreservesCompactObjects X T tensor) :
    perfectBaseChangeGenerators X T P
        (baseChangeExternalProduct X T P pullX pullT tensor) ≤
      ObjectProperty.compactObjects.{u} := by
  rintro E ⟨F, G, ⟨e⟩⟩
  exact ObjectProperty.isCompactObject_of_iso e
    (baseChangeExternalProduct_obj_isCompact X T P pullX pullT tensor
      hpullX hpullT htensor F G)

/-- Universal property of the perfect envelope: any thick triangulated
property containing the external-product generators contains the envelope. -/
theorem perfectBaseChangeEnvelope_le
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left))
    {Q : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)}
    [Q.IsStableUnderRetracts] [Q.IsTriangulated]
    (h : perfectBaseChangeGenerators X T P externalProduct ≤ Q) :
    perfectBaseChangeEnvelope X T P externalProduct ≤ Q :=
  (ObjectProperty.triangEnvelope_le_iff
    (P := perfectBaseChangeGenerators X T P externalProduct) (Q := Q)).2 h

/-- Compactness half of the perfect-envelope construction in Proposition
3.15.  Once compact objects of the ambient `Dqc(X_T)` are available as a thick
triangulated property, compact-preserving pullback and tensor put the whole
external-product envelope inside them.

The two typeclass hypotheses are deliberately explicit: their general proof
for the repository's coproduct-based `IsCompactObject` API has not yet been
formalized and is independent of the scheme-theoretic tensor construction. -/
theorem perfectBaseChangeEnvelope_externalProduct_le_compact
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pullX : DqcLeftDerivedPullback (baseChangeFst X T))
    (pullT : DqcLeftDerivedPullback (baseChangeSnd X T))
    (tensor : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    [ObjectProperty.IsStableUnderRetracts
      (ObjectProperty.compactObjects.{u}
        (C := Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left))]
    [ObjectProperty.IsTriangulated
      (ObjectProperty.compactObjects.{u}
        (C := Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left))]
    (hpullX : pullX.PreservesCompactObjects)
    (hpullT : pullT.PreservesCompactObjects)
    (htensor : TensorPreservesCompactObjects X T tensor) :
    perfectBaseChangeEnvelope X T P
        (baseChangeExternalProduct X T P pullX pullT tensor) ≤
      ObjectProperty.compactObjects.{u} :=
  perfectBaseChangeEnvelope_le X T P
    (baseChangeExternalProduct X T P pullX pullT tensor)
    (perfectBaseChangeGenerators_externalProduct_le_compact X T P pullX pullT
      tensor hpullX hpullT htensor)

/-- Universal property of the quasi-coherent construction: any property
closed under isomorphisms, `Type u`-indexed coproducts, and extensions which
contains the perfect envelope contains `(Dqc)_T`. -/
theorem quasicoherentBaseChangeComponent_le
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left))
    {Q : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)}
    [Q.IsClosedUnderIsomorphisms]
    [∀ (ι : Type u), Q.IsClosedUnderColimitsOfShape (Discrete ι)]
    [Q.IsTriangulatedClosed₂]
    (h : perfectBaseChangeEnvelope X T P externalProduct ≤ Q) :
    quasicoherentBaseChangeComponent X T P externalProduct ≤ Q :=
  (perfectBaseChangeEnvelope X T P externalProduct).coprodClosure_le h

/-- The perfect base-change envelope lies in its quasi-coherent companion. -/
theorem perfectBaseChangeEnvelope_le_quasicoherent
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)) :
    perfectBaseChangeEnvelope X T P externalProduct ≤
      quasicoherentBaseChangeComponent X T P externalProduct :=
  (perfectBaseChangeEnvelope X T P externalProduct).le_coprodClosure

/-- Membership in `D_T` is definitionally membership of the intrinsic
bounded-coherent object's image in `(Dqc)_T`. -/
theorem mem_boundedBaseChangeComponent_iff
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (externalProduct : SourcePerfectPartCategory X P ⥤
      (CompactDqcFiber T ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left))
    (E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) :
    boundedBaseChangeComponent X T P externalProduct E ↔
      quasicoherentBaseChangeComponent X T P externalProduct
        ((boundedCoherentFiberToDqc X T).obj E) :=
  Iff.rfl

end SchemeBaseChange

end


end AlgebraicGeometry.DerivedCategory.Families
