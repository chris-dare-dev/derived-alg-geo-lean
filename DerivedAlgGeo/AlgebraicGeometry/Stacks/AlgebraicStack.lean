/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Algebraic
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent

/-!
# Pointwise stack presentations at the fppf level

`Stacks/Algebraic.lean` builds pointwise presentation data -- a pointwise
representable diagonal, an atlas scheme, a pointwise smooth-surjective atlas,
and pointwise local finite presentation over a base -- and says of it, in its
own words, that it is not an algebraic stack: its atlas and diagonal conditions
are pointwise in the test scheme, and that file only ever asks for Zariski
descent.

`Stacks/Representable.lean` supplies `representableFppfStack`,
whose stack condition is Mathlib's fpqc descent theorem for representable
presheaves restricted along `Scheme.fppfTopology ≤ Scheme.fpqcTopology`.

This file puts the two together. The presentations below are the same data as
the big-Zariski ones, over stacks whose descent is fppf.

## Main definitions

* `representableFppfStackMap` — the morphism of representable big-fppf stacks
  induced by a scheme morphism.
* `PointwiseFppfStackPresentation`, `PointwiseFppfStackPresentationOver` —
  pointwise fppf presentations: a pointwise scheme diagonal and a pointwise
  smooth-surjective scheme atlas, optionally pointwise locally of finite
  presentation over a base.
* `representablePointwiseFppfStackPresentationOver` and
  `affineLinePointwiseFppfStackPresentationOver` — the presentations of a
  locally finitely presented scheme morphism and of the affine line.

## Main results

* `representableFppfStackMap_eq_zariski` — the fppf and Zariski representable
  stack maps of a scheme morphism are the same data.
* `representableFppfStackMap_hasPointwiseRepresentableProperty` — a
  base-change-stable property of a scheme morphism passes to the induced
  morphism of representable fppf stacks.
* `representableFppfStack_hasPointwiseRepresentableDiagonal` — the diagonal of
  a representable fppf stack is pointwise represented by scheme-theoretic
  equalizers.

## Implementation notes

### What is and is not claimed

The atlas and diagonal conditions here are pointwise, in the sense of
`StackMorphism.PointwiseFiberRepresentation`: a representing scheme is chosen
for each test scheme separately, and nothing relates the choices along maps of
test schemes. So fppf descent alone does not make these presentations
algebraic stacks, and they are not named as though they were. The diagonal is
also represented by **schemes**, not by algebraic spaces. No Artin
representability theorem is postulated, here or anywhere below it: every atlas,
diagonal and finiteness datum is an actual scheme morphism statement carried in
the structure.

### Why the fppf layer costs almost nothing here

`representableFppfStack X` and `representableZariskiStack X` have *the same*
presheaf -- both are `discretePseudofunctor (yoneda.obj X)`, and
`representableFppfStack_presheaf` proves it by `rfl`. They differ only in
which descent theorem they carry, which is a `Prop` field.

A `StackMorphism`, its `PointwiseFiberRepresentation`, and the pointwise
representability vocabulary generalized over an arbitrary topology in
`Stacks/Algebraic.lean` all speak about presheaves and about representing
scheme morphisms. None mentions a covering family. So the fppf morphism *is* the Zariski morphism,
and the constructions below are definitional transports rather than new
proofs. That is the content of `representableFppfStackMap_eq_zariski`: it is
`rfl`, and it is stated precisely so the reader does not have to take the
claim on trust.

This is not a claim that fppf descent is free. It is the observation that the
work of proving it was already done in `Stacks/Descent.lean`, and that
nothing in the presentation vocabulary needed redoing once it stopped naming
a topology it never used.

## References

This file builds on `Stacks/Algebraic.lean`, `Stacks/Representable.lean` and
`Stacks/Descent.lean`, and on Mathlib's `Scheme.fppfTopology`.

## Tags

stack presentation, fppf topology, representable stack, diagonal, atlas
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

universe u

/-! ## The fppf representable stack map -/

/-- A scheme morphism induces the corresponding morphism of representable
big-fppf stacks.

This is the big-Zariski morphism unchanged: the two stacks have the same
presheaf, and a `StackMorphism` is data about presheaves. -/
def representableFppfStackMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StackMorphism (representableFppfStack X) (representableFppfStack Y) :=
  StackInGroupoids.representableMap Scheme.fppfTopology f

/-- The fppf and Zariski representable stack maps of a scheme morphism are the
same data. Stated, rather than left implicit, because every transport below
relies on it. -/
theorem representableFppfStackMap_eq_zariski {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableFppfStackMap f : StackMorphism _ _) =
      representableZariskiStackMap f :=
  rfl

/-- Every scheme-induced morphism of representable fppf stacks is pointwise
representable, by the same fiber products as at the Zariski level. -/
instance representableFppfStackMap_isPointwiseRepresentable
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableFppfStackMap f).IsPointwiseRepresentable where
  representation y :=
    ⟨{ representing :=
         (RepresentableZariskiStackMap.pointwiseFiberRepresentation f y).representing
       fiberEquivalence :=
         (RepresentableZariskiStackMap.pointwiseFiberRepresentation f y).fiberEquivalence }⟩

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable fppf stacks, checked on the actual representing
scheme morphisms. -/
theorem representableFppfStackMap_hasPointwiseRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasPointwiseRepresentableProperty P (representableFppfStackMap f) := by
  constructor
  intro S y
  exact ⟨{ representing :=
             (RepresentableZariskiStackMap.pointwiseFiberRepresentation f y).representing
           fiberEquivalence :=
             (RepresentableZariskiStackMap.pointwiseFiberRepresentation f y).fiberEquivalence
           property :=
             P.pullback_snd f ((StackInGroupoids.representableObjEquiv _).symm y) hf }⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity atlas of a representable fppf stack is pointwise smooth and
surjective: smooth and surjective on every representing scheme. -/
theorem representableFppfStackMap_id_isPointwiseSmoothSurjective (X : Scheme.{u}) :
    StackMorphism.IsPointwiseSmoothSurjective (representableFppfStackMap (𝟙 X)) :=
  representableFppfStackMap_hasPointwiseRepresentableProperty
    (@Smooth ⊓ @Surjective) (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- A locally finitely presented scheme morphism induces a pointwise locally
finitely presented morphism of representable fppf stacks. -/
theorem representableFppfStackMap_isPointwiseLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    StackMorphism.IsPointwiseLocallyOfFinitePresentation (representableFppfStackMap f) :=
  representableFppfStackMap_hasPointwiseRepresentableProperty
    @LocallyOfFinitePresentation f inferInstance

/-- A scheme-theoretic open immersion induces a pointwise open immersion of
representable fppf stacks. -/
theorem representableFppfStackMap_isPointwiseOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsPointwiseOpenImmersion (representableFppfStackMap f) :=
  representableFppfStackMap_hasPointwiseRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-- The diagonal of a representable fppf stack is pointwise represented by
the same scheme-theoretic equalizers as at the Zariski level. -/
instance representableFppfStack_hasPointwiseRepresentableDiagonal (X : Scheme.{u}) :
    AlgebraicGeometry.StackInGroupoids.HasPointwiseRepresentableDiagonal
      (representableFppfStack X) where
  representation x y :=
    ⟨{ representing :=
         (representableZariskiPointwiseDiagonalFiberRepresentation x y).representing
       isomorphismEquiv :=
         (representableZariskiPointwiseDiagonalFiberRepresentation x y).isomorphismEquiv }⟩

/-! ## Pointwise fppf presentations -/

/-- Pointwise presentation data for a big-fppf stack: a pointwise
representable diagonal, an atlas scheme, and an atlas whose every pointwise
representing scheme is smooth and surjective over the test scheme.

The atlas and diagonal conditions are pointwise, so this is not an algebraic
stack at any topology.  The diagonal is also represented by schemes rather
than by algebraic spaces. -/
structure PointwiseFppfStackPresentation where
  /-- The underlying big-fppf stack in groupoids. -/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.fppfTopology
  /-- The diagonal is pointwise represented by schemes via its isomorphism
  functors. -/
  schemeDiagonal : AlgebraicGeometry.StackInGroupoids.HasPointwiseRepresentableDiagonal
    toStackInGroupoids
  /-- The scheme presenting the stack. -/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable fppf stack. -/
  atlas : StackMorphism (representableFppfStack atlasScheme) toStackInGroupoids
  /-- Every pointwise representing scheme of the atlas is smooth and
  surjective over the test scheme. -/
  atlasPointwiseSmoothSurjective : StackMorphism.IsPointwiseSmoothSurjective atlas

/-- Every representable big-fppf stack has a pointwise fppf presentation,
using its identity atlas and its scheme-theoretic equalizer diagonal. -/
def representablePointwiseFppfStackPresentation (X : Scheme.{u}) :
    PointwiseFppfStackPresentation where
  toStackInGroupoids := representableFppfStack X
  schemeDiagonal := inferInstance
  atlasScheme := X
  atlas := representableFppfStackMap (𝟙 X)
  atlasPointwiseSmoothSurjective :=
    representableFppfStackMap_id_isPointwiseSmoothSurjective X

/-- A pointwise fppf stack presentation locally of finite presentation over a
base scheme, with local finite presentation checked on all pointwise scheme
representatives of the structural morphism.

The atlas, diagonal and finiteness conditions are pointwise, so this is not an
algebraic stack at any topology. -/
structure PointwiseFppfStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying pointwise fppf presentation. -/
  toPointwiseFppfStackPresentation : PointwiseFppfStackPresentation
  /-- Its structural morphism to the representable fppf stack of the base. -/
  structureMorphism : StackMorphism
    toPointwiseFppfStackPresentation.toStackInGroupoids
      (representableFppfStack S)
  /-- Local finite presentation, on every pointwise scheme representative. -/
  pointwiseLocallyOfFinitePresentation :
    StackMorphism.IsPointwiseLocallyOfFinitePresentation structureMorphism

/-- A locally finitely presented scheme morphism gives a locally finitely
presented pointwise fppf presentation over its target. -/
def representablePointwiseFppfStackPresentationOver {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFinitePresentation p] :
    PointwiseFppfStackPresentationOver S where
  toPointwiseFppfStackPresentation :=
    representablePointwiseFppfStackPresentation X
  structureMorphism := representableFppfStackMap p
  pointwiseLocallyOfFinitePresentation :=
    representableFppfStackMap_isPointwiseLocallyOfFinitePresentation p

/-- A concrete positive-dimensional supported case at the fppf level: the
representable affine-line stack has a pointwise fppf presentation locally of
finite presentation over every base scheme.

This is the fppf counterpart of
`affineLinePointwiseZariskiStackPresentationOver`, and
it is the reason the presentations above are inhabited by something other
than a point. -/
def affineLinePointwiseFppfStackPresentationOver (S : Scheme.{u}) :
    PointwiseFppfStackPresentationOver S :=
  representablePointwiseFppfStackPresentationOver
    (𝔸(ULift.{u} (Fin 1); S) ↘ S)

end

end AlgebraicGeometry
