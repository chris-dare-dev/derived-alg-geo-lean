/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Algebraic
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent

/-!
# Stack presentations at the fppf level

`Stacks/Algebraic.lean` builds presentation data -- a representable diagonal,
an atlas scheme, a smooth-surjective atlas, and local finite presentation over
a base -- and says of it, in its own words, that it is not an algebraic stack:
the standard notion asks for fppf descent, and that file only ever asks for
Zariski descent.

`Stacks/Descent.lean` supplies the missing half, `representableFppfStack`,
whose stack condition is Mathlib's fpqc descent theorem for representable
presheaves restricted along `Scheme.fppfTopology ≤ Scheme.fpqcTopology`.

This file puts the two together. The presentations below are the same data as
the big-Zariski ones, over stacks whose descent is fppf.

## What is and is not claimed

The diagonal here is represented by **schemes**, not by algebraic spaces. That
is stronger than the usual condition, not weaker, so a presentation in this
file is more than the definition asks for on that axis -- but it also means
these are not literally the standard `AlgebraicStack` of the literature, and
they are not named as though they were. No Artin representability theorem is
postulated, here or anywhere below it: every atlas, diagonal and finiteness
datum is an actual scheme morphism statement carried in the structure.

## Why the fppf layer costs almost nothing here

`representableFppfStack X` and `representableZariskiStack X` have *the same*
presheaf -- both are `discretePseudofunctor (yoneda.obj X)`, and
`representableFppfStack_presheaf` proves it by `rfl`. They differ only in
which descent theorem they carry, which is a `Prop` field.

A `StackMorphism`, its `FiberRepresentation`, and the representability
vocabulary generalized over an arbitrary topology in `Stacks/Algebraic.lean`
all speak about presheaves and about representing scheme morphisms. None
mentions a covering family. So the fppf morphism *is* the Zariski morphism,
and the constructions below are definitional transports rather than new
proofs. That is the content of `representableFppfStackMap_eq_zariski`: it is
`rfl`, and it is stated precisely so the reader does not have to take the
claim on trust.

This is not a claim that fppf descent is free. It is the observation that the
work of proving it was already done in `Stacks/Descent.lean`, and that
nothing in the presentation vocabulary needed redoing once it stopped naming
a topology it never used.
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
  representableZariskiStackMap f

/-- The fppf and Zariski representable stack maps of a scheme morphism are the
same data. Stated, rather than left implicit, because every transport below
relies on it. -/
theorem representableFppfStackMap_eq_zariski {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableFppfStackMap f : StackMorphism _ _) =
      representableZariskiStackMap f :=
  rfl

/-- Every scheme-induced morphism of representable fppf stacks is
representable, by the same fiber products as at the Zariski level. -/
instance representableFppfStackMap_isRepresentable
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableFppfStackMap f).IsRepresentable where
  representation y :=
    ⟨{ representing :=
         (RepresentableZariskiStackMap.fiberRepresentation f y).representing
       fiberEquivalence :=
         (RepresentableZariskiStackMap.fiberRepresentation f y).fiberEquivalence }⟩

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable fppf stacks, checked on the actual representing
scheme morphisms. -/
theorem representableFppfStackMap_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasRepresentableProperty P (representableFppfStackMap f) := by
  constructor
  intro S y
  exact ⟨{ representing :=
             (RepresentableZariskiStackMap.fiberRepresentation f y).representing
           fiberEquivalence :=
             (RepresentableZariskiStackMap.fiberRepresentation f y).fiberEquivalence
           property := P.pullback_snd f y.as hf }⟩

/-- The identity atlas of a representable fppf stack is smooth and
surjective on every representing scheme. -/
theorem representableFppfStackMap_id_isSmoothSurjective (X : Scheme.{u}) :
    StackMorphism.IsSmoothSurjective (representableFppfStackMap (𝟙 X)) :=
  representableFppfStackMap_hasRepresentableProperty
    (@Smooth ⊓ @Surjective) (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- A locally finitely presented scheme morphism induces a locally finitely
presented morphism of representable fppf stacks. -/
theorem representableFppfStackMap_isLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    StackMorphism.IsLocallyOfFinitePresentation (representableFppfStackMap f) :=
  representableFppfStackMap_hasRepresentableProperty
    @LocallyOfFinitePresentation f inferInstance

/-- A scheme-theoretic open immersion induces an open immersion of
representable fppf stacks. -/
theorem representableFppfStackMap_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsOpenImmersion (representableFppfStackMap f) :=
  representableFppfStackMap_hasRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-- The diagonal of a representable fppf stack is represented by the same
scheme-theoretic equalizers as at the Zariski level. -/
instance representableFppfStack_hasRepresentableDiagonal (X : Scheme.{u}) :
    AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
      (representableFppfStack X) where
  representation x y :=
    ⟨{ representing :=
         (representableZariskiDiagonalFiberRepresentation x y).representing
       isomorphismEquiv :=
         (representableZariskiDiagonalFiberRepresentation x y).isomorphismEquiv }⟩

/-! ## Fppf presentations -/

/-- Presentation data for a big-fppf stack: a representable diagonal, an
atlas scheme, and an atlas whose every base change is an actual
smooth-surjective scheme morphism.

Not called `AlgebraicStack`: the diagonal here is represented by schemes
rather than by algebraic spaces, which is a different -- stronger --
condition than the standard definition asks for. -/
structure FppfStackPresentation where
  /-- The underlying big-fppf stack in groupoids. -/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.fppfTopology
  /-- The diagonal is represented by schemes via its isomorphism functors. -/
  schemeDiagonal : AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
    toStackInGroupoids
  /-- The scheme presenting the stack. -/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable fppf stack. -/
  atlas : StackMorphism (representableFppfStack atlasScheme) toStackInGroupoids
  /-- Every base change of the atlas is an actual smooth-surjective scheme
  morphism. -/
  atlasSmoothSurjective : StackMorphism.IsSmoothSurjective atlas

/-- Every representable big-fppf stack has an fppf presentation, using its
identity atlas and its scheme-theoretic equalizer diagonal. -/
def representableFppfStackPresentation (X : Scheme.{u}) :
    FppfStackPresentation where
  toStackInGroupoids := representableFppfStack X
  schemeDiagonal := inferInstance
  atlasScheme := X
  atlas := representableFppfStackMap (𝟙 X)
  atlasSmoothSurjective := representableFppfStackMap_id_isSmoothSurjective X

/-- An fppf stack presentation locally of finite presentation over a base
scheme, with local finite presentation checked on all scheme representatives
of the structural morphism. -/
structure FppfStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying fppf presentation. -/
  toFppfStackPresentation : FppfStackPresentation
  /-- Its structural morphism to the representable fppf stack of the base. -/
  structureMorphism : StackMorphism
    toFppfStackPresentation.toStackInGroupoids
      (representableFppfStack S)
  /-- Local finite presentation, on every scheme representative. -/
  locallyOfFinitePresentation :
    StackMorphism.IsLocallyOfFinitePresentation structureMorphism

/-- A locally finitely presented scheme morphism gives a locally finitely
presented fppf presentation over its target. -/
def representableFppfStackPresentationOver {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFinitePresentation p] :
    FppfStackPresentationOver S where
  toFppfStackPresentation := representableFppfStackPresentation X
  structureMorphism := representableFppfStackMap p
  locallyOfFinitePresentation :=
    representableFppfStackMap_isLocallyOfFinitePresentation p

/-- A concrete positive-dimensional supported case at the fppf level: the
representable affine-line stack has an fppf presentation locally of finite
presentation over every base scheme.

This is the fppf counterpart of `affineLineZariskiStackPresentationOver`, and
it is the reason the presentations above are inhabited by something other
than a point. -/
def affineLineFppfStackPresentationOver (S : Scheme.{u}) :
    FppfStackPresentationOver S :=
  representableFppfStackPresentationOver
    (𝔸(ULift.{u} (Fin 1); S) ↘ S)

end

end AlgebraicGeometry
