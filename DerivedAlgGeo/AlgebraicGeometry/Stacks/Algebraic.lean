/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Representable

/-!
# Scheme morphisms and pointwise big-Zariski stack presentation data

This file provides two pieces of data that retain their geometric content:

* a scheme morphism induces a pullback-compatible morphism between the
  corresponding representable big-Zariski stacks;
* a property of a pointwise-represented stack morphism is required on the
  actual structure morphism of every representing scheme.

Every representability notion here is pointwise in the test object, in the
sense of `StackMorphism.PointwiseFiberRepresentation`: an equivalence with the
fiber is chosen for each test scheme separately, and nothing relates the
choices along maps of test schemes. So `IsPointwiseSmoothSurjective` constrains
a pointwise representing scheme, not the 2-fibre product, and the presentations
at the end of this file are not algebraic stacks at any topology. They are also
deliberately named for the big Zariski topology: no fppf or étale descent
theorem is proved here, and the diagonal is represented by schemes rather than
algebraic spaces. No Artin representability theorem or opaque algebraicity
proposition is introduced.

## Main definitions

* `representableZariskiStackMap` — the morphism of representable big-Zariski
  stacks induced by a scheme morphism.
* `StackMorphism.HasPointwiseRepresentableProperty` — every fiber of a stack
  morphism has a pointwise representing scheme whose structure morphism
  satisfies a given property, with the specializations
  `StackMorphism.IsPointwiseLocallyOfFinitePresentation`,
  `StackMorphism.IsPointwiseSmoothSurjective` and
  `StackMorphism.IsPointwiseOpenImmersion`.
* `StackInGroupoids.HasPointwiseRepresentableDiagonal` — for every pair of
  objects of a stack, a scheme whose points over each test scheme are in
  bijection with the isomorphisms, through
  `StackInGroupoids.PointwiseDiagonalFiberRepresentation`.
* `PointwiseZariskiStackPresentation`, `PointwiseZariskiStackPresentationOver`
  — pointwise big-Zariski presentations: a scheme diagonal and a
  smooth-surjective scheme atlas, optionally locally of finite presentation
  over a base, all in the pointwise sense.

## Main results

* `representableZariskiStackMap_isPointwiseRepresentable` — a scheme-induced
  morphism of representable stacks is pointwise represented by the actual fiber
  products.
* `representableZariskiStackMap_hasPointwiseRepresentableProperty` — a
  base-change-stable property of a scheme morphism passes to the induced stack
  morphism.
* `representableZariskiStack_hasPointwiseRepresentableDiagonal` — the diagonal
  of a representable stack is pointwise represented by scheme-theoretic
  equalizers.
* `representablePointwiseZariskiStackPresentationOver` and
  `affineLinePointwiseZariskiStackPresentationOver` — every locally finitely
  presented scheme morphism, and in particular the affine line, gives a
  pointwise big-Zariski presentation over its target.

## Implementation notes

The fppf and étale descent level lives in
`DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent`, which also shows that a
smooth surjection is an fppf covering family.  That module does not change
anything here: the diagonal below is still represented by schemes, and the
presentations below are still pointwise big-Zariski presentations.

### Which declarations here fix the topology, and which do not

The pointwise representability vocabulary --
`StackMorphism.HasPointwiseRepresentableProperty` with its
`IsPointwiseLocallyOfFinitePresentation`, `IsPointwiseSmoothSurjective` and
`IsPointwiseOpenImmersion` specializations, and
`StackInGroupoids.HasPointwiseRepresentableDiagonal` with its fiber
representation -- says nothing about which covering families the stack
condition quantifies over.  Each is a statement about the *representing scheme
morphisms* of a stack morphism's fibers, so each is stated for an arbitrary
Grothendieck topology `J` on `Scheme` and reads identically at Zariski, étale
and fppf.

What genuinely is Zariski is everything named for it: the
`representableZariski*` constructions, whose descent comes from
`Scheme.zariskiTopology` being subcanonical, and
`PointwiseZariskiStackPresentation` and
`PointwiseZariskiStackPresentationOver`, whose names record exactly the gap
between what they supply and an algebraic stack.

The split is deliberate: raising the presentations to fppf should not also
have to widen the vocabulary they are stated in.

## References

This file builds on `StackInGroupoids`, `StackMorphism.IsPointwiseRepresentable`
and `StackInGroupoids.representableMap`, and on Mathlib's
`Scheme.zariskiTopology` and `MorphismProperty`.

## Tags

algebraic stack, representable morphism, diagonal, atlas, Zariski topology, stack in groupoids
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open Opposite

noncomputable section

universe u

/-- A scheme morphism induces the corresponding morphism between
representable big-Zariski stacks by postcomposition on every test scheme. -/
def representableZariskiStackMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StackMorphism (representableZariskiStack X)
      (representableZariskiStack Y) :=
  StackInGroupoids.representableMap Scheme.zariskiTopology f

@[simp]
theorem representableZariskiStackMap_obj {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ X) :
    ((representableZariskiStackMap f).app T).obj
        (representableZariskiObject g) =
      representableZariskiObject (g ≫ f) :=
  rfl

/-- Three scheme-induced stack morphisms compose through Mathlib's strong
transformation composition, with the expected pointwise action.  The
associator and unitors for this composition are the ones supplied by the
pseudofunctor bicategory. -/
@[simp]
theorem representableZariskiStackMap_tripleComp_obj
    {W X Y Z T : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : T ⟶ W) :
    ((((representableZariskiStackMap f).comp
      (representableZariskiStackMap g)).comp
        (representableZariskiStackMap h)).app T).obj
          (representableZariskiObject x) =
      representableZariskiObject (((x ≫ f) ≫ g) ≫ h) :=
  rfl

/-- The scheme morphism `S ⟶ X` underlying an object of the stack represented by `X`. -/
private abbrev representableZariskiHom {X S : Scheme.{u}}
    (x : (representableZariskiStack X).presheaf.obj (.mk (op S))) : S ⟶ X :=
  (StackInGroupoids.representableObjEquiv _).symm x

namespace RepresentableZariskiStackMap

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (y : (representableZariskiStack Y).presheaf.obj (.mk (op S)))

/-- The ordinary scheme fiber product representing the fiber of a
representable-stack morphism over an object `y` of the stack represented by `Y`, that is, over
a morphism `S ⟶ Y`. -/
def fiberProduct : Over S :=
  Over.mk (pullback.snd f (representableZariskiHom y))

private def fiberObject (T : Over S)
    (a : T ⟶ fiberProduct f y) :
    StructuredArrow
      (((representableZariskiStack Y).presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      ((representableZariskiStackMap f).app T.left) :=
  let y' := representableZariskiHom y
  StructuredArrow.mk (Y := representableZariskiObject (a.left ≫ pullback.fst f y'))
    (eqToHom (congrArg (representableZariskiObject (T := T.left)) (by
      have ha : a.left ≫ pullback.snd f y' = T.hom := a.w
      calc
        T.hom ≫ y' = (a.left ≫ pullback.snd f y') ≫ y' :=
          congrArg (fun k ↦ k ≫ y') ha.symm
        _ = a.left ≫ (pullback.snd f y' ≫ y') := Category.assoc ..
        _ = a.left ≫ (pullback.fst f y' ≫ f) :=
          congrArg (fun k ↦ a.left ≫ k)
            (pullback.condition (f := f) (g := y')).symm
        _ = (a.left ≫ pullback.fst f y') ≫ f := (Category.assoc ..).symm)))

/-- Yoneda's fiber-product comparison as a functor into the actual groupoid
fiber of the induced stack morphism. -/
def fiberFunctor (T : Over S) :
    Discrete (T ⟶ fiberProduct f y) ⥤
      (representableZariskiStackMap f).FiberCategory y T :=
  Core.functorToCore (Discrete.functor (fiberObject f y T))

instance fiberFunctor_faithful (T : Over S) :
    (fiberFunctor f y T).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance fiberFunctor_full (T : Over S) :
    (fiberFunctor f y T).Full where
  map_surjective {a b} h := by
    have hfst : a.as.left ≫ pullback.fst f (representableZariskiHom y) =
        b.as.left ≫ pullback.fst f (representableZariskiHom y) :=
      representableZariskiObject_injective (IsDiscrete.eq_of_hom h.iso.hom.right)
    have hsnd : a.as.left ≫ pullback.snd f (representableZariskiHom y) =
        b.as.left ≫ pullback.snd f (representableZariskiHom y) :=
      a.as.w.trans b.as.w.symm
    have hab : a.as = b.as := by
      apply CostructuredArrow.hom_ext
      apply pullback.hom_ext
      · exact hfst
      · exact hsnd
    refine ⟨eqToHom (Discrete.ext hab), ?_⟩
    apply Core.hom_ext
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim

instance fiberFunctor_essSurj (T : Over S) :
    (fiberFunctor f y T).EssSurj := by
  constructor
  intro z
  let x : T.left ⟶ X := representableZariskiHom z.of.right
  have hxy : T.hom ≫ representableZariskiHom y = x ≫ f :=
    congrArg (StackInGroupoids.representableObjEquiv _).symm (IsDiscrete.eq_of_hom z.of.hom)
  let a : T ⟶ fiberProduct f y :=
    Over.homMk (pullback.lift x T.hom hxy.symm)
      (pullback.lift_snd x T.hom hxy.symm)
  refine ⟨Discrete.mk a, ?_⟩
  apply Nonempty.intro
  apply Core.isoMk
  refine StructuredArrow.isoMk (eqToIso (congrArg (representableZariskiObject (T := T.left))
    (pullback.lift_fst x T.hom hxy.symm))) ?_
  apply Subsingleton.elim

/-- The fiber of a morphism between representable stacks is represented by
the ordinary scheme fiber product.  The comparison at each test object is the
Yoneda bijection of the fiber product, packaged as a
`PointwiseFiberRepresentation`. -/
def pointwiseFiberRepresentation :
    (representableZariskiStackMap f).PointwiseFiberRepresentation y where
  representing := fiberProduct f y
  fiberEquivalence T := by
    letI := fiberFunctor_faithful f y T
    letI := fiberFunctor_full f y T
    letI := fiberFunctor_essSurj f y T
    letI : (fiberFunctor f y T).IsEquivalence :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    exact (fiberFunctor f y T).asEquivalence

end RepresentableZariskiStackMap

/-- Every scheme-induced morphism of representable stacks is pointwise
representable, and its representing schemes are the actual fiber products. -/
instance representableZariskiStackMap_isPointwiseRepresentable
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableZariskiStackMap f).IsPointwiseRepresentable where
  representation y :=
    ⟨RepresentableZariskiStackMap.pointwiseFiberRepresentation f y⟩

/-- A pointwise-represented fiber together with a property of its actual
structure morphism to the test scheme. -/
structure StackMorphism.PointwiseFiberRepresentationWithProperty
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) (P : MorphismProperty Scheme.{u})
    {S : Scheme.{u}} (y : G.presheaf.obj (.mk (op S)))
    extends f.PointwiseFiberRepresentation y where
  /-- The geometric property is asserted on the representing scheme
  morphism, not on an abstract stack-level token. -/
  property : P representing.hom

/-- A stack morphism is pointwise representable with property `P` when every
one of its fibers has a `PointwiseFiberRepresentation` whose representing
scheme's structure morphism satisfies `P`.

`P` constrains a pointwise representing scheme and says nothing about the
2-fibre product itself; the docstring of `PointwiseFiberRepresentation` gives a
non-smooth morphism that is `IsPointwiseSmoothSurjective`. -/
class StackMorphism.HasPointwiseRepresentableProperty
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (P : MorphismProperty Scheme.{u}) (f : StackMorphism F G) : Prop where
  representation {S : Scheme.{u}}
    (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (StackMorphism.PointwiseFiberRepresentationWithProperty f P y)

namespace StackMorphism

variable {J : GrothendieckTopology Scheme.{u}}
  {F G : StackInGroupoids Scheme.{u} J}
  {P Q : MorphismProperty Scheme.{u}} {f : StackMorphism F G}

/-- Forgetting the geometric property recovers pointwise representability. -/
theorem isPointwiseRepresentable_of_hasPointwiseRepresentableProperty
    [HasPointwiseRepresentableProperty P f] : f.IsPointwiseRepresentable := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasPointwiseRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨R.toPointwiseFiberRepresentation⟩

/-- Pointwise representable properties are monotone under implication of the
underlying scheme-morphism properties. -/
theorem hasPointwiseRepresentableProperty_mono (hPQ : P ≤ Q)
    [HasPointwiseRepresentableProperty P f] : HasPointwiseRepresentableProperty Q f := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasPointwiseRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨{ R.toPointwiseFiberRepresentation with property := hPQ _ R.property }⟩

end StackMorphism

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable stacks because each representing morphism is the
corresponding scheme-theoretic pullback. -/
theorem representableZariskiStackMap_hasPointwiseRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasPointwiseRepresentableProperty P (representableZariskiStackMap f) := by
  constructor
  intro S y
  exact ⟨{
    RepresentableZariskiStackMap.pointwiseFiberRepresentation f y with
    property := P.pullback_snd f (representableZariskiHom y) hf }⟩

/-- Pointwise local finite presentation of a stack morphism, measured on the
pointwise representing scheme morphisms of all fibers. -/
abbrev StackMorphism.IsPointwiseLocallyOfFinitePresentation
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasPointwiseRepresentableProperty @LocallyOfFinitePresentation f

/-- A pointwise smooth-surjective stack morphism is pointwise representable
and every representing scheme morphism is both smooth and surjective.

This does not make the morphism smooth: the docstring of
`PointwiseFiberRepresentation` gives a morphism with this property whose
underlying scheme morphism is not smooth. -/
abbrev StackMorphism.IsPointwiseSmoothSurjective
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasPointwiseRepresentableProperty (@Smooth ⊓ @Surjective) f

/-- A pointwise open immersion of stacks is pointwise representable and is an
open immersion on every scheme pointwise representing one of its fibers. -/
abbrev StackMorphism.IsPointwiseOpenImmersion
    {J : GrothendieckTopology Scheme.{u}}
    {F G : StackInGroupoids Scheme.{u} J}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasPointwiseRepresentableProperty @AlgebraicGeometry.IsOpenImmersion f

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity atlas of every representable stack is pointwise smooth and
surjective. -/
theorem representableZariskiStackMap_id_isPointwiseSmoothSurjective
    (X : Scheme.{u}) :
    StackMorphism.IsPointwiseSmoothSurjective (representableZariskiStackMap (𝟙 X)) :=
  representableZariskiStackMap_hasPointwiseRepresentableProperty
    (@Smooth ⊓ @Surjective) (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- The identity structural morphism of every representable stack is
pointwise locally of finite presentation, on the actual fiber schemes. -/
theorem representableZariskiStackMap_id_isPointwiseLocallyOfFinitePresentation
    (X : Scheme.{u}) :
    StackMorphism.IsPointwiseLocallyOfFinitePresentation
      (representableZariskiStackMap (𝟙 X)) :=
  representableZariskiStackMap_hasPointwiseRepresentableProperty
    @LocallyOfFinitePresentation (𝟙 X) inferInstance

/-- A scheme-theoretic open immersion induces a pointwise open immersion of
its representable big-Zariski stacks, checked on the actual pullback schemes. -/
theorem representableZariskiStackMap_isPointwiseOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsPointwiseOpenImmersion (representableZariskiStackMap f) :=
  representableZariskiStackMap_hasPointwiseRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-! ## Pointwise diagonal representability and big-Zariski presentations -/

/-- A scheme whose points over each test scheme are in bijection with the
isomorphisms between the pullbacks of two objects of a stack.

`isomorphismEquiv T` is a bijection for each `T` separately, not an
isomorphism of presheaves, so this does not represent the Isom sheaf of the
diagonal. -/
structure StackInGroupoids.PointwiseDiagonalFiberRepresentation
    {J : GrothendieckTopology Scheme.{u}}
    (F : StackInGroupoids Scheme.{u} J)
    {S : Scheme.{u}} (x y : F.presheaf.obj (.mk (op S))) where
  /-- The scheme of isomorphisms over `S`. -/
  representing : Over S
  /-- Arrows from `T` to the representing scheme are in bijection with the
  isomorphisms after pullback to `T`, for this `T` alone. -/
  isomorphismEquiv (T : Over S) :
    (T ⟶ representing) ≃
      (((F.presheaf.map T.hom.op.toLoc).toFunctor.obj x) ≅
        ((F.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      )

/-- A stack has pointwise representable diagonal when every pair of objects
has a `PointwiseDiagonalFiberRepresentation`. -/
class StackInGroupoids.HasPointwiseRepresentableDiagonal
    {J : GrothendieckTopology Scheme.{u}}
    (F : StackInGroupoids Scheme.{u} J) : Prop where
  representation {S : Scheme.{u}}
    (x y : F.presheaf.obj (.mk (op S))) :
    Nonempty
      (AlgebraicGeometry.StackInGroupoids.PointwiseDiagonalFiberRepresentation F x y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For a representable stack, the diagonal fiber over two maps `x,y : S ⟶ X`
is the scheme-theoretic equalizer of those maps. -/
def representableZariskiPointwiseDiagonalFiberRepresentation
    {X S : Scheme.{u}} (x y : (representableZariskiStack X).presheaf.obj (.mk (op S))) :
    AlgebraicGeometry.StackInGroupoids.PointwiseDiagonalFiberRepresentation
      (representableZariskiStack X) x y :=
  let x' := representableZariskiHom x
  let y' := representableZariskiHom y
  { representing := Over.mk (equalizer.ι x' y')
    isomorphismEquiv T :=
      { toFun := fun a ↦ eqToIso (congrArg (representableZariskiObject (T := T.left)) (by
          have ha : a.left ≫ equalizer.ι x' y' = T.hom := a.w
          calc
            T.hom ≫ x' = (a.left ≫ equalizer.ι x' y') ≫ x' :=
              congrArg (fun k ↦ k ≫ x') ha.symm
            _ = a.left ≫ (equalizer.ι x' y' ≫ x') := Category.assoc ..
            _ = a.left ≫ (equalizer.ι x' y' ≫ y') :=
              congrArg (fun k ↦ a.left ≫ k) (equalizer.condition x' y')
            _ = (a.left ≫ equalizer.ι x' y') ≫ y' := (Category.assoc ..).symm
            _ = T.hom ≫ y' := congrArg (fun k ↦ k ≫ y') ha))
        invFun := fun e ↦
          have he : T.hom ≫ x' = T.hom ≫ y' :=
            congrArg (StackInGroupoids.representableObjEquiv _).symm (IsDiscrete.eq_of_hom e.hom)
          Over.homMk (equalizer.lift T.hom he) (equalizer.lift_ι T.hom he)
        left_inv := fun a ↦ by
          apply CostructuredArrow.hom_ext
          change equalizer.lift T.hom _ = a.left
          apply equalizer.hom_ext
          rw [equalizer.lift_ι]
          exact a.w.symm
        right_inv := fun e ↦ by
          apply Iso.ext
          apply Subsingleton.elim } }

instance representableZariskiStack_hasPointwiseRepresentableDiagonal
    (X : Scheme.{u}) :
    AlgebraicGeometry.StackInGroupoids.HasPointwiseRepresentableDiagonal
      (representableZariskiStack X) where
  representation x y :=
    ⟨representableZariskiPointwiseDiagonalFiberRepresentation x y⟩

/-- A pointwise big-Zariski stack presentation: effective Zariski descent, a
pointwise scheme-represented diagonal, and a scheme atlas whose every fiber is
pointwise represented by a smooth-surjective scheme morphism.

The atlas and diagonal conditions are pointwise, so this is not an algebraic
stack at any topology.  Nor is it called `AlgebraicStack` on the other axes:
the standard notion requires fppf descent or an equivalent étale formulation,
and usually asks for the diagonal to be representable by algebraic spaces. -/
structure PointwiseZariskiStackPresentation where
  /-- The underlying big-Zariski stack in groupoids. -/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.zariskiTopology
  /-- The diagonal is pointwise represented by schemes via its isomorphism
  functors. -/
  schemeDiagonal :
    AlgebraicGeometry.StackInGroupoids.HasPointwiseRepresentableDiagonal
      toStackInGroupoids
  /-- The scheme presenting the stack. -/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable stack. -/
  atlas : StackMorphism (representableZariskiStack atlasScheme)
    toStackInGroupoids
  /-- Every pointwise representing scheme of the atlas is smooth and
  surjective over the test scheme. -/
  atlasPointwiseSmoothSurjective : StackMorphism.IsPointwiseSmoothSurjective atlas

/-- Every representable big-Zariski stack has a pointwise Zariski presentation
using its identity atlas and its scheme-theoretic equalizer diagonal. -/
def representablePointwiseZariskiStackPresentation (X : Scheme.{u}) :
    PointwiseZariskiStackPresentation where
  toStackInGroupoids := representableZariskiStack X
  schemeDiagonal := inferInstance
  atlasScheme := X
  atlas := representableZariskiStackMap (𝟙 X)
  atlasPointwiseSmoothSurjective :=
    representableZariskiStackMap_id_isPointwiseSmoothSurjective X

/-- A pointwise big-Zariski stack presentation locally of finite presentation
over a base scheme, expressed by an actual stack morphism whose every fiber has
a locally-finite-presentation pointwise representing scheme morphism.

The atlas, diagonal and finiteness conditions are pointwise, so this is not an
algebraic stack at any topology. -/
structure PointwiseZariskiStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying pointwise big-Zariski presentation. -/
  toPointwiseZariskiStackPresentation : PointwiseZariskiStackPresentation
  /-- Its structural morphism to the representable stack of the base. -/
  structureMorphism : StackMorphism
    toPointwiseZariskiStackPresentation.toStackInGroupoids
      (representableZariskiStack S)
  /-- Local finite presentation is checked on all pointwise scheme
  representatives of the structural morphism. -/
  pointwiseLocallyOfFinitePresentation :
    StackMorphism.IsPointwiseLocallyOfFinitePresentation structureMorphism

/-- A locally finitely presented scheme morphism gives a locally finitely
presented pointwise big-Zariski presentation over the target.  All fiber
representatives are the actual scheme fiber products. -/
def representablePointwiseZariskiStackPresentationOver {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFinitePresentation p] :
    PointwiseZariskiStackPresentationOver S where
  toPointwiseZariskiStackPresentation :=
    representablePointwiseZariskiStackPresentation X
  structureMorphism := representableZariskiStackMap p
  pointwiseLocallyOfFinitePresentation :=
    representableZariskiStackMap_hasPointwiseRepresentableProperty
      @LocallyOfFinitePresentation p inferInstance

/-- A concrete positive-dimensional supported case: the representable
affine-line stack has a pointwise Zariski presentation locally of finite
presentation over every base scheme. -/
def affineLinePointwiseZariskiStackPresentationOver (S : Scheme.{u}) :
    PointwiseZariskiStackPresentationOver S :=
  representablePointwiseZariskiStackPresentationOver
    (𝔸(ULift.{u} (Fin 1); S) ↘ S)

end

end AlgebraicGeometry
