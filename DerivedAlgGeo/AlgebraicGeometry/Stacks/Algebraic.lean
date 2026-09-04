/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import DerivedAlgGeo.AlgebraicGeometry.Stacks.Representable

/-!
# Scheme morphisms and big-Zariski stack presentation data

This file starts the algebraicity layer with two pieces of data that retain
their geometric content:

* a scheme morphism induces a pullback-compatible morphism between the
  corresponding representable big-Zariski stacks;
* a property of a representable stack morphism is required on the actual
  structure morphism of every representing scheme.

The presentation structure at the end of this file is deliberately named for
the big Zariski topology.  It is useful geometric data, but it is not the
standard definition of an algebraic stack: no fppf or étale descent theorem is
proved here, and the diagonal is represented by schemes rather than algebraic
spaces.  No Artin representability theorem or opaque algebraicity proposition
is introduced.
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
      (representableZariskiStack Y) where
  app T := Discrete.functor
    (Discrete.mk ∘ fun g : T.as.unop ⟶ X ↦ g ≫ f) |>.toCatHom
  naturality {S T} g := by
    exact Cat.Hom.isoMk (NatIso.ofComponents
      (fun h : Discrete (S.as.unop ⟶ X) ↦ Discrete.eqToIso (by
        change (g.as.unop ≫ h.as) ≫ f =
          g.as.unop ≫ (h.as ≫ f)
        simp))
      (by
        intro A B h
        letI : IsDiscrete
            ((representableZariskiStack Y).presheaf.obj T) := by
          exact discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) T
        apply Subsingleton.elim))
  naturality_naturality {S T} {g h} η := by
    letI : IsDiscrete
        ((representableZariskiStack Y).presheaf.obj T) :=
      discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) T
    apply Cat.Hom₂.ext
    ext
    apply Subsingleton.elim
  naturality_id S := by
    letI : IsDiscrete
        ((representableZariskiStack Y).presheaf.obj S) :=
      discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) S
    apply Cat.Hom₂.ext
    ext
    apply Subsingleton.elim
  naturality_comp {S T U} _ _ := by
    letI : IsDiscrete
        ((representableZariskiStack Y).presheaf.obj U) :=
      discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) U
    apply Cat.Hom₂.ext
    ext
    apply Subsingleton.elim

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

namespace RepresentableZariskiStackMap

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)
  (y : Discrete (S ⟶ Y))

/-- The ordinary scheme fiber product representing the fiber of a
representable-stack morphism over `y : S ⟶ Y`. -/
def fiberProduct : Over S :=
  Over.mk (pullback.snd f y.as)

private def fiberObject (T : Over S)
    (a : T ⟶ fiberProduct f y) :
    StructuredArrow
      (((representableZariskiStack Y).presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      ((representableZariskiStackMap f).app T.left) :=
  StructuredArrow.mk (Discrete.eqToHom (by
    change T.hom ≫ y.as = (a.left ≫ pullback.fst f y.as) ≫ f
    have ha : a.left ≫ pullback.snd f y.as = T.hom := a.w
    calc
      T.hom ≫ y.as = (a.left ≫ pullback.snd f y.as) ≫ y.as :=
        congrArg (fun k ↦ k ≫ y.as) ha.symm
      _ = a.left ≫ (pullback.snd f y.as ≫ y.as) := Category.assoc ..
      _ = a.left ≫ (pullback.fst f y.as ≫ f) :=
        congrArg (fun k ↦ a.left ≫ k)
          (pullback.condition (f := f) (g := y.as)).symm
      _ = (a.left ≫ pullback.fst f y.as) ≫ f := (Category.assoc ..).symm))

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
    have hfst : a.as.left ≫ pullback.fst f y.as =
        b.as.left ≫ pullback.fst f y.as :=
      Discrete.eq_of_hom h.iso.hom.right
    have hsnd : a.as.left ≫ pullback.snd f y.as =
        b.as.left ≫ pullback.snd f y.as :=
      a.as.w.trans b.as.w.symm
    have hab : a.as = b.as := by
      apply CostructuredArrow.hom_ext
      apply pullback.hom_ext
      · exact hfst
      · exact hsnd
    refine ⟨eqToHom (Discrete.ext hab), ?_⟩
    letI : IsDiscrete
        ((representableZariskiStack X).presheaf.obj (.mk (op T.left))) := by
      exact discretePseudofunctor_obj_isDiscrete (yoneda.obj X) _
    apply Core.hom_ext
    apply StructuredArrow.hom_ext
    apply Subsingleton.elim

instance fiberFunctor_essSurj (T : Over S) :
    (fiberFunctor f y T).EssSurj := by
  constructor
  intro z
  let x : T.left ⟶ X := z.of.right.as
  have hxy : T.hom ≫ y.as = x ≫ f :=
    Discrete.eq_of_hom z.of.hom
  let a : T ⟶ fiberProduct f y :=
    Over.homMk (pullback.lift x T.hom hxy.symm)
      (pullback.lift_snd x T.hom hxy.symm)
  refine ⟨Discrete.mk a, ?_⟩
  apply Nonempty.intro
  apply Core.isoMk
  refine StructuredArrow.isoMk (Discrete.eqToIso (by
    change (pullback.lift x T.hom hxy.symm ≫ pullback.fst f y.as) = x
    exact pullback.lift_fst x T.hom hxy.symm)) ?_
  letI : IsDiscrete
      ((representableZariskiStack Y).presheaf.obj (.mk (op T.left))) := by
    exact discretePseudofunctor_obj_isDiscrete (yoneda.obj Y) _
  apply Subsingleton.elim

/-- The fiber of a morphism between representable stacks is represented by
the ordinary scheme fiber product, with its full Yoneda universal property. -/
def fiberRepresentation :
    (representableZariskiStackMap f).FiberRepresentation y where
  representing := fiberProduct f y
  fiberEquivalence T := by
    letI := fiberFunctor_faithful f y T
    letI := fiberFunctor_full f y T
    letI := fiberFunctor_essSurj f y T
    letI : (fiberFunctor f y T).IsEquivalence :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    exact (fiberFunctor f y T).asEquivalence

end RepresentableZariskiStackMap

/-- Every scheme-induced morphism of representable stacks is representable,
and its representing schemes are the actual fiber products. -/
instance representableZariskiStackMap_isRepresentable
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (representableZariskiStackMap f).IsRepresentable where
  representation y :=
    ⟨RepresentableZariskiStackMap.fiberRepresentation f y⟩

/-- A represented fiber together with a property of its actual structure
morphism to the test scheme. -/
structure StackMorphism.FiberRepresentationWithProperty
    {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
    (f : StackMorphism F G) (P : MorphismProperty Scheme.{u})
    {S : Scheme.{u}} (y : G.presheaf.obj (.mk (op S)))
    extends f.FiberRepresentation y where
  /-- The geometric property is asserted on the representing scheme
  morphism, not on an abstract stack-level token. -/
  property : P representing.hom

/-- A stack morphism is representable with property `P` when every one of its
fibers has a representing scheme whose structure morphism satisfies `P`. -/
class StackMorphism.HasRepresentableProperty
    {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
    (P : MorphismProperty Scheme.{u}) (f : StackMorphism F G) : Prop where
  representation {S : Scheme.{u}}
    (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (StackMorphism.FiberRepresentationWithProperty f P y)

namespace StackMorphism

variable {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
  {P Q : MorphismProperty Scheme.{u}} {f : StackMorphism F G}

/-- Forgetting the geometric property recovers ordinary representability. -/
theorem isRepresentable_of_hasRepresentableProperty
    [HasRepresentableProperty P f] : f.IsRepresentable := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨R.toFiberRepresentation⟩

/-- Representable properties are monotone under implication of the underlying
scheme-morphism properties. -/
theorem hasRepresentableProperty_mono (hPQ : P ≤ Q)
    [HasRepresentableProperty P f] : HasRepresentableProperty Q f := by
  constructor
  intro S y
  obtain ⟨R⟩ := HasRepresentableProperty.representation (P := P) (f := f) y
  exact ⟨{ R.toFiberRepresentation with property := hPQ _ R.property }⟩

end StackMorphism

/-- A base-change-stable scheme-morphism property passes to the induced
morphism of representable stacks because each representing morphism is the
corresponding scheme-theoretic pullback. -/
theorem representableZariskiStackMap_hasRepresentableProperty
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) :
    StackMorphism.HasRepresentableProperty P (representableZariskiStackMap f) := by
  constructor
  intro S y
  exact ⟨{
    RepresentableZariskiStackMap.fiberRepresentation f y with
    property := P.pullback_snd f y.as hf }⟩

/-- Local finite presentation for stack morphisms is measured on the actual
representing scheme morphisms of all fibers. -/
abbrev StackMorphism.IsLocallyOfFinitePresentation
    {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty @LocallyOfFinitePresentation f

/-- A smooth-surjective stack cover is representable and every representing
scheme morphism is both smooth and surjective. -/
abbrev StackMorphism.IsSmoothSurjective
    {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty (@Smooth ⊓ @Surjective) f

/-- An open immersion of stacks is representable and is an open immersion
on every actual scheme representing one of its fibers. -/
abbrev StackMorphism.IsOpenImmersion
    {F G : StackInGroupoids Scheme.{u} Scheme.zariskiTopology}
    (f : StackMorphism F G) : Prop :=
  StackMorphism.HasRepresentableProperty @AlgebraicGeometry.IsOpenImmersion f

/-- The identity atlas of every representable stack is an actual
smooth-surjective representable morphism. -/
theorem representableZariskiStackMap_id_isSmoothSurjective
    (X : Scheme.{u}) :
    StackMorphism.IsSmoothSurjective (representableZariskiStackMap (𝟙 X)) :=
  representableZariskiStackMap_hasRepresentableProperty
    (@Smooth ⊓ @Surjective) (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- The identity structural morphism of every representable stack is locally
of finite presentation on all actual fiber schemes. -/
theorem representableZariskiStackMap_id_isLocallyOfFinitePresentation
    (X : Scheme.{u}) :
    StackMorphism.IsLocallyOfFinitePresentation
      (representableZariskiStackMap (𝟙 X)) :=
  representableZariskiStackMap_hasRepresentableProperty
    @LocallyOfFinitePresentation (𝟙 X) inferInstance

/-- A scheme-theoretic open immersion induces an open immersion of its
representable big-Zariski stacks, checked on the actual pullback schemes. -/
theorem representableZariskiStackMap_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    StackMorphism.IsOpenImmersion (representableZariskiStackMap f) :=
  representableZariskiStackMap_hasRepresentableProperty
    @AlgebraicGeometry.IsOpenImmersion f inferInstance

/-! ## Diagonal representability and big-Zariski presentations -/

/-- A scheme representing the isomorphisms between the pullbacks of two
objects of a stack.  The equivalence is the pointwise Yoneda universal
property of the representing object over the test scheme. -/
structure StackInGroupoids.DiagonalFiberRepresentation
    (F : StackInGroupoids Scheme.{u} Scheme.zariskiTopology)
    {S : Scheme.{u}} (x y : F.presheaf.obj (.mk (op S))) where
  /-- The scheme of isomorphisms over `S`. -/
  representing : Over S
  /-- Arrows to the representing scheme classify actual isomorphisms after
  pullback. -/
  isomorphismEquiv (T : Over S) :
    (T ⟶ representing) ≃
      (((F.presheaf.map T.hom.op.toLoc).toFunctor.obj x) ≅
        ((F.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
      )

/-- A stack has representable diagonal when every pair of objects has an
actual scheme representing its isomorphism functor. -/
class StackInGroupoids.HasRepresentableDiagonal
    (F : StackInGroupoids Scheme.{u} Scheme.zariskiTopology) : Prop where
  representation {S : Scheme.{u}}
    (x y : F.presheaf.obj (.mk (op S))) :
    Nonempty
      (AlgebraicGeometry.StackInGroupoids.DiagonalFiberRepresentation F x y)

/-- For a representable stack, the diagonal fiber over two maps `x,y : S ⟶ X`
is the scheme-theoretic equalizer of those maps. -/
def representableZariskiDiagonalFiberRepresentation
    {X S : Scheme.{u}} (x y : Discrete (S ⟶ X)) :
    AlgebraicGeometry.StackInGroupoids.DiagonalFiberRepresentation
      (representableZariskiStack X) x y where
  representing := Over.mk (equalizer.ι x.as y.as)
  isomorphismEquiv T :=
    { toFun := fun a ↦ Discrete.eqToIso (by
        have ha : a.left ≫ equalizer.ι x.as y.as = T.hom := a.w
        calc
          T.hom ≫ x.as = (a.left ≫ equalizer.ι x.as y.as) ≫ x.as :=
            congrArg (fun k ↦ k ≫ x.as) ha.symm
          _ = a.left ≫ (equalizer.ι x.as y.as ≫ x.as) := Category.assoc ..
          _ = a.left ≫ (equalizer.ι x.as y.as ≫ y.as) :=
            congrArg (fun k ↦ a.left ≫ k) (equalizer.condition x.as y.as)
          _ = (a.left ≫ equalizer.ι x.as y.as) ≫ y.as := (Category.assoc ..).symm
          _ = T.hom ≫ y.as := congrArg (fun k ↦ k ≫ y.as) ha)
      invFun := fun e ↦ Over.homMk
        (equalizer.lift T.hom (Discrete.eq_of_hom e.hom))
        (equalizer.lift_ι T.hom (Discrete.eq_of_hom e.hom))
      left_inv := fun a ↦ by
        apply CostructuredArrow.hom_ext
        change equalizer.lift T.hom _ = a.left
        apply equalizer.hom_ext
        rw [equalizer.lift_ι]
        exact a.w.symm
      right_inv := fun e ↦ by
        apply Iso.ext
        apply Subsingleton.elim }

instance representableZariskiStack_hasRepresentableDiagonal
    (X : Scheme.{u}) :
    AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
      (representableZariskiStack X) where
  representation x y :=
    ⟨representableZariskiDiagonalFiberRepresentation x y⟩

/-- A provisional big-Zariski stack presentation: effective Zariski descent,
a diagonal represented by schemes, and a scheme atlas whose every fiber is
represented by a smooth-surjective scheme morphism.

This is not called `AlgebraicStack`: the standard notion requires fppf descent
or an equivalent étale formulation, and usually asks for the diagonal to be
representable by algebraic spaces. -/
structure ZariskiStackPresentation where
  /-- The underlying big-Zariski stack in groupoids. -/
  toStackInGroupoids : StackInGroupoids Scheme.{u} Scheme.zariskiTopology
  /-- The diagonal is represented by schemes via its isomorphism functors.
  The scheme-level representability is explicit because it is stronger than
  the usual algebraic-space diagonal condition. -/
  schemeDiagonal : AlgebraicGeometry.StackInGroupoids.HasRepresentableDiagonal
    toStackInGroupoids
  /-- The scheme presenting the stack. -/
  atlasScheme : Scheme.{u}
  /-- The atlas morphism from the corresponding representable stack. -/
  atlas : StackMorphism (representableZariskiStack atlasScheme)
    toStackInGroupoids
  /-- Every base change of the atlas is an actual smooth-surjective scheme
  morphism. -/
  atlasSmoothSurjective : StackMorphism.IsSmoothSurjective atlas

/-- Every representable big-Zariski stack has a Zariski presentation using its
identity atlas and its scheme-theoretic equalizer diagonal. -/
def representableZariskiStackPresentation (X : Scheme.{u}) :
    ZariskiStackPresentation where
  toStackInGroupoids := representableZariskiStack X
  schemeDiagonal := inferInstance
  atlasScheme := X
  atlas := representableZariskiStackMap (𝟙 X)
  atlasSmoothSurjective :=
    representableZariskiStackMap_id_isSmoothSurjective X

/-- A big-Zariski stack presentation locally of finite presentation over a
base scheme, expressed by an actual stack morphism whose every fiber has a
locally-finite-presentation representing scheme morphism. -/
structure ZariskiStackPresentationOver (S : Scheme.{u}) where
  /-- The underlying big-Zariski presentation. -/
  toZariskiStackPresentation : ZariskiStackPresentation
  /-- Its structural morphism to the representable stack of the base. -/
  structureMorphism : StackMorphism
    toZariskiStackPresentation.toStackInGroupoids
      (representableZariskiStack S)
  /-- Local finite presentation is checked on all scheme representatives of
  the structural morphism. -/
  locallyOfFinitePresentation :
    StackMorphism.IsLocallyOfFinitePresentation structureMorphism

/-- A locally finitely presented scheme morphism gives a locally finitely
presented big-Zariski presentation over the target.  All fiber representatives
are the actual scheme fiber products. -/
def representableZariskiStackPresentationOver {X S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFinitePresentation p] :
    ZariskiStackPresentationOver S where
  toZariskiStackPresentation := representableZariskiStackPresentation X
  structureMorphism := representableZariskiStackMap p
  locallyOfFinitePresentation :=
    representableZariskiStackMap_hasRepresentableProperty
      @LocallyOfFinitePresentation p inferInstance

/-- A concrete positive-dimensional supported case: the representable
affine-line stack has a Zariski presentation locally of finite presentation
over every base scheme. -/
def affineLineZariskiStackPresentationOver (S : Scheme.{u}) :
    ZariskiStackPresentationOver S :=
  representableZariskiStackPresentationOver
    (𝔸(ULift.{u} (Fin 1); S) ↘ S)

end

end AlgebraicGeometry
