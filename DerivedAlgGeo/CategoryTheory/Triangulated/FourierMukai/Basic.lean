/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Kernel functors between triangulated categories

A Fourier--Mukai transform is assembled from a correspondence.  Geometrically,
for the projections `p : X × Y ⟶ X` and `q : X × Y ⟶ Y` and a kernel
`P ∈ D(X × Y)`, the transform is

`Φ_P(E) = Rq_*(Lp^* E ⊗^L P)`.

This file records the three functors of that composite and nothing else about
them: a `Correspondence` supplies a source functor in the role of `Lp^*`, a
bifunctor in the role of `⊗^L`, and a target functor in the role of `Rq_*`.
The transform with a chosen kernel is their composite, and `IsKernelFunctor`
is the property of being isomorphic to such a composite.

Following `StabilityCondition.Families.ExactPullback`, exactness is an explicit
hypothesis rather than a conclusion.  The `Correspondence` structure asks for
no triangulated structure at all; the section that concludes the transform is
triangulated states the hypotheses on the three constituents.

## What this file does not assert

The geometric content of Fourier--Mukai theory is exactly the part that is
absent here.  This file does not

* construct any of the three functors, or assume a scheme, a product, a
  derived category, or a derived functor anywhere;
* assume `pull` and `push` are adjoint, in either order, or supply a
  projection formula relating `tensor` to either of them;
* assume `tensor` is monoidal, symmetric, associative, or unital, or that it
  is exact in either variable;
* convolve two kernels or prove that a composite of two transforms is a
  transform;
* prove that a kernel is determined by its transform, or that any particular
  class of functors consists of kernel functors (Orlov's theorem);
* connect a kernel functor to a stability condition, a t-structure, or a
  Grothendieck group.

The last of those is deliberate placement rather than difficulty: the
Grothendieck-group statements need `Triangulated.K₀`, which lives under
`StabilityCondition.Foundation`, and importing it here would point a generic
module at the stability track.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v v' v'' u u' u''

section Data

variable (𝒳 : Type u) (𝒴 : Type u') (𝒵 : Type u'')
  [Category.{v} 𝒳] [Category.{v'} 𝒴] [Category.{v''} 𝒵]

/-- The functorial data a Fourier--Mukai transform is built from, with no
kernel chosen and no compatibility between the three functors assumed.

`𝒵` plays the role of the derived category of the product, `pull` the role of
`Lp^*`, `tensor` the role of `⊗^L` on the product, and `push` the role of
`Rq_*`.  A caller supplies all three; nothing here constructs them. -/
structure Correspondence where
  /-- The functor in the role of derived pullback along the first projection. -/
  pull : 𝒳 ⥤ 𝒵
  /-- The bifunctor in the role of the derived tensor product on the product
  category.  `tensor.obj K` is the twist by the kernel `K`. -/
  tensor : 𝒵 ⥤ 𝒵 ⥤ 𝒵
  /-- The functor in the role of derived pushforward along the second
  projection. -/
  push : 𝒵 ⥤ 𝒴

end Data

namespace Correspondence

variable {𝒳 : Type u} {𝒴 : Type u'} {𝒵 : Type u''}
  [Category.{v} 𝒳] [Category.{v'} 𝒴] [Category.{v''} 𝒵]

/-- The Fourier--Mukai transform of `C` with kernel `K`: pull back, twist by
`K`, push forward.  An `abbrev` so that instance search sees the composite and
derives the shift and triangulation instances from those of the three
constituents. -/
abbrev transform (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) : 𝒳 ⥤ 𝒴 :=
  C.pull ⋙ C.tensor.obj K ⋙ C.push

@[simp]
theorem transform_obj (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) (E : 𝒳) :
    (C.transform K).obj E = C.push.obj ((C.tensor.obj K).obj (C.pull.obj E)) :=
  rfl

@[simp]
theorem transform_map (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) {E F : 𝒳} (f : E ⟶ F) :
    (C.transform K).map f =
      C.push.map ((C.tensor.obj K).map (C.pull.map f)) :=
  rfl

/-- A morphism of kernels induces a natural transformation of transforms. This
  is the categorical map needed before a cone of kernels can be transported;
  it uses only the functoriality already present in the abstract correspondence
  and makes no claim that a suitable kernel morphism or cone exists. -/
def transformMap (C : Correspondence 𝒳 𝒴 𝒵) {K L : 𝒵} (f : K ⟶ L) :
    C.transform K ⟶ C.transform L :=
  Functor.whiskerLeft C.pull (Functor.whiskerRight (C.tensor.map f) C.push)

@[simp]
theorem transformMap_app (C : Correspondence 𝒳 𝒴 𝒵) {K L : 𝒵} (f : K ⟶ L)
    (E : 𝒳) :
    (C.transformMap f).app E = C.push.map ((C.tensor.map f).app (C.pull.obj E)) :=
  rfl

@[simp]
theorem transformMap_id (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) :
    C.transformMap (𝟙 K) = 𝟙 (C.transform K) := by
  simp [transformMap]

@[simp]
theorem transformMap_comp (C : Correspondence 𝒳 𝒴 𝒵) {K L M : 𝒵}
    (f : K ⟶ L) (g : L ⟶ M) :
    C.transformMap (f ≫ g) = C.transformMap f ≫ C.transformMap g := by
  simp [transformMap]

/-- The Fourier--Mukai transform as a functor of its kernel.

Packaging `transform` and `transformMap` into one functor is the canonical
interface for constructions, such as dg cones, which vary the kernel.  It
also makes the identity and composition laws available through ordinary
functoriality rather than requiring each consumer to restate them. -/
def kernelTransform (C : Correspondence 𝒳 𝒴 𝒵) :
    𝒵 ⥤ (𝒳 ⥤ 𝒴) where
  obj K := C.transform K
  map f := C.transformMap f
  map_id K := C.transformMap_id K
  map_comp f g := C.transformMap_comp f g

@[simp]
theorem kernelTransform_obj (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) :
    C.kernelTransform.obj K = C.transform K := rfl

@[simp]
theorem kernelTransform_map (C : Correspondence 𝒳 𝒴 𝒵) {K L : 𝒵}
    (f : K ⟶ L) :
    C.kernelTransform.map f = C.transformMap f := rfl

/-- Evaluate the kernel-variable transform functor on one source object.
This is the exact functor whose preservation of a kernel triangle says that
the corresponding transforms form a pointwise distinguished triangle. -/
def kernelEvaluation (C : Correspondence 𝒳 𝒴 𝒵) (E : 𝒳) :
    𝒵 ⥤ 𝒴 :=
  C.kernelTransform ⋙ (evaluation 𝒳 𝒴).obj E

@[simp]
theorem kernelEvaluation_obj (C : Correspondence 𝒳 𝒴 𝒵) (E : 𝒳)
    (K : 𝒵) :
    (C.kernelEvaluation E).obj K = (C.transform K).obj E := rfl

@[simp]
theorem kernelEvaluation_map (C : Correspondence 𝒳 𝒴 𝒵) (E : 𝒳)
    {K L : 𝒵} (f : K ⟶ L) :
    (C.kernelEvaluation E).map f = (C.transformMap f).app E := rfl

/-- Isomorphic kernels give isomorphic transforms.  This is the only
comparison between two kernels that holds with no hypothesis on `tensor`; the
converse is the hard direction and is not asserted anywhere in this file. -/
def transformMapIso (C : Correspondence 𝒳 𝒴 𝒵) {K L : 𝒵} (e : K ≅ L) :
    C.transform K ≅ C.transform L :=
  Functor.isoWhiskerLeft C.pull
    (Functor.isoWhiskerRight (C.tensor.mapIso e) C.push)

@[simp]
theorem transformMapIso_hom (C : Correspondence 𝒳 𝒴 𝒵) {K L : 𝒵} (e : K ≅ L) :
    (C.transformMapIso e).hom = C.transformMap e.hom := by
  rfl

@[simp]
theorem transformMapIso_refl (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) :
    C.transformMapIso (Iso.refl K) = Iso.refl (C.transform K) := by
  simp [transformMapIso]

/-- A functor is a *kernel functor* for `C` when it is isomorphic to the
transform of some kernel.  The kernel is existentially quantified and the
witnessing isomorphism is only `Nonempty`: this is the property, not a choice
of kernel.

That every functor in a suitable setting has this property is the theorem
Fourier--Mukai theory is aimed at.  It is stated nowhere in this file. -/
def IsKernelFunctor (C : Correspondence 𝒳 𝒴 𝒵) (Φ : 𝒳 ⥤ 𝒴) : Prop :=
  ∃ K : 𝒵, Nonempty (Φ ≅ C.transform K)

/-- A transform is a kernel functor, witnessed by its own kernel. -/
theorem isKernelFunctor_transform (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵) :
    C.IsKernelFunctor (C.transform K) :=
  ⟨K, ⟨Iso.refl _⟩⟩

/-- Being a kernel functor is invariant under natural isomorphism. -/
theorem IsKernelFunctor.of_natIso {C : Correspondence 𝒳 𝒴 𝒵} {Φ Ψ : 𝒳 ⥤ 𝒴}
    (h : C.IsKernelFunctor Φ) (e : Φ ≅ Ψ) : C.IsKernelFunctor Ψ := by
  obtain ⟨K, ⟨f⟩⟩ := h
  exact ⟨K, ⟨e.symm ≪≫ f⟩⟩

/-- A named kernel for a kernel functor, together with its isomorphism.  The
choice is not canonical, and no result in this file depends on which kernel is
returned. -/
noncomputable def IsKernelFunctor.kernel {C : Correspondence 𝒳 𝒴 𝒵} {Φ : 𝒳 ⥤ 𝒴}
    (h : C.IsKernelFunctor Φ) : 𝒵 :=
  h.choose

/-- The isomorphism witnessing that `Φ` is the transform of the chosen
kernel. -/
noncomputable def IsKernelFunctor.iso {C : Correspondence 𝒳 𝒴 𝒵} {Φ : 𝒳 ⥤ 𝒴}
    (h : C.IsKernelFunctor Φ) : Φ ≅ C.transform h.kernel :=
  h.choose_spec.some

end Correspondence

section Exact

open Correspondence

variable {𝒳 : Type u} {𝒴 : Type u'} {𝒵 : Type u''}
  [Category.{v} 𝒳] [Category.{v'} 𝒴] [Category.{v''} 𝒵]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒵] [HasShift 𝒵 ℤ] [Preadditive 𝒵]
  [∀ n : ℤ, (shiftFunctor 𝒵 n).Additive] [Pretriangulated 𝒵]

variable (C : Correspondence 𝒳 𝒴 𝒵) (K : 𝒵)
  [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]

variable [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
  [C.push.IsTriangulated]

/-- The transform is triangulated as soon as its three constituents are.

Exactness of the twist `tensor.obj K` is a hypothesis on the chosen kernel,
not a property of `C`: the geometric statement it stands for is that `− ⊗^L P`
is exact, which for a general kernel needs the derived tensor product rather
than the underived one. -/
theorem transform_isTriangulated : (C.transform K).IsTriangulated := inferInstance

/-- A transform of triangulated constituents is additive.  Immediate from
`transform_isTriangulated`, and stated separately because `Additive` is the
hypothesis the Grothendieck-group API asks for. -/
theorem transform_additive : (C.transform K).Additive := inferInstance

end Exact

end CategoryTheory.Triangulated.FourierMukai
