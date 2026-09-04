/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Categorical base change for triangulated fibers

The numerical family interfaces initially indexed unrelated triangulated
categories by a type. This file records the next layer needed for families: a
contravariant Cat-valued pseudofunctor, triangulated pullback functors, and
their induced action on the repository-owned triangulated Grothendieck group.

The pseudofunctor supplies identity and composition coherence by natural
isomorphisms. An ordinary strict functor is admitted through `ofFunctor`; it is
a specialization, not the general root. No geometric origin is asserted: the
base is an abstract category, not a scheme, and this file constructs neither
derived pullback nor transport of slicings. Relative Harder--Narasimhan
structures, openness, and boundedness remain separate geometric obligations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v w

namespace CategoryTheory.Triangulated.Families

variable {B : Type u} [Category.{v} B]

/-- A contravariant category-valued family whose fibers and transition
functors carry the structures used by ordinary stability conditions.

For `f : s ⟶ t`, the pseudofunctorial map of `fibers` is interpreted as
pullback from the fiber over `t` to the fiber over `s`. -/
structure TriangulatedFiberFamily where
  /-- The underlying contravariant category-valued family. -/
  fibers : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{w, w}
  /-- Every fiber is preadditive. -/
  fiberPreadditive : ∀ b, Preadditive (fibers.obj (.mk (Opposite.op b)))
  /-- Every fiber has a zero object. -/
  fiberZero : ∀ b, HasZeroObject (fibers.obj (.mk (Opposite.op b)))
  /-- Every fiber has an integer shift. -/
  fiberShift : ∀ b, HasShift.{w, w, 0} (fibers.obj (.mk (Opposite.op b))) ℤ
  /-- Every shift functor is additive. -/
  fiberShiftAdditive : ∀ b (n : ℤ),
    (shiftFunctor (fibers.obj (.mk (Opposite.op b))) n).Additive
  /-- Every fiber is pretriangulated. -/
  fiberPretriangulated : ∀ b, Pretriangulated (fibers.obj (.mk (Opposite.op b)))
  /-- Every pullback functor is additive. -/
  pullAdditive : ∀ {s t} (f : s ⟶ t),
    ((fibers.map f.op.toLoc).toFunctor).Additive
  /-- Every pullback functor commutes with the integer shift. -/
  pullCommShift : ∀ {s t} (f : s ⟶ t),
    ((fibers.map f.op.toLoc).toFunctor).CommShift ℤ
  /-- Every pullback functor preserves distinguished triangles. -/
  pullTriangulated : ∀ {s t} (f : s ⟶ t),
    ((fibers.map f.op.toLoc).toFunctor).IsTriangulated

namespace TriangulatedFiberFamily

variable (F : TriangulatedFiberFamily (B := B))

attribute [instance] fiberPreadditive fiberZero fiberShift fiberShiftAdditive
  fiberPretriangulated pullAdditive pullCommShift pullTriangulated

/-- The triangulated category over one object of the base. -/
abbrev Fiber (b : B) : Type w := F.fibers.obj (.mk (Opposite.op b))

/-- The pullback functor attached to a base morphism. -/
abbrev pull {s t : B} (f : s ⟶ t) : Functor (F.Fiber t) (F.Fiber s) :=
  (F.fibers.map f.op.toLoc).toFunctor

/-- The pseudofunctorial unit identifying pullback along an identity with the
identity functor on the fiber. -/
def pullIdIso (b : B) : F.pull (𝟙 b) ≅ 𝟭 (F.Fiber b) := by
  simpa [pull] using Cat.Hom.toNatIso
    (F.fibers.mapId (.mk (Opposite.op b)))

/-- The pseudofunctorial compositor identifying pullback along a composite
with the corresponding iterated pullback. -/
def pullCompIso {r s t : B} (f : r ⟶ s) (g : s ⟶ t) :
    F.pull (f ≫ g) ≅ F.pull g ⋙ F.pull f := by
  simpa [pull] using Cat.Hom.toNatIso
    (F.fibers.mapComp g.op.toLoc f.op.toLoc)

/-- Pullback on the repository-owned triangulated Grothendieck groups. -/
def pullK₀ {s t : B} (f : s ⟶ t) : K₀ (F.Fiber t) →+ K₀ (F.Fiber s) :=
  K₀.map (F.pull f)

@[simp]
theorem pullK₀_of {s t : B} (f : s ⟶ t) (E : F.Fiber t) :
    F.pullK₀ f (K₀.of _ E) = K₀.of _ ((F.pull f).obj E) := by
  simp [pullK₀]

@[simp]
theorem pullK₀_id (b : B) :
    F.pullK₀ (𝟙 b) = AddMonoidHom.id (K₀ (F.Fiber b)) := by
  change K₀.map (F.pull (𝟙 b)) = AddMonoidHom.id (K₀ (F.Fiber b))
  rw [K₀.map_congr (F.pullIdIso b), K₀.map_id]

@[simp]
theorem pullK₀_comp {r s t : B} (f : r ⟶ s) (g : s ⟶ t) :
    F.pullK₀ (f ≫ g) = (F.pullK₀ f).comp (F.pullK₀ g) := by
  change K₀.map (F.pull (f ≫ g)) =
    (K₀.map (F.pull f)).comp (K₀.map (F.pull g))
  rw [K₀.map_congr (F.pullCompIso f g), K₀.map_comp]

/-- Promote an ordinary strict contravariant functor to a triangulated fiber
family. The resulting pseudofunctor has equality-induced unit and compositor
isomorphisms. -/
def ofFunctor (fibers : Functor Bᵒᵖ Cat.{w, w})
    (fiberPreadditive : ∀ b, Preadditive (fibers.obj (Opposite.op b)))
    (fiberZero : ∀ b, HasZeroObject (fibers.obj (Opposite.op b)))
    (fiberShift : ∀ b, HasShift.{w, w, 0} (fibers.obj (Opposite.op b)) ℤ)
    (fiberShiftAdditive : ∀ b (n : ℤ),
      (shiftFunctor (fibers.obj (Opposite.op b)) n).Additive)
    (fiberPretriangulated : ∀ b, Pretriangulated (fibers.obj (Opposite.op b)))
    (pullAdditive : ∀ {s t} (f : s ⟶ t),
      ((fibers.map f.op).toFunctor).Additive)
    (pullCommShift : ∀ {s t} (f : s ⟶ t),
      ((fibers.map f.op).toFunctor).CommShift ℤ)
    (pullTriangulated : ∀ {s t} (f : s ⟶ t),
      ((fibers.map f.op).toFunctor).IsTriangulated) :
    TriangulatedFiberFamily (B := B) where
  fibers := fibers.toPseudofunctor'
  fiberPreadditive := fiberPreadditive
  fiberZero := fiberZero
  fiberShift := fiberShift
  fiberShiftAdditive := fiberShiftAdditive
  fiberPretriangulated := fiberPretriangulated
  pullAdditive := pullAdditive
  pullCommShift := pullCommShift
  pullTriangulated := pullTriangulated

/-- The constant category-valued family. -/
def constant (B : Type u) [Category.{v} B]
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] : TriangulatedFiberFamily (B := B) :=
  ofFunctor (B := B)
    (fibers := (Functor.const Bᵒᵖ).obj (Cat.of C))
    (fiberPreadditive := fun _ ↦ by change Preadditive C; infer_instance)
    (fiberZero := fun _ ↦ by change HasZeroObject C; infer_instance)
    (fiberShift := fun _ ↦ by change HasShift C ℤ; infer_instance)
    (fiberShiftAdditive := fun _ n ↦ by
      change (shiftFunctor C n).Additive
      infer_instance)
    (fiberPretriangulated := fun _ ↦ by change Pretriangulated C; infer_instance)
    (pullAdditive := fun _ ↦ by change (Functor.id C).Additive; infer_instance)
    (pullCommShift := fun _ ↦ by change (Functor.id C).CommShift ℤ; infer_instance)
    (pullTriangulated := fun _ ↦ by
      change (Functor.id C).IsTriangulated
      infer_instance)

/-- Class maps to one common group which are invariant under every
categorical pullback. -/
structure CompatibleClassMaps (V : Type*) [AddCommGroup V]
    (classMap : ∀ b, K₀ (F.Fiber b) →+ V) : Prop where
  /-- Pullback does not change the common numerical class. -/
  pull_compatible : ∀ {s t} (f : s ⟶ t) (x : K₀ (F.Fiber t)),
    classMap s (F.pullK₀ f x) = classMap t x

namespace CompatibleClassMaps

variable {F} {V : Type*} [AddCommGroup V]
  {classMap : ∀ b, K₀ (F.Fiber b) →+ V}

/-- Compatibility on Grothendieck groups specializes to the class of an
actual pulled-back object. -/
theorem class_pull (h : F.CompatibleClassMaps V classMap)
    {s t : B} (f : s ⟶ t) (E : F.Fiber t) :
    classMap s (K₀.of _ ((F.pull f).obj E)) = classMap t (K₀.of _ E) := by
  rw [← F.pullK₀_of f E]
  exact h.pull_compatible f _

/-- A single class map gives compatible maps on the constant family. -/
theorem constant (C : Type w) [Category.{w} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (V : Type*) [AddCommGroup V] (v₀ : K₀ C →+ V) :
    (TriangulatedFiberFamily.constant B C).CompatibleClassMaps V (fun _ ↦ v₀) := by
  constructor
  intro s t f x
  have h : (TriangulatedFiberFamily.constant B C).pullK₀ f =
      AddMonoidHom.id (K₀ C) := by
    ext E
    rw [TriangulatedFiberFamily.pullK₀_of]
    rfl
  rw [h]
  rfl

end CompatibleClassMaps

end TriangulatedFiberFamily

end CategoryTheory.Triangulated.Families
