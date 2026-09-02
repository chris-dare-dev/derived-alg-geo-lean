/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullback

/-!
# Quotient presentations of module sheaves

This file defines the elementary input to a Quot construction: an actual
epimorphism from a fixed module sheaf.  Morphisms are maps of targets commuting
with the quotient arrows.  Pullback of module sheaves preserves these
presentations because it preserves finite colimits, so quotient presentations
have a genuine base-change operation before any representability theorem is
claimed.

No scheme named `QuotScheme` is introduced here.  Representability, when it
is available, is a separate Yoneda universal property.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open scoped ZeroObject

noncomputable section

universe u

/-- An epimorphic presentation `F ⟶ Q` of a quotient module sheaf. -/
structure ModuleQuotient {X : Scheme.{u}} (F : X.Modules) where
  /-- The quotient module sheaf. -/
  target : X.Modules
  /-- The quotient arrow. -/
  hom : F ⟶ target
  /-- The quotient arrow is an epimorphism. -/
  isEpi : Epi hom

namespace ModuleQuotient

variable {X Y : Scheme.{u}} {F : X.Modules}

instance hom_isEpi (q : ModuleQuotient F) : Epi q.hom :=
  q.isEpi

/-- A morphism of quotient presentations is a commuting map of targets. -/
structure Hom (q r : ModuleQuotient F) where
  /-- The map between quotient targets. -/
  right : q.target ⟶ r.target
  /-- Compatibility with the two quotient arrows. -/
  comm : q.hom ≫ right = r.hom := by aesop_cat

namespace Hom

variable {q r s : ModuleQuotient F}

@[ext]
theorem ext (f g : Hom q r) (h : f.right = g.right) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      cases h
      rfl

end Hom

instance category : Category (ModuleQuotient F) where
  Hom := Hom
  id q := ⟨𝟙 q.target, by simp⟩
  comp f g := ⟨f.right ≫ g.right, by
    rw [← Category.assoc, f.comm, g.comm]⟩
  id_comp f := Hom.ext _ _ (by simp)
  comp_id f := Hom.ext _ _ (by simp)
  assoc f g h := Hom.ext _ _ (by simp)

@[simp]
theorem id_right (q : ModuleQuotient F) :
    (𝟙 q : q ⟶ q).right = 𝟙 q.target :=
  rfl

@[simp]
theorem comp_right {q r s : ModuleQuotient F}
    (f : q ⟶ r) (g : r ⟶ s) :
    (f ≫ g).right = f.right ≫ g.right :=
  rfl

/-- The forgetful functor from quotient presentations to their targets. -/
def targetFunctor (F : X.Modules) : ModuleQuotient F ⥤ X.Modules where
  obj q := q.target
  map f := f.right

/-- Pull a quotient presentation back along a scheme morphism. -/
def pullback (f : X ⟶ Y) {G : Y.Modules} (q : ModuleQuotient G) :
    ModuleQuotient ((Scheme.Modules.pullback f).obj G) where
  target := (Scheme.Modules.pullback f).obj q.target
  hom := (Scheme.Modules.pullback f).map q.hom
  isEpi := by
    letI : Epi q.hom := q.isEpi
    infer_instance

/-- Pullback acts functorially on the categories of quotient
presentations. -/
def pullbackFunctor (f : X ⟶ Y) (G : Y.Modules) :
    ModuleQuotient G ⥤
      ModuleQuotient ((Scheme.Modules.pullback f).obj G) where
  obj q := q.pullback f
  map g := ⟨(Scheme.Modules.pullback f).map g.right, by
    simpa only [pullback, Functor.map_comp] using
      congrArg (Scheme.Modules.pullback f).map g.comm⟩
  map_id q := Hom.ext _ _ (by simp [pullback])
  map_comp g h := Hom.ext _ _ (by simp [pullback])

/-- The identity arrow presents a module sheaf as a quotient of itself. -/
def identity (F : X.Modules) : ModuleQuotient F where
  target := F
  hom := 𝟙 F
  isEpi := inferInstance

/-- The zero module sheaf has its canonical identity quotient. -/
def zero (X : Scheme.{u}) : ModuleQuotient (0 : X.Modules) :=
  identity 0

/-- Pullback of the identity quotient is canonically isomorphic to the
identity quotient of the pulled-back module. -/
def pullbackIdentityIso (f : X ⟶ Y) (G : Y.Modules) :
    (identity G).pullback f ≅ identity ((Scheme.Modules.pullback f).obj G) := by
  refine ⟨⟨𝟙 _, by simp [identity, pullback]⟩,
    ⟨𝟙 _, by simp [identity, pullback]⟩, ?_, ?_⟩
  · exact Hom.ext _ _ (by simp [pullback, identity])
  · exact Hom.ext _ _ (by simp [pullback, identity])

/-- In particular, the zero quotient is preserved by every scheme base
change, up to the canonical pullback comparison for zero module sheaves. -/
def pullbackZeroIso (f : X ⟶ Y) :
    (zero Y).pullback f ≅
      identity ((Scheme.Modules.pullback f).obj (0 : Y.Modules)) :=
  pullbackIdentityIso f 0

end ModuleQuotient

end

end AlgebraicGeometry
