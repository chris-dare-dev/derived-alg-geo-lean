/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Quotient presentations of module sheaves

This file defines the elementary input to a Quot construction: an actual
epimorphism from a fixed module sheaf.  Morphisms are maps of targets commuting
with the quotient arrows; since quotient arrows are epimorphisms there is at most
one between two presentations (`ModuleQuotient.instSubsingletonHom`), and an
isomorphism of targets compatible with the arrows is an isomorphism
(`ModuleQuotient.isoMk`).  Pullback of module sheaves preserves these
presentations because it preserves finite colimits, so quotient presentations
have a genuine base-change operation before any representability theorem is
claimed.  A presentation can also be read through an epimorphism into its source
(`ModuleQuotient.precomp`), and every module sheaf has the zero quotient
(`ModuleQuotient.toZero`).

The Quot functor built from these presentations is `quotFunctor` in
`Moduli/Quot/Functor.lean`; representability is Mathlib's Yoneda
`Functor.RepresentableBy`, not a structure on this carrier.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
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

/-- Quotient arrows are epimorphisms, so there is at most one morphism between two quotient
presentations of the same module sheaf. -/
instance instSubsingletonHom (q r : ModuleQuotient F) : Subsingleton (q ⟶ r) :=
  ⟨fun f g ↦ Hom.ext _ _ ((cancel_epi q.hom).1 (f.comm.trans g.comm.symm))⟩

/-- An isomorphism of targets that commutes with the quotient arrows is an isomorphism of
quotient presentations. -/
@[simps]
def isoMk {q r : ModuleQuotient F} (e : q.target ≅ r.target) (w : q.hom ≫ e.hom = r.hom) :
    q ≅ r where
  hom := ⟨e.hom, w⟩
  inv := ⟨e.inv, by rw [← w, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

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

/-- Precompose a quotient presentation of `F` with an epimorphism `G ⟶ F`, giving a quotient
presentation of `G` with the same target. -/
@[simps]
def precomp {G : X.Modules} (f : G ⟶ F) [Epi f] (q : ModuleQuotient F) : ModuleQuotient G where
  target := q.target
  hom := f ≫ q.hom
  isEpi := epi_comp f q.hom

/-- The quotient `F ⟶ 0` onto the zero module sheaf. -/
@[simps]
def toZero (F : X.Modules) : ModuleQuotient F where
  target := 0
  hom := 0
  isEpi := (isZero_zero _).epi _

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
