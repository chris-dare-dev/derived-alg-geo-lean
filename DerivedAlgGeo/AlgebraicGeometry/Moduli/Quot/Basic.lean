/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.IsomorphismClasses
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB

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
claimed. This operation is `ModuleQuotient.pullbackVia`: a quotient of `G` pulled back along a
morphism and read on any module sheaf identified with the pullback of `G`, with the coherences of
that identification against the unit and composition comparisons of pullback
(`ModuleQuotient.pullbackViaId`, `ModuleQuotient.pullbackViaComp`). Isomorphism classes of
quotients in any full subcategory form a `u`-small type
(`ModuleQuotient.small_isIsomorphicSetoid`).  A presentation can also be read through an
epimorphism into its source (`ModuleQuotient.precomp`), and every module sheaf has the zero
quotient (`ModuleQuotient.toZero`).

The Quot functor built from these presentations is `quotFunctor` in
`Moduli/Quot/Functor.lean`; representability is Mathlib's Yoneda
`Functor.RepresentableBy`, not a structure on this carrier.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite
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

namespace Scheme.Modules

/-- Pulling back along a morphism equal to the identity, read through the composition
comparison, is the comparison for `φ' = φ`. -/
lemma pullbackCongr_comp_pullbackId {Y Z : Scheme.{u}} (φ : Y ⟶ Z) {b : Y ⟶ Y}
    (hb : b = 𝟙 Y) {φ' : Y ⟶ Z} (w : φ' = b ≫ φ) (M : Z.Modules) :
    (pullbackCongr w).hom.app M ≫ (pullbackComp b φ).inv.app M ≫
      (pullbackCongr hb).hom.app _ ≫ (pullbackId Y).hom.app _ =
      (pullbackCongr (w.trans (by rw [hb, Category.id_comp]))).hom.app M := by
  subst hb w
  have h := NatTrans.congr_app (pseudofunctor_right_unitality φ) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  simpa [pullbackCongr] using h

set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphisms for pullback along a composite agree with those along its two
factors. -/
lemma pullbackCongr_comp_assoc {Y₂ Y₁ Y₀ Z : Scheme.{u}} (a : Y₂ ⟶ Y₁) (b : Y₁ ⟶ Y₀)
    {c : Y₂ ⟶ Y₀} (hc : a ≫ b = c) (φ₀ : Y₀ ⟶ Z) {φ₁ : Y₁ ⟶ Z} {φ₂ : Y₂ ⟶ Z}
    (w₁ : φ₁ = b ≫ φ₀) (w₂ : φ₂ = a ≫ φ₁) (w₃ : φ₂ = c ≫ φ₀) (M : Z.Modules) :
    ((pullbackCongr w₂).hom.app M ≫ (pullbackComp a φ₁).inv.app M) ≫
      (Scheme.Modules.pullback a).map
        ((pullbackCongr w₁).hom.app M ≫ (pullbackComp b φ₀).inv.app M) ≫
        (pullbackComp a b).hom.app _ ≫ (pullbackCongr hc).hom.app _ =
      (pullbackCongr w₃).hom.app M ≫ (pullbackComp c φ₀).inv.app M := by
  subst hc w₁ w₂
  have h := NatTrans.congr_app (pseudofunctor_associativity a b φ₀) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
  rw [← cancel_mono ((pullbackComp (a ≫ b) φ₀).hom.app M)]
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc, eqToHom_refl, Iso.inv_hom_id_app] at h ⊢
  exact h

end Scheme.Modules

namespace ModuleQuotient

section BaseChange

open Scheme.Modules

variable {Y Y' Y'' : Scheme.{u}} {G : Y.Modules} {G' : Y'.Modules} {G'' : Y''.Modules}

/-- A quotient of `G` pulled back along `b : Y' ⟶ Y` and read on `G'` through `e`. -/
abbrev pullbackVia (b : Y' ⟶ Y) (e : G' ≅ (Scheme.Modules.pullback b).obj G)
    (q : ModuleQuotient G) : ModuleQuotient G' :=
  (q.pullback b).precomp e.hom

/-- `pullbackVia` sends isomorphic quotients to isomorphic quotients. -/
def pullbackViaIso (b : Y' ⟶ Y) (e : G' ≅ (Scheme.Modules.pullback b).obj G)
    {q r : ModuleQuotient G} (i : q ≅ r) : pullbackVia b e q ≅ pullbackVia b e r :=
  ModuleQuotient.isoMk ((Scheme.Modules.pullback b).mapIso
    ((ModuleQuotient.targetFunctor G).mapIso i)) (by
    change (e.hom ≫ (Scheme.Modules.pullback b).map q.hom) ≫
      (Scheme.Modules.pullback b).map i.hom.right = e.hom ≫ (Scheme.Modules.pullback b).map r.hom
    rw [Category.assoc, ← Functor.map_comp, i.hom.comm])

/-- Along the identity, read through an identification that is the unitor of pullback,
`pullbackVia` returns the quotient it started with. -/
def pullbackViaId {b : Y ⟶ Y} (hb : b = 𝟙 Y)
    (e : G ≅ (Scheme.Modules.pullback b).obj G)
    (he : e.hom ≫ (pullbackCongr hb).hom.app G ≫ (pullbackId Y).hom.app G = 𝟙 G)
    (q : ModuleQuotient G) : pullbackVia b e q ≅ q :=
  ModuleQuotient.isoMk ((pullbackCongr hb).app q.target ≪≫ (pullbackId Y).app q.target) (by
    change (e.hom ≫ (Scheme.Modules.pullback b).map q.hom) ≫
      (pullbackCongr hb).hom.app q.target ≫ (pullbackId Y).hom.app q.target = q.hom
    have h₁ := (pullbackCongr hb).hom.naturality q.hom
    have h₂ := (pullbackId Y).hom.naturality q.hom
    simp only [Functor.id_map] at h₂
    simp only [Category.assoc]
    rw [reassoc_of% h₁, h₂, reassoc_of% he])

/-- Pulling back along `a` then `b` is pulling back along `a ≫ b`, when the identifications of
the three sources with pullbacks of `G` are compatible with the compositor of pullback. -/
def pullbackViaComp (a : Y'' ⟶ Y') (b : Y' ⟶ Y) {c : Y'' ⟶ Y} (hc : a ≫ b = c)
    (e₁ : G' ≅ (Scheme.Modules.pullback b).obj G)
    (e₂ : G'' ≅ (Scheme.Modules.pullback a).obj G')
    (e₃ : G'' ≅ (Scheme.Modules.pullback c).obj G)
    (he : e₂.hom ≫ (Scheme.Modules.pullback a).map e₁.hom ≫ (pullbackComp a b).hom.app G ≫
      (pullbackCongr hc).hom.app G = e₃.hom)
    (q : ModuleQuotient G) : pullbackVia a e₂ (pullbackVia b e₁ q) ≅ pullbackVia c e₃ q :=
  ModuleQuotient.isoMk ((pullbackComp a b).app q.target ≪≫ (pullbackCongr hc).app q.target) (by
    change (e₂.hom ≫ (Scheme.Modules.pullback a).map (e₁.hom ≫
      (Scheme.Modules.pullback b).map q.hom)) ≫ (pullbackComp a b).hom.app q.target ≫
        (pullbackCongr hc).hom.app q.target = e₃.hom ≫ (Scheme.Modules.pullback c).map q.hom
    have h₁ := (pullbackComp a b).hom.naturality q.hom
    have h₂ := (pullbackCongr hc).hom.naturality q.hom
    simp only [Functor.comp_map] at h₁
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₁, h₂, ← he]
    simp only [Category.assoc])

end BaseChange


/-- Isomorphism classes of quotient presentations of a module sheaf, in any full subcategory,
form a `u`-small type: sending a quotient `G ⟶ Q` to the subobject `op Q ⟶ op G` is injective, and
`Y.Modules` is co-well-powered. -/
instance small_isIsomorphicSetoid {Y : Scheme.{u}} {G : Y.Modules}
    (P : ObjectProperty (ModuleQuotient G)) :
    Small.{u} (Quotient (isIsomorphicSetoid P.FullSubcategory)) := by
  let φ : Quotient (isIsomorphicSetoid P.FullSubcategory) → Subobject (op G) :=
    Quotient.lift (fun r ↦ Subobject.mk r.obj.hom.op) fun r s ⟨e⟩ ↦ by
      let t : r.obj.target ≅ s.obj.target :=
        (ModuleQuotient.targetFunctor G).mapIso (P.ι.mapIso e)
      refine Subobject.mk_eq_mk_of_comm _ _ t.symm.op (Quiver.Hom.unop_inj ?_)
      simp only [Iso.op_hom, Iso.symm_hom, unop_comp, Quiver.Hom.unop_op]
      rw [Iso.comp_inv_eq]
      exact ((P.ι.map e.hom).comm).symm
  refine small_of_injective (f := φ) fun x y h ↦ ?_
  induction x using Quotient.inductionOn with | h r => ?_
  induction y using Quotient.inductionOn with | h s => ?_
  let i := Subobject.isoOfMkEqMk _ _ h
  have w : i.hom ≫ s.obj.hom.op = r.obj.hom.op := Subobject.ofMkLEMk_comp _
  exact Quotient.sound ⟨(P.isoMk (ModuleQuotient.isoMk i.unop
    (Quiver.Hom.op_inj (by simpa using w)))).symm⟩

end ModuleQuotient

end

end AlgebraicGeometry
