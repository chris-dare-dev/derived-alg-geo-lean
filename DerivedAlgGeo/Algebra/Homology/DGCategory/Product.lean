/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.Prod
import DerivedAlgGeo.Algebra.Homology.DGCategory.Basic

/-!
# The product of two dg categories

Objects are pairs, and the Hom-complex between two pairs is the degreewise
product of the two Hom-complexes, with componentwise differential, identity and
composition.

Unlike the opposite, no sign enters: the product is a limit construction and
every axiom holds componentwise. The work is entirely in getting Lean to see
the Hom-objects as products. `AddCommGrpCat.of (_ × _)`'s carrier is opaque to
instance search, so two techniques carry the file:

* **Build at plain types.** `prodComp` is stated for arbitrary
  `AddCommGroup`s and then applied to the carriers. Term elaboration unifies up
  to defeq, so this works where instance search does not.
* **Restate the projection lemmas where `simp` will match them.** `Prod.fst_add`
  does not fire on `(dgHom X Y).X p`, because the operation carries the
  carrier's instance rather than `Prod`'s. The `rfl` lemmas below say the same
  thing at the type the goals actually have — and the type has to be exactly
  that one, not the `prodComplex` it unfolds to.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct

/-- The differential of the degreewise product, named separately: a proof in a
later field of a structure instance cannot see an earlier field given inline,
so `d` has to exist before `shape` and `d_comp_d'` can mention it. -/
def prodD (K L : CochainComplex AddCommGrpCat.{v} ℤ) (p q : ℤ) :
    AddCommGrpCat.of ((K.X p) × (L.X p)) ⟶ AddCommGrpCat.of ((K.X q) × (L.X q)) :=
  AddCommGrpCat.ofHom
    (((K.d p q).hom.comp (AddMonoidHom.fst _ _)).prod ((L.d p q).hom.comp (AddMonoidHom.snd _ _)))

/-- The degreewise product of two cochain complexes of abelian groups. -/
@[simps]
def prodComplex (K L : CochainComplex AddCommGrpCat.{v} ℤ) :
    CochainComplex AddCommGrpCat.{v} ℤ where
  X p := AddCommGrpCat.of ((K.X p) × (L.X p))
  d := prodD K L
  shape p q h := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    rintro ⟨x, y⟩
    apply Prod.ext <;> simp [prodD, K.shape p q h, L.shape p q h]
  d_comp_d' p q r _ _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    rintro ⟨x, y⟩
    apply Prod.ext <;>
      simp [prodD, ← AddCommGrpCat.comp_apply, K.d_comp_d p q r, L.d_comp_d p q r]

/-!
## Building the instance at plain types

The obstacle the first attempt hit is that `((prodComplex K L).X p)` is
`AddCommGrpCat.of (_ × _)`, whose carrier instance *search* will not see
through. Term elaboration is a different matter: it unifies up to defeq, so a
helper stated at plain types with `AddCommGroup` instances applies to those
carriers without complaint.

So the composition is built once, generically, and then applied. Nothing below
asks instance search to recognise a carrier as a product.
-/

section Plain

variable {A₁ A₂ B₁ B₂ M₁ M₂ : Type*} [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup M₁] [AddCommGroup M₂]

/-- Componentwise biadditive composition on a pair of products. -/
def prodComp (c₁ : A₁ →+ B₁ →+ M₁) (c₂ : A₂ →+ B₂ →+ M₂) :
    (A₁ × A₂) →+ (B₁ × B₂) →+ (M₁ × M₂) :=
  AddMonoidHom.mk' (fun a =>
      AddMonoidHom.prod ((c₁ a.1).comp (AddMonoidHom.fst B₁ B₂))
        ((c₂ a.2).comp (AddMonoidHom.snd B₁ B₂)))
    (fun a a' => by ext b <;> simp)

@[simp]
lemma prodComp_apply (c₁ : A₁ →+ B₁ →+ M₁) (c₂ : A₂ →+ B₂ →+ M₂)
    (a : A₁ × A₂) (b : B₁ × B₂) :
    prodComp c₁ c₂ a b = (c₁ a.1 b.1, c₂ a.2 b.2) := rfl

end Plain

variable (C : Type u) (D : Type u') [DGCategory.{v} C] [DGCategory.{v} D]

namespace DGCategory

/-- The product of two dg categories. -/
instance prodStruct : DGCategoryStruct.{v} (C × D) where
  dgHom X Y := prodComplex (dgHom X.1 Y.1) (dgHom X.2 Y.2)
  dgId X := (dgId X.1, dgId X.2)
  dgComp p q r h := prodComp (dgComp p q r h) (dgComp p q r h)

variable {C D}

@[simp]
lemma prod_d_apply {X Y : C × D} (p q : ℤ)
    (f : ((dgHom X.1 Y.1).X p) × ((dgHom X.2 Y.2).X p)) :
    ((dgHom (C := C × D) X Y).d p q).hom f =
      ((((dgHom X.1 Y.1).d p q).hom f.1), (((dgHom X.2 Y.2).d p q).hom f.2)) := rfl

/-! `Prod.fst_add` and friends do not fire on these goals: the operations carry
the carrier's `AddCommGroup` instance, which is definitionally but not
syntactically `Prod`'s, and `simp` matches syntactically. These `rfl` lemmas say
the same thing at the type the goals actually have.

The type matters twice over. Stating them at `(prodComplex K L).X p` is not
enough — the goals are about `(dgHom X Y).X p` for the product instance, which
is `prodComplex …` definitionally and not syntactically, so those versions miss
as well. They have to be stated exactly here. -/

@[simp]
lemma dgProd_fst_add {X Y : C × D} {p : ℤ} (a b : (dgHom (C := C × D) X Y).X p) :
    (a + b).1 = a.1 + b.1 := rfl

@[simp]
lemma dgProd_snd_add {X Y : C × D} {p : ℤ} (a b : (dgHom (C := C × D) X Y).X p) :
    (a + b).2 = a.2 + b.2 := rfl

@[simp]
lemma dgProd_fst_units_smul {X Y : C × D} {p : ℤ} (c : ℤˣ)
    (a : (dgHom (C := C × D) X Y).X p) : (c • a).1 = c • a.1 := rfl

@[simp]
lemma dgProd_snd_units_smul {X Y : C × D} {p : ℤ} (c : ℤˣ)
    (a : (dgHom (C := C × D) X Y).X p) : (c • a).2 = c • a.2 := rfl

@[simp]
lemma prod_dgId (X : C × D) :
    dgId (C := C × D) X = (dgId X.1, dgId X.2) := rfl

@[simp]
lemma prod_dgComp_apply {X Y Z : C × D} (p q r : ℤ) (h : p + q = r)
    (f : ((dgHom X.1 Y.1).X p) × ((dgHom X.2 Y.2).X p))
    (g : ((dgHom Y.1 Z.1).X q) × ((dgHom Y.2 Z.2).X q)) :
    dgComp (C := C × D) p q r h f g =
      (dgComp p q r h f.1 g.1, dgComp p q r h f.2 g.2) := rfl

/-- The product dg category. Every axiom holds componentwise and no sign
enters, so each proof is `Prod.ext` followed by the corresponding axiom in each
factor. -/
instance prod : DGCategory.{v} (C × D) where
  dgComp_assoc p q r pq qr pqr hpq hqr hpqr f g h := by
    subst hpq; subst hqr; subst hpqr
    apply Prod.ext <;> simp [prod_dgComp_apply, dgComp_assoc]
  dgId_comp p f := by
    apply Prod.ext <;> simp [prod_dgComp_apply, prod_dgId, dgId_comp]
  dgComp_id p f := by
    apply Prod.ext <;> simp [prod_dgComp_apply, prod_dgId, dgComp_id]
  dgId_cocycle X := by
    simp only [prod_d_apply, prod_dgId, dgId_cocycle]
    rfl
  dgComp_leibniz p q r r' h hr f g := by
    apply Prod.ext <;> simp [prod_d_apply, prod_dgComp_apply, dgComp_leibniz p q r r' h hr,
      dgProd_fst_add, dgProd_snd_add, dgProd_fst_units_smul, dgProd_snd_units_smul]

end DGCategory

end CategoryTheory
