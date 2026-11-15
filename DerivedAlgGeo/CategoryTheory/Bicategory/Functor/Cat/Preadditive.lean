/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ULift

/-!
# Strong transformations into a pseudofunctor with preadditive fibres

Let `G : B ⥤ᵖ Cat` be a pseudofunctor whose fibres are preadditive and whose transition
functors are additive. For every pseudofunctor `F`, the category of strong transformations
`F ⟶ G`, with modifications as morphisms (Mathlib's `Pseudofunctor.StrongTrans.homCategory`),
is preadditive: modifications are added componentwise.

## Main definitions

* `CategoryTheory.Pseudofunctor.StrongTrans.homOfApp`: the modification with given components,
  from the naturality of its components at each object of the fibres.
* `CategoryTheory.Pseudofunctor.StrongTrans.preadditive`: the preadditive structure, as a scoped
  instance alongside `Pseudofunctor.StrongTrans.homCategory`.
* `CategoryTheory.Pseudofunctor.ulift.preadditive_obj`: the fibres of `F.ulift` are
  preadditive where those of `F` are, and its transition functors are additive where those of
  `F` are.

## Implementation notes

The group structure on modifications is pulled back along the injective map sending a
modification to its family of components, with `Function.Injective.addCommGroup`. Each
operation is built with `homOfApp`, whose naturality condition is checked with the additivity
of the transition functors of `G`.

## Tags

pseudofunctor, strong transformation, modification, preadditive category
-/

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe w₁ w₂ w v v' u u'

namespace StrongTrans

open scoped StrongTrans

variable {B : Type u} [Bicategory.{w, v} B] {F G : B ⥤ᵖ Cat.{v', u'}}

/-- The modification `η ⟶ θ` with components `app`, from the naturality of `app` at each object
of the fibres of `F`. -/
def homOfApp {η θ : F ⟶ G} (app : ∀ a, (η.app a).toFunctor ⟶ (θ.app a).toFunctor)
    (naturality : ∀ ⦃a b : B⦄ (f : a ⟶ b) (x : F.obj a),
      (app b).app ((F.map f).toFunctor.obj x) ≫ (θ.naturality f).hom.toNatTrans.app x =
        (η.naturality f).hom.toNatTrans.app x ≫ (G.map f).toFunctor.map ((app a).app x)) :
    η ⟶ θ :=
  .of
    { app a := Cat.Hom₂.ofNatTrans (app a)
      naturality f := by
        ext x
        exact naturality f x }

/-- The components of `CategoryTheory.Pseudofunctor.StrongTrans.homOfApp app _` are `app`. -/
@[simp]
lemma homOfApp_as_app_toNatTrans {η θ : F ⟶ G}
    (app : ∀ a, (η.app a).toFunctor ⟶ (θ.app a).toFunctor) (naturality) (a : B) :
    ((homOfApp app naturality).as.app a).toNatTrans = app a :=
  rfl

/-- A modification is determined by its components. -/
lemma hom_ext' {η θ : F ⟶ G} {Γ Δ : η ⟶ θ}
    (h : ∀ a, (Γ.as.app a).toNatTrans = (Δ.as.app a).toNatTrans) : Γ = Δ :=
  homCategory.ext fun a ↦ Cat.Hom₂.ext (h a)

variable [∀ a, Preadditive (G.obj a)] [∀ ⦃a b : B⦄ (f : a ⟶ b), (G.map f).toFunctor.Additive]

section Group

variable {η θ : F ⟶ G}

/-- A family of components closed under a binary operation that commutes with every transition
functor is again a modification. -/
private lemma naturality_binop (op : ∀ ⦃a⦄, ((η.app a).toFunctor ⟶ (θ.app a).toFunctor) →
      ((η.app a).toFunctor ⟶ (θ.app a).toFunctor) → ((η.app a).toFunctor ⟶ (θ.app a).toFunctor))
    (hop : ∀ ⦃a⦄ (Γ Δ : (η.app a).toFunctor ⟶ (θ.app a).toFunctor) (x : F.obj a),
      (op Γ Δ).app x = Γ.app x + Δ.app x)
    (Γ Δ : η ⟶ θ) ⦃a b : B⦄ (f : a ⟶ b) (x : F.obj a) :
    (op (Γ.as.app b).toNatTrans (Δ.as.app b).toNatTrans).app ((F.map f).toFunctor.obj x) ≫
        (θ.naturality f).hom.toNatTrans.app x =
      (η.naturality f).hom.toNatTrans.app x ≫
        (G.map f).toFunctor.map ((op (Γ.as.app a).toNatTrans (Δ.as.app a).toNatTrans).app x) := by
  have hΓ := congrArg (fun t ↦ t.toNatTrans.app x) (Γ.as.naturality f)
  have hΔ := congrArg (fun t ↦ t.toNatTrans.app x) (Δ.as.naturality f)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at hΓ hΔ
  rw [hop, hop, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add, hΓ, hΔ]

/-- Componentwise sum of modifications. -/
instance : Add (η ⟶ θ) where
  add Γ Δ := homOfApp (fun a ↦ (Γ.as.app a).toNatTrans + (Δ.as.app a).toNatTrans)
    (naturality_binop (fun _ ↦ (· + ·)) (fun _ _ _ _ ↦ NatTrans.app_add _ _ _) Γ Δ)

/-- The zero modification. -/
instance : Zero (η ⟶ θ) where
  zero := homOfApp (fun _ ↦ 0) (fun _ _ f x ↦ by simp)

/-- Componentwise negation of modifications. -/
instance : Neg (η ⟶ θ) where
  neg Γ := homOfApp (fun a ↦ -(Γ.as.app a).toNatTrans) (fun _ _ f x ↦ by
    have h := congrArg (fun t ↦ t.toNatTrans.app x) (Γ.as.naturality f)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
    simp [h])

/-- Componentwise difference of modifications. -/
instance : Sub (η ⟶ θ) where
  sub Γ Δ := homOfApp (fun a ↦ (Γ.as.app a).toNatTrans - (Δ.as.app a).toNatTrans)
    (fun _ _ f x ↦ by
      have hΓ := congrArg (fun t ↦ t.toNatTrans.app x) (Γ.as.naturality f)
      have hΔ := congrArg (fun t ↦ t.toNatTrans.app x) (Δ.as.naturality f)
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at hΓ hΔ
      simp [Preadditive.sub_comp, Preadditive.comp_sub, hΓ, hΔ])

/-- Componentwise natural-number multiples of modifications. -/
instance : SMul ℕ (η ⟶ θ) where
  smul n Γ := homOfApp (fun a ↦ n • (Γ.as.app a).toNatTrans) (fun _ _ f x ↦ by
    have h := congrArg (fun t ↦ t.toNatTrans.app x) (Γ.as.naturality f)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
    simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Functor.map_nsmul, h])

/-- Componentwise integer multiples of modifications. -/
instance : SMul ℤ (η ⟶ θ) where
  smul n Γ := homOfApp (fun a ↦ n • (Γ.as.app a).toNatTrans) (fun _ _ f x ↦ by
    have h := congrArg (fun t ↦ t.toNatTrans.app x) (Γ.as.naturality f)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Functor.map_zsmul, h])

/-- The components of a sum of modifications. -/
@[simp]
lemma add_as_app_toNatTrans (Γ Δ : η ⟶ θ) (a : B) :
    ((Γ + Δ).as.app a).toNatTrans = (Γ.as.app a).toNatTrans + (Δ.as.app a).toNatTrans :=
  rfl

/-- The components of the zero modification. -/
@[simp]
lemma zero_as_app_toNatTrans (a : B) : ((0 : η ⟶ θ).as.app a).toNatTrans = 0 :=
  rfl

/-- The components of the negation of a modification. -/
@[simp]
lemma neg_as_app_toNatTrans (Γ : η ⟶ θ) (a : B) :
    ((-Γ).as.app a).toNatTrans = -(Γ.as.app a).toNatTrans :=
  rfl

/-- The components of a difference of modifications. -/
@[simp]
lemma sub_as_app_toNatTrans (Γ Δ : η ⟶ θ) (a : B) :
    ((Γ - Δ).as.app a).toNatTrans = (Γ.as.app a).toNatTrans - (Δ.as.app a).toNatTrans :=
  rfl

/-- The components of a natural-number multiple of a modification. -/
@[simp]
lemma nsmul_as_app_toNatTrans (n : ℕ) (Γ : η ⟶ θ) (a : B) :
    ((n • Γ).as.app a).toNatTrans = n • (Γ.as.app a).toNatTrans :=
  rfl

/-- The components of an integer multiple of a modification. -/
@[simp]
lemma zsmul_as_app_toNatTrans (n : ℤ) (Γ : η ⟶ θ) (a : B) :
    ((n • Γ).as.app a).toNatTrans = n • (Γ.as.app a).toNatTrans :=
  rfl

/-- The family of components of a modification. -/
private def components (Γ : η ⟶ θ) : ∀ a, (η.app a).toFunctor ⟶ (θ.app a).toFunctor :=
  fun a ↦ (Γ.as.app a).toNatTrans

omit [∀ a, Preadditive (G.obj a)] [∀ ⦃a b : B⦄ (f : a ⟶ b), (G.map f).toFunctor.Additive] in
private lemma components_injective : Function.Injective (components (η := η) (θ := θ)) :=
  fun _ _ h ↦ hom_ext' fun a ↦ congrFun h a

/-- Modifications between two strong transformations form an abelian group under componentwise
addition. -/
instance : AddCommGroup (η ⟶ θ) :=
  components_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Group

/-- Strong transformations `F ⟶ G` form a preadditive category when the fibres of `G` are
preadditive and its transition functors are additive. Scoped, like the category structure
`Pseudofunctor.StrongTrans.homCategory` it extends. -/
scoped instance preadditive : Preadditive (F ⟶ G) where
  add_comp _ _ _ _ _ _ := hom_ext' fun _ ↦ Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := hom_ext' fun _ ↦ Preadditive.comp_add _ _ _ _ _ _

end StrongTrans

namespace ulift

attribute [local instance] uliftCategory

variable {B₀ : Type u} [Category.{v} B₀] (F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'})

/-- The fibres of `F.ulift` are preadditive where those of `F` are: the morphisms of
`ULiftHom (ULift C)` are lifts of those of `C`, added as such. -/
instance preadditive_obj (X : LocallyDiscrete B₀) [Preadditive (F.obj X)] :
    Preadditive ((F.ulift.{w₁, w₂}).obj X) where
  homGroup a b := inferInstanceAs (AddCommGroup (ULift.{w₁}
    ((objEquivalence.{w₁, w₂} F X).inverse.obj a ⟶ (objEquivalence.{w₁, w₂} F X).inverse.obj b)))
  add_comp _ _ _ _ _ _ := ULift.ext (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := ULift.ext (Preadditive.comp_add _ _ _ _ _ _)

/-- The equivalence between a fibre of `F` and the corresponding fibre of `F.ulift` is
additive. -/
instance objEquivalence_functor_additive (X : LocallyDiscrete B₀) [Preadditive (F.obj X)] :
    (objEquivalence.{w₁, w₂} F X).functor.Additive where
  map_add := rfl

/-- The inverse of the equivalence between a fibre of `F` and the corresponding fibre of
`F.ulift` is additive. -/
instance objEquivalence_inverse_additive (X : LocallyDiscrete B₀) [Preadditive (F.obj X)] :
    (objEquivalence.{w₁, w₂} F X).inverse.Additive where
  map_add := rfl

/-- The transition functors of `F.ulift` are additive where those of `F` are. -/
instance map_additive [∀ X, Preadditive (F.obj X)] {X Y : LocallyDiscrete B₀} (f : X ⟶ Y)
    [(F.map f).toFunctor.Additive] : ((F.ulift.{w₁, w₂}).map f).toFunctor.Additive where
  map_add {_ _ φ ψ} := by
    rw [map_toFunctor_map, map_toFunctor_map, map_toFunctor_map, Functor.map_add,
      Functor.map_add, Functor.map_add]
    rfl

end ulift

end CategoryTheory.Pseudofunctor
