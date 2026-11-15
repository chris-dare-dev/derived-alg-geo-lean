/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Module objects of a linear category

Let `k` be a commutative ring, `A` a `k`-linear category and `R` a `k`-algebra. An `R`-module
object of `A` is an object `E` together with a morphism of `k`-algebras `R →ₐ[k] End E`, and a
morphism of module objects is a morphism of `A` commuting with the actions. This is the category
`A_R` of Alper, Halpern-Leistner and Heinloth [AHLH, Definition 7.3], who take it from Artin and
Zhang [AZ, §B2]; here it is `ModuleObject k A R`.

## Main definitions

* `CategoryTheory.ModuleObject k A R`: the category of `R`-module objects of `A`.
* `CategoryTheory.ModuleObject.forget k A R`: the forgetful functor to `A`; for `R = k` it is an
  equivalence, `ModuleObject.forgetEquivalence`.
* `CategoryTheory.ModuleObject.restrict φ`: for `φ : R₁ →ₐ[k] R₂`, the restriction functor
  `A_{R₂} ⥤ A_{R₁}`, written `φ_*` by AHLH.

## Main results

* `ModuleObject k A R` is preadditive, `R`-linear when `R` is commutative, and abelian when `A` is
  [AHLH, §7.1, citing AZ, Prop. B2.2].
* The forgetful functor creates all limits and colimits, so `A_R` has the limits and colimits that
  `A` has, computed on the underlying objects.
* `restrict φ` is faithful, preserves every limit and colimit that exists in `A` (so it is exact
  and commutes with filtered colimits), and is full when `φ` is surjective [AHLH, §7.1, citing
  AZ, Prop. B2.3].

The numbering of [AZ] is quoted from [AHLH, §7.1] and has not been checked against the text of
[AZ].

## References

* [AHLH] J. Alper, D. Halpern-Leistner, J. Heinloth, *Existence of moduli spaces for algebraic
  stacks*, arXiv:1812.01128v5, §7.1.
* [AZ] M. Artin, J. J. Zhang, *Abstract Hilbert schemes*, Algebr. Represent. Theory 4 (2001),
  305–394.
-/

universe u v w u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable (k : Type u) [CommSemiring k] (A : Type v) [Category.{w} A]

section

variable [Preadditive A] [Linear k A]

/-- An `R`-module object of a `k`-linear category `A`: an object of `A` together with a morphism
of `k`-algebras from `R` to its endomorphisms [AHLH, Definition 7.3]. -/
structure ModuleObject (R : Type u₁) [Semiring R] [Algebra k R] where
  /-- The underlying object. -/
  obj : A
  /-- The action of `R` on the underlying object. -/
  act : R →ₐ[k] End obj

namespace ModuleObject

variable {k A}

section Category

variable {R : Type u₁} [Semiring R] [Algebra k R]

/-- A morphism of `R`-module objects: a morphism of the underlying objects commuting with the
actions. -/
@[ext]
structure Hom (X Y : ModuleObject k A R) where
  /-- The underlying morphism. -/
  hom : X.obj ⟶ Y.obj
  comm (r : R) : (X.act r).asHom ≫ hom = hom ≫ (Y.act r).asHom := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity morphism of a module object. -/
@[simps]
def Hom.id (X : ModuleObject k A R) : Hom X X where
  hom := 𝟙 X.obj

/-- The composition of two morphisms of module objects. -/
@[simps]
def Hom.comp {X Y Z : ModuleObject k A R} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  hom := f.hom ≫ g.hom

instance : Category (ModuleObject k A R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {X Y : ModuleObject k A R} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
lemma id_hom (X : ModuleObject k A R) : Hom.hom (𝟙 X) = 𝟙 X.obj := rfl

@[simp, reassoc]
lemma comp_hom {X Y Z : ModuleObject k A R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Construct an isomorphism of module objects from an isomorphism of the underlying objects that
commutes with the actions. -/
@[simps]
def isoMk {X Y : ModuleObject k A R} (e : X.obj ≅ Y.obj)
    (he : ∀ r, (X.act r).asHom ≫ e.hom = e.hom ≫ (Y.act r).asHom) : X ≅ Y where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, fun r => by rw [e.comp_inv_eq, Category.assoc, he, e.inv_hom_id_assoc]⟩

variable (k A R) in
/-- The forgetful functor from `R`-module objects to `A`. -/
@[simps]
def forget : ModuleObject k A R ⥤ A where
  obj X := X.obj
  map f := f.hom

instance : (forget k A R).Faithful where
  map_injective h := Hom.ext h

instance : (forget k A R).ReflectsIsomorphisms where
  reflects f hf :=
    have : IsIso f.hom := hf
    (isoMk (asIso f.hom) f.comm).isIso_hom

end Category

section Base

/-- An object of `A` with its unique structure of `k`-module object. -/
abbrev ofObj (X : A) : ModuleObject k A k where
  obj := X
  act := Algebra.ofId k (End X)

@[simp]
lemma ofObj_act_asHom (X : A) (c : k) : ((ofObj X).act c).asHom = c • 𝟙 X :=
  rfl

variable (k A) in
/-- Every object of `A` is a `k`-module object, in a unique way. -/
@[simps]
def ofObjFunctor : A ⥤ ModuleObject k A k where
  obj X := ofObj X
  map {X Y} f := ⟨f, fun c => show (c • 𝟙 X) ≫ f = f ≫ (c • 𝟙 Y) by simp⟩

variable (k A) in
/-- `k`-module objects of `A` are the objects of `A`: `A_k = A` [AHLH, §7.1]. -/
@[simps]
def forgetEquivalence : ModuleObject k A k ≌ A where
  functor := forget k A k
  inverse := ofObjFunctor k A
  unitIso := NatIso.ofComponents
    (fun E => isoMk (Iso.refl E.obj) fun c => by
      change (E.act c).asHom ≫ 𝟙 E.obj = 𝟙 E.obj ≫ ((Algebra.ofId k (End E.obj)) c).asHom
      rw [Subsingleton.elim E.act (Algebra.ofId k _), Category.comp_id, Category.id_comp])
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _

end Base

section Preadditive

variable {R : Type u₁} [Semiring R] [Algebra k R] {X Y : ModuleObject k A R}

instance : Zero (X ⟶ Y) := ⟨⟨0, by simp⟩⟩
instance : Add (X ⟶ Y) := ⟨fun f g => ⟨f.hom + g.hom, by simp⟩⟩
instance : Neg (X ⟶ Y) := ⟨fun f => ⟨-f.hom, by simp⟩⟩
instance : Sub (X ⟶ Y) := ⟨fun f g => ⟨f.hom - g.hom, by simp⟩⟩
instance : SMul ℕ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, by simp⟩⟩
instance : SMul ℤ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, by simp⟩⟩

@[simp] lemma zero_hom : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
@[simp] lemma neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
@[simp] lemma sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
@[simp] lemma nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
@[simp] lemma zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup Hom.hom (fun _ _ => Hom.ext) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Preadditive (ModuleObject k A R) where

instance : (forget k A R).Additive where

end Preadditive

section Linear

variable {R : Type u₁} [CommSemiring R] [Algebra k R] {X Y : ModuleObject k A R}

lemma act_comm (X : ModuleObject k A R) (r s : R) :
    (X.act r).asHom ≫ (X.act s).asHom = (X.act s).asHom ≫ (X.act r).asHom := by
  rw [← End.mul_asHom, ← End.mul_asHom, ← map_mul, ← map_mul, mul_comm]

instance : SMul R (X ⟶ Y) :=
  ⟨fun r f => ⟨(X.act r).asHom ≫ f.hom, fun s => by
    rw [reassoc_of% act_comm X s r, Hom.comm, Category.assoc]⟩⟩

@[simp] lemma smul_hom (r : R) (f : X ⟶ Y) : (r • f).hom = (X.act r).asHom ≫ f.hom := rfl

lemma smul_hom_eq_hom_comp (r : R) (f : X ⟶ Y) : (r • f).hom = f.hom ≫ (Y.act r).asHom := f.comm r

instance : Module R (X ⟶ Y) where
  one_smul f := by ext; simp
  mul_smul r s f := by ext; simp [act_comm Y r s]
  smul_zero r := by ext; simp
  smul_add r f g := by ext; simp
  add_smul r s f := by ext; simp
  zero_smul f := by ext; simp

/-- The category of `R`-module objects is `R`-linear [AHLH, §7.1]. -/
instance : Linear R (ModuleObject k A R) where
  smul_comp _ _ _ r f g := by ext; simp
  comp_smul _ _ _ f r g := by ext; simp

end Linear

section Limits

variable {R : Type u₁} [Semiring R] [Algebra k R] {J : Type u₂} [Category.{u₃} J]
  (K : J ⥤ ModuleObject k A R)

/-- The action of `r` on the diagram underlying a diagram of module objects. -/
@[simps]
def diagramAct (r : R) : K ⋙ forget k A R ⟶ K ⋙ forget k A R where
  app j := ((K.obj j).act r).asHom
  naturality _ _ f := ((K.map f).comm r).symm

/-- Endomorphisms of an object `X` with a jointly epimorphic family `p j : P j ⟶ X` from
module objects form a `k`-algebra action as soon as each `a r` is compatible with the `p j`. -/
def actOfJointlyEpi {ι : Type u₂} {X : A} {P : ι → ModuleObject k A R} (p : ∀ j, (P j).obj ⟶ X)
    (hp : ∀ {f g : X ⟶ X}, (∀ j, p j ≫ f = p j ≫ g) → f = g) (a : R → (X ⟶ X))
    (ha : ∀ r j, p j ≫ a r = ((P j).act r).asHom ≫ p j) : R →ₐ[k] End X where
  toFun r := .of (a r)
  map_one' := End.ext <| hp fun j => by simp [ha]
  map_mul' r s := End.ext <| hp fun j => by simp [reassoc_of% ha, ha]
  map_zero' := End.ext <| hp fun j => by simp [ha]
  map_add' r s := End.ext <| hp fun j => by simp [ha]
  commutes' c := End.ext <| hp fun j => by simp [ha, Algebra.algebraMap_eq_smul_one]

@[simp]
lemma actOfJointlyEpi_apply_asHom {ι : Type u₂} {X : A} {P : ι → ModuleObject k A R}
    (p : ∀ j, (P j).obj ⟶ X) (hp : ∀ {f g : X ⟶ X}, (∀ j, p j ≫ f = p j ≫ g) → f = g)
    (a : R → (X ⟶ X)) (ha : ∀ r j, p j ≫ a r = ((P j).act r).asHom ≫ p j) (r : R) :
    (actOfJointlyEpi p hp a ha r).asHom = a r :=
  rfl

/-- Endomorphisms of an object `X` with a jointly monomorphic family `p j : X ⟶ P j` to module
objects form a `k`-algebra action as soon as each `a r` is compatible with the `p j`. -/
def actOfJointlyMono {ι : Type u₂} {X : A} {P : ι → ModuleObject k A R} (p : ∀ j, X ⟶ (P j).obj)
    (hp : ∀ {f g : X ⟶ X}, (∀ j, f ≫ p j = g ≫ p j) → f = g) (a : R → (X ⟶ X))
    (ha : ∀ r j, a r ≫ p j = p j ≫ ((P j).act r).asHom) : R →ₐ[k] End X where
  toFun r := .of (a r)
  map_one' := End.ext <| hp fun j => by simp [ha]
  map_mul' r s := End.ext <| hp fun j => by simp [ha, reassoc_of% ha]
  map_zero' := End.ext <| hp fun j => by simp [ha]
  map_add' r s := End.ext <| hp fun j => by simp [ha]
  commutes' c := End.ext <| hp fun j => by simp [ha, Algebra.algebraMap_eq_smul_one]

@[simp]
lemma actOfJointlyMono_apply_asHom {ι : Type u₂} {X : A} {P : ι → ModuleObject k A R}
    (p : ∀ j, X ⟶ (P j).obj) (hp : ∀ {f g : X ⟶ X}, (∀ j, f ≫ p j = g ≫ p j) → f = g)
    (a : R → (X ⟶ X)) (ha : ∀ r j, a r ≫ p j = p j ≫ ((P j).act r).asHom) (r : R) :
    (actOfJointlyMono p hp a ha r).asHom = a r :=
  rfl

variable {K}

/-- A colimit cocone of the underlying diagram, with the action induced on its apex. -/
@[simps]
def liftedCocone {c : Cocone (K ⋙ forget k A R)} (hc : IsColimit c) : Cocone K where
  pt :=
    { obj := c.pt
      act := actOfJointlyEpi (P := K.obj) c.ι.app (fun h => hc.hom_ext h)
        (fun r => hc.map c (diagramAct K r)) (fun r j => hc.ι_map c (diagramAct K r) j) }
  ι :=
    { app j := ⟨c.ι.app j, fun r => (hc.ι_map c (diagramAct K r) j).symm⟩
      naturality _ _ f := Hom.ext ((c.w f).trans (Category.comp_id _).symm) }

/-- The lifted cocone is a colimit cocone. -/
def isColimitLiftedCocone {c : Cocone (K ⋙ forget k A R)} (hc : IsColimit c) :
    IsColimit (liftedCocone hc) where
  desc s := ⟨hc.desc ((forget k A R).mapCocone s), fun r => hc.hom_ext fun j =>
    (hc.ι_map_assoc c (diagramAct K r) j (hc.desc ((forget k A R).mapCocone s))).trans <|
      (congrArg (((K.obj j).act r).asHom ≫ ·) (hc.fac ((forget k A R).mapCocone s) j)).trans <|
        ((s.ι.app j).comm r).trans
          (hc.fac_assoc ((forget k A R).mapCocone s) j (s.pt.act r).asHom).symm⟩
  fac _ j := Hom.ext (hc.fac _ j)
  uniq s m hm := Hom.ext (hc.uniq ((forget k A R).mapCocone s) m.hom
    fun j => congrArg Hom.hom (hm j))

/-- A limit cone of the underlying diagram, with the action induced on its apex. -/
@[simps]
def liftedCone {c : Cone (K ⋙ forget k A R)} (hc : IsLimit c) : Cone K where
  pt :=
    { obj := c.pt
      act := actOfJointlyMono (P := K.obj) c.π.app (fun h => hc.hom_ext h)
        (fun r => hc.map c (diagramAct K r)) (fun r j => hc.map_π c (diagramAct K r) j) }
  π :=
    { app j := ⟨c.π.app j, fun r => hc.map_π c (diagramAct K r) j⟩
      naturality _ _ f := Hom.ext ((Category.id_comp _).trans (c.w f).symm) }

/-- The lifted cone is a limit cone. -/
def isLimitLiftedCone {c : Cone (K ⋙ forget k A R)} (hc : IsLimit c) :
    IsLimit (liftedCone hc) where
  lift s := ⟨hc.lift ((forget k A R).mapCone s), fun r => hc.hom_ext fun j =>
    (Category.assoc (s.pt.act r).asHom (hc.lift ((forget k A R).mapCone s)) (c.π.app j)).trans <|
      (congrArg ((s.pt.act r).asHom ≫ ·) (hc.fac ((forget k A R).mapCone s) j)).trans <|
        ((s.π.app j).comm r).trans <|
          (hc.fac_assoc ((forget k A R).mapCone s) j ((K.obj j).act r).asHom).symm.trans <|
            (congrArg (hc.lift ((forget k A R).mapCone s) ≫ ·)
              (hc.map_π c (diagramAct K r) j)).symm.trans (Category.assoc _ _ _).symm⟩
  fac _ j := Hom.ext (hc.fac _ j)
  uniq s m hm := Hom.ext (hc.uniq ((forget k A R).mapCone s) m.hom
    fun j => congrArg Hom.hom (hm j))

variable (k A R)

/-- The forgetful functor creates all colimits. -/
instance : CreatesColimitsOfSize.{u₃, u₂} (forget k A R) where
  CreatesColimitsOfShape :=
    { CreatesColimit := createsColimitOfReflectsIso fun _ hc =>
        { liftedCocone := liftedCocone hc
          validLift := Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)
          makesColimit := isColimitLiftedCocone hc } }

/-- The forgetful functor creates all limits. -/
instance : CreatesLimitsOfSize.{u₃, u₂} (forget k A R) where
  CreatesLimitsOfShape :=
    { CreatesLimit := createsLimitOfReflectsIso fun _ hc =>
        { liftedCone := liftedCone hc
          validLift := Cone.ext (Iso.refl _) (fun _ => (Category.id_comp _).symm)
          makesLimit := isLimitLiftedCone hc } }

variable (J)

instance [HasColimitsOfShape J A] : HasColimitsOfShape J (ModuleObject k A R) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget k A R)

instance [HasLimitsOfShape J A] : HasLimitsOfShape J (ModuleObject k A R) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget k A R)

instance [HasColimitsOfSize.{u₃, u₂} A] : HasColimitsOfSize.{u₃, u₂} (ModuleObject k A R) where
  has_colimits_of_shape _ _ := inferInstance

instance [HasLimitsOfSize.{u₃, u₂} A] : HasLimitsOfSize.{u₃, u₂} (ModuleObject k A R) where
  has_limits_of_shape _ _ := inferInstance

instance [HasFiniteColimits A] : HasFiniteColimits (ModuleObject k A R) where
  out _ _ _ := inferInstance

instance [HasFiniteLimits A] : HasFiniteLimits (ModuleObject k A R) where
  out _ _ _ := inferInstance

end Limits

section Restrict

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [Algebra k R₁] [Algebra k R₂] [Algebra k R₃]

/-- Restriction of scalars along a morphism of `k`-algebras `φ : R₁ →ₐ[k] R₂`, written `φ_*` by
AHLH: the action of `R₂` is precomposed with `φ` [AHLH, §7.1]. -/
@[simps]
def restrict (φ : R₁ →ₐ[k] R₂) : ModuleObject k A R₂ ⥤ ModuleObject k A R₁ where
  obj X := ⟨X.obj, X.act.comp φ⟩
  map f := ⟨f.hom, fun r => f.comm (φ r)⟩

variable (φ : R₁ →ₐ[k] R₂)

/-- Restriction does not change the underlying object. -/
def restrictCompForget : restrict φ ⋙ forget k A R₁ ≅ forget k A R₂ :=
  Iso.refl _

instance : (restrict (A := A) φ).Faithful :=
  Functor.Faithful.of_comp_iso (restrictCompForget φ)

instance : (restrict (A := A) φ).Additive where

/-- Restriction along a surjective morphism of algebras is full [AHLH, §7.1, citing AZ,
Prop. B2.3]. -/
lemma full_restrict (hφ : Function.Surjective φ) : (restrict (A := A) φ).Full where
  map_surjective {X Y} f := ⟨⟨f.hom, fun r => by
    obtain ⟨s, rfl⟩ := hφ r
    exact f.comm s⟩, rfl⟩

variable {J : Type u₃} [Category.{w} J]

/-- Restriction preserves every colimit that exists in `A`; in particular it is right exact and
commutes with filtered colimits [AHLH, §7.1, citing AZ, Prop. B2.3]. -/
instance [HasColimitsOfShape J A] : PreservesColimitsOfShape J (restrict (A := A) φ) :=
  have : PreservesColimitsOfShape J (restrict φ ⋙ forget k A R₁) :=
    inferInstanceAs (PreservesColimitsOfShape J (forget k A R₂))
  preservesColimitsOfShape_of_reflects_of_preserves (restrict φ) (forget k A R₁)

/-- Restriction preserves every limit that exists in `A`; in particular it is left exact
[AHLH, §7.1, citing AZ, Prop. B2.3]. -/
instance [HasLimitsOfShape J A] : PreservesLimitsOfShape J (restrict (A := A) φ) :=
  have : PreservesLimitsOfShape J (restrict φ ⋙ forget k A R₁) :=
    inferInstanceAs (PreservesLimitsOfShape J (forget k A R₂))
  preservesLimitsOfShape_of_reflects_of_preserves (restrict φ) (forget k A R₁)

variable (k A R₁) in
/-- Restriction along the identity is the identity. -/
@[simps!]
def restrictId : restrict (A := A) (AlgHom.id k R₁) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction along a composite is the composite of the restrictions. -/
@[simps!]
def restrictComp (ψ : R₂ →ₐ[k] R₃) :
    restrict (A := A) ψ ⋙ restrict φ ≅ restrict (ψ.comp φ) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Restrict

end ModuleObject

end

namespace ModuleObject

section Abelian

variable {k A} [Abelian A] [Linear k A] {R : Type u₁} [Semiring R] [Algebra k R]

/-- The category of `R`-module objects of an abelian category is abelian [AHLH, §7.1, citing
AZ, Prop. B2.2]. Kernels and cokernels are computed on the underlying objects. -/
noncomputable instance : Abelian (ModuleObject k A R) := by
  have : ∀ {X Y : ModuleObject k A R} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    have : IsIso ((forget k A R).map (Abelian.coimageImageComparison f)) := by
      exact (Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso (forget k A R) f).hom).2 inferInstance
    exact isIso_of_reflects_iso _ (forget k A R)
  exact Abelian.ofCoimageImageComparisonIsIso

end Abelian

end ModuleObject

end CategoryTheory
