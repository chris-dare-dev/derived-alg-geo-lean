/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Functor

/-!
# Homogeneous natural transformations of dg functors

For dg functors `F G : C ⟶ D`, a homogeneous natural transformation of
degree `n` has components `F X ⟶ G X` of degree `n` and satisfies graded
naturality

`F f ≫ η Y = (-1)^(n * p) • (η X ≫ G f)`

for every homogeneous `f : X ⟶ Y` of degree `p`.  The sign convention is
written for this repository's diagrammatic `dgComp`.

The natural transformations of every degree form an additive subgroup of the
product of the component Hom-groups.  Packaging them that way gives the
additive structure by restriction rather than re-proving the group laws for a
large record.  The pointwise differential and vertical composition defined
below are the ingredients of the dg category of dg functors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]

/-- Families of degree-`n` components between two dg functors. -/
abbrev HomogeneousFamily (F G : DGFunctor C D) (n : ℤ) :=
  ∀ X : C, (dgHom (F.obj X) (G.obj X)).X n

/-- Graded naturality for a family of degree-`n` components.

The common result degree is quantified explicitly.  This mirrors the
repository's `dgComp p q r h` encoding and lets later Leibniz arguments choose
one fibre for all terms instead of inserting transports between associatively
or commutatively equal integer expressions. -/
def HomogeneousFamily.IsNatural {F G : DGFunctor C D} {n : ℤ}
    (η : HomogeneousFamily F G n) : Prop :=
  ∀ {X Y : C} (p r : ℤ) (hpn : p + n = r) (hnp : n + p = r)
    (f : (dgHom X Y).X p),
    dgComp p n r hpn (F.map p f) (η Y) =
      (n * p).negOnePow •
        dgComp n p r hnp (η X) (G.map p f)

/-- The additive subgroup of component families satisfying graded
naturality. -/
def homogeneousNatTransSubgroup (F G : DGFunctor C D) (n : ℤ) :
    AddSubgroup (HomogeneousFamily F G n) where
  carrier := HomogeneousFamily.IsNatural
  zero_mem' := by
    intro X Y p r hpn hnp f
    simp
  add_mem' {η θ} hη hθ := by
    intro X Y p r hpn hnp f
    rw [show (η + θ : HomogeneousFamily F G n) Y = η Y + θ Y from rfl,
      map_add, hη p r hpn hnp f, hθ p r hpn hnp f]
    rw [show (η + θ : HomogeneousFamily F G n) X = η X + θ X from rfl,
      map_add]
    simp [Units.smul_def]
  neg_mem' {η} hη := by
    intro X Y p r hpn hnp f
    rw [show (-η : HomogeneousFamily F G n) Y = -η Y from rfl,
      map_neg, hη p r hpn hnp f]
    rw [show (-η : HomogeneousFamily F G n) X = -η X from rfl,
      map_neg]
    simp [Units.smul_def]

/-- A homogeneous dg natural transformation, as the natural-family
subgroup. -/
abbrev HomogeneousNatTrans (F G : DGFunctor C D) (n : ℤ) :=
  homogeneousNatTransSubgroup F G n

namespace HomogeneousNatTrans

variable {F G H I : DGFunctor C D} {n m k : ℤ}

/-- `dgComp` is equivariant for the sign action in its first input. -/
private lemma dgComp_units_smul_left {X Y Z : D}
    (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- `dgComp` is equivariant for the sign action in its second input. -/
private lemma dgComp_units_smul_right {X Y Z : D}
    (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- The two unit laws compared in an arbitrary common result degree.

Generalizing the result index before replacing it by `p` avoids dependent
rewrites between the fibres in degrees `p + 0` and `p`. -/
private lemma dgComp_id_naturality {X Y : D}
    (p r : ℤ) (hp : p + 0 = r) (h0p : 0 + p = r)
    (f : (dgHom X Y).X p) :
    dgComp p 0 r hp f (dgId Y) =
      dgComp 0 p r h0p (dgId X) f := by
  have hr : r = p := by omega
  cases hr
  rw [dgComp_id, dgId_comp]

/-- The component of a homogeneous dg natural transformation. -/
def app (η : HomogeneousNatTrans F G n) (X : C) :
    (dgHom (F.obj X) (G.obj X)).X n :=
  η.1 X

@[simp]
theorem zero_app (X : C) : app (0 : HomogeneousNatTrans F G n) X = 0 :=
  rfl

@[simp]
theorem add_app (η θ : HomogeneousNatTrans F G n) (X : C) :
    app (η + θ) X = app η X + app θ X :=
  rfl

@[simp]
theorem neg_app (η : HomogeneousNatTrans F G n) (X : C) :
    app (-η) X = -app η X :=
  rfl

@[simp]
theorem zsmul_app (a : ℤ) (η : HomogeneousNatTrans F G n) (X : C) :
    app (a • η) X = a • app η X :=
  rfl

@[simp]
theorem units_smul_app (a : ℤˣ) (η : HomogeneousNatTrans F G n) (X : C) :
    app (a • η) X = a • app η X := by
  rw [Units.smul_def, Units.smul_def]
  rfl

/-- Graded naturality, exposed from subgroup membership. -/
theorem naturality (η : HomogeneousNatTrans F G n)
    {X Y : C} (p r : ℤ) (hpn : p + n = r) (hnp : n + p = r)
    (f : (dgHom X Y).X p) :
    dgComp p n r hpn (F.map p f) (app η Y) =
      (n * p).negOnePow •
        dgComp n p r hnp (app η X) (G.map p f) :=
  η.2 p r hpn hnp f

/-- Homogeneous transformations are equal when all components are equal. -/
@[ext]
theorem ext {η θ : HomogeneousNatTrans F G n}
    (h : ∀ X, app η X = app θ X) : η = θ := by
  apply Subtype.ext
  funext X
  exact h X

/-- The degree-zero identity dg natural transformation. -/
def id (F : DGFunctor C D) : HomogeneousNatTrans F F 0 :=
  ⟨fun X => dgId (F.obj X), by
    intro X Y p r hp h0p f
    simpa only [zero_mul, Int.negOnePow_zero, one_smul] using
      dgComp_id_naturality p r hp h0p (F.map p f)⟩

@[simp]
theorem id_app (F : DGFunctor C D) (X : C) :
    app (id F) X = dgId (F.obj X) :=
  rfl

/-- Vertical composition of homogeneous dg natural transformations. -/
def comp (η : HomogeneousNatTrans F G n) (θ : HomogeneousNatTrans G H m) :
    HomogeneousNatTrans F H (n + m) :=
  ⟨fun X => dgComp n m (n + m) rfl (app η X) (app θ X), by
    intro X Y p r hpnm hnmp f
    rw [← dgComp_assoc p n m (p + n) (n + m) r
        (by omega) (by omega) (by omega),
      naturality η p (p + n) (by omega) (by omega) f,
      dgComp_units_smul_left,
      dgComp_assoc n p m (p + n) (p + m) r
        (by omega) (by omega) (by omega),
      naturality θ p (p + m) (by omega) (by omega) f,
      dgComp_units_smul_right,
      ← dgComp_assoc n m p (n + m) (p + m) r
        (by omega) (by omega) (by omega),
      smul_smul, ← Int.negOnePow_add, add_mul]⟩

@[simp]
theorem comp_app (η : HomogeneousNatTrans F G n)
    (θ : HomogeneousNatTrans G H m) (X : C) :
    app (comp η θ) X = dgComp n m (n + m) rfl (app η X) (app θ X) :=
  rfl

/-- A morphism of additive groups commutes with the `ℤˣ` sign action. -/
private lemma hom_units_smul {M N : AddCommGrpCat.{v}}
    (φ : M ⟶ N) (c : ℤˣ) (x : M) :
    φ.hom (c • x) = c • φ.hom x := by
  simp [Units.smul_def, map_zsmul]

/-- The pointwise differential of a homogeneous dg natural transformation.

Its graded naturality is not merely pointwise: the proof differentiates the
naturality equation for `η`, then uses naturality of `η` once more on `d f`.
The two extra terms cancel after the Koszul signs are normalized. -/
def differential (η : HomogeneousNatTrans F G n) :
    HomogeneousNatTrans F G (n + 1) :=
  ⟨fun X => ((dgHom (F.obj X) (G.obj X)).d n (n + 1)).hom (app η X), by
    intro X Y p r hpn hnp f
    have hδ := congrArg
      (fun z => ((dgHom (F.obj X) (G.obj Y)).d (p + n) r).hom z)
      (naturality η p (p + n) (by omega) (by omega) f)
    rw [hom_units_smul,
      dgComp_leibniz p n (p + n) r (by omega) (by omega)
        (F.map p f) (app η Y),
      dgComp_leibniz n p (p + n) r (by omega) (by omega)
        (app η X) (G.map p f),
      ← F.map_d p (p + 1) f, ← G.map_d p (p + 1) f,
      naturality η (p + 1) r (by omega) (by omega)
        (((dgHom X Y).d p (p + 1)).hom f)] at hδ
    have hs₁ : n.negOnePow * (n * (p + 1)).negOnePow =
        (n * p).negOnePow := by
      simp only [mul_add, mul_one, Int.negOnePow_add]
      rw [mul_comm (n * p).negOnePow n.negOnePow,
        ← mul_assoc, Int.units_mul_self, one_mul]
    have hs₂ : (n * p).negOnePow * p.negOnePow =
        ((n + 1) * p).negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    simp only [smul_add, smul_smul] at hδ
    rw [hs₁, hs₂] at hδ
    apply add_right_cancel (b :=
      (n * p).negOnePow •
        dgComp n (p + 1) r (by omega) (app η X)
          (G.map (p + 1) (((dgHom X Y).d p (p + 1)).hom f)))
    simpa only [add_comm] using hδ⟩

@[simp]
theorem differential_app (η : HomogeneousNatTrans F G n) (X : C) :
    app (differential η) X =
      ((dgHom (F.obj X) (G.obj X)).d n (n + 1)).hom (app η X) :=
  rfl

/-- A homogeneous dg natural transformation is closed when its pointwise
differential vanishes.  Keeping this predicate at the dg-functor root lets
cones, adjunctions, and future enriched constructions share one notion. -/
def IsClosed (η : HomogeneousNatTrans F G n) : Prop :=
  differential η = 0

/-- Every component of a closed homogeneous dg natural transformation is
closed in the corresponding Hom-complex. -/
lemma IsClosed.app_d {η : HomogeneousNatTrans F G n} (hη : IsClosed η) (X : C) :
    ((dgHom (F.obj X) (G.obj X)).d n (n + 1)).hom (app η X) = 0 := by
  have h := congrArg (fun θ => HomogeneousNatTrans.app θ X) hη
  simpa only [differential_app, zero_app] using h

/-- The pointwise differential as an additive homomorphism. -/
def differentialHom (F G : DGFunctor C D) (n : ℤ) :
    HomogeneousNatTrans F G n →+ HomogeneousNatTrans F G (n + 1) where
  toFun := differential
  map_zero' := by
    ext X
    simp [differential_app]
  map_add' η θ := by
    ext X
    simp [differential_app]

@[simp]
theorem differentialHom_apply (η : HomogeneousNatTrans F G n) :
    differentialHom F G n η = differential η :=
  rfl

/-- The pointwise differential squares to zero. -/
theorem differential_differential (η : HomogeneousNatTrans F G n) :
    differential (differential η) = 0 := by
  ext X
  change ((dgHom (F.obj X) (G.obj X)).d (n + 1) (n + 1 + 1)).hom
      (((dgHom (F.obj X) (G.obj X)).d n (n + 1)).hom (app η X)) = 0
  rw [← AddCommGrpCat.comp_apply,
    (dgHom (F.obj X) (G.obj X)).d_comp_d]
  rfl

/-- The Hom-complex of homogeneous dg natural transformations. -/
@[reducible] def complex (F G : DGFunctor C D) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  CochainComplex.of
    (fun n => AddCommGrpCat.of (HomogeneousNatTrans F G n))
    (fun n => AddCommGrpCat.ofHom (differentialHom F G n))
    (fun n => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro η
      exact differential_differential η)

@[simp]
theorem complex_X (F G : DGFunctor C D) (n : ℤ) :
    (complex F G).X n = AddCommGrpCat.of (HomogeneousNatTrans F G n) :=
  rfl

theorem complex_d_apply (η : HomogeneousNatTrans F G n) :
    ((complex F G).d n (n + 1)).hom η = differential η := by
  simp [complex, CochainComplex.of.d]

/-- Biadditive vertical composition in an arbitrary result degree. -/
@[reducible] def composition (F G H : DGFunctor C D)
    (n m r : ℤ) (h : n + m = r) :
    HomogeneousNatTrans F G n →+
      HomogeneousNatTrans G H m →+
        HomogeneousNatTrans F H r := by
  subst r
  refine AddMonoidHom.mk'
    (fun η => AddMonoidHom.mk' (fun θ => comp η θ) ?_) ?_
  · intro θ κ
    ext X
    simp [comp_app]
  · intro η θ
    apply AddMonoidHom.ext
    intro κ
    ext X
    simp [comp_app]

@[simp]
theorem composition_apply_app (η : HomogeneousNatTrans F G n)
    (θ : HomogeneousNatTrans G H m) (r : ℤ) (h : n + m = r) (X : C) :
    app (composition F G H n m r h η θ) X =
      dgComp n m r h (app η X) (app θ X) := by
  subst r
  rfl

end HomogeneousNatTrans

/-- Dg functors `C ⟶ D`, homogeneous dg natural transformations, and their
pointwise differential form a dg category. -/
noncomputable instance dgCategory :
    DGCategory.{max u v} (DGFunctor C D) where
  dgHom F G := HomogeneousNatTrans.complex F G
  dgId F := HomogeneousNatTrans.id F
  dgComp n m r h := HomogeneousNatTrans.composition _ _ _ n m r h
  dgComp_assoc := fun {W X Y Z} p q r pq qr pqr hpq hqr hpqr η θ κ => by
    apply HomogeneousNatTrans.ext
    intro A
    rw [HomogeneousNatTrans.composition_apply_app
        (((HomogeneousNatTrans.composition W X Y p q pq hpq) η) θ)
        κ pqr hpqr A,
      HomogeneousNatTrans.composition_apply_app η θ pq hpq A,
      HomogeneousNatTrans.composition_apply_app η
        (((HomogeneousNatTrans.composition X Y Z q r qr hqr) θ) κ)
        pqr (by omega) A,
      HomogeneousNatTrans.composition_apply_app θ κ qr hqr A]
    exact DGCategory.dgComp_assoc p q r pq qr pqr hpq hqr hpqr
      (HomogeneousNatTrans.app η A) (HomogeneousNatTrans.app θ A)
      (HomogeneousNatTrans.app κ A)
  dgId_comp := fun {X Y} p η => by
    apply HomogeneousNatTrans.ext
    intro A
    rw [HomogeneousNatTrans.composition_apply_app
        (HomogeneousNatTrans.id X) η p (zero_add p) A,
      HomogeneousNatTrans.id_app]
    exact DGCategory.dgId_comp p (HomogeneousNatTrans.app η A)
  dgComp_id := fun {X Y} p η => by
    apply HomogeneousNatTrans.ext
    intro A
    rw [HomogeneousNatTrans.composition_apply_app η
        (HomogeneousNatTrans.id Y) p (add_zero p) A,
      HomogeneousNatTrans.id_app]
    exact DGCategory.dgComp_id p (HomogeneousNatTrans.app η A)
  dgId_cocycle := fun F => by
    change HomogeneousNatTrans.differential (HomogeneousNatTrans.id F) = 0
    apply HomogeneousNatTrans.ext
    intro A
    change ((dgHom (F.obj A) (F.obj A)).d 0 1).hom (dgId (F.obj A)) = 0
    exact DGCategory.dgId_cocycle (F.obj A)
  dgComp_leibniz := fun {X Y Z} p q r r' h hr η θ => by
    cases hr
    rw [HomogeneousNatTrans.complex_d_apply
        (((HomogeneousNatTrans.composition X Y Z p q r h) η) θ),
      HomogeneousNatTrans.complex_d_apply θ,
      HomogeneousNatTrans.complex_d_apply η]
    apply HomogeneousNatTrans.ext
    intro A
    rw [HomogeneousNatTrans.differential_app,
      HomogeneousNatTrans.composition_apply_app η θ r h A]
    change _ = HomogeneousNatTrans.app
      (((HomogeneousNatTrans.composition X Y Z p (q + 1) (r + 1)
          (by omega)) η) (HomogeneousNatTrans.differential θ)) A +
        q.negOnePow • HomogeneousNatTrans.app
          (((HomogeneousNatTrans.composition X Y Z (p + 1) q (r + 1)
            (by omega)) (HomogeneousNatTrans.differential η)) θ) A
    rw [
      HomogeneousNatTrans.composition_apply_app η
        (HomogeneousNatTrans.differential θ) (r + 1) (by omega) A,
      HomogeneousNatTrans.differential_app,
      HomogeneousNatTrans.composition_apply_app
        (HomogeneousNatTrans.differential η) θ (r + 1) (by omega) A,
      HomogeneousNatTrans.differential_app]
    exact DGCategory.dgComp_leibniz p q r (r + 1) h rfl
      (HomogeneousNatTrans.app η A) (HomogeneousNatTrans.app θ A)

end DGFunctor

end CategoryTheory
