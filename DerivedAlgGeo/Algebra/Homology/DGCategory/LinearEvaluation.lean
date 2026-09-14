/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopower
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-!
# Scalar-linear evaluation data in a dg category

`LinearEvaluationData k E` chooses the `k`-linear copower
`DGLinear.homComplex k E X ⊗ E` for every object `X`.  The universal properties
assemble into a `k`-linear dg functor, and lifting the identity cochain gives a
closed evaluation transformation to the identity functor.

The action cochain is built from `DGLinear.postcompCochain`: postcomposition by
`f : X ⟶ Y` first sends `Hom(E,X)` to `Hom(E,Y)`, then the universal chain map
for the target sends it to `Hom(E, Hom(E,Y) ⊗ E)`.  Thus the construction uses
Mathlib's `HomComplex.Cochain` composition rather than another componentwise
cochain interface.

This is deliberately parallel to, not a refinement of, additive
`EvaluationData`.  Its copowers represent only `k`-linear cochains, so there is
no general map from `LinearEvaluationData` to `EvaluationData`.  Coefficient-
complex homotopy invariance is supplied separately by `LinearCopowerFunctor`;
this file stops before cones, exactness, Euler-class formulas, finite
presentations, or concrete existence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- A choice of the scalar-linear copower `Hom(E,X) ⊗ E` for every `X`. -/
structure LinearEvaluationData (E : C) where
  /-- The chosen object `Hom(E,X) ⊗ E`. -/
  obj : C → C
  /-- The chosen object has the scalar-linear copower universal property. -/
  isLinearCopower (X : C) :
    IsLinearCopowerOf k (DGLinear.homComplex k E X) E (obj X)

/-- Mere existence of scalar-linear evaluation data at `E`. -/
class HasLinearEvaluationData (E : C) : Prop where
  exists_linearEvaluationData : Nonempty (LinearEvaluationData k E)

/-- Scalar-linear evaluation data selected from its existence capability. -/
noncomputable def chosenLinearEvaluationData (E : C)
    [HasLinearEvaluationData k E] : LinearEvaluationData k E :=
  Classical.choice HasLinearEvaluationData.exists_linearEvaluationData

namespace LinearEvaluationData

/-- All scalar-linear copowers supply scalar-linear evaluation data at `E`. -/
noncomputable def ofHasLinearCopowers [HasLinearCopowers k C]
    (E : C) : LinearEvaluationData k E where
  obj Y := linearCopowerObj (DGLinear.homComplex k E Y) E
  isLinearCopower Y :=
    linearCopowerIsLinearCopower (DGLinear.homComplex k E Y) E

/-- A category with all scalar-linear copowers has scalar-linear evaluation
data at every object. -/
instance (priority := 100) hasLinearEvaluationDataOfHasLinearCopowers
    [HasLinearCopowers k C] (E : C) : HasLinearEvaluationData k E :=
  ⟨⟨ofHasLinearCopowers k E⟩⟩

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {E : C} (V : LinearEvaluationData k E)

/-- The cochain induced by a homogeneous morphism before applying the source
copower's representing inverse. -/
private def mapCochain {X Y : C} (p : ℤ) :
    (DGLinear.homComplex k X Y).X p →ₗ[k]
      CochainComplex.HomComplex.Cochain
        (DGLinear.homComplex k E X)
        (DGLinear.homComplex k E (V.obj Y)) p where
  toFun f := (DGLinear.postcompCochain k E p f).comp
    (CochainComplex.HomComplex.Cochain.ofHom (V.isLinearCopower Y).univ)
    (add_zero p)
  map_add' f f' := by
    rw [map_add, CochainComplex.HomComplex.Cochain.add_comp]
  map_smul' c f := by
    rw [map_smul, CochainComplex.HomComplex.Cochain.smul_comp]
    rfl

/-- The scalar-linear action on homogeneous morphisms. -/
noncomputable def map {X Y : C} (p : ℤ) :
    (dgHom X Y).X p →ₗ[k] (dgHom (V.obj X) (V.obj Y)).X p :=
  (V.isLinearCopower X).cochainLinearEquiv (V.obj Y) p |>.symm.toLinearMap.comp
    (V.mapCochain p)

@[simp]
lemma univ_comp_map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p)
    (i j : ℤ) (hij : i + p = j) (g : (dgHom E X).X i) :
    dgComp i p j hij ((V.isLinearCopower X).univ.f i g) (V.map p f) =
      (V.isLinearCopower Y).univ.f j (dgComp i p j hij g f) := by
  change dgComp i p j hij ((V.isLinearCopower X).univ.f i g)
      ((V.isLinearCopower X).lift p (V.mapCochain p f)) = _
  rw [(V.isLinearCopower X).univ_comp_lift]
  change (((((DGLinear.postcompCochain k E p f).comp
      (CochainComplex.HomComplex.Cochain.ofHom
        (V.isLinearCopower Y).univ) (add_zero p)).v i j hij).hom g)) = _
  rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  rfl

/-- The scalar-linear evaluation functor `Hom(E,-) ⊗ E`. -/
noncomputable def functor : DGFunctor C C where
  obj := V.obj
  map {X Y} p := AddMonoidHom.mk' (V.map p) (V.map p).map_add
  map_d {X Y} p q f := by
    by_cases hpq : p + 1 = q
    · subst hpq
      refine (V.isLinearCopower X).lift_unique (fun i j hij g => ?_)
      show dgComp i (p + 1) j hij ((V.isLinearCopower X).univ.f i g)
          (V.map (p + 1) (((dgHom X Y).d p (p + 1)).hom f)) =
        dgComp i (p + 1) j hij ((V.isLinearCopower X).univ.f i g)
          (((dgHom (V.obj X) (V.obj Y)).d p (p + 1)).hom (V.map p f))
      rw [univ_comp_map]
      have hleib := dgComp_leibniz (C := C) i p (i + p) j (by omega) (by omega)
        ((V.isLinearCopower X).univ.f i g) (V.map p f)
      rw [univ_comp_map (i := i) (j := i + p) (hij := by omega),
        ← (V.isLinearCopower Y).univ_d (i + p) j,
        ← (V.isLinearCopower X).univ_d i (i + 1),
        univ_comp_map (i := i + 1) (j := j) (hij := by omega)] at hleib
      change (V.isLinearCopower Y).univ.f j
          (((dgHom E Y).d (i + p) j).hom
            (dgComp i p (i + p) (by omega) g f)) =
        dgComp i (p + 1) j (by omega)
            ((V.isLinearCopower X).univ.f i g)
            (((dgHom (V.obj X) (V.obj Y)).d p (p + 1)).hom (V.map p f)) +
          p.negOnePow • (V.isLinearCopower Y).univ.f j
            (dgComp (i + 1) p j (by omega)
              (((dgHom E X).d i (i + 1)).hom g) f) at hleib
      rw [dgComp_leibniz (C := C) i p (i + p) j (by omega) (by omega) g f,
        _root_.map_add] at hleib
      simp only [Units.smul_def, map_zsmul] at hleib
      exact add_right_cancel hleib
    · have hshape : ¬(ComplexShape.up ℤ).Rel p q := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpq
      rw [(dgHom X Y).shape p q hshape,
        (dgHom (V.obj X) (V.obj Y)).shape p q hshape]
      show V.map q 0 = _
      rw [(V.map q).map_zero]
      simp
  map_id X := by
    refine (V.isLinearCopower X).lift_unique (fun i j hij g => ?_)
    have hji : j = i := by omega
    cases hji
    show dgComp i 0 i hij ((V.isLinearCopower X).univ.f i g)
        (V.map 0 (dgId X)) =
      dgComp i 0 i hij ((V.isLinearCopower X).univ.f i g) (dgId (V.obj X))
    rw [univ_comp_map, dgComp_id, dgComp_id]
  map_comp {X Y Z} p q r h f g := by
    refine (V.isLinearCopower X).lift_unique (fun i j hij x => ?_)
    show dgComp i r j hij ((V.isLinearCopower X).univ.f i x)
        (V.map r (dgComp p q r h f g)) =
      dgComp i r j hij ((V.isLinearCopower X).univ.f i x)
        (dgComp p q r h (V.map p f) (V.map q g))
    rw [← dgComp_assoc i p q (i + p) r j rfl h (by omega)
        ((V.isLinearCopower X).univ.f i x) (V.map p f) (V.map q g),
      univ_comp_map (i := i) (j := i + p) (hij := rfl),
      univ_comp_map (i := i + p) (j := j) (hij := by omega),
      univ_comp_map (i := i) (j := j) (hij := hij),
      ← dgComp_assoc i p q (i + p) r j rfl h (by omega) x f g]

@[simp]
lemma functor_obj (X : C) : V.functor.obj X = V.obj X := rfl

/-- Kept out of the simp set for the same normal-form reason as the additive
evaluation functor's map projection. -/
lemma functor_map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    V.functor.map p f = V.map p f := rfl

/-- The scalar-linear evaluation functor preserves the `k`-action. -/
noncomputable instance functorLinear : V.functor.Linear k where
  map_smul p c f := by
    change V.map p (c • f) = c • V.map p f
    exact (V.map p).map_smul c f

/-- The evaluation morphism corresponding to the identity cochain of
`DGLinear.homComplex k E X`. -/
noncomputable def evalHom (X : C) : (dgHom (V.obj X) X).X 0 :=
  (V.isLinearCopower X).lift 0
    (CochainComplex.HomComplex.Cochain.ofHom
      (𝟙 (DGLinear.homComplex k E X)))

@[simp]
lemma univ_comp_evalHom (X : C) (i : ℤ) (g : (dgHom E X).X i) :
    dgComp i 0 i (by omega) ((V.isLinearCopower X).univ.f i g)
      (V.evalHom X) = g := by
  rw [evalHom, (V.isLinearCopower X).univ_comp_lift]
  change ((CochainComplex.HomComplex.Cochain.ofHom
    (𝟙 (DGLinear.homComplex k E X))).v i i (add_zero i)).hom g = g
  rw [CochainComplex.HomComplex.Cochain.ofHom_v]
  rfl

/-- The closed degree-zero evaluation transformation
`Hom(E,-) ⊗ E ⟶ id`. -/
noncomputable def evaluation :
    DGFunctor.HomogeneousNatTrans V.functor (DGFunctor.id C) 0 :=
  ⟨V.evalHom, by
    intro X Y p r hpr hrp f
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    have hrp' : r = p := by omega
    cases hrp'
    refine (V.isLinearCopower X).lift_unique (fun i j hij g => ?_)
    have hji : j = i + p := by omega
    cases hji
    show dgComp i p (i + p) hij ((V.isLinearCopower X).univ.f i g)
        (dgComp p 0 p hpr (V.map p f) (V.evalHom Y)) =
      dgComp i p (i + p) hij ((V.isLinearCopower X).univ.f i g)
        (dgComp 0 p p hrp (V.evalHom X) f)
    rw [← dgComp_assoc i p 0 (i + p) p (i + p) rfl hpr (by omega)
        ((V.isLinearCopower X).univ.f i g) (V.map p f) (V.evalHom Y),
      univ_comp_map (i := i) (j := i + p) (hij := rfl),
      univ_comp_evalHom,
      ← dgComp_assoc i 0 p i p (i + p) (by omega) hrp (by omega)
        ((V.isLinearCopower X).univ.f i g) (V.evalHom X) f,
      univ_comp_evalHom]⟩

/-- The scalar-linear evaluation transformation is closed. -/
lemma evaluation_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed V.evaluation := by
  ext X
  show ((dgHom (V.obj X) X).d 0 1).hom (V.evalHom X) = 0
  refine (V.isLinearCopower X).lift_unique (fun i j hij g => ?_)
  have hji : j = i + 1 := by omega
  cases hji
  have hleib := dgComp_leibniz (C := C) i 0 i (i + 1) (by omega) (by omega)
    ((V.isLinearCopower X).univ.f i g) (V.evalHom X)
  rw [V.univ_comp_evalHom, ← (V.isLinearCopower X).univ_d i (i + 1),
    V.univ_comp_evalHom] at hleib
  simp only [Int.negOnePow_zero, one_smul, _root_.map_zero] at hleib ⊢
  exact add_right_cancel (hleib.symm.trans (zero_add _).symm)

/-- The canonical closed natural comparison between two scalar-linear
evaluation choices. -/
noncomputable def compare (V W : LinearEvaluationData k E) :
    DGFunctor.HomogeneousNatTrans V.functor W.functor 0 :=
  ⟨fun Y => (V.isLinearCopower Y).compare (W.isLinearCopower Y), by
    intro Y Y' p r hpr hrp f
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    have hrp' : r = p := by omega
    cases hrp'
    change dgComp p 0 p hpr (V.map p f)
        ((V.isLinearCopower Y').compare (W.isLinearCopower Y')) =
      dgComp 0 p p hrp ((V.isLinearCopower Y).compare
        (W.isLinearCopower Y)) (W.map p f)
    refine (V.isLinearCopower Y).lift_unique (fun i j hij g => ?_)
    rw [← dgComp_assoc i p 0 j p j hij hpr (by omega),
      V.univ_comp_map,
      (V.isLinearCopower Y').univ_comp_compare (W.isLinearCopower Y'),
      ← dgComp_assoc i 0 p i p j (by omega) hrp (by omega),
      (V.isLinearCopower Y).univ_comp_compare (W.isLinearCopower Y),
      W.univ_comp_map]⟩

@[simp]
lemma compare_app (V W : LinearEvaluationData k E) (Y : C) :
    DGFunctor.HomogeneousNatTrans.app (compare V W) Y =
      (V.isLinearCopower Y).compare (W.isLinearCopower Y) :=
  rfl

/-- The canonical scalar-linear evaluation comparison is closed. -/
lemma compare_isClosed (V W : LinearEvaluationData k E) :
    DGFunctor.HomogeneousNatTrans.IsClosed (compare V W) := by
  apply DGFunctor.HomogeneousNatTrans.ext
  intro Y
  exact IsLinearCopowerOf.compare_mem_cocycles _ _

/-- Canonical scalar-linear evaluation comparisons compose strictly. -/
lemma compare_comp (V W U : LinearEvaluationData k E) :
    DGFunctor.HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
        (compare V W) (compare W U) = compare V U := by
  apply DGFunctor.HomogeneousNatTrans.ext
  intro Y
  rw [DGFunctor.HomogeneousNatTrans.composition_apply_app,
    compare_app, compare_app, compare_app]
  exact (V.isLinearCopower Y).compare_trans
    (W.isLinearCopower Y) (U.isLinearCopower Y)

/-- The scalar-linear evaluation comparison from a choice to itself is the
identity. -/
@[simp]
lemma compare_self (V : LinearEvaluationData k E) :
    compare V V = DGFunctor.HomogeneousNatTrans.id V.functor := by
  apply DGFunctor.HomogeneousNatTrans.ext
  intro Y
  rw [compare_app, DGFunctor.HomogeneousNatTrans.id_app]
  exact IsLinearCopowerOf.compare_self _

/-- The canonical comparison as an isomorphism in the closed degree-zero
dg-functor category. -/
noncomputable def compareIso (V W : LinearEvaluationData k E) :
    (show Z0 (DGFunctor C C) from V.functor) ≅
      (show Z0 (DGFunctor C C) from W.functor) where
  hom := ⟨compare V W, compare_isClosed V W⟩
  inv := ⟨compare W V, compare_isClosed W V⟩
  hom_inv_id := Subtype.ext ((compare_comp V W V).trans (compare_self V))
  inv_hom_id := Subtype.ext ((compare_comp W V W).trans (compare_self W))

@[simp]
lemma compareIso_hom_val (V W : LinearEvaluationData k E) :
    (compareIso V W).hom.val = compare V W :=
  rfl

@[simp]
lemma compareIso_inv_val (V W : LinearEvaluationData k E) :
    (compareIso V W).inv.val = compare W V :=
  rfl

/-- The canonical comparison from a choice to itself is the identity
isomorphism. -/
@[simp]
lemma compareIso_self (V : LinearEvaluationData k E) :
    compareIso V V = Iso.refl _ := by
  apply Iso.ext
  apply Subtype.ext
  exact compare_self V

/-- Canonical scalar-linear evaluation comparison isomorphisms are
transitive. -/
lemma compareIso_trans (V W U : LinearEvaluationData k E) :
    (compareIso V W).trans (compareIso W U) = compareIso V U := by
  apply Iso.ext
  apply Subtype.ext
  exact compare_comp V W U

/-- The canonical comparison commutes strictly with scalar-linear
evaluation. -/
lemma compare_comp_evaluation (V W : LinearEvaluationData k E) :
    DGFunctor.HomogeneousNatTrans.composition _ _ _ 0 0 0 (by omega)
        (compare V W) W.evaluation = V.evaluation := by
  apply DGFunctor.HomogeneousNatTrans.ext
  intro Y
  rw [DGFunctor.HomogeneousNatTrans.composition_apply_app, compare_app]
  change dgComp 0 0 0 (by omega)
      ((V.isLinearCopower Y).compare (W.isLinearCopower Y))
        (W.evalHom Y) = V.evalHom Y
  refine (V.isLinearCopower Y).lift_unique (fun i j hij g => ?_)
  have hji : j = i := by omega
  cases hji
  rw [← dgComp_assoc i 0 0 i 0 i (by omega) (by omega) (by omega),
    (V.isLinearCopower Y).univ_comp_compare (W.isLinearCopower Y),
    W.univ_comp_evalHom, V.univ_comp_evalHom]

end LinearEvaluationData

end CategoryTheory
