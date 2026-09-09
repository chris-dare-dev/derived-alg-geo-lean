/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformationH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousLift

/-!
# Dg functors obtained from objectwise cones

A closed degree-zero dg natural transformation `α : F ⟶ G` has a cone dg
functor once a cone of every component `α.app X` has been chosen.  This file
separates those two concerns:

* `ConeData α` is the minimal objectwise representability data;
* `ConeData.functor` supplies every homogeneous map by the signed cone lift;
* `ConeData.inr` and `ConeData.inl` are the canonical degree `0` and degree
  `-1` homogeneous natural transformations of the cone sequence.

The construction is dg-level.  It does not choose ordinary triangulated cones
or quotient morphisms in `H⁰`, and it does not depend on Fourier--Mukai
kernels.  Those are downstream realizations of this canonical root.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  {F G : DGFunctor C D}

/-- The minimal choices needed to turn componentwise cones of `α` into a dg
functor.  No compatibility fields are necessary: graded naturality of `α`
and the universal all-degree cone lift force the map laws. -/
structure ConeData (α : HomogeneousNatTrans F G 0) where
  /-- The chosen cone object of each component. -/
  obj : C → D
  /-- The chosen dg cone presentation of each component. -/
  isCone (X : C) : IsConeOf (app α X) (obj X)

/-- A pretriangulated target supplies objectwise cone data for every closed
degree-zero dg natural transformation. -/
noncomputable def chosenConeData [IsPretriangulated D]
    (α : HomogeneousNatTrans F G 0) (hα : IsClosed α) : ConeData α where
  obj X := (IsPretriangulated.exists_cone
    (app α X) (hα.app_mem_cocycles X)).choose
  isCone X := (IsPretriangulated.exists_cone
    (app α X) (hα.app_mem_cocycles X)).choose_spec.some

namespace ConeData

variable {α : HomogeneousNatTrans F G 0} (K : ConeData α)

/-- Graded naturality of `α`, oriented as the strict homogeneous square used
by the cone lift. -/
private lemma naturalitySquare {X Y : C} (p : ℤ)
    (f : (dgHom X Y).X p) :
    dgComp 0 p p (by omega) (app α X) (G.map p f) =
      dgComp p 0 p (by omega) (F.map p f) (app α Y) := by
  symm
  simpa only [zero_mul, Int.negOnePow_zero, one_smul] using
    naturality α p p (by omega) (by omega) f

/-- The dg functor obtained by taking the chosen cone of every component of
`α`.  Its action on a degree-`p` morphism is the signed strict homogeneous
cone lift of `F.map p f` and `G.map p f`. -/
noncomputable abbrev functor : DGFunctor C D where
  obj := K.obj
  map {X Y} p :=
    { toFun := fun f =>
        (K.isCone X).homogeneousLift (K.isCone Y) p
          (F.map p f) (G.map p f) 0
      map_zero' := by
        simp [IsConeOf.homogeneousLift]
      map_add' := by
        intro f g
        rw [map_add, map_add]
        exact (K.isCone X).homogeneousLift_strict_add (K.isCone Y) p
          (F.map p f) (F.map p g) (G.map p f) (G.map p g) }
  map_d {X Y} p q f := by
    change (K.isCone X).homogeneousLift (K.isCone Y) q
        (F.map q (((dgHom X Y).d p q).hom f))
        (G.map q (((dgHom X Y).d p q).hom f)) 0 =
      ((dgHom (K.obj X) (K.obj Y)).d p q).hom
        ((K.isCone X).homogeneousLift (K.isCone Y) p
          (F.map p f) (G.map p f) 0)
    rw [F.map_d p q f, G.map_d p q f]
    exact ((K.isCone X).homogeneousLift_strict_map_d (K.isCone Y) p q
      (F.map p f) (G.map p f) (naturalitySquare (α := α) p f)).symm
  map_id X := by
    change (K.isCone X).homogeneousLift (K.isCone X) 0
      (F.map 0 (dgId X)) (G.map 0 (dgId X)) 0 = dgId (K.obj X)
    rw [F.map_id, G.map_id]
    exact (K.isCone X).homogeneousLift_id
  map_comp {X Y Z} p q r h f g := by
    subst r
    change (K.isCone X).homogeneousLift (K.isCone Z) (p + q)
        (F.map (p + q) (dgComp p q (p + q) (by omega) f g))
        (G.map (p + q) (dgComp p q (p + q) (by omega) f g)) 0 =
      dgComp p q (p + q) (by omega)
        ((K.isCone X).homogeneousLift (K.isCone Y) p
          (F.map p f) (G.map p f) 0)
        ((K.isCone Y).homogeneousLift (K.isCone Z) q
          (F.map q g) (G.map q g) 0)
    rw [F.map_comp, G.map_comp]
    exact ((K.isCone X).homogeneousLift_strict_comp
      (K.isCone Y) (K.isCone Z) p q
      (F.map p f) (G.map p f) (F.map q g) (G.map q g)).symm

@[simp]
theorem functor_obj (X : C) : K.functor.obj X = K.obj X :=
  rfl

@[simp]
theorem functor_map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    K.functor.map p f =
      (K.isCone X).homogeneousLift (K.isCone Y) p
        (F.map p f) (G.map p f) 0 :=
  rfl

/-- The target inclusions form the canonical closed degree-zero dg natural
transformation `G ⟶ Cone(α)`. -/
noncomputable def inr : HomogeneousNatTrans G K.functor 0 :=
  ⟨fun X => (K.isCone X).inr, by
    intro X Y p r hp h0p f
    simp only [zero_mul, Int.negOnePow_zero, one_smul]
    change dgComp p 0 r hp (G.map p f) (K.isCone Y).inr =
      dgComp 0 p r h0p (K.isCone X).inr
        ((K.isCone X).homogeneousLift (K.isCone Y) p
          (F.map p f) (G.map p f) 0)
    exact ((K.isCone X).inr_comp_homogeneousLift_general (K.isCone Y)
      p r h0p hp (F.map p f) (G.map p f) 0).symm⟩

@[simp]
theorem inr_app (X : C) : app K.inr X = (K.isCone X).inr :=
  rfl

/-- The canonical target inclusion is closed in the dg functor category. -/
theorem inr_isClosed : IsClosed K.inr := by
  ext X
  exact (K.isCone X).inr_closed

/-- The shifted source inclusions form the canonical degree-`-1` homogeneous
dg natural transformation `F ⟶ Cone(α)`. -/
noncomputable def inl : HomogeneousNatTrans F K.functor (-1) :=
  ⟨fun X => (K.isCone X).inl, by
    intro X Y p r hp hnp f
    change dgComp p (-1) r hp (F.map p f) (K.isCone Y).inl =
      (-1 * p).negOnePow •
        dgComp (-1) p r hnp (K.isCone X).inl
          ((K.isCone X).homogeneousLift (K.isCone Y) p
            (F.map p f) (G.map p f) 0)
    have h := (K.isCone X).inl_comp_homogeneousLift_strict_general
      (K.isCone Y) p r hnp hp (F.map p f) (G.map p f)
    rw [h, smul_smul, ← Int.negOnePow_add,
      show -1 * p + p = 0 by ring, Int.negOnePow_zero, one_smul]⟩

@[simp]
theorem inl_app (X : C) : app K.inl X = (K.isCone X).inl :=
  rfl

/-- The boundary of the shifted source inclusion is the component map followed
by the target inclusion.  This is the dg-functor-level cone equation. -/
theorem differential_inl :
    differential K.inl = comp α K.inr := by
  ext X
  exact (K.isCone X).δ_inl

end ConeData

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
