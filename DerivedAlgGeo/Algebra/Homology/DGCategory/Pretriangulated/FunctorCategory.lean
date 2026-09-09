/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone

/-!
# The dg category of dg functors is pretriangulated

`DGFunctor C D` is a dg category, and `IsPretriangulated` asks it for three
things: a zero object, a shift of every object in every degree, and a cone on
every closed degree-zero morphism.  When `D` is pretriangulated all three are
available objectwise, and this file assembles them into the instance.

* **The zero object** is the constant dg functor at a dg zero object of `D`.
* **The shift** is `DGFunctor.shiftedFunctor`, whose value at `X` is a chosen
  shift of `F.obj X` and whose action on a degree-`p` morphism is the
  transport of `F.map p f` across those choices, with the sign `(-1)^(n * p)`.
* **The cone** is `HomogeneousNatTrans.ConeData.isConeOf`, built from the
  objectwise cones of a closed degree-zero dg natural transformation.  Its
  splitting is natural because the cone projections are, which is what
  `ConeData.fst` and `ConeData.snd` record.

The last of these is what makes the repository's objectwise twist a cone *of
functors*, which is the form Anno--Logvinenko's triangle `SR ⟶ Id_B ⟶ T`
takes.

## The sign on the shift is forced

Writing `s X : IsShiftBy (F.obj X) n (Y X)` for the chosen witnesses, the map
on a degree-`p` morphism is

`(F[n]).map p f = (-1)^(n * p) • (s X).inv ≫ F.map p f ≫ (s Y).hom`,

and the sign is forced, not chosen.  Both `(s X).inv` and `(s Y).hom` are
closed, so the Leibniz rule leaves one term, and with the repository's
convention `δ(a ≫ b) = a ≫ δb + (-1)^|b| δa ≫ b` and `|(s Y).hom| = -n` that
term carries `(-1)^n`; this is `IsShiftBy.shiftMap_d`.  A dg functor must
satisfy `map (p+1) (δ f) = δ (map p f)`, so the coefficient `ε` must satisfy
`ε (p+1) = (-1)^n ε p`.  No constant sign does, and `ε p = (-1)^(n * p)` is
the solution.  With it `map_id` is the unit law, `map_comp` is
`(-1)^(n p) (-1)^(n q) = (-1)^(n (p+q))`, and the shift witness is the family
`(s X).hom`, whose graded naturality is exactly the same sign cancelling
against `(-1)^(-n p)`.

## Two spellings of the same object

`shiftObj` names the chosen shift and `shiftedFunctor` carries it as its
`obj` field, so `(F.shiftedFunctor n).obj X` and `F.shiftObj n X` are
definitionally equal and syntactically different.  A goal that mixes them is
not type-correct at `instances` transparency, and `rw` then rejects every
motive it builds.  Two proofs below therefore go through `show` or through
the object-general lemmas `IsShiftBy.comp_inv_naturality` and
`IsShiftBy.comp_inv_comp_hom`, where unification at default transparency
identifies the two spellings; each such place says so.

## What this does not give

`IsPretriangulated` is dg data, not a triangulated structure.  Turning the
instance below into a pretriangulated structure on `H⁰ (DGFunctor C D)` needs
the `DGEnhancement` layer, and nothing here asserts that the shift chosen
objectwise agrees with any shift already present on `H⁰`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]

/-- The dg functor constant at an object with vanishing dg identity.

Only a *zero* object gives a dg functor this way: `map_id` asks for
`0 = dgId Z`, which is exactly the hypothesis. -/
def constZero (Z : D) (hZ : dgId Z = 0) : DGFunctor C D where
  obj _ := Z
  map _ := 0
  map_d _ _ _ := by simp
  map_id _ := by simp [hZ]
  map_comp _ _ _ _ _ _ := by simp

@[simp]
theorem constZero_obj (Z : D) (hZ : dgId Z = 0) (X : C) :
    (constZero (C := C) Z hZ).obj X = Z :=
  rfl

-- Not `@[simp]`: the constant functor's action is the zero map by definition,
-- so `simp` reduces the left-hand side without help.
theorem constZero_map (Z : D) (hZ : dgId Z = 0) {X Y : C} (p : ℤ)
    (f : (dgHom X Y).X p) :
    (constZero (C := C) Z hZ).map p f = 0 :=
  rfl

/-- **The dg category of dg functors has a zero object**, as soon as the
target has one: the constant functor at it. -/
theorem dgId_constZero_eq_zero (Z : D) (hZ : dgId Z = 0) :
    dgId (constZero (C := C) Z hZ) = 0 := by
  apply HomogeneousNatTrans.ext
  intro X
  exact hZ

/-- The dg category of dg functors has a zero object whenever the target is
pretriangulated. -/
theorem exists_zero_dgFunctor [IsPretriangulated D] :
    ∃ Z : DGFunctor C D, dgId Z = 0 := by
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_zero (C := D)
  exact ⟨constZero Z hZ, dgId_constZero_eq_zero Z hZ⟩

/-- **Every closed degree-zero dg natural transformation has a cone in the dg
category of dg functors**, whenever the target is pretriangulated.

This is `ConeData.isConeOf` applied to the objectwise cones the target
supplies, and it is the `exists_cone` field of a pretriangulated structure on
`DGFunctor C D`.  The remaining field is the shift; see the module
docstring. -/
theorem exists_cone_dgFunctor [IsPretriangulated D] {F G : DGFunctor C D}
    (α : (dgHom F G).X 0) (hα : α ∈ cocycles F G) :
    ∃ Z : DGFunctor C D, Nonempty (IsConeOf α Z) := by
  have hclosed : HomogeneousNatTrans.IsClosed α := by
    apply HomogeneousNatTrans.ext
    intro X
    exact congrArg (fun σ => HomogeneousNatTrans.app σ X) hα
  refine ⟨(HomogeneousNatTrans.chosenConeData α hclosed).functor,
    ⟨(HomogeneousNatTrans.chosenConeData α hclosed).isConeOf⟩⟩

section Shift

variable [IsPretriangulated D] (F : DGFunctor C D) (n : ℤ)

/-- The chosen shift by `n` of one value of `F`. -/
noncomputable def shiftObj (X : C) : D :=
  (IsPretriangulated.exists_shift (F.obj X) n).choose

/-- The chosen shift witness at one object. -/
noncomputable def shiftWitness (X : C) :
    IsShiftBy (F.obj X) n (F.shiftObj n X) :=
  (IsPretriangulated.exists_shift (F.obj X) n).choose_spec.some

/-- **The shift of a dg functor.**

The value at `X` is a chosen shift of `F.obj X`, and the action on a
degree-`p` morphism is the transport of `F.map p f` across those choices,
multiplied by `(-1)^(n * p)`.

That sign is forced.  `IsShiftBy.shiftMap_d` says transport anticommutes with
the differential by `(-1)^n`, so a coefficient `ε` makes the assignment a dg
functor only if `ε (p+1) = (-1)^n ε p`; no constant sign satisfies that, and
`(-1)^(n * p)` is the solution.  With it `map_id` and `map_comp` also hold,
the latter because `(-1)^(n p) (-1)^(n q) = (-1)^(n (p+q))`. -/
noncomputable def shiftedFunctor : DGFunctor C D where
  obj X := F.shiftObj n X
  map {X Y} p :=
    { toFun := fun f => (n * p).negOnePow •
        (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p (F.map p f)
      map_zero' := by simp
      map_add' := fun f g => by
        rw [map_add, IsShiftBy.shiftMap_add, smul_add] }
  map_d {X Y} p q f := by
    by_cases hpq : p + 1 = q
    · subst hpq
      show (n * (p + 1)).negOnePow •
          (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) (p + 1)
            (F.map (p + 1) (((dgHom X Y).d p (p + 1)).hom f)) =
        ((dgHom (F.shiftObj n X) (F.shiftObj n Y)).d p (p + 1)).hom
          ((n * p).negOnePow •
            (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p (F.map p f))
      rw [F.map_d p (p + 1) f,
        show ((dgHom (F.shiftObj n X) (F.shiftObj n Y)).d p (p + 1)).hom
              ((n * p).negOnePow •
                (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p
                  (F.map p f)) =
            (n * p).negOnePow •
              ((dgHom (F.shiftObj n X) (F.shiftObj n Y)).d p (p + 1)).hom
                ((F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p
                  (F.map p f)) from by simp [Units.smul_def, map_zsmul],
        IsShiftBy.shiftMap_d, smul_smul, ← Int.negOnePow_add,
        show n * p + n = n * (p + 1) by ring]
    · have hshape : ¬(ComplexShape.up ℤ).Rel p q := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpq
      rw [(dgHom X Y).shape p q hshape,
        (dgHom (F.shiftObj n X) (F.shiftObj n Y)).shape p q hshape]
      simp
  map_id X := by
    show (n * 0).negOnePow •
      (F.shiftWitness n X).shiftMap (F.shiftWitness n X) 0
        (F.map 0 (dgId X)) = dgId (F.shiftObj n X)
    rw [F.map_id, IsShiftBy.shiftMap_id, mul_zero, Int.negOnePow_zero, one_smul]
  map_comp {X Y Z} p q r h f g := by
    show (n * r).negOnePow •
        (F.shiftWitness n X).shiftMap (F.shiftWitness n Z) r
          (F.map r (dgComp p q r h f g)) =
      dgComp p q r h
        ((n * p).negOnePow •
          (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p (F.map p f))
        ((n * q).negOnePow •
          (F.shiftWitness n Y).shiftMap (F.shiftWitness n Z) q (F.map q g))
    rw [F.map_comp p q r h f g,
      IsShiftBy.shiftMap_comp _ (F.shiftWitness n Y) _ p q r h]
    rw [dgComp_units_smul_left, dgComp_units_smul_right, smul_smul,
      ← Int.negOnePow_add, show n * p + n * q = n * r by rw [← h]; ring]

@[simp]
theorem shiftedFunctor_obj (X : C) :
    (F.shiftedFunctor n).obj X = F.shiftObj n X :=
  rfl

/-- Not `@[simp]`: `shiftedFunctor_obj` rewrites the objects in this
statement's own type, so its left-hand side is not in simp normal form.  Use
it with `rw`. -/
theorem shiftedFunctor_map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    (F.shiftedFunctor n).map p f = (n * p).negOnePow •
      (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p (F.map p f) :=
  rfl

/-- The chosen shift elements assemble into a degree-`-n` homogeneous dg
natural transformation `F ⟶ F[n]`.

Its graded naturality is the characterising square of `shiftMap`, with the
functor's sign `(-1)^(n p)` cancelling the naturality sign `(-1)^(-n p)`. -/
noncomputable def shiftHom :
    HomogeneousNatTrans F (F.shiftedFunctor n) (-n) :=
  ⟨fun X => (F.shiftWitness n X).hom, by
    intro X Y p r hpr hrp f
    -- Spell the goal with `shiftObj` rather than `(F.shiftedFunctor n).obj`.
    -- The two are definitionally equal, but `rw` builds a motive that fails
    -- the instance-transparency check when the two spellings are mixed.
    show dgComp p (-n) r hpr (F.map p f) ((F.shiftWitness n Y).hom) =
        (-n * p).negOnePow • dgComp (-n) p r hrp ((F.shiftWitness n X).hom)
          ((n * p).negOnePow •
            (F.shiftWitness n X).shiftMap (F.shiftWitness n Y) p (F.map p f))
    rw [dgComp_units_smul_right, smul_smul, ← Int.negOnePow_add,
      show -n * p + n * p = 0 by ring, Int.negOnePow_zero, one_smul,
      (F.shiftWitness n X).hom_comp_shiftMap (F.shiftWitness n Y) p r hrp hpr
        (F.map p f)]⟩

@[simp]
theorem shiftHom_app (X : C) :
    HomogeneousNatTrans.app (F.shiftHom n) X = (F.shiftWitness n X).hom :=
  rfl

/-- **The shift of a dg functor is a shift in the dg category of dg
functors.** -/
noncomputable def shiftedFunctorWitness :
    IsShiftBy F n (F.shiftedFunctor n) where
  hom := F.shiftHom n
  hom_closed := by
    apply HomogeneousNatTrans.ext
    intro X
    -- The differential of the dg category of dg functors is the pointwise
    -- differential, so closedness is closedness of every chosen shift element.
    have hd : ((dgHom F (F.shiftedFunctor n)).d (-n) (-n + 1)).hom (F.shiftHom n) =
        HomogeneousNatTrans.differential (F.shiftHom n) :=
      HomogeneousNatTrans.complex_d_apply (F.shiftHom n)
    rw [hd, HomogeneousNatTrans.differential_app, HomogeneousNatTrans.zero_app]
    exact (F.shiftWitness n X).hom_closed
  bijective W p q hq := by
    have hcomp : ∀ (θ : (dgHom W F).X p) (X : C),
        HomogeneousNatTrans.app (compRight W (F.shiftHom n) p q hq θ) X =
          dgComp p (-n) q hq (HomogeneousNatTrans.app θ X)
            ((F.shiftWitness n X).hom) := by
      intro θ X
      exact HomogeneousNatTrans.composition_apply_app θ (F.shiftHom n) q hq X
    constructor
    · intro θ₁ θ₂ h
      apply HomogeneousNatTrans.ext
      intro X
      refine ((F.shiftWitness n X).bijective (W.obj X) p q hq).injective ?_
      have hX := congrArg (fun σ => HomogeneousNatTrans.app σ X) h
      rw [hcomp θ₁ X, hcomp θ₂ X] at hX
      exact hX
    · intro ψ
      refine ⟨⟨fun X => dgComp q n p (by omega)
          (HomogeneousNatTrans.app ψ X) ((F.shiftWitness n X).inv), ?_⟩, ?_⟩
      · intro X Y r m hpm hmp f
        -- Every step is one general `IsShiftBy` identity.  It has to be, and
        -- not a rewrite chain here: `HomogeneousNatTrans.app ψ X` is typed
        -- through `(F.shiftedFunctor n).obj X` while the shift witness is
        -- typed through `F.shiftObj n X`, and a goal mixing the two spellings
        -- is not type-correct at `instances` transparency, so `rw` rejects
        -- every motive.  Application unifies them at default transparency.
        exact IsShiftBy.comp_inv_naturality (F.shiftWitness n X)
          (F.shiftWitness n Y) q p r m (r + q) (by omega) (by omega) hpm hmp
          (W.map r f) (HomogeneousNatTrans.app ψ X)
          (HomogeneousNatTrans.app ψ Y) (F.map r f)
          (HomogeneousNatTrans.naturality ψ r (r + q) (by omega) (by omega) f)
      · apply HomogeneousNatTrans.ext
        intro X
        rw [hcomp]
        exact IsShiftBy.comp_inv_comp_hom (F.shiftWitness n X) q p (by omega) hq
          (HomogeneousNatTrans.app ψ X)

/-- Every dg functor has a shift in every degree, in the dg category of dg
functors. -/
theorem exists_shift_dgFunctor (F : DGFunctor C D) (n : ℤ) :
    ∃ G : DGFunctor C D, Nonempty (IsShiftBy F n G) :=
  ⟨F.shiftedFunctor n, ⟨F.shiftedFunctorWitness n⟩⟩

end Shift

/-- **The dg category of dg functors is pretriangulated whenever the target
is.**

The zero object is the constant functor at one, the shift is the objectwise
shift with the Koszul sign `(-1)^(n p)`, and the cone is the objectwise cone
assembled by `ConeData`.  With this instance the twist candidate attached to a
dg adjunction is a cone in a pretriangulated dg category, so its triangle is a
triangle of functors in the sense Anno--Logvinenko use. -/
noncomputable instance isPretriangulated_dgFunctor [IsPretriangulated D] :
    IsPretriangulated (DGFunctor C D) where
  exists_zero := exists_zero_dgFunctor
  exists_shift F n := exists_shift_dgFunctor F n
  exists_cone := exists_cone_dgFunctor

end DGFunctor

end CategoryTheory
