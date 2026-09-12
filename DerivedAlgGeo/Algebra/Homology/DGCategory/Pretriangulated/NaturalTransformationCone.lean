/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformationH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift

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


/-- The cone projections to the source form a degree-one homogeneous dg
natural transformation `Cone(α) ⟶ F`.

Graded naturality at degree one is exactly `homogeneousLift_comp_fst`: the
sign `(-1)^p` that lemma produces is the Koszul sign `(-1)^(1 * p)` the
naturality convention asks for, which is why the cone projection is natural
on the nose and not only up to homotopy. -/
noncomputable def fst : HomogeneousNatTrans K.functor F 1 :=
  ⟨fun X => (K.isCone X).fst, by
    intro X Y p r hpr hrp f
    rw [one_mul]
    exact (K.isCone X).homogeneousLift_comp_fst_general (K.isCone Y) p r
      hpr hrp (F.map p f) (G.map p f) 0⟩

@[simp]
theorem fst_app (X : C) : app K.fst X = (K.isCone X).fst :=
  rfl

/-- The cone projections to the target form a closed degree-zero homogeneous
dg natural transformation `Cone(α) ⟶ G`. -/
noncomputable def snd : HomogeneousNatTrans K.functor G 0 :=
  ⟨fun X => (K.isCone X).snd, by
    intro X Y p r hpr hrp f
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact (K.isCone X).homogeneousLift_comp_snd_general (K.isCone Y) p r
      hpr hrp (F.map p f) (G.map p f)⟩

@[simp]
theorem snd_app (X : C) : app K.snd X = (K.isCone X).snd :=
  rfl

/-- **The objectwise cones assemble into a cone in the dg category of dg
functors.**

This is what upgrades `ConeData` from a family of cones to a cone: the two
inclusions are the transformations already built, and a homogeneous
transformation into the cone splits along them objectwise.  The splitting is
natural because `fst` and `snd` are, which is the content of the two
constructions above.

Anno--Logvinenko's triangles are triangles *of functors*; this is the
statement that the repository's objectwise construction produces one.

## Why every step is a `show`

Composition and the differential of the dg category `DGFunctor C D` are
`HomogeneousNatTrans.composition` and the pointwise differential *by
definition*, so a goal stated with `dgComp` is definitionally a goal about
components — but not syntactically, and `rw` matches syntactically.  Each
`show` below is that definitional step, made explicit so the rest of the
proof can be an ordinary calculation in `D`. -/
noncomputable def isConeOf : IsConeOf (α : (dgHom F G).X 0) K.functor where
  inr := K.inr
  inr_closed := K.inr_isClosed
  inl := K.inl
  δ_inl := by
    show differential K.inl = _
    rw [K.differential_inl]
    apply HomogeneousNatTrans.ext
    intro X
    show dgComp 0 0 0 (by omega) (app α X) (app K.inr X) = _
    rfl
  bijective W p q hq := by
    -- The splitting map, written with `composition` rather than `dgComp`.
    -- The two are the same by definition of the dg category of dg functors,
    -- but only `composition` has a component lemma to rewrite with.
    set Φ : (dgHom W F).X q × (dgHom W G).X p → (dgHom W K.functor).X p :=
      fun ab =>
        HomogeneousNatTrans.composition W F K.functor q (-1) p (by omega)
            ab.1 K.inl +
          HomogeneousNatTrans.composition W G K.functor p 0 p (by omega)
            ab.2 K.inr with hΦ
    have happ : ∀ (ab : (dgHom W F).X q × (dgHom W G).X p) (X : C),
        app (Φ ab) X =
          dgComp q (-1) p (by omega) (app ab.1 X) ((K.isCone X).inl) +
            dgComp p 0 p (by omega) (app ab.2 X) ((K.isCone X).inr) := by
      intro ab X
      rw [hΦ]
      rw [show app (HomogeneousNatTrans.composition W F K.functor q (-1) p
              (by omega) ab.1 K.inl +
            HomogeneousNatTrans.composition W G K.functor p 0 p
              (by omega) ab.2 K.inr) X =
          app (HomogeneousNatTrans.composition W F K.functor q (-1) p
              (by omega) ab.1 K.inl) X +
            app (HomogeneousNatTrans.composition W G K.functor p 0 p
              (by omega) ab.2 K.inr) X from rfl,
        composition_apply_app, composition_apply_app, inl_app, inr_app]
    show Function.Bijective Φ
    constructor
    · rintro ⟨θ₁, ρ₁⟩ ⟨θ₂, ρ₂⟩ h
      have hX : ∀ X : C, (app θ₁ X, app ρ₁ X) = (app θ₂ X, app ρ₂ X) := by
        intro X
        refine ((K.isCone X).bijective (W.obj X) p q hq).injective ?_
        have := congrArg (fun σ => HomogeneousNatTrans.app σ X) h
        rw [happ (θ₁, ρ₁) X, happ (θ₂, ρ₂) X] at this
        exact this
      have h₁ : θ₁ = θ₂ := by
        apply HomogeneousNatTrans.ext
        intro X
        exact congrArg (fun z => z.1) (hX X)
      have h₂ : ρ₁ = ρ₂ := by
        apply HomogeneousNatTrans.ext
        intro X
        exact congrArg (fun z => z.2) (hX X)
      rw [h₁, h₂]
    · intro σ
      refine ⟨(HomogeneousNatTrans.composition W K.functor F p 1 q (by omega)
          σ K.fst,
        HomogeneousNatTrans.composition W K.functor G p 0 p (by omega)
          σ K.snd), ?_⟩
      apply HomogeneousNatTrans.ext
      intro X
      rw [happ]
      dsimp only
      rw [composition_apply_app, composition_apply_app, fst_app, snd_app,
        dgComp_assoc p 1 (-1) q 0 p (by omega) (by omega) (by omega),
        dgComp_assoc p 0 0 p 0 p (by omega) (by omega) (by omega),
        ← map_add, (K.isCone X).fst_inl_add_snd_inr, dgComp_id]

private lemma explicitProjections_splitId :
    dgComp 1 (-1) 0 (by omega) K.fst K.inl +
        dgComp 0 0 0 (by omega) K.snd K.inr =
      dgId K.functor := by
  apply HomogeneousNatTrans.ext
  intro X
  change dgComp 1 (-1) 0 (by omega)
        (HomogeneousNatTrans.app K.fst X) (HomogeneousNatTrans.app K.inl X) +
      dgComp 0 0 0 (by omega)
        (HomogeneousNatTrans.app K.snd X) (HomogeneousNatTrans.app K.inr X) =
    dgId (K.functor.obj X)
  rw [fst_app, inl_app, snd_app, inr_app]
  exact (K.isCone X).fst_inl_add_snd_inr

/-- The projection selected from the assembled cone in the dg-functor category
is the explicit pointwise source projection transformation. -/
@[simp]
lemma isConeOf_fst : K.isConeOf.fst = K.fst := by
  symm
  exact (K.isConeOf.splitId_unique K.explicitProjections_splitId).1

/-- The projection selected from the assembled cone in the dg-functor category
is the explicit pointwise target projection transformation. -/
@[simp]
lemma isConeOf_snd : K.isConeOf.snd = K.snd := by
  symm
  exact (K.isConeOf.splitId_unique K.explicitProjections_splitId).2

private lemma isConeOf_lift_app {F' G' : DGFunctor C D}
    {α' : HomogeneousNatTrans F' G' 0} (K' : ConeData α')
    (u : HomogeneousNatTrans F F' 0) (v : HomogeneousNatTrans G G' 0)
    (X : C) :
    HomogeneousNatTrans.app (K.isConeOf.lift K'.isConeOf u v 0) X =
      (K.isCone X).lift (K'.isCone X)
        (HomogeneousNatTrans.app u X) (HomogeneousNatTrans.app v X) 0 := by
  apply (K'.isCone X).homogeneous_ext 0
  · have h := congrArg (fun θ => HomogeneousNatTrans.app θ X)
      (K.isConeOf.lift_comp_fst K'.isConeOf u v 0)
    rw [K'.isConeOf_fst, K.isConeOf_fst] at h
    change HomogeneousNatTrans.app
        (HomogeneousNatTrans.composition K.functor K'.functor F'
          0 1 1 (by omega) (K.isConeOf.lift K'.isConeOf u v 0) K'.fst) X =
      HomogeneousNatTrans.app
        (HomogeneousNatTrans.composition K.functor F F'
          1 0 1 (by omega) K.fst u) X at h
    rw [HomogeneousNatTrans.composition_apply_app,
      HomogeneousNatTrans.composition_apply_app, fst_app, fst_app] at h
    exact h.trans ((K.isCone X).lift_comp_fst
      (K'.isCone X) (HomogeneousNatTrans.app u X)
      (HomogeneousNatTrans.app v X) 0).symm
  · have h := congrArg (fun θ => HomogeneousNatTrans.app θ X)
      (K.isConeOf.homogeneousLift_comp_snd K'.isConeOf 0 u v)
    rw [K'.isConeOf_snd, K.isConeOf_snd] at h
    change HomogeneousNatTrans.app
        (HomogeneousNatTrans.composition K.functor K'.functor G'
          0 0 0 (by omega) (K.isConeOf.lift K'.isConeOf u v 0) K'.snd) X =
      HomogeneousNatTrans.app
        (HomogeneousNatTrans.composition K.functor G G'
          0 0 0 (by omega) K.snd v) X at h
    rw [HomogeneousNatTrans.composition_apply_app,
      HomogeneousNatTrans.composition_apply_app, snd_app, snd_app] at h
    exact h.trans ((K.isCone X).homogeneousLift_comp_snd
      (K'.isCone X) 0 (HomogeneousNatTrans.app u X)
      (HomogeneousNatTrans.app v X)).symm

section StrictSquareIso

variable {F' G' : DGFunctor C D} {α' : HomogeneousNatTrans F' G' 0}
  (K' : ConeData α')

/-- A strict isomorphism square between two dg natural transformations lifts
to an isomorphism between their chosen cone dg functors. -/
noncomputable def isoOfStrictSquare
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α') :
    (show Z0 (DGFunctor C D) from K.functor) ≅
      (show Z0 (DGFunctor C D) from K'.functor) :=
  IsConeOf.isoOfStrictSquare K.isConeOf K'.isConeOf eF eG hsq

@[simp]
lemma isoOfStrictSquare_hom_val
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α') :
    (K.isoOfStrictSquare K' eF eG hsq).hom.val =
      K.isConeOf.lift K'.isConeOf eF.hom.val eG.hom.val 0 :=
  rfl

@[simp]
lemma isoOfStrictSquare_inv_val
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α') :
    (K.isoOfStrictSquare K' eF eG hsq).inv.val =
      K'.isConeOf.lift K.isConeOf eF.inv.val eG.inv.val 0 :=
  rfl

lemma isoOfStrictSquare_hom_app
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : C) :
    HomogeneousNatTrans.app (K.isoOfStrictSquare K' eF eG hsq).hom.val X =
      (K.isCone X).lift (K'.isCone X)
        (HomogeneousNatTrans.app eF.hom.val X)
        (HomogeneousNatTrans.app eG.hom.val X) 0 := by
  rw [isoOfStrictSquare_hom_val]
  exact K.isConeOf_lift_app K' eF.hom.val eG.hom.val X

lemma isoOfStrictSquare_inv_app
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : C) :
    HomogeneousNatTrans.app (K.isoOfStrictSquare K' eF eG hsq).inv.val X =
      (K'.isCone X).lift (K.isCone X)
        (HomogeneousNatTrans.app eF.inv.val X)
        (HomogeneousNatTrans.app eG.inv.val X) 0 := by
  rw [isoOfStrictSquare_inv_val]
  exact K'.isConeOf_lift_app K eF.inv.val eG.inv.val X

/-- The lifted dg-functor isomorphism strictly commutes with the canonical
target inclusions of the two cone sequences. -/
lemma inr_comp_isoOfStrictSquare_hom
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α') :
    composition G K.functor K'.functor 0 0 0 (by omega)
        K.inr (K.isoOfStrictSquare K' eF eG hsq).hom.val =
      composition G G' K'.functor 0 0 0 (by omega) eG.hom.val K'.inr :=
  IsConeOf.inr_comp_isoOfStrictSquare_hom
    K.isConeOf K'.isConeOf eF eG hsq

end StrictSquareIso

end ConeData

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
