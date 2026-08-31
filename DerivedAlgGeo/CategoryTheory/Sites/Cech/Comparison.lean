/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Contractible
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Bicomplex
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# The Cech-to-derived comparison boundary

This file supplies the first reusable layer of the comparison between Cech cohomology and
derived-functor sheaf cohomology.

Mathlib defines the Cech complex and `Sheaf.H`, but it does not define the cohomology of that
complex, a comparison morphism, or a theorem identifying the two.  We therefore:

* name the homology objects of the Cech complex;
* prove the natural isomorphism `F.H' n T ≃+ F.H n` for a terminal object `T`;
* record the standard acyclicity hypothesis on all finite intersections in a cover;
* package, as a proposition, the exact conclusion a Cech-to-derived comparison theorem must
  produce; and
* prove the positive-degree comparison for the singleton cover of a terminal object, as well as
  the general implication from Cech exactness to derived vanishing once comparison is available.

This file is a layer, not the whole comparison.  The nontrivial-cover step -- that
`IsCechAcyclicCover U F` implies `CechComputesDerivedCohomologyAt U F n` -- is **proved**, in
`DerivedAlgGeo.CategoryTheory.Sites.Cech.GlobalComparison`, by the augmented Cech
resolution and its column-filtration spectral sequence.  The chain runs:

* `Bicomplex` builds `C^{p,q} = Cech^p(U, I^q)` from an injective resolution, totalizes its column
  filtration, constructs the spectral sequence, and computes the initial page as the homology of an
  adjacent filtration layer;
* `InitialPage` identifies the degree-zero row, including its horizontal differential, with the
  integer-extended Cech complex, so the following page is ordinary Cech cohomology along that row;
* `TotalComparison` proves that under local acyclicity the augmentation from the ordinary Cech
  complex to the total injective Cech complex is a quasi-isomorphism, which is the abutment
  statement Mathlib's `SpectralSequence` structure cannot record as a field;
* `GlobalComparison` assembles these into
  `isCechAcyclicCover_cechComputesDerivedCohomology`.

The declarations below take an explicit `InjectiveResolution F` because the site here is a general
`C : Type u` with `Category.{a} C`, and the pinned Mathlib supplies `EnoughInjectives` for abelian
sheaves only over a *small* site.  That is the only obstruction: on a small site the resolution is
chosen rather than assumed.
`DerivedAlgGeo.CategoryTheory.Sites.Cech.SmallSiteResolution` restates this interface
without the resolution argument, and
`GlobalComparison.isCechAcyclicCover_cechComputesDerivedCohomology_opens` states the comparison
itself with neither a resolution nor a `HasExt` argument.
-/

universe i h a v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

section CechCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type a} [Category A] [Abelian A] [HasProducts.{i} A]
  {ι : Type i}

/-- Degree-`n` Cech cohomology is the homology of Mathlib's explicit Cech cochain complex. -/
noncomputable abbrev cechCohomology (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((cechComplexFunctor U).obj P).homology n

/-- Exactness of the explicit Cech complex at `n` kills degree-`n` Cech cohomology. -/
lemma cechCohomology_isZero_of_exactAt (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (h : ((cechComplexFunctor U).obj P).ExactAt n) :
    IsZero (cechCohomology U P n) :=
  h.isZero_homology

end CechCohomology

namespace Sheaf

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
  {ι : Type a}

/-- The free abelian sheaf represented by `X`; this is the first argument of `F.H' n X`. -/
noncomputable abbrev freeAbelianYonedaSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{a}] (X : C) :
    Sheaf J AddCommGrpCat.{a} :=
  (presheafToSheaf J _).obj (yoneda.obj X ⋙ AddCommGrpCat.free)

/-- Maps from the free abelian representable presheaf are sections. -/
noncomputable def freeAbelianYonedaPresheafHomAddEquiv (X : C)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{a}) :
    ((yoneda.obj X ⋙ AddCommGrpCat.free) ⟶ G) ≃+ G.obj (op X) where
  toFun f := f.app (op X) (FreeAbelianGroup.of (𝟙 X))
  invFun s :=
    { app := fun Y => AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift fun φ => G.map φ.op s)
      naturality := fun {Y Z} f => by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro φ
        simp only [Functor.comp_map, AddCommGrpCat.hom_comp]
        change (FreeAbelianGroup.lift fun φ => G.map φ.op s)
            ((AddCommGrpCat.free.map ((yoneda.obj X).map f)).hom
              (FreeAbelianGroup.of φ)) =
          (G.map f).hom
            ((FreeAbelianGroup.lift fun φ => G.map φ.op s) (FreeAbelianGroup.of φ))
        rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of,
          FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
        change G.map (((yoneda.obj X).map f) φ).op s = G.map f (G.map φ.op s)
        simp }
  left_inv f := by
    apply NatTrans.ext
    funext Y
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro φ
    dsimp
    change (FreeAbelianGroup.lift fun ψ =>
        G.map ψ.op (f.app (op X) (FreeAbelianGroup.of (𝟙 X))))
      (FreeAbelianGroup.of φ) = f.app Y (FreeAbelianGroup.of φ)
    rw [FreeAbelianGroup.lift_apply_of]
    symm
    have h := CategoryTheory.congr_fun (f.naturality φ.op)
      (FreeAbelianGroup.of (𝟙 X))
    simp only [CategoryTheory.comp_apply] at h
    change f.app Y
      ((AddCommGrpCat.free.map ((yoneda.obj X).map φ.op)).hom
        (FreeAbelianGroup.of (𝟙 X))) =
      G.map φ.op (f.app (op X) (FreeAbelianGroup.of (𝟙 X))) at h
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of] at h
    simpa using h
  right_inv s := by
    dsimp
    change (FreeAbelianGroup.lift fun φ => G.map φ.op s)
      (FreeAbelianGroup.of (𝟙 X)) = s
    rw [FreeAbelianGroup.lift_apply_of]
    simp
  map_add' f g := rfl

lemma freeAbelianYonedaPresheafHomAddEquiv_comp (X : C)
    {G H : Cᵒᵖ ⥤ AddCommGrpCat.{a}}
    (f : yoneda.obj X ⋙ AddCommGrpCat.free ⟶ G) (g : G ⟶ H) :
    freeAbelianYonedaPresheafHomAddEquiv X H (f ≫ g) =
      g.app (op X) (freeAbelianYonedaPresheafHomAddEquiv X G f) := by
  rfl

/-- Maps from the free abelian representable sheaf are sections. -/
noncomputable def freeAbelianYonedaSheafHomAddEquiv (X : C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (freeAbelianYonedaSheaf J X ⟶ G) ≃+ G.obj.obj (op X) :=
  ((sheafificationAdjunction J AddCommGrpCat.{a}).homAddEquiv
    (yoneda.obj X ⋙ AddCommGrpCat.free) G).trans
      (freeAbelianYonedaPresheafHomAddEquiv X G.obj)

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] in
lemma freeAbelianYonedaSheafHomAddEquiv_comp (X : C)
    {G H : Sheaf J AddCommGrpCat.{a}}
    (f : freeAbelianYonedaSheaf J X ⟶ G) (g : G ⟶ H) :
    freeAbelianYonedaSheafHomAddEquiv X H (f ≫ g) =
      g.hom.app (op X) (freeAbelianYonedaSheafHomAddEquiv X G f) := by
  change freeAbelianYonedaPresheafHomAddEquiv X H.obj
      ((sheafificationAdjunction J AddCommGrpCat.{a}).homEquiv _ _ (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  exact freeAbelianYonedaPresheafHomAddEquiv_comp X _ _

/-- Sections over `X`, as an additive functor on abelian sheaves. -/
noncomputable def sectionsAtFunctorUnlifted (X : C) :
    Sheaf J AddCommGrpCat.{a} ⥤ AddCommGrpCat.{a} :=
  sheafToPresheaf J AddCommGrpCat.{a} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{a}).obj (op X)

noncomputable instance sectionsAtFunctorUnlifted_additive (X : C) :
    (sectionsAtFunctorUnlifted (J := J) X).Additive := by
  dsimp only [sectionsAtFunctorUnlifted]
  infer_instance

/-- Sections over `X`, lifted to the universe in which morphisms of sheaves live. -/
noncomputable def sectionsAtFunctor (X : C) :
    Sheaf J AddCommGrpCat.{a} ⥤ AddCommGrpCat.{max a u} :=
  sectionsAtFunctorUnlifted X ⋙ AddCommGrpCat.uliftFunctor.{u, a}

noncomputable instance sectionsAtFunctor_additive (X : C) :
    (sectionsAtFunctor (J := J) X).Additive := by
  dsimp only [sectionsAtFunctor]
  infer_instance

/-- Apply ordinary, unlifted sections over `X` degreewise to an explicit injective resolution. -/
noncomputable def injectiveResolutionSectionsComplexUnlifted
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{a} ℤ :=
  ((sectionsAtFunctorUnlifted X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    I.cochainComplex

/-- Apply sections over `X` degreewise to an explicit injective resolution. -/
noncomputable def injectiveResolutionSectionsComplex
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    CochainComplex AddCommGrpCat.{max a u} ℤ :=
  ((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (injectiveResolutionSectionsComplexUnlifted X I)

/-- In each degree, cochains from the free abelian representable sheaf are sections. -/
noncomputable def freeAbelianYonedaHomComplexXIso
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) (n : ℤ) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) I.cochainComplex).X n ≅
      (injectiveResolutionSectionsComplex X I).X n :=
  ((CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := freeAbelianYonedaSheaf J X) (K := I.cochainComplex) (zero_add n)).trans
    ((freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X n)).trans
      AddEquiv.ulift.symm)).toAddCommGrpIso

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] in
@[simp]
lemma freeAbelianYonedaHomComplexXIso_hom_apply
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) I.cochainComplex n) :
    (freeAbelianYonedaHomComplexXIso X I n).hom α =
      ULift.up (freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X n)
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n) α)) := by
  rfl

/-- The Hom complex from the free abelian representable sheaf is the sections complex. -/
noncomputable def freeAbelianYonedaHomComplexIsoSections
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) I.cochainComplex ≅
      injectiveResolutionSectionsComplex X I :=
  HomologicalComplex.Hom.isoOfComponents
    (freeAbelianYonedaHomComplexXIso X I) (by
      intro i j hij
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro α
      obtain ⟨f, rfl⟩ :=
        CochainComplex.HomComplex.Cochain.fromSingleMk_surjective
          (X := freeAbelianYonedaSheaf J X) (K := I.cochainComplex) α i (zero_add i)
      change i + 1 = j at hij
      simp only [CategoryTheory.comp_apply,
        freeAbelianYonedaHomComplexXIso_hom_apply,
        CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      dsimp [injectiveResolutionSectionsComplex, sectionsAtFunctor]
      change ULift.up
          ((I.cochainComplex.d i j).hom.app (op X)
            (freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X i) f)) =
        ULift.up
          (freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X j)
            (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
              (CochainComplex.HomComplex.δ i j
                (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add i)))))
      apply ULift.ext
      change (I.cochainComplex.d i j).hom.app (op X)
          (freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X i) f) =
        freeAbelianYonedaSheafHomAddEquiv X (I.cochainComplex.X j)
          (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
            (CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add i))))
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i)
        j j (zero_add j)]
      rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
      exact (freeAbelianYonedaSheafHomAddEquiv_comp X f
        (I.cochainComplex.d i j)).symm)

/-- The cohomology of the sections of an explicit injective resolution computes `H'`. -/
noncomputable def injectiveResolutionSectionsCohomologyAddEquivHPrime
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) (n : ℕ) :
    (injectiveResolutionSectionsComplex X I).homology (n : ℤ) ≃+ F.H' n X :=
  ((HomologicalComplex.homologyMapIso
      (freeAbelianYonedaHomComplexIsoSections X I).symm (n : ℤ)).addCommGroupIsoToAddEquiv).trans
    ((CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor (Sheaf J AddCommGrpCat.{a}) 0).obj
        (freeAbelianYonedaSheaf J X)) I.cochainComplex (n : ℤ)).trans
      I.extAddEquivCohomologyClass.symm)

/-- At a terminal object, the free abelian representable presheaf is the constant presheaf
`ULift ℤ`. -/
noncomputable def freeAbelianYonedaPresheafIsoConstant {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) :=
  NatIso.ofComponents (fun X ↦ by
    letI : Unique (X.unop ⟶ T) :=
      { default := hT.from X.unop
        uniq := fun _ ↦ hT.hom_ext _ _ }
    exact ((FreeAbelianGroup.uniqueEquiv (X.unop ⟶ T)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (fun {X Y} f ↦ by
        letI : Unique ((yoneda.obj T).obj X) :=
          { default := hT.from X.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique (X.unop ⟶ T) :=
          { default := hT.from X.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique ((yoneda.obj T).obj Y) :=
          { default := hT.from Y.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique (Y.unop ⟶ T) :=
          { default := hT.from Y.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro x
        change ULift.up ((FreeAbelianGroup.uniqueEquiv _)
            (FreeAbelianGroup.map _ (FreeAbelianGroup.of x))) =
          ULift.up ((FreeAbelianGroup.uniqueEquiv _) (FreeAbelianGroup.of x))
        rw [FreeAbelianGroup.map_of_apply]
        apply ULift.ext
        change (1 : ℤ) = (FreeAbelianGroup.lift fun _ ↦ 1) (FreeAbelianGroup.of x)
        rw [FreeAbelianGroup.lift_apply_of])

/-- Sheafified form of `freeAbelianYonedaPresheafIsoConstant`. -/
noncomputable def freeAbelianYonedaSheafIsoConstant {T : C} (hT : IsTerminal T) :
    freeAbelianYonedaSheaf J T ≅
      (constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift ℤ)) := by
  simpa only [freeAbelianYonedaSheaf, constantSheaf, Functor.comp_obj] using
    (presheafToSheaf J _).mapIso (freeAbelianYonedaPresheafIsoConstant hT)

/-- The missing terminal-object natural isomorphism noted in Mathlib's sheaf-cohomology API:
cohomology represented by a terminal object agrees with global sheaf cohomology. -/
noncomputable def HPrimeNatIsoH {T : C} (hT : IsTerminal T) (n : ℕ) :
    cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{h}).obj (Opposite.op T) ≅
        cohomologyFunctor J n := by
  change (Abelian.extFunctor n).obj
      (Opposite.op (freeAbelianYonedaSheaf J T)) ≅
    (Abelian.extFunctor n).obj (Opposite.op
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift ℤ))))
  exact (Abelian.extFunctor n).mapIso
    (freeAbelianYonedaSheafIsoConstant (J := J) hT).symm.op

/-- Pointwise additive equivalence supplied by `HPrimeNatIsoH`. -/
noncomputable def HPrimeAddEquivH {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) : F.H' n T ≃+ F.H n :=
  ((HPrimeNatIsoH (J := J) hT n).app F).addCommGroupIsoToAddEquiv

/-- Vanishing of terminal-object cohomology in the `H'` presentation is equivalent to vanishing
of global sheaf cohomology. -/
lemma subsingleton_HPrime_iff_H {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) :
    Subsingleton (F.H' n T) ↔ Subsingleton (F.H n) :=
  (HPrimeAddEquivH (J := J) hT F n).toEquiv.subsingleton_congr

variable [HasFiniteProducts C]

/-- In a nonnegative Čech degree, a column of the injective bicomplex is degreewise the
product of sections over the corresponding finite intersections. -/
noncomputable def cechInjectiveBicomplexColumnXIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (p : ℕ) (q : ℤ) :
    ((cechInjectiveBicomplex U I).X (p : ℤ)).X q ≅
      ∏ᶜ fun x : Fin (p + 1) → ι =>
        (I.cochainComplex.X q).obj.obj (op (∏ᶜ fun k => U (x k))) := by
  dsimp [cechInjectiveBicomplex, cechResolutionBicomplexUnflipped,
    cechCochainFunctorInt, cechComplexFunctor,
    Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor]
  let K := AlgebraicTopology.AlternatingCofaceMapComplex.obj
    (Functor.rightOp (Limits.FormalCoproduct.mk ι U).cech ⋙
      (Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj
        (I.cochainComplex.X q).obj)
  refine K.extendXIso ComplexShape.embeddingUpNat rfl ≪≫ ?_
  exact Iso.refl _

/-- The explicit product complex of sections over the intersections in a fixed Cech degree. -/
noncomputable def cechColumnSectionsComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (p : ℕ) : CochainComplex AddCommGrpCat.{a} ℤ where
  X q := ∏ᶜ fun x : Fin (p + 1) → ι =>
    (I.cochainComplex.X q).obj.obj (op (∏ᶜ fun k => U (x k)))
  d q r := Limits.Pi.map fun x =>
    (I.cochainComplex.d q r).hom.app (op (∏ᶜ fun k => U (x k)))
  shape q r hqr := by
    apply Limits.Pi.hom_ext
    intro x
    rw [Limits.Pi.map_π]
    rw [I.cochainComplex.shape q r hqr]
    simp
  d_comp_d' q r s hqr hrs := by
    apply Limits.Pi.hom_ext
    intro x
    rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, Limits.Pi.map_π]
    change Pi.π
        (fun x : Fin (p + 1) → ι =>
          (I.cochainComplex.X q).obj.obj (op (∏ᶜ fun k => U (x k)))) x ≫
      ((I.cochainComplex.d q r ≫ I.cochainComplex.d r s).hom.app
        (op (∏ᶜ fun k => U (x k)))) = _
    rw [I.cochainComplex.d_comp_d]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A fixed column of the Cech-injective bicomplex is the product of the corresponding
intersection-wise section complexes, including its resolution differential. -/
noncomputable def cechInjectiveBicomplexColumnIsoSectionsComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (p : ℕ) :
    (cechInjectiveBicomplex U I).X (p : ℤ) ≅ cechColumnSectionsComplex U I p :=
  HomologicalComplex.Hom.isoOfComponents
    (cechInjectiveBicomplexColumnXIso U I p) (by
      intro q r hqr
      let Kq := AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (Functor.rightOp (Limits.FormalCoproduct.mk ι U).cech ⋙
          (Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj
            (I.cochainComplex.X q).obj)
      let Kr := AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (Functor.rightOp (Limits.FormalCoproduct.mk ι U).cech ⋙
          (Limits.FormalCoproduct.evalOp C AddCommGrpCat.{a}).obj
            (I.cochainComplex.X r).obj)
      let φ : Kq ⟶ Kr := (cechComplexFunctor (A := AddCommGrpCat.{a}) U).map
        ((sheafToPresheaf J AddCommGrpCat.{a}).map (I.cochainComplex.d q r))
      let hp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
      change (Kq.extendXIso ComplexShape.embeddingUpNat hp).hom ≫
          (cechColumnSectionsComplex U I p).d q r =
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f (p : ℤ) ≫
          (Kr.extendXIso ComplexShape.embeddingUpNat hp).hom
      rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
        (i := p) (i' := (p : ℤ)) hp]
      rw [Category.assoc, Category.assoc]
      rw [(Kr.extendXIso ComplexShape.embeddingUpNat hp).inv_hom_id]
      simp only [Category.comp_id]
      rfl)

omit [HasExt.{h} (Sheaf J AddCommGrpCat.{a})] in
/-- Exactness of all the intersection-wise section complexes is preserved by the product that
forms a fixed Cech column. -/
lemma cechColumnSectionsComplex_exactAt
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (p : ℕ) (q : ℤ)
    (hlocal : ∀ x : Fin (p + 1) → ι,
      (injectiveResolutionSectionsComplexUnlifted
        (∏ᶜ fun k => U (x k)) I).ExactAt q) :
    (cechColumnSectionsComplex U I p).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  intro y hy
  let K := fun x : Fin (p + 1) → ι =>
    injectiveResolutionSectionsComplexUnlifted (∏ᶜ fun k => U (x k)) I
  have hlocal' (x : Fin (p + 1) → ι) :
      ∀ (yx : ((K x).sc q).X₂), ((K x).sc q).g yx = 0 →
        ∃ zx : ((K x).sc q).X₁, ((K x).sc q).f zx = yx := by
    rw [← ShortComplex.ab_exact_iff, ← HomologicalComplex.exactAt_iff]
    exact hlocal x
  have hyx (x : Fin (p + 1) → ι) :
      ((K x).sc q).g
        (Concrete.productEquiv (fun x => ((K x).sc q).X₂) y x) = 0 := by
    have hx := congrArg
      (fun z => Concrete.productEquiv (fun x => ((K x).sc q).X₃) z x) hy
    simp only [Concrete.productEquiv_apply_apply] at hx
    dsimp [cechColumnSectionsComplex, HomologicalComplex.sc, K] at hx
    change (Pi.π (fun x => ((K x).sc q).X₃) x)
      ((Limits.Pi.map (fun x => ((K x).sc q).g)) y) =
        (Pi.π (fun x => ((K x).sc q).X₃) x) 0 at hx
    have hπ := CategoryTheory.congr_fun
      (Limits.Pi.map_π (fun x => ((K x).sc q).g) x) y
    simp only [CategoryTheory.comp_apply] at hπ
    rw [hπ] at hx
    rw [Concrete.productEquiv_apply_apply]
    change ((K x).sc q).g
      ((Pi.π (fun x => ((K x).sc q).X₂) x) y) = 0
    simpa only [map_zero] using hx
  choose z hz using fun x => hlocal' x _ (hyx x)
  refine ⟨(Concrete.productEquiv (fun x => ((K x).sc q).X₁)).symm z, ?_⟩
  apply (Concrete.productEquiv (fun x => ((K x).sc q).X₂)).injective
  funext x
  simp only [Concrete.productEquiv_apply_apply]
  change ((Limits.Pi.map (fun x => ((K x).sc q).f) ≫
    Pi.π (fun x => ((K x).sc q).X₂) x)
      ((Concrete.productEquiv (fun x => ((K x).sc q).X₁)).symm z)) =
    Pi.π (fun x => ((K x).sc q).X₂) x y
  rw [Limits.Pi.map_π, CategoryTheory.comp_apply,
    Concrete.productEquiv_symm_apply_π]
  simpa only [Concrete.productEquiv_apply_apply] using hz x

/-- A cover is Cech-acyclic for `F` when `F` has no positive cohomology on any nonempty finite
intersection occurring in its Cech nerve.

Coverage itself is intentionally separate: `U` is just the family used to form the Cech complex.
Use `IsCechAcyclicCover` for the complete Leray hypothesis. -/
def IsCechAcyclicFor (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (x : Fin (n + 1) → ι),
    Subsingleton (F.H' q (∏ᶜ fun k ↦ U (x k)))

/-- Under the local acyclicity hypothesis, the positive-degree cohomology of the sections
complex of the chosen injective resolution vanishes on every Čech intersection. -/
lemma subsingleton_injectiveResolutionSectionsHomology_of_isCechAcyclicFor
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (hacyclic : IsCechAcyclicFor U F) (q : ℕ) (hq : 0 < q)
    (n : ℕ) (x : Fin (n + 1) → ι) :
    Subsingleton
      ((injectiveResolutionSectionsComplex (∏ᶜ fun k ↦ U (x k)) I).homology (q : ℤ)) :=
  (injectiveResolutionSectionsCohomologyAddEquivHPrime
    (∏ᶜ fun k ↦ U (x k)) I q).toEquiv.subsingleton_congr.mpr
      (hacyclic q hq n x)

/-- If the homology of the universe-lifted complex vanishes, then the original complex is exact
in the same degree. -/
lemma exactAt_of_subsingleton_map_ulift_homology
    (K : CochainComplex AddCommGrpCat.{a} ℤ) (q : ℤ)
    (h : Subsingleton
      ((((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology q)) :
    K.ExactAt q := by
  let L := ((AddCommGrpCat.uliftFunctor.{u, a}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  letI : Subsingleton (L.homology q) := h
  have hL : L.ExactAt q :=
    (HomologicalComplex.exactAt_iff_isZero_homology L q).2
      (AddCommGrpCat.isZero_of_subsingleton _)
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hL ⊢
  intro y hy
  have hy' : (L.sc q).g (ULift.up y) = 0 := by
    apply ULift.ext
    exact hy
  obtain ⟨z, hz⟩ := hL (ULift.up y) hy'
  obtain ⟨z⟩ := z
  refine ⟨z, ?_⟩
  exact congrArg ULift.down hz

/-- Local acyclicity makes every fixed Cech column exact in positive resolution degree. -/
lemma cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (hacyclic : IsCechAcyclicFor U F) (p q : ℕ) (hq : 0 < q) :
    ((cechInjectiveBicomplex U I).X (p : ℤ)).ExactAt (q : ℤ) := by
  apply HomologicalComplex.ExactAt.of_iso
    (cechColumnSectionsComplex_exactAt U I p (q : ℤ) (fun x => ?_))
    (cechInjectiveBicomplexColumnIsoSectionsComplex U I p).symm
  apply exactAt_of_subsingleton_map_ulift_homology
  simpa only [injectiveResolutionSectionsComplex,
    injectiveResolutionSectionsComplexUnlifted, sectionsAtFunctor,
    sectionsAtFunctorUnlifted] using
    (subsingleton_injectiveResolutionSectionsHomology_of_isCechAcyclicFor
      U I hacyclic q hq p x)

/-- Equivalently, every positive-resolution-degree homology object of a fixed Cech column
vanishes under local acyclicity. -/
lemma subsingleton_cechInjectiveBicomplexColumnHomology_of_isCechAcyclicFor
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (hacyclic : IsCechAcyclicFor U F) (p q : ℕ) (hq : 0 < q) :
    Subsingleton
      (((cechInjectiveBicomplex U I).X (p : ℤ)).homology (q : ℤ)) :=
  AddCommGrpCat.subsingleton_of_isZero
    (cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
      U I hacyclic p q hq).isZero_homology

/-- Under local acyclicity, every positive-resolution-degree entry on the initial page of the
column-filtration spectral sequence is zero. -/
lemma isZero_cechInjectiveInitialPage_of_isCechAcyclicFor
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (hacyclic : IsCechAcyclicFor U F) (p q : ℕ) (hq : 0 < q) :
    IsZero (((cechInjectiveSpectralSequence U I).page 2).X
      ((p : ℤ), (q : ℤ))) :=
  IsZero.of_iso
    (cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
      U I hacyclic p q hq).isZero_homology
    (cechInjectiveInitialPageColumnHomologyIso U I (p : ℤ) (q : ℤ))

/-- Elementwise form of `isZero_cechInjectiveInitialPage_of_isCechAcyclicFor`. -/
lemma subsingleton_cechInjectiveInitialPage_of_isCechAcyclicFor
    {F : Sheaf J AddCommGrpCat.{a}} (U : ι → C) (I : InjectiveResolution F)
    (hacyclic : IsCechAcyclicFor U F) (p q : ℕ) (hq : 0 < q) :
    Subsingleton (((cechInjectiveSpectralSequence U I).page 2).X
      ((p : ℤ), (q : ℤ))) :=
  AddCommGrpCat.subsingleton_of_isZero
    (isZero_cechInjectiveInitialPage_of_isCechAcyclicFor
      U I hacyclic p q hq)

/-- The standard Leray hypothesis for a Cech-to-derived comparison: `U` covers the terminal
object and `F` is acyclic on every nonempty finite intersection in the Cech nerve. -/
def IsCechAcyclicCover (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  J.CoversTop U ∧ IsCechAcyclicFor U F

/-- The conclusion of a degreewise Cech-to-derived comparison theorem.

This is a proposition so downstream vanishing results need not depend on a particular choice of
isomorphism.  It is not an assumption installed globally and it contains no unproved declaration. -/
def CechComputesDerivedCohomologyAt (U : ι → C) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) : Prop :=
  Nonempty ((cechCohomology U F.obj n : AddCommGrpCat.{a}) ≃+ F.H n)

/-- A cover computes derived sheaf cohomology when it does so in every degree. -/
def CechComputesDerivedCohomology (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  ∀ n, CechComputesDerivedCohomologyAt U F n

/-- The positive-degree comparison for the singleton cover by a terminal object.  Here the Cech
complex is contractible, while `IsCechAcyclicFor` says precisely that the derived group vanishes;
`HPrimeAddEquivH` identifies its terminal-object and global presentations. -/
theorem cechComputesDerivedCohomologyAt_singleton_terminal_of_pos
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) (hn : 0 < n)
    (hacyclic : IsCechAcyclicFor (fun _ : PUnit ↦ T) F) :
    CechComputesDerivedCohomologyAt (fun _ : PUnit ↦ T) F n := by
  let V : C := ∏ᶜ fun _ : Fin 1 ↦ T
  have hV : IsTerminal V := IsTerminal.ofUniqueHom
    (fun X ↦ Pi.lift fun _ ↦ hT.from X)
    (fun X f ↦ Pi.hom_ext f (Pi.lift fun _ ↦ hT.from X) fun k ↦ hT.hom_ext _ _)
  have hHPrime := hacyclic n hn 0 (fun _ ↦ PUnit.unit)
  change Subsingleton (F.H' n V) at hHPrime
  have hH : Subsingleton (F.H n) :=
    (subsingleton_HPrime_iff_H (J := J) hV F n).mp hHPrime
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  have hexact := cechComplex_exactAt_succ_of_isTerminal
    (i₀ := PUnit.unit) (fun _ : PUnit ↦ T) hT (𝟙 T) F.obj m
  have hzero : IsZero
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1)) :=
    hexact.isZero_homology
  letI : Subsingleton
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1) : AddCommGrpCat.{a}) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  letI : Subsingleton (F.H (m + 1)) := hH
  letI : Unique
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1) : AddCommGrpCat.{a}) :=
    { default := 0
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  letI : Unique (F.H (m + 1)) :=
    { default := 0
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact ⟨AddEquiv.ofUnique⟩

/-- If Cech cohomology computes derived sheaf cohomology in degree `n`, exactness of the explicit
Cech complex at `n` implies vanishing of derived sheaf cohomology there. -/
lemma subsingleton_H_of_cech_exactAt (U : ι → C) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) (hcomparison : CechComputesDerivedCohomologyAt U F n)
    (hexact : ((cechComplexFunctor U).obj F.obj).ExactAt n) :
    Subsingleton (F.H n) := by
  let e := hcomparison.some
  have hzero : IsZero (cechCohomology U F.obj n) :=
    cechCohomology_isZero_of_exactAt U F.obj n hexact
  letI : Subsingleton (cechCohomology U F.obj n : AddCommGrpCat.{a}) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

end Sheaf

end CategoryTheory
