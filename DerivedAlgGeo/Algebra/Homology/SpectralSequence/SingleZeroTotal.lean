/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomologicalBicomplex
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.TotalFlipNaturality
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Total complex of a bicomplex supported in degree zero

Placing an integer-indexed cochain complex in horizontal degree zero gives a
bicomplex whose total is naturally isomorphic to the original complex.
Exchanging axes gives the corresponding vertical-degree-zero comparison.
Under an ambient total-existence assumption, the signed flipped comparison
is natural in the input integer-indexed cochain complex.
For any source complex shape embedded into integer cochains with a chosen
degree mapping to zero, the total of its extended single is naturally the
input integer-indexed cochain complex.

## Main definitions

* `HomologicalComplex₂.singleZeroBicomplex` places a complex in horizontal degree zero.

## Main results

* `HomologicalComplex₂.singleZeroHasTotal` constructs its total without ambient coproducts.
* `HomologicalComplex₂.singleZeroTotalIso` and
  `HomologicalComplex₂.singleZeroTotalIso_naturality` identify that total
  naturally with the original complex.
* `HomologicalComplex₂.singleZeroFlipTotalIso` and
  `HomologicalComplex₂.singleZeroFlipTotalIso_naturality` give the corresponding
  comparison after exchanging axes.
* `HomologicalComplex₂.singleZeroFlipTotalNatIso` assembles the signed
  flipped degree-zero comparisons into a natural isomorphism.
* `HomologicalComplex₂.singleExtendMapTotalIso` compares the total of an
  extended single with the original complex when the selected degree maps to zero.

## Implementation notes

The total-degree `n` diagonal has one surviving summand, at `(0, n)`. Its
cofan supplies the required total in any preadditive category with a zero
object. The flipped comparison uses Mathlib's signed total symmetry, so its
sign agrees with the existing totalization convention.
The natural isomorphism uses these component isomorphisms and their proved
naturality, rather than changing the sign convention. The extended-single
comparison first normalizes the bicomplex, then applies that signed isomorphism.

## References

The construction uses Mathlib's `HomologicalComplex.single` and
`HomologicalComplex₂.totalFlipIso` and the repository's
`HomologicalComplex₂.singleExtendMapFlipIso`. It introduces no geometric assumptions.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C]

section Zero

variable [HasZeroMorphisms C]

@[reassoc]
private lemma singleZeroComponent_hom_inv {A B : CochainComplex C ℤ} (e : A ≅ B) (n : ℤ) :
    e.hom.f n ≫ e.inv.f n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id]
  rfl

@[reassoc]
private lemma singleZeroComponent_inv_hom {A B : CochainComplex C ℤ} (e : A ≅ B) (n : ℤ) :
    e.inv.f n ≫ e.hom.f n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id]
  rfl

attribute [local simp] singleZeroComponent_hom_inv singleZeroComponent_hom_inv_assoc
  singleZeroComponent_inv_hom singleZeroComponent_inv_hom_assoc
variable [HasZeroObject C]
variable (A : CochainComplex C ℤ)

/-- A bicomplex concentrated in horizontal degree zero. -/
noncomputable def singleZeroBicomplex :
    HomologicalComplex₂ C
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) 0).obj A

/-- Accepts an explicit equality identifying the horizontal index with zero, so callers can
evaluate at their existing index without first rewriting the whole bicomplex. -/
noncomputable def singleZeroXIso (i : ℤ) (hi : i = 0) :
    (singleZeroBicomplex A).X i ≅ A := by
  subst i
  exact HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A

variable {A B : CochainComplex C ℤ}

/-- Apply a cochain map to the supported horizontal degree. This uses no additive
structure beyond the zero morphisms needed to form the single complex. -/
noncomputable def singleZeroBicomplexMap (f : A ⟶ B) :
    singleZeroBicomplex A ⟶ singleZeroBicomplex B :=
  (HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) 0).map f

variable (A : CochainComplex C ℤ)

private noncomputable def singleZeroCofan (n : ℤ) :
    (singleZeroBicomplex A).toGradedObject.CofanMapObjFun
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n :=
  GradedObject.CofanMapObjFun.mk _ _ _ (A.X n) (fun ⟨i, j⟩ hij =>
    if hi : i = 0 then
      (singleZeroXIso A i hi).hom.f j ≫
        (A.XIsoOfEq (by dsimp at hij; omega)).hom
    else 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def singleZeroCofanIsColimit (n : ℤ) :
    IsColimit (singleZeroCofan A n) :=
  Cofan.IsColimit.mk _
    (fun s => (singleZeroXIso A 0 rfl).inv.f n ≫ s.inj ⟨⟨0, n⟩, by simp⟩)
    (fun s => by
      rintro ⟨⟨i, j⟩, hij⟩
      by_cases hi : i = 0
      · subst i
        have hj : j = n := by simpa using hij
        subst j
        dsimp [singleZeroCofan, singleZeroXIso]
        simp only [Category.comp_id, singleZeroComponent_hom_inv_assoc]
      · apply IsZero.eq_of_src
        apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    (fun s m hm => by
      have h := hm ⟨⟨0, n⟩, by simp⟩
      dsimp [singleZeroCofan, singleZeroXIso] at h
      have h' := congrArg (fun k => (singleZeroXIso A 0 rfl).inv.f n ≫ k) h
      simpa [singleZeroXIso, Category.assoc] using h')

end Zero

attribute [local simp] singleZeroComponent_hom_inv singleZeroComponent_hom_inv_assoc
  singleZeroComponent_inv_hom singleZeroComponent_inv_hom_assoc

variable [Preadditive C] [HasZeroObject C]
variable (A : CochainComplex C ℤ)

/-- The unique supported summand gives the total cofan without a category-wide
coproduct assumption. -/
instance singleZeroHasTotal : (singleZeroBicomplex A).HasTotal (ComplexShape.up ℤ) :=
  GradedObject.CofanMapObjFun.hasMap _ _ (singleZeroCofan A) (singleZeroCofanIsColimit A)

/-- Projects the total-degree diagonal onto its surviving `(0,n)` summand; the inverse is
that summand's canonical inclusion. Every other summand is zero. -/
noncomputable def singleZeroTotalXIso (n : ℤ) :
    ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X n ≅ A.X n where
  hom := HomologicalComplex₂.totalDesc _ (fun i j hij ↦
    if hi : i = 0 then
      (singleZeroXIso A i hi).hom.f j ≫
        (A.XIsoOfEq (by dsimp at hij; omega)).hom
    else 0)
  inv := (singleZeroXIso A 0 rfl).inv.f n ≫
    (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ) 0 n n (by simp)
  hom_inv_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi
  inv_hom_id := by
    dsimp
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [singleZeroXIso]

/-- The horizontal differential vanishes and the totalization sign on the surviving
column is positive, so the component projections commute with the original differential. -/
noncomputable def singleZeroTotalIso :
    (singleZeroBicomplex A).total (ComplexShape.up ℤ) ≅ A :=
  HomologicalComplex.Hom.isoOfComponents (singleZeroTotalXIso A) (by
    intro n m hnm
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by dsimp at hij; omega
      subst j
      dsimp [singleZeroTotalXIso]
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp [singleZeroXIso]
      rw [← Category.assoc, HomologicalComplex₂.total_d]
      let ι := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 n n hij
      let d₁ := (singleZeroBicomplex A).D₁ (ComplexShape.up ℤ) n m
      let d₂ := (singleZeroBicomplex A).D₂ (ComplexShape.up ℤ) n m
      let φ : ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m ⟶
          A.X m := (singleZeroBicomplex A).totalDesc (fun i j hij ↦
        if h : i = 0 then
          (singleZeroXIso A i h).hom.f j ≫
            (A.XIsoOfEq (by
              change i + j = m at hij
              omega)).hom
        else 0)
      change ((singleZeroBicomplex A).X 0).d n m ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℤ) 0 A).hom.f m =
        (ι ≫ (d₁ + d₂)) ≫ φ
      have hcomp : ι ≫ (d₁ + d₂) = ι ≫ d₁ + ι ≫ d₂ :=
        Preadditive.comp_add _ _ _ _ _ _
      have hadd : (ι ≫ d₁ + ι ≫ d₂) ≫ φ =
          (ι ≫ d₁) ≫ φ + (ι ≫ d₂) ≫ φ :=
        Preadditive.add_comp _ _ _ _ _ _
      refine Eq.trans ?_ ((congrArg (fun x ↦ x ≫ φ) hcomp).trans hadd).symm
      have ha₁ : (ι ≫ d₁) ≫ φ = ι ≫ d₁ ≫ φ := Category.assoc _ _ _
      have ha₂ : (ι ≫ d₂) ≫ φ = ι ≫ d₂ ≫ φ := Category.assoc _ _ _
      rw [ha₁, ha₂]
      dsimp [ι, d₁, d₂, φ]
      rw [HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc]
      rw [(singleZeroBicomplex A).d₁_eq' (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) n m]
      rw [(singleZeroBicomplex A).d₂_eq (ComplexShape.up ℤ)
        0 hnm m (by simp)]
      simp [singleZeroBicomplex]
      let δ := ((singleZeroBicomplex A).X 0).d n m
      let ιm := (singleZeroBicomplex A).ιTotal (ComplexShape.up ℤ)
        0 m m (by simp)
      let e := HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 A
      change δ ≫ e.hom.f m =
        (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
        (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ)
      have hzero : (1 : ℤˣ) •
          (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) = 0 :=
        one_smul _ _
      have hvertical : (1 : ℤˣ) • (δ ≫ ιm) = δ ≫ ιm := one_smul _ _
      have hright :
          (((1 : ℤˣ) • (0 : ((singleZeroBicomplex A).X 0).X n ⟶
            ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m)) ≫ φ) +
            (((1 : ℤˣ) • (δ ≫ ιm)) ≫ φ) =
          (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) :=
        congrArg₂ (fun x y ↦ x + y)
          (congrArg (fun x ↦ x ≫ φ) hzero)
          (congrArg (fun x ↦ x ≫ φ) hvertical)
      refine Eq.trans ?_ hright.symm
      have hz : (0 : ((singleZeroBicomplex A).X 0).X n ⟶
          ((singleZeroBicomplex A).total (ComplexShape.up ℤ)).X m) ≫ φ = 0 :=
        zero_comp
      rw [show (0 ≫ φ) + ((δ ≫ ιm) ≫ φ) =
          ((δ ≫ ιm) ≫ φ) by rw [hz, zero_add]]
      have hdesc : ιm ≫ φ = e.hom.f m := by
        dsimp [ιm, φ, e]
        rw [HomologicalComplex₂.ι_totalDesc]
        simp [singleZeroXIso]
      exact (congrArg (fun x ↦ δ ≫ x) hdesc.symm).trans
        (Category.assoc δ ιm φ).symm
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
      apply HomologicalComplex.isZero_single_obj_X
      exact hi)

variable {A B : CochainComplex C ℤ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The total-complex identification for a bicomplex supported in horizontal degree zero is
natural. -/
@[reassoc]
lemma singleZeroTotalIso_naturality (f : A ⟶ B) :
    total.map (singleZeroBicomplexMap f) (ComplexShape.up ℤ) ≫
        (singleZeroTotalIso B).hom =
      (singleZeroTotalIso A).hom ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [← cancel_epi (singleZeroTotalXIso A n).inv]
  dsimp [singleZeroTotalIso]
  simp [singleZeroTotalXIso, singleZeroBicomplexMap, singleZeroBicomplex,
    singleZeroXIso]
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv.f n ≫
      (((HomologicalComplex.single (CochainComplex C ℤ)
        (ComplexShape.up ℤ) 0).map f).f 0).f n ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).hom.f n = f.f n
  rw [HomologicalComplex.single_map_f_self]
  simp

/-- Exchanges axes using Mathlib's signed total symmetry, then applies
`HomologicalComplex₂.singleZeroTotalIso`, preserving the established totalization sign. -/
noncomputable def singleZeroFlipTotalIso (A : CochainComplex C ℤ) :
    (singleZeroBicomplex A).flip.total (ComplexShape.up ℤ) ≅ A :=
  (singleZeroBicomplex A).totalFlipIso (ComplexShape.up ℤ) ≪≫ singleZeroTotalIso A

/-- Composes naturality of the signed total symmetry with naturality of the
first-axis comparison. -/
@[reassoc]
lemma singleZeroFlipTotalIso_naturality (f : A ⟶ B) :
    total.map (flipMap (singleZeroBicomplexMap f)) (ComplexShape.up ℤ) ≫
        (singleZeroFlipTotalIso B).hom =
      (singleZeroFlipTotalIso A).hom ≫ f := by
  simp only [singleZeroFlipTotalIso, Iso.trans_hom]
  rw [← Category.assoc, totalFlipIso_naturality]
  rw [Category.assoc, singleZeroTotalIso_naturality]
  simp only [Category.assoc]

/-- Packages `HomologicalComplex₂.singleZeroFlipTotalIso` into a natural
isomorphism. Mathlib's `HomologicalComplex₂.totalFunctor` requires totals for every bicomplex;
the objectwise single-zero totals alone do not construct that functor.
Flipping moves support from outer to inner degree zero. -/
noncomputable def singleZeroFlipTotalNatIso
    [∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      K.HasTotal (ComplexShape.up ℤ)] :
    HomologicalComplex.single (CochainComplex C ℤ) (ComplexShape.up ℤ) 0 ⋙
      flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
      totalFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
    𝟭 (CochainComplex C ℤ) :=
  NatIso.ofComponents
    (fun K => singleZeroFlipTotalIso K)
    (by
      intro K L f
      exact singleZeroFlipTotalIso_naturality f)

/-- Extend a single along any complex-shape embedding whose chosen degree
maps to integer degree zero. The pre-total bicomplex isomorphism identifies
its target with the flipped single-zero bicomplex; the signed total natural
isomorphism then recovers the input cochain complex. -/
noncomputable def singleExtendMapTotalIso
    [∀ K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      K.HasTotal (ComplexShape.up ℤ)]
    {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) (i : ι) (h : e.f i = 0) :
    ((HomologicalComplex.single C c i ⋙ e.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
        totalFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex C ℤ) :=
  (Functor.isoWhiskerRight
    (singleExtendMapFlipIso (C := C) (ComplexShape.up ℤ) e i 0 h) _).trans
    (singleZeroFlipTotalNatIso (C := C))

end HomologicalComplex₂
