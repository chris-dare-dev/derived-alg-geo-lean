/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedHeart
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HomFiniteWitness
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Algebraic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.JordanHolder
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic.ChargeRay
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan.Ambient
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The algebraic stability condition on the bounded derived category of a field

This file constructs the standard, nonzero algebraic stability condition on
`Dᵇ(FGModuleCat k)`.  Its heart is finite-dimensional vector spaces, every
nonzero heart object has phase one, and the unique stable orbit is represented
by the one-dimensional vector space in degree zero.

The construction is deliberately categorical.  Its central charge is minus
the Euler pairing with the degree-zero copy of `k`; no free lattice is
identified with the triangulated Grothendieck group.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.Triangulated.AlgebraicWitness

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

universe u

variable (k : Type u) [Field k]

/-- Algebraic Artinianness of a module gives categorical Artinianness. -/
local instance moduleCat_isArtinianObject (M : ModuleCat.{u} k)
    [IsArtinian k M] : IsArtinianObject M := by
  apply ObjectProperty.is_of_prop isArtinianObject
  exact RelHomClass.isWellFounded
    (ModuleCat.subobjectModule M).toOrderEmbedding.ltEmbedding

/-- A finitely generated vector space is Artinian as an object of
`FGModuleCat`. -/
local instance fgModuleCat_isArtinianObject (M : FGModuleCat.{u} k) :
    IsArtinianObject M := by
  letI : Module.Finite k M := M.property
  letI : IsArtinian k M := inferInstance
  let F := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
  have hM : IsArtinianObject (ModuleCat.of k M) := inferInstance
  letI : IsArtinianObject (F.obj M) := hM
  exact isArtinianObject_of_fullFaithful_preservesMono F

/-- A finite-dimensional vector space is a simple categorical object exactly
when it has dimension one. -/
theorem fgModuleCat_simple_iff_finrank_eq_one (V : FGModuleCat.{u} k) :
    Simple V ↔ Module.finrank k V = 1 := by
  constructor
  · intro hsimple
    letI : Simple V := hsimple
    letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp (fun hV ↦
      Simple.not_isZero V
        (ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (ModuleCat.isZero_of_subsingleton V.obj)))
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    let l : k →ₗ[k] V := LinearMap.toSpanSingleton k V v
    let f : FGModuleCat.of k k ⟶ V := FGModuleCat.ofHom l
    have hl : Function.Injective l :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton k hv)
    let U := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
    letI : Mono (U.map f) := (ModuleCat.mono_iff_injective _).2 hl
    letI : Mono f := U.mono_of_mono_map inferInstance
    have hf : f ≠ 0 := by
      intro hf
      have hfv := congrArg (fun g : FGModuleCat.of k k ⟶ V ↦ g.hom.hom 1) hf
      change l 1 = 0 at hfv
      exact hv (by simpa [l] using hfv)
    letI : IsIso f := isIso_of_mono_of_nonzero hf
    have hrank := (FGModuleCat.isoToLinearEquiv (asIso f)).finrank_eq
    simpa using hrank.symm
  · intro hrank
    let U := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
    have hsimple : Simple (U.obj V) := by
      exact (simple_iff_isSimpleModule' (U.obj V)).2
        (isSimpleModule_iff_finrank_eq_one.2 hrank)
    letI : Simple (U.obj V) := hsimple
    exact U.simple_of_simple_obj V

/-- The concrete proper triangulated category used by the witness. -/
abbrev DerivedFiniteVect := DerivedCategory.Bounded (FGModuleCat.{u} k)

/-- The standard bounded t-structure on `Dᵇ(FGModuleCat k)`. -/
abbrev standardT : TStructure (DerivedFiniteVect k) :=
  DerivedCategory.TStructure.t.onBounded

/-- The one-dimensional vector space, placed in cohomological degree zero. -/
noncomputable abbrev residueObject : DerivedFiniteVect k :=
  DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k) |>.obj
    (FGModuleCat.of k k)

/-- Every bounded-derived object is bounded for the induced standard
t-structure. -/
theorem standardT_isBounded : TStructure.IsBounded (standardT k) := by
  intro E
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := E.property
  exact ⟨⟨a, (ObjectProperty.tStructure_isGE_iff
    DerivedCategory.TStructure.t.bounded DerivedCategory.TStructure.t E a).2 ha⟩,
    ⟨b, (ObjectProperty.tStructure_isLE_iff
      DerivedCategory.TStructure.t.bounded DerivedCategory.TStructure.t E b).2 hb⟩⟩

/-- The essential image of honest bounded complexes lies in the canonical
bounded derived category. -/
theorem boundedQh_essImage_le_bounded :
    (boundedQh k).essImage ≤
      (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded := by
  intro Y hY
  obtain ⟨X, ⟨e⟩⟩ := hY
  apply (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded.prop_of_iso e
  obtain ⟨K, hK, hX⟩ :=
    (HomotopyCategory.bounded_iff_exists X.obj).1 X.property
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK
  letI := ha
  letI := hb
  have hQ : (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded
      (DerivedCategory.Q.obj K) := ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  let eQ : (boundedQh k).obj X ≅ DerivedCategory.Q.obj K :=
    eqToIso (congrArg (fun Z ↦ DerivedCategory.Qh.obj Z) hX.symm) ≪≫
      (DerivedCategory.quotientCompQhIso (FGModuleCat.{u} k)).app K
  exact (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded.prop_of_iso
    eQ.symm hQ

/-- The fully faithful restriction from the derived essential image to the
canonical bounded derived category. -/
noncomputable def boundedImageToBounded :
    CategoryTheory.Functor (boundedQh k).essImage.FullSubcategory
      (DerivedFiniteVect k) :=
  (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded.lift
    (boundedQh k).essImage.ι
    (fun X ↦ boundedQh_essImage_le_bounded k X.obj X.property)

noncomputable instance boundedImageToBounded_additive :
    (boundedImageToBounded k).Additive := by
  dsimp [boundedImageToBounded]
  infer_instance

noncomputable instance boundedImageToBounded_linear :
    Functor.Linear k (boundedImageToBounded k) where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    change r • f.hom = r • f.hom
    rfl

noncomputable instance boundedImageToBounded_full :
    (boundedImageToBounded k).Full := by
  dsimp [boundedImageToBounded]
  infer_instance

noncomputable instance boundedImageToBounded_faithful :
    (boundedImageToBounded k).Faithful := by
  dsimp [boundedImageToBounded]
  infer_instance

noncomputable instance boundedImageToBounded_commShift :
    (boundedImageToBounded k).CommShift ℤ := by
  dsimp [boundedImageToBounded]
  infer_instance

/-- Every canonically bounded derived object is represented by an honest
bounded complex. -/
noncomputable instance boundedImageToBounded_essSurj :
    (boundedImageToBounded k).EssSurj where
  mem_essImage E := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := E.property
    letI := ha
    letI := hb
    obtain ⟨K, hKge, hKle, ⟨e⟩⟩ :=
      DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE E.obj a b
    let X : HomotopyCategory.Bounded (FGModuleCat.{u} k) :=
      ⟨(HomotopyCategory.quotient _ _).obj K,
        (HomotopyCategory.bounded_quotient_obj_iff K).2
          ⟨⟨a, hKge⟩, ⟨b, hKle⟩⟩⟩
    let Y : (boundedQh k).essImage.FullSubcategory :=
      ⟨(boundedQh k).obj X, (boundedQh k).obj_mem_essImage X⟩
    refine ⟨Y, ⟨?_⟩⟩
    exact (DerivedCategory.TStructure.t (C := FGModuleCat.{u} k)).bounded.ι.preimageIso
      ((DerivedCategory.quotientCompQhIso (FGModuleCat.{u} k)).app K ≪≫ e.symm)

/-- The canonical bounded derived category of finite-dimensional vector
spaces is Hom-finite with finite shift amplitude. -/
noncomputable instance homFiniteBounded_derivedFiniteVect :
    HomFiniteBounded k (DerivedFiniteVect k) :=
  HomFiniteBounded.of_essSurj (boundedImageToBounded k)
    (Functor.FullyFaithful.ofFullyFaithful _)

/-- Properness also supplies ordinary (unshifted) Hom-finiteness. -/
noncomputable instance homFinite_derivedFiniteVect :
    SerreFunctor.HomFinite k (DerivedFiniteVect k) where
  finite X Y := by
    letI : Module.Finite k (X ⟶ Y⟦(0 : ℤ)⟧) := inferInstance
    exact Module.Finite.equiv
      (Linear.homCongr k (Iso.refl X)
        ((shiftFunctorZero (DerivedFiniteVect k) ℤ).app Y))

/-- From the degree-zero residue object to an object of the standard heart,
all nonzero shifted Hom spaces vanish.  Positive shifts vanish because every
finite-dimensional vector space is projective; negative shifts vanish by the
standard t-structure. -/
theorem subsingleton_residue_shiftedHom_of_ne_zero
    (E : DerivedFiniteVect k) (hE : (standardT k).heart E)
    (i : ℤ) (hi : i ≠ 0) : Subsingleton (residueObject k ⟶ E⟦i⟧) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hresHeart : (standardT k).heart (residueObject k) :=
      DerivedCategory.boundedHeart_singleFunctor_obj _ _
    rw [TStructure.mem_heart_iff] at hresHeart hE
    letI : (standardT k).IsGE E 0 := hE.2
    have hGEshift : (standardT k).IsGE (E⟦i⟧) (-i) :=
      (standardT k).isGE_shift E 0 i (-i) (by omega)
    exact ⟨fun f g ↦ by
      rw [(standardT k).zero_of_isLE_of_isGE f 0 (-i) (by omega)
          hresHeart.1 hGEshift,
        (standardT k).zero_of_isLE_of_isGE g 0 (-i) (by omega)
          hresHeart.1 hGEshift]⟩
  · have himage :
        (DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).essImage E := by
      rw [DerivedCategory.essImage_boundedSingleFunctor_eq_boundedHeart]
      exact hE
    obtain ⟨Y, ⟨e⟩⟩ := himage
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    have hn : n ≠ 0 := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    letI : Subsingleton (Abelian.Ext (FGModuleCat.of k k) Y (m + 1)) :=
      Abelian.Ext.subsingleton_of_projective (FGModuleCat.of k k) Y m
    have hamb : Subsingleton
        (DerivedCategory.Bounded.ι.obj (residueObject k) ⟶
          (DerivedCategory.Bounded.ι.obj
            ((DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).obj Y))
              ⟦((m + 1 : ℕ) : ℤ)⟧) := by
      change Subsingleton
        (ShiftedHom
          ((DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj
            (FGModuleCat.of k k))
          ((DerivedCategory.singleFunctor (FGModuleCat.{u} k) 0).obj Y)
          ((m + 1 : ℕ) : ℤ))
      exact (Abelian.Ext.homLinearEquiv (R := k) (X := FGModuleCat.of k k)
        (Y := Y) (n := m + 1)).symm.toEquiv.subsingleton
    have hbase : Subsingleton
        (residueObject k ⟶
          (DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k) |>.obj Y)
            ⟦((m + 1 : ℕ) : ℤ)⟧) := by
      letI := hamb
      exact (homShiftLinearEquiv (k := k)
        (DerivedCategory.Bounded.ι (C := FGModuleCat.{u} k))
        (ObjectProperty.fullyFaithfulι _) (residueObject k)
        ((DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).obj Y)
        ((m + 1 : ℕ) : ℤ)).toEquiv.subsingleton
    letI := hbase
    exact (Linear.homCongr k (Iso.refl _)
      ((shiftFunctor (DerivedFiniteVect k) ((m + 1 : ℕ) : ℤ)).mapIso e)).symm.toEquiv.subsingleton

/-- On the standard heart, the Euler pairing with the residue object is the
ordinary dimension of the degree-zero Hom space. -/
theorem chiHom_residue_eq_finrank (E : DerivedFiniteVect k)
    (hE : (standardT k).heart E) :
    chiHom k (DerivedFiniteVect k) (residueObject k) E =
      (Module.finrank k (residueObject k ⟶ E) : ℤ) := by
  rw [chiHom, finsum_eq_single (f := fun i : ℤ ↦
    (i.negOnePow : ℤ) * Module.finrank k (residueObject k ⟶ E⟦i⟧)) 0]
  · let e₀ : (residueObject k ⟶ E⟦(0 : ℤ)⟧) ≃ₗ[k]
        (residueObject k ⟶ E) :=
      Linear.homCongr k (Iso.refl (residueObject k))
        ((shiftFunctorZero (DerivedFiniteVect k) ℤ).app E)
    rw [e₀.finrank_eq]
    norm_num
  · intro i hi
    letI := subsingleton_residue_shiftedHom_of_ne_zero k E hE i hi
    simp [Module.finrank_zero_of_subsingleton]

/-- The honest central charge of the witness: minus the Euler pairing with
the degree-zero copy of the ground field. -/
noncomputable def centralCharge : K₀ (DerivedFiniteVect k) →+ ℂ where
  toFun x := -((chiRight k (DerivedFiniteVect k) (residueObject k) x : ℤ) : ℂ)
  map_zero' := by simp
  map_add' x y := by simp only [map_add, Int.cast_add]; abel

/-- A morphism from the residue object to a degree-zero vector space is the
same thing as a vector in that space. -/
noncomputable def residueHomEquiv (Y : FGModuleCat.{u} k) :
    (residueObject k ⟶
        (DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).obj Y) ≃ₗ[k] Y :=
  (Linear.homCongr k (Iso.refl (residueObject k))
      ((shiftFunctorZero (DerivedFiniteVect k) ℤ).app
        ((DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).obj Y)).symm).trans
    ((homShiftLinearEquiv (k := k)
      (DerivedCategory.Bounded.ι (C := FGModuleCat.{u} k))
      (ObjectProperty.fullyFaithfulι _) (residueObject k)
      ((DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).obj Y) 0).trans
    ((Abelian.Ext.homLinearEquiv (R := k) (X := FGModuleCat.of k k)
      (Y := Y) (n := 0)).symm.trans
      ((Abelian.Ext.linearEquiv₀ (R := k) (X := FGModuleCat.of k k)
        (Y := Y)).trans
        (((ModuleCat.homLinearEquiv
          (M := (FGModuleCat.of k k).obj) (N := Y.obj) (S := k)).symm.trans
            (InducedCategory.homLinearEquiv (R := k)).symm).symm.trans
          (LinearMap.ringLmapEquivSelf k k Y)))))

/-- A nonzero object of the standard heart receives a genuinely negative,
rather than merely nonpositive, charge. -/
theorem finrank_residueHom_pos (E : DerivedFiniteVect k)
    (hE : (standardT k).heart E) (hE₀ : ¬IsZero E) :
    0 < Module.finrank k (residueObject k ⟶ E) := by
  have himage :
      (DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).essImage E := by
    rw [DerivedCategory.essImage_boundedSingleFunctor_eq_boundedHeart]
    exact hE
  obtain ⟨Y, ⟨e⟩⟩ := himage
  have hY : ¬IsZero Y := by
    intro hY
    apply hE₀
    exact ((DerivedCategory.boundedSingleFunctor (FGModuleCat.{u} k)).map_isZero hY).of_iso e.symm
  have hYobj : ¬IsZero Y.obj := by
    intro hYobj
    exact hY (IsZero.of_full_of_faithful_of_isZero
      (ModuleCat.isFG.{u} k).ι Y hYobj)
  have hnotSub : ¬Subsingleton Y := by
    simpa only [ModuleCat.isZero_iff_subsingleton, not_iff_not] using hYobj
  letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hnotSub
  rw [← (Linear.homCongr k (Iso.refl (residueObject k)) e).finrank_eq,
    (residueHomEquiv k Y).finrank_eq]
  exact Module.finrank_pos

theorem centralCharge_of_heart (E : DerivedFiniteVect k)
    (hE : (standardT k).heart E) :
    centralCharge k (K₀.of (DerivedFiniteVect k) E) =
      -((Module.finrank k (residueObject k ⟶ E) : ℤ) : ℂ) := by
  change -(((chiRight k (DerivedFiniteVect k) (residueObject k))
    (K₀.of (DerivedFiniteVect k) E) : ℤ) : ℂ) = _
  rw [chiRight_of, chiHom_residue_eq_finrank k E hE]

/-- The standard stability function: every nonzero heart object lies on the
negative real axis. -/
noncomputable def standardStabilityFunction :
    WeakStabilityCondition.StabilityFunction (standardT k) where
  Z := centralCharge k
  nonzero_mem E hE := by
    change centralCharge k (K₀.of (DerivedFiniteVect k) E) ∈
      semiClosedUpperHalfPlane
    rw [centralCharge_of_heart k E hE.1]
    refine Or.inr ⟨by simp, ?_⟩
    simpa using (show (0 : ℤ) < Module.finrank k (residueObject k ⟶ E) by
      exact_mod_cast finrank_residueHom_pos k E hE.1 hE.2)

/-- The weak stability function used by the heart-to-slicing construction. -/
noncomputable def standardWeakStabilityFunction :
    WeakStabilityCondition.WeakStabilityFunction (standardT k) :=
  (standardStabilityFunction k).toWeak

theorem standardWeak_slope_eq_top (E : DerivedFiniteVect k)
    (hE : (standardT k).heart E) :
    (standardWeakStabilityFunction k).slope E = ⊤ := by
  apply (standardWeakStabilityFunction k).slope_of_im_nonpos
  rw [show (standardWeakStabilityFunction k).charge E =
      centralCharge k (K₀.of (DerivedFiniteVect k) E) by rfl,
    centralCharge_of_heart k E hE]
  simp

/-- Since all nonzero heart objects have the same phase, every heart object
is weak-semistable. -/
theorem standardWeak_isSemistable (E : DerivedFiniteVect k)
    (hE : (standardT k).heart E) :
    (standardWeakStabilityFunction k).IsSemistable E := by
  refine ⟨hE, ?_⟩
  intro A B hA hB hA₀ hB₀ f g d hdist
  rw [standardWeak_slope_eq_top k A hA,
    standardWeak_slope_eq_top k B hB]

/-- The standard weak stability function has one-step HN filtrations. -/
theorem standardWeak_hasHNProperty :
    (standardWeakStabilityFunction k).HasHNProperty := by
  intro E hE
  obtain ⟨F, -⟩ :=
    WeakStabilityCondition.WeakStabilityFunction.exists_hn_with_last_slope_of_semistable
      (standardWeakStabilityFunction k) hE
        (standardWeak_isSemistable k E.obj E.property)
  exact ⟨F⟩

/-- Ambient HN existence follows from boundedness of the standard
t-structure. -/
theorem standardWeak_ambientHN : ∀ E : DerivedFiniteVect k,
    Nonempty (HNFiltration (DerivedFiniteVect k)
      (standardWeakStabilityFunction k).ambientPhasePredicate E) :=
  (standardWeakStabilityFunction k).ambientHN_of_bounded
    (standardT_isBounded k) (standardWeak_hasHNProperty k)

/-- The slicing reconstructed from the constant-phase standard heart. -/
noncomputable def standardSlicing : Slicing (DerivedFiniteVect k) :=
  ((standardWeakStabilityFunction k).reverseSlicingObligationsOfHN
    (standardWeak_ambientHN k)).toSlicing

/-- The Euler charge cannot vanish on a nonzero object in one of the
reconstructed slices. -/
theorem centralCharge_ne_zero_of_ambientPhasePredicate
    (phi : ℝ) (E : DerivedFiniteVect k)
    (hP : (standardWeakStabilityFunction k).ambientPhasePredicate phi E)
    (hE₀ : ¬IsZero E) :
    centralCharge k (K₀.of (DerivedFiniteVect k) E) ≠ 0 := by
  let n : ℤ := WeakStabilityCondition.phaseIndex phi
  let H : DerivedFiniteVect k := E⟦(-n : ℤ)⟧
  have hshifted :
      WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate
        (standardWeakStabilityFunction k)
        (WeakStabilityCondition.phaseBase phi) n E := by
    simpa [WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate,
      n] using hP
  rcases hshifted with hzero | ⟨hHss, hHphase⟩
  · exact False.elim (hE₀ hzero)
  · have hH₀ : ¬IsZero H := by
      intro hHzero
      apply hE₀
      let e : H⟦n⟧ ≅ E :=
        (shiftFunctorCompIsoId (DerivedFiniteVect k) (-n : ℤ) n (by simp)).app E
      exact ((shiftFunctor (DerivedFiniteVect k) n).map_isZero hHzero).of_iso e.symm
    have hHcharge : centralCharge k
        (K₀.of (DerivedFiniteVect k) H) ≠ 0 :=
      semiClosedUpperHalfPlane_ne_zero
        ((standardStabilityFunction k).nonzero_mem H ⟨hHss.1, hH₀⟩)
    intro hcharge
    apply hHcharge
    rw [show H = E⟦(-n : ℤ)⟧ by rfl, K₀.of_shift_int, map_zsmul,
      hcharge, smul_zero]

/-- The ordinary pre-stability condition underlying the algebraic witness. -/
noncomputable def standardPreStabilityCondition :
    PreStabilityCondition (DerivedFiniteVect k) :=
  PreStabilityCondition.WithClassMap.ofStrict (standardSlicing k)
    (centralCharge k) (by
      intro phi E hP hE₀
      have hP' :
          WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate
            (standardWeakStabilityFunction k) phi E := hP
      obtain ⟨m, hm, -, hcharge⟩ :=
        (standardWeakStabilityFunction k).ambientPhasePredicate_charge_ray
          phi E hP' hE₀
      have hm₀ : m ≠ 0 := by
        intro hmzero
        apply centralCharge_ne_zero_of_ambientPhasePredicate k phi E hP' hE₀
        rw [show centralCharge k (K₀.of (DerivedFiniteVect k) E) =
          (standardWeakStabilityFunction k).charge E by rfl,
          hcharge, hmzero]
        simp
      refine ⟨m, lt_of_le_of_ne hm hm₀.symm, ?_⟩
      change centralCharge k (K₀.of (DerivedFiniteVect k) E) = _
      calc
        _ = (standardWeakStabilityFunction k).charge E := by rfl
        _ = (m : ℂ) * Complex.exp
            (((Real.pi : ℂ) * (phi : ℂ)) * Complex.I) := hcharge
        _ = _ := by push_cast; rfl)

/-- Nonzero semistable objects in the standard slicing occur only at
integral phases. -/
theorem standardSlicing_phase_integer {phi : ℝ} {E : DerivedFiniteVect k}
    (hP : (standardSlicing k).P phi E) (hE₀ : ¬IsZero E) :
    ∃ n : ℤ, phi = (n : ℝ) := by
  have hP' : (standardWeakStabilityFunction k).ambientPhasePredicate phi E := hP
  let n : ℤ := WeakStabilityCondition.phaseIndex phi
  let H : DerivedFiniteVect k := E⟦(-n : ℤ)⟧
  have hshifted :
      WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate
        (standardWeakStabilityFunction k)
          (WeakStabilityCondition.phaseBase phi) n E := by
    simpa [WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate,
      n] using hP'
  rcases hshifted with hzero | ⟨hHss, hHphase⟩
  · exact False.elim (hE₀ hzero)
  · have hphaseOne : (standardWeakStabilityFunction k).phase H = 1 := by
      unfold WeakStabilityCondition.WeakStabilityFunction.phase
      rw [standardWeak_slope_eq_top k H hHss.1]
      simp
    have hbase : WeakStabilityCondition.phaseBase phi = 1 :=
      hHphase.symm.trans hphaseOne
    refine ⟨n + 1, ?_⟩
    calc
      phi = WeakStabilityCondition.phaseBase phi +
          WeakStabilityCondition.phaseIndex phi :=
        (WeakStabilityCondition.phaseBase_add_phaseIndex phi).symm
      _ = 1 + (n : ℝ) := by rw [hbase]
      _ = ((n + 1 : ℤ) : ℝ) := by push_cast; ring

/-- Every half-open unit heart of the discrete standard slicing is exactly
the slice at the unique integral phase it contains. -/
theorem standardDualHeart_heart_iff (r : ℝ) (E : DerivedFiniteVect k) :
    (((standardSlicing k).phaseShift (DerivedFiniteVect k) r).toDualTStructure
        (DerivedFiniteVect k)).heart E ↔
      (standardSlicing k).P ((⌈r⌉ : ℤ) : ℝ) E := by
  let s := standardSlicing k
  let q : ℤ := ⌈r⌉
  have hrq : r ≤ (q : ℝ) := Int.le_ceil r
  have hqr : (q : ℝ) < r + 1 := Int.ceil_lt_add_one r
  constructor
  · intro hheart
    by_cases hE₀ : IsZero E
    · exact s.zero_mem_of_isZero (DerivedFiniteVect k) (q : ℝ) E hE₀
    · have hcuts : s.geProp (DerivedFiniteVect k) r E ∧
          s.ltProp (DerivedFiniteVect k) (1 + r) E := by
        rw [((s.phaseShift (DerivedFiniteVect k) r).toDualTStructure_heart_iff
          (DerivedFiniteVect k) E),
          s.phaseShift_geProp_zero (DerivedFiniteVect k) r E,
          s.phaseShift_ltProp (DerivedFiniteVect k) r 1 E] at hheart
        exact hheart
      have hminus := s.phiMinus_ge_of_geProp (DerivedFiniteVect k) hE₀ hcuts.1
      have hplus := s.phiPlus_lt_of_ltProp (DerivedFiniteVect k) hE₀ hcuts.2
      obtain ⟨F, hn, hfirst, hlast⟩ :=
        s.exists_hn_nonzero_boundaries (DerivedFiniteVect k) hE₀
      have hplusEq := s.phiPlus_eq (DerivedFiniteVect k) E hE₀ F hn hfirst
      have hminusEq := s.phiMinus_eq (DerivedFiniteVect k) E hE₀ F hn hlast
      obtain ⟨p, hp⟩ := standardSlicing_phase_integer k
        (F.semistable ⟨0, hn⟩) hfirst
      obtain ⟨m, hm⟩ := standardSlicing_phase_integer k
        (F.semistable ⟨F.n - 1, by omega⟩) hlast
      have hpRange : r ≤ (p : ℝ) ∧ (p : ℝ) < r + 1 := by
        constructor
        · calc
            r ≤ s.phiMinus (DerivedFiniteVect k) E hE₀ := hminus
            _ ≤ s.phiPlus (DerivedFiniteVect k) E hE₀ :=
              s.phiMinus_le_phiPlus (DerivedFiniteVect k) E hE₀
            _ = F.phiPlus (DerivedFiniteVect k) hn := hplusEq
            _ = (p : ℝ) := hp
        · calc
            (p : ℝ) = F.phiPlus (DerivedFiniteVect k) hn := hp.symm
            _ = s.phiPlus (DerivedFiniteVect k) E hE₀ := hplusEq.symm
            _ < 1 + r := hplus
            _ = r + 1 := by ring
      have hmRange : r ≤ (m : ℝ) ∧ (m : ℝ) < r + 1 := by
        constructor
        · calc
            r ≤ s.phiMinus (DerivedFiniteVect k) E hE₀ := hminus
            _ = F.phiMinus (DerivedFiniteVect k) hn := hminusEq
            _ = (m : ℝ) := hm
        · calc
            (m : ℝ) = F.phiMinus (DerivedFiniteVect k) hn := hm.symm
            _ ≤ s.phiPlus (DerivedFiniteVect k) E hE₀ :=
              hminusEq.symm.le.trans
                (s.phiMinus_le_phiPlus (DerivedFiniteVect k) E hE₀)
            _ < 1 + r := hplus
            _ = r + 1 := by ring
      have hpq : p = q := by
        apply le_antisymm
        · have hp_lt : (p : ℝ) < (q : ℝ) + 1 := by linarith
          exact_mod_cast (Int.lt_add_one_iff.mp (by exact_mod_cast hp_lt))
        · exact Int.ceil_le.mpr hpRange.1
      have hmq : m = q := by
        apply le_antisymm
        · have hm_lt : (m : ℝ) < (q : ℝ) + 1 := by linarith
          exact_mod_cast (Int.lt_add_one_iff.mp (by exact_mod_cast hm_lt))
        · exact Int.ceil_le.mpr hmRange.1
      have hendpoints : s.phiPlus (DerivedFiniteVect k) E hE₀ =
          s.phiMinus (DerivedFiniteVect k) E hE₀ := by
        calc
          _ = (p : ℝ) := hplusEq.trans hp
          _ = (q : ℝ) := by rw [hpq]
          _ = (m : ℝ) := by rw [hmq]
          _ = _ := (hminusEq.trans hm).symm
      have hsemi := s.semistable_of_phiPlus_eq_phiMinus
        (DerivedFiniteVect k) hE₀ hendpoints
      have hphase : s.phiPlus (DerivedFiniteVect k) E hE₀ = (q : ℝ) := by
        calc
          s.phiPlus (DerivedFiniteVect k) E hE₀ = (p : ℝ) := hplusEq.trans hp
          _ = (q : ℝ) := by rw [hpq]
      change s.P (q : ℝ) E
      rw [← hphase]
      exact hsemi
  · intro hP
    rw [((s.phaseShift (DerivedFiniteVect k) r).toDualTStructure_heart_iff
      (DerivedFiniteVect k) E),
      s.phaseShift_geProp_zero (DerivedFiniteVect k) r E,
      s.phaseShift_ltProp (DerivedFiniteVect k) r 1 E]
    exact ⟨s.geProp_anti (DerivedFiniteVect k) hrq E
        (s.geProp_of_semistable (DerivedFiniteVect k) hP),
      s.ltProp_of_leProp_of_lt (DerivedFiniteVect k) (by linarith : (q : ℝ) < 1 + r) E
        (s.leProp_of_semistable (DerivedFiniteVect k) hP le_rfl)⟩

/-- The normalized representative of an integral phase is the endpoint
`1` of the standard half-open interval. -/
theorem phaseBase_int (q : ℤ) :
    WeakStabilityCondition.phaseBase (q : ℝ) = 1 := by
  let n := WeakStabilityCondition.phaseIndex (q : ℝ)
  have hdecomp := WeakStabilityCondition.phaseBase_add_phaseIndex (q : ℝ)
  have hmem := WeakStabilityCondition.phaseBase_mem (q : ℝ)
  have hcast : WeakStabilityCondition.phaseBase (q : ℝ) = ((q - n : ℤ) : ℝ) := by
    push_cast
    linarith
  have hpos : 0 < q - n := by
    exact_mod_cast (hcast ▸ hmem.1)
  have hle : q - n ≤ 1 := by
    exact_mod_cast (hcast ▸ hmem.2)
  have hqn : q - n = 1 := by omega
  rw [hcast, hqn]
  norm_num

/-- At an integral phase, membership in the standard slice is exactly
membership in the standard heart after the normalizing shift. -/
theorem standardSlicing_mem_integer_iff (q : ℤ) (E : DerivedFiniteVect k) :
    (standardSlicing k).P (q : ℝ) E ↔
      (standardT k).heart
        (E⟦(-WeakStabilityCondition.phaseIndex (q : ℝ) : ℤ)⟧) := by
  change (standardWeakStabilityFunction k).ambientPhasePredicate (q : ℝ) E ↔ _
  unfold WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate
  rw [show WeakStabilityCondition.phaseBase (q : ℝ) = 1 from phaseBase_int q]
  change (IsZero E ∨
      ((standardWeakStabilityFunction k).IsSemistable
          (E⟦(-WeakStabilityCondition.phaseIndex (q : ℝ) : ℤ)⟧) ∧
        (standardWeakStabilityFunction k).phase
          (E⟦(-WeakStabilityCondition.phaseIndex (q : ℝ) : ℤ)⟧) = 1)) ↔ _
  constructor
  · rintro (hE | ⟨hss, -⟩)
    · exact (standardT k).heart.prop_of_isZero
        ((shiftFunctor (DerivedFiniteVect k)
          (-WeakStabilityCondition.phaseIndex (q : ℝ) : ℤ)).map_isZero hE)
    · exact hss.1
  · intro hheart
    refine Or.inr ⟨standardWeak_isSemistable k _ hheart, ?_⟩
    unfold WeakStabilityCondition.WeakStabilityFunction.phase
    rw [standardWeak_slope_eq_top k _ hheart]
    simp

/-- The canonical heart of the reconstructed discrete slicing is its unique
slice in `(0, 1]`, namely phase one. -/
theorem standardCanonicalHeart_heart_iff (E : DerivedFiniteVect k) :
    (standardSlicing k).toTStructure.heart E ↔
      (standardSlicing k).P 1 E := by
  let s := standardSlicing k
  constructor
  · intro hheart
    by_cases hE₀ : IsZero E
    · exact s.zero_mem_of_isZero (DerivedFiniteVect k) 1 E hE₀
    · have hcuts := (s.toTStructure_heart_iff (DerivedFiniteVect k) E).mp hheart
      have hminus := s.phiMinus_gt_of_gtProp
        (DerivedFiniteVect k) hE₀ hcuts.1
      have hplus := s.phiPlus_le_of_leProp
        (DerivedFiniteVect k) hE₀ hcuts.2
      obtain ⟨F, hn, hfirst, hlast⟩ :=
        s.exists_hn_nonzero_boundaries (DerivedFiniteVect k) hE₀
      have hplusEq := s.phiPlus_eq (DerivedFiniteVect k) E hE₀ F hn
        hfirst
      have hminusEq := s.phiMinus_eq (DerivedFiniteVect k) E hE₀ F hn
        hlast
      obtain ⟨p, hp⟩ := standardSlicing_phase_integer k
        (F.semistable ⟨0, hn⟩) hfirst
      obtain ⟨m, hm⟩ := standardSlicing_phase_integer k
        (F.semistable ⟨F.n - 1, by omega⟩) hlast
      have hpLe : p ≤ 1 := by
        exact_mod_cast (show (p : ℝ) ≤ 1 by
          calc
            (p : ℝ) = F.phiPlus (DerivedFiniteVect k) hn := hp.symm
            _ = s.phiPlus (DerivedFiniteVect k) E hE₀ := hplusEq.symm
            _ ≤ 1 := hplus)
      have hmPos : 0 < m := by
        exact_mod_cast (show (0 : ℝ) < (m : ℝ) by
          calc
            (0 : ℝ) < s.phiMinus (DerivedFiniteVect k) E hE₀ := hminus
            _ = F.phiMinus (DerivedFiniteVect k) hn := hminusEq
            _ = (m : ℝ) := hm)
      have hmp : m ≤ p := by
        exact_mod_cast (show (m : ℝ) ≤ (p : ℝ) by
          calc
            (m : ℝ) = F.phiMinus (DerivedFiniteVect k) hn := hm.symm
            _ = s.phiMinus (DerivedFiniteVect k) E hE₀ := hminusEq.symm
            _ ≤ s.phiPlus (DerivedFiniteVect k) E hE₀ :=
              s.phiMinus_le_phiPlus (DerivedFiniteVect k) E hE₀
            _ = F.phiPlus (DerivedFiniteVect k) hn := hplusEq
            _ = (p : ℝ) := hp)
      have hpOne : p = 1 := by omega
      have hmOne : m = 1 := by omega
      have hendpoints : s.phiPlus (DerivedFiniteVect k) E hE₀ =
          s.phiMinus (DerivedFiniteVect k) E hE₀ := by
        calc
          _ = (p : ℝ) := hplusEq.trans hp
          _ = 1 := by rw [hpOne]; norm_num
          _ = (m : ℝ) := by rw [hmOne]; norm_num
          _ = _ := (hminusEq.trans hm).symm
      have hsemi := s.semistable_of_phiPlus_eq_phiMinus
        (DerivedFiniteVect k) hE₀ hendpoints
      have hphase : s.phiPlus (DerivedFiniteVect k) E hE₀ = 1 := by
        calc
          _ = (p : ℝ) := hplusEq.trans hp
          _ = 1 := by rw [hpOne]; norm_num
      rw [← hphase]
      exact hsemi
  · intro hP
    rw [s.toTStructure_heart_iff (DerivedFiniteVect k) E]
    exact ⟨s.gtProp_of_semistable (DerivedFiniteVect k) hP (by norm_num),
      s.leProp_of_semistable (DerivedFiniteVect k) hP le_rfl⟩

/-- Shifting by the normalizing degree identifies every half-open unit heart
with the standard bounded heart. -/
noncomputable def dualHeartToStandardEquivalence (r : ℝ) :
    (((standardSlicing k).phaseShift (DerivedFiniteVect k) r).toDualTStructure
        (DerivedFiniteVect k)).heart.FullSubcategory ≌
      (standardT k).heart.FullSubcategory :=
  let q : ℤ := ⌈r⌉
  let n : ℤ := WeakStabilityCondition.phaseIndex (q : ℝ)
  (shiftEquiv (DerivedFiniteVect k) (-n)).congrFullSubcategory (by
    ext E
    exact (standardSlicing_mem_integer_iff k q E).symm.trans
      (standardDualHeart_heart_iff k r E).symm)

/-- Every half-open unit heart of the standard slicing is equivalent to
finite-dimensional vector spaces. -/
noncomputable def dualHeartEquivalence (r : ℝ) :
    (((standardSlicing k).phaseShift (DerivedFiniteVect k) r).toDualTStructure
        (DerivedFiniteVect k)).heart.FullSubcategory ≌ FGModuleCat.{u} k :=
  (dualHeartToStandardEquivalence k r).trans
    (DerivedCategory.boundedHeartEquivalence (FGModuleCat.{u} k)).symm

/-- The canonical slicing heart is equivalent to finite-dimensional vector
spaces. -/
noncomputable def canonicalHeartEquivalence :
    (standardSlicing k).toTStructure.heart.FullSubcategory ≌ FGModuleCat.{u} k :=
  let eHeart : (standardSlicing k).toTStructure.heart.FullSubcategory ≌
      (((standardSlicing k).phaseShift (DerivedFiniteVect k) 1).toDualTStructure
        (DerivedFiniteVect k)).heart.FullSubcategory :=
    (Equivalence.refl : DerivedFiniteVect k ≌ DerivedFiniteVect k).congrFullSubcategory (by
      ext E
      change ((((standardSlicing k).phaseShift (DerivedFiniteVect k) 1).toDualTStructure
        (DerivedFiniteVect k)).heart E ↔
          (standardSlicing k).toTStructure.heart E)
      have hdual := standardDualHeart_heart_iff k 1 E
      refine hdual.trans ?_
      convert (standardCanonicalHeart_heart_iff k E).symm using 1
      all_goals norm_num)
  eHeart.trans (dualHeartEquivalence k 1)

/-- In an integral half-open heart, whose every object has one phase,
stability is exactly categorical simplicity. -/
theorem dualHeart_isStableAt_iff_simple (q : ℤ)
    (E : (((standardSlicing k).phaseShift (DerivedFiniteVect k) (q : ℝ)).toDualTStructure
      (DerivedFiniteVect k)).heart.FullSubcategory) :
    (standardSlicing k).IsStableAt (q : ℝ) E.obj ↔ Simple E := by
  let s := standardSlicing k
  let tR := (s.phaseShift (DerivedFiniteVect k) (q : ℝ)).toDualTStructure
    (DerivedFiniteVect k)
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory :=
    TStructure.heartFullSubcategoryAbelian tR
  letI : IsNormalMonoCategory tR.heart.FullSubcategory :=
    Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory tR.heart.FullSubcategory :=
    Abelian.toIsNormalEpiCategory
  letI : Balanced tR.heart.FullSubcategory := by infer_instance
  have hmem (X : DerivedFiniteVect k) : tR.heart X ↔ s.P (q : ℝ) X := by
    change ((((standardSlicing k).phaseShift (DerivedFiniteVect k) (q : ℝ)).toDualTStructure
      (DerivedFiniteVect k)).heart X ↔ (standardSlicing k).P (q : ℝ) X)
    convert standardDualHeart_heart_iff k (q : ℝ) X using 1
    all_goals norm_num
  constructor
  · intro hstable
    refine ⟨fun {X} f _ ↦ ?_⟩
    constructor
    · intro hfIso hfZero
      have hzeroIso : IsIso (0 : X ⟶ E) := by simpa [hfZero] using hfIso
      have hEzero : IsZero E := (isIsoZero_iff_source_target_isZero X E).1 hzeroIso |>.2
      exact False.elim (hstable.2.1 (tR.heart.ι.map_isZero hEzero))
    · intro hfNonzero
      let Q := cokernel f
      let p : E ⟶ Q := cokernel.π f
      have hS : (ShortComplex.mk f p (cokernel.condition f)).ShortExact :=
        StabilityFunction.shortExact_of_mono f
      letI : Epi p := hS.epi_g
      obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
        (C := DerivedFiniteVect k) tR f p (cokernel.condition f) (fun {W} a ha ↦ by
          exact ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
            hS.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
      rcases hstable.2.2 ((hmem X.obj).1 X.property) ((hmem Q.obj).1 Q.property)
          f.hom p.hom d hd with hX | hQ
      · exact False.elim (hfNonzero (by
          apply ObjectProperty.hom_ext
          exact hX.eq_of_src _ _))
      · have hQ' : IsZero Q :=
          ObjectProperty.FullSubcategory.isZero_of_obj_isZero hQ
        letI : Epi f := Preadditive.epi_of_isZero_cokernel f hQ'
        exact isIso_of_mono_of_epi f
  · intro hsimple
    letI : Simple E := hsimple
    refine ⟨(hmem E.obj).1 E.property, ?_, ?_⟩
    · intro hE
      exact Simple.not_isZero E
        (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hE)
    · intro X Y hX hY f g d hd
      let XH : tR.heart.FullSubcategory := ⟨X, (hmem X).2 hX⟩
      let YH : tR.heart.FullSubcategory := ⟨Y, (hmem Y).2 hY⟩
      let fH : XH ⟶ E := ObjectProperty.homMk f
      let gH : E ⟶ YH := ObjectProperty.homMk g
      have hS := TStructure.heartFullSubcategory_shortExact_of_distTriang
        tR (A := XH) (B := E) (Q := YH) (f := fH) (g := gH) hd
      letI : Mono fH := hS.mono_f
      by_cases hf : fH = 0
      · exact Or.inl (tR.heart.ι.map_isZero (Limits.IsZero.of_mono_eq_zero fH hf))
      · letI : IsIso fH := isIso_of_mono_of_nonzero hf
        haveI : IsIso f := by
          change IsIso fH.hom
          infer_instance
        exact Or.inr ((Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hd).mpr
          (by change IsIso f; infer_instance))

/-- Objects of every half-open unit heart of the standard slicing are
Artinian. -/
theorem dualHeart_isArtinianObject (r : ℝ)
    (E : (((standardSlicing k).phaseShift (DerivedFiniteVect k) r).toDualTStructure
      (DerivedFiniteVect k)).heart.FullSubcategory) : IsArtinianObject E := by
  let F := (dualHeartEquivalence k r).functor
  letI : IsArtinianObject (F.obj E) := inferInstance
  exact isArtinianObject_of_fullFaithful_preservesMono F

/-- Objects of every half-open unit heart of the standard slicing are
Noetherian. -/
theorem dualHeart_isNoetherianObject (r : ℝ)
    (E : (((standardSlicing k).phaseShift (DerivedFiniteVect k) r).toDualTStructure
      (DerivedFiniteVect k)).heart.FullSubcategory) : IsNoetherianObject E := by
  let F := (dualHeartEquivalence k r).functor
  letI : IsNoetherianObject (F.obj E) := inferInstance
  exact isNoetherianObject_of_fullFaithful_preservesMono F

/-- The discrete standard slicing is locally finite. -/
theorem standardSlicing_isLocallyFinite :
    (standardSlicing k).IsLocallyFinite (DerivedFiniteVect k) := by
  apply Slicing.IsLocallyFinite.of_strictFiniteLength
    (DerivedFiniteVect k) (standardSlicing k)
      (η := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  intro t
  letI : Fact (t - (1 : ℝ) / 4 < t + (1 : ℝ) / 4) := ⟨by linarith⟩
  letI : Fact ((t + (1 : ℝ) / 4) - (t - (1 : ℝ) / 4) ≤ 1) := ⟨by linarith⟩
  intro E
  let F := Slicing.IntervalCat.toRightHeart
    (C := DerivedFiniteVect k) (s := standardSlicing k)
      (t - (1 : ℝ) / 4) (t + (1 : ℝ) / 4)
      (Fact.out : (t + (1 : ℝ) / 4) - (t - (1 : ℝ) / 4) ≤ 1)
  letI : IsArtinianObject (F.obj E) :=
    dualHeart_isArtinianObject k ((t + (1 : ℝ) / 4) - 1) (F.obj E)
  letI : IsNoetherianObject (F.obj E) :=
    dualHeart_isNoetherianObject k ((t + (1 : ℝ) / 4) - 1) (F.obj E)
  exact ⟨Slicing.IntervalCat.isStrictArtinianObject_of_rightHeart
      (DerivedFiniteVect k) (standardSlicing k),
    Slicing.IntervalCat.isStrictNoetherianObject_of_rightHeart
      (DerivedFiniteVect k) (standardSlicing k)⟩

/-- The genuine locally finite stability condition carried by the standard
heart of finite-dimensional vector spaces. -/
noncomputable def standardStabilityCondition :
    StabilityCondition (DerivedFiniteVect k) where
  toWithClassMap := standardPreStabilityCondition k
  locallyFinite := standardSlicing_isLocallyFinite k

/-- Objects of the canonical slicing heart are Artinian. -/
theorem canonicalHeart_isArtinianObject
    (E : (standardSlicing k).toTStructure.heart.FullSubcategory) :
    IsArtinianObject E := by
  let F := (canonicalHeartEquivalence k).functor
  letI : IsArtinianObject (F.obj E) := inferInstance
  exact isArtinianObject_of_fullFaithful_preservesMono F

/-- Objects of the canonical slicing heart are Noetherian. -/
theorem canonicalHeart_isNoetherianObject
    (E : (standardSlicing k).toTStructure.heart.FullSubcategory) :
    IsNoetherianObject E := by
  let F := (canonicalHeartEquivalence k).functor
  letI : IsNoetherianObject (F.obj E) := inferInstance
  exact isNoetherianObject_of_fullFaithful_preservesMono F

/-- The unique simple object of the canonical heart, transported from the
one-dimensional vector space. -/
noncomputable def simpleHeartObject :
    (standardSlicing k).toTStructure.heart.FullSubcategory :=
  (canonicalHeartEquivalence k).inverse.obj (FGModuleCat.of k k)

/-- The distinguished one-dimensional object of the canonical heart is
simple. -/
theorem simpleHeartObject_simple : Simple (simpleHeartObject k) := by
  have hsimple : Simple (FGModuleCat.of k k) :=
    (fgModuleCat_simple_iff_finrank_eq_one k _).2 (by simp)
  letI : Simple (FGModuleCat.of k k) := hsimple
  exact simple_obj (canonicalHeartEquivalence k).inverse _

/-- Every simple object of the canonical heart is isomorphic to the
distinguished one-dimensional object. -/
theorem canonicalHeart_simple_iso
    (T : (standardSlicing k).toTStructure.heart.FullSubcategory)
    (hT : Simple T) : Nonempty (T ≅ simpleHeartObject k) := by
  let e := canonicalHeartEquivalence k
  letI : Simple T := hT
  let V : FGModuleCat.{u} k := e.functor.obj T
  letI : Module.Finite k V := V.property
  have hsimpleV : Simple V := simple_obj e.functor T
  have hrank : Module.finrank k V = 1 :=
    (fgModuleCat_simple_iff_finrank_eq_one k _).1 hsimpleV
  let l : V ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq V k (by simpa using hrank)
  let iV : V ≅ FGModuleCat.of k k :=
    l.toFGModuleCatIso
  exact ⟨e.unitIso.app T ≪≫ e.inverse.mapIso iV⟩

/-- The canonical heart of the standard stability condition has finite
length and exactly one simple isomorphism class. -/
theorem standardStabilityCondition_hasFiniteLengthHeart :
    (standardStabilityCondition k).HasFiniteLengthHeart := by
  refine ⟨1, fun _ ↦ simpleHeartObject k, ?_, ?_, ?_⟩
  · intro E
    exact ⟨canonicalHeart_isArtinianObject k E,
      canonicalHeart_isNoetherianObject k E⟩
  · intro i
    exact simpleHeartObject_simple k
  · intro T hT
    exact ⟨0, canonicalHeart_simple_iso k T hT⟩

/-- A simple object of the standard bounded heart is isomorphic, in the
ambient derived category, to the degree-zero one-dimensional vector space. -/
theorem standardHeart_simple_iso_residue
    (H : (standardT k).heart.FullSubcategory) (hH : Simple H) :
    Nonempty (H.obj ≅ residueObject k) := by
  let e := (DerivedCategory.boundedHeartEquivalence (FGModuleCat.{u} k)).symm
  letI : Simple H := hH
  let V : FGModuleCat.{u} k := e.functor.obj H
  letI : Module.Finite k V := V.property
  have hsimpleV : Simple V := simple_obj e.functor H
  have hrank : Module.finrank k V = 1 :=
    (fgModuleCat_simple_iff_finrank_eq_one k _).1 hsimpleV
  let l : V ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq V k (by simpa using hrank)
  let iV : V ≅ FGModuleCat.of k k := l.toFGModuleCatIso
  let iH : H ≅ e.inverse.obj (FGModuleCat.of k k) :=
    e.unitIso.app H ≪≫ e.inverse.mapIso iV
  exact ⟨(standardT k).heart.ι.mapIso iH⟩

/-- A fixed stable representative, obtained by transporting the
one-dimensional vector space into the phase-one half-open heart. -/
noncomputable def stableRepresentative : DerivedFiniteVect k :=
  ((dualHeartEquivalence k ((1 : ℤ) : ℝ)).inverse.obj (FGModuleCat.of k k)).obj

/-- The fixed representative is genuinely stable at phase one. -/
theorem stableRepresentative_isStable :
    (standardSlicing k).IsStableAt 1 (stableRepresentative k) := by
  let E := (dualHeartEquivalence k ((1 : ℤ) : ℝ)).inverse.obj (FGModuleCat.of k k)
  have hsimple : Simple (FGModuleCat.of k k) :=
    (fgModuleCat_simple_iff_finrank_eq_one k _).2 (by simp)
  letI : Simple (FGModuleCat.of k k) := hsimple
  have hsimpleE : Simple E :=
    simple_obj (dualHeartEquivalence k ((1 : ℤ) : ℝ)).inverse _
  simpa [stableRepresentative, E] using
    (dualHeart_isStableAt_iff_simple k (1 : ℤ) E).2 hsimpleE

/-- Every stable object is a shift of the degree-zero one-dimensional vector
space, with the normalizing shift made explicit. -/
theorem stable_iso_residue_shift {phi : ℝ} {F : DerivedFiniteVect k}
    (hF : (standardSlicing k).IsStableAt phi F) :
    ∃ q : ℤ, phi = (q : ℝ) ∧
      Nonempty (F ≅ (residueObject k)⟦WeakStabilityCondition.phaseIndex (q : ℝ)⟧) := by
  obtain ⟨q, hq⟩ := standardSlicing_phase_integer k hF.1 hF.2.1
  subst phi
  let n : ℤ := WeakStabilityCondition.phaseIndex (q : ℝ)
  let tR := (((standardSlicing k).phaseShift
    (DerivedFiniteVect k) (q : ℝ)).toDualTStructure (DerivedFiniteVect k))
  let E : tR.heart.FullSubcategory :=
    ⟨F, (standardDualHeart_heart_iff k (q : ℝ) F).2 (by simpa using hF.1)⟩
  have hsimpleE : Simple E :=
    (dualHeart_isStableAt_iff_simple k q E).1 (by simpa using hF)
  let H : (standardT k).heart.FullSubcategory :=
    (dualHeartToStandardEquivalence k (q : ℝ)).functor.obj E
  have hsimpleH : Simple H := by
    letI : Simple E := hsimpleE
    exact simple_obj (dualHeartToStandardEquivalence k (q : ℝ)).functor E
  obtain ⟨iH⟩ := standardHeart_simple_iso_residue k H hsimpleH
  let iShifted : F⟦(-n : ℤ)⟧ ≅ residueObject k := by
    simpa [H, dualHeartToStandardEquivalence, n] using iH
  let iBack : F ≅ (F⟦(-n : ℤ)⟧)⟦n⟧ :=
    ((shiftFunctorCompIsoId (DerivedFiniteVect k) (-n : ℤ) n (by simp)).app F).symm
  refine ⟨q, rfl, ⟨iBack ≪≫ (shiftFunctor (DerivedFiniteVect k) n).mapIso iShifted⟩⟩

/-- The phase index of an integral phase is the preceding integer. -/
theorem phaseIndex_int_eq (q : ℤ) :
    WeakStabilityCondition.phaseIndex (q : ℝ) = q - 1 := by
  have h := WeakStabilityCondition.phaseBase_add_phaseIndex (q : ℝ)
  rw [phaseBase_int q] at h
  have hz : (1 : ℤ) + WeakStabilityCondition.phaseIndex (q : ℝ) = q := by
    exact_mod_cast h
  omega

/-- The fixed stable representative is isomorphic to the degree-zero residue
object. -/
theorem stableRepresentative_iso_residue :
    Nonempty (stableRepresentative k ≅ residueObject k) := by
  obtain ⟨q, hq, ⟨i⟩⟩ :=
    stable_iso_residue_shift k (stableRepresentative_isStable k)
  have hq' : q = 1 := by exact_mod_cast hq.symm
  subst q
  have hidx : WeakStabilityCondition.phaseIndex (1 : ℝ) = 0 := by
    convert phaseIndex_int_eq (1 : ℤ) using 1 <;> norm_num
  let i0 : stableRepresentative k ≅ (residueObject k)⟦(0 : ℤ)⟧ := by
    simpa [hidx] using i
  exact ⟨i0 ≪≫ (shiftFunctorZero (DerivedFiniteVect k) ℤ).app (residueObject k)⟩

/-- Stable objects in the standard slicing form one shift orbit. -/
theorem stable_iso_representative_shift {phi : ℝ} {F : DerivedFiniteVect k}
    (hF : (standardSlicing k).IsStableAt phi F) :
    ∃ m : ℤ, Nonempty (F ≅ (stableRepresentative k)⟦m⟧) := by
  obtain ⟨q, -, ⟨iF⟩⟩ := stable_iso_residue_shift k hF
  obtain ⟨iS⟩ := stableRepresentative_iso_residue k
  let m : ℤ := WeakStabilityCondition.phaseIndex (q : ℝ)
  exact ⟨m, ⟨iF ≪≫ (shiftFunctor (DerivedFiniteVect k) m).mapIso iS.symm⟩⟩

/-- The locally finite standard slicing has Jordan--Hölder filtrations. -/
theorem standardSlicing_hasJordanHolderFiltrations :
    (standardSlicing k).HasJordanHolderFiltrations :=
  (standardStabilityCondition k).locallyFinite.hasJordanHolderFiltrations

/-- The standard stability condition has exactly one stable shift orbit. -/
theorem standardStabilityCondition_hasFiniteStableOrbits :
    (standardStabilityCondition k).HasFiniteStableOrbits := by
  refine ⟨1, fun _ ↦ stableRepresentative k, by omega,
    standardSlicing_hasJordanHolderFiltrations k, ?_, ?_⟩
  · intro i
    exact ⟨1, stableRepresentative_isStable k⟩
  · intro F phi hF
    obtain ⟨m, hm⟩ := stable_iso_representative_shift k hF
    exact ⟨0, m, hm⟩

/-- The standard stability condition on `Dᵇ(FGModuleCat k)` is algebraic. -/
theorem standardStabilityCondition_isAlgebraic :
    (standardStabilityCondition k).IsAlgebraic :=
  ⟨standardStabilityCondition_hasFiniteLengthHeart k,
    standardStabilityCondition_hasFiniteStableOrbits k⟩

/-- The abstract algebraic theorem therefore gives a genuine global
mass--Hom bound on this nonzero example. -/
theorem standardStabilityCondition_hasGlobalMassHomBound :
    (standardStabilityCondition k).HasGlobalMassHomBound (k := k) :=
  (standardStabilityCondition_isAlgebraic k).hasGlobalMassHomBound

/-- The witness charge takes the value `-1` on the residue class. -/
theorem centralCharge_residue :
    centralCharge k (K₀.of (DerivedFiniteVect k) (residueObject k)) = -1 := by
  have hheart : (standardT k).heart (residueObject k) :=
    DerivedCategory.boundedHeart_singleFunctor_obj _ _
  rw [centralCharge_of_heart k _ hheart]
  rw [(residueHomEquiv k (FGModuleCat.of k k)).finrank_eq]
  simp

/-- In particular, the central charge of the algebraic witness is nonzero. -/
theorem centralCharge_ne_zero : centralCharge k ≠ 0 := by
  intro hzero
  have hvalue := DFunLike.congr_fun hzero
    (K₀.of (DerivedFiniteVect k) (residueObject k))
  rw [centralCharge_residue k] at hvalue
  norm_num at hvalue

end

end CategoryTheory.Triangulated.AlgebraicWitness
