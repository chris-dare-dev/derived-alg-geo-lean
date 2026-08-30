/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HeartComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Distance.Topology
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.PolygonPerimeter
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.CohomologyExactness
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.SourceTopology
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Stability
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Heart.Equivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.WeakCompatibility.PreStability

/-!
# The observable stability function on the canonical heart

This file owns the bridge from a stability condition with an arbitrary class
map to an ordinary `StabilityFunction` on its canonical heart.  It forgets the
presentation lattice, transports the charge, and proves that the resulting
heart-level stability function has Harder--Narasimhan filtrations and that its
semistable objects are exactly the ambient slicing's.

Only this bridge lives here.  Mass estimates along distinguished triangles are
developed in the sibling modules and consume this file through the umbrella.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction Matrix
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Forget the presentation lattice while retaining the observable charge on
`K₀(C)`.  This is composition of additive homomorphisms, not an operation on
stability conditions.  It lets the ordinary heart-equivalence API be reused
for a condition defined with an arbitrary class map. -/
def StabilityCondition.WithClassMap.observable
    (σ : StabilityCondition.WithClassMap C v) : StabilityCondition C where
  slicing := σ.slicing
  Z := σ.Z.comp v
  compatible := by
    intro φ E hP hE
    simpa using σ.compat φ E hP hE
  locallyFinite := σ.locallyFinite

omit [IsTriangulated C] in
@[simp]
theorem StabilityCondition.WithClassMap.observable_slicing
    (σ : StabilityCondition.WithClassMap C v) :
    σ.observable.slicing = σ.slicing := rfl

omit [IsTriangulated C] in
@[simp]
theorem StabilityCondition.WithClassMap.observable_charge
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    σ.observable.charge E = σ.charge E := rfl

/-- The heart stability function associated to a class-map stability
condition, obtained from its observable ordinary stability condition. -/
def StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  refine
    { Z := σ.Z.comp (v.comp (K₀Ab.toAmbient t))
      nonzero_mem := fun E hE ↦ by
        classical
        show σ.charge E.obj ∈ _
        have hEobj : ¬IsZero E.obj := fun h ↦
          hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
        have hheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
        obtain ⟨F, hn, hfirst, hlast⟩ :=
          σ.slicing.exists_hn_nonzero_boundaries C hEobj
        let P := F.toPostnikovTower
        let s : Finset (Fin F.n) :=
          Finset.univ.filter (fun i ↦ ¬IsZero (P.factor i))
        have hs : s.Nonempty := by
          obtain ⟨i, hi⟩ := F.exists_nonzero_factor C hEobj
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        have hminus : 0 < σ.slicing.phiMinus C E.obj hEobj :=
          σ.slicing.phiMinus_gt_of_gtProp C hEobj hheart.1
        have hplus : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
          σ.slicing.phiPlus_le_of_leProp C hEobj hheart.2
        have hphase : ∀ i ∈ s, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
          intro i hi
          constructor
          · calc
              0 < σ.slicing.phiMinus C E.obj hEobj := hminus
              _ = F.φ ⟨F.n - 1, by lia⟩ := by
                simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus] using
                  σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast
              _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
          · calc
              F.φ i ≤ F.φ ⟨0, hn⟩ :=
                F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
              _ = σ.slicing.phiPlus C E.obj hEobj := by
                simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
                  (σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst).symm
              _ ≤ 1 := hplus
        let f : Fin F.n → ℂ := fun i ↦ σ.charge (P.factor i)
        have hterm : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane := by
          intro i hi
          have hne : ¬IsZero (P.factor i) := by simpa [s] using hi
          obtain ⟨m, hm, hZ⟩ := σ.compat (F.φ i) (P.factor i)
            (F.semistable i) hne
          by_cases hone : F.φ i = 1
          · right
            rw [show f i = (m : ℂ) *
                Complex.exp ((Real.pi * (1 : ℝ) : ℂ) * Complex.I) by
              simpa [f, hone] using hZ]
            constructor
            · simp [Complex.exp_mul_I]
            · simp [Complex.exp_mul_I, hm]
          · left
            have hlt : F.φ i < 1 := lt_of_le_of_ne (hphase i hi).2 hone
            rw [show f i = (m : ℂ) *
                Complex.exp ((Real.pi * F.φ i : ℝ) * Complex.I) by
              simpa [f] using hZ]
            rw [Complex.exp_ofReal_mul_I]
            change 0 < ((m : ℂ) *
              ((Real.cos (Real.pi * F.φ i) : ℂ) +
                (Real.sin (Real.pi * F.φ i) : ℂ) * Complex.I)).im
            simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_im, Complex.I_re, zero_mul, mul_zero,
              mul_one, add_zero]
            simp only [zero_add]
            exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
              (mul_pos Real.pi_pos (hphase i hi).1)
              (by nlinarith [Real.pi_pos]))
        have hsum : σ.charge E.obj = ∑ i ∈ s, f i := by
          have hall := σ.charge_postnikovTower_eq_sum P
          rw [hall]
          let z : Finset (Fin F.n) :=
            Finset.univ.filter (fun i ↦ IsZero (P.factor i))
          have hz : ∑ i ∈ z, f i = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp only [z, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact σ.charge_isZero hi
          calc
            ∑ i, f i = (∑ i ∈ s, f i) + ∑ i ∈ z, f i := by
              simpa [s, z, f] using
                (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                  (p := fun i : Fin F.n ↦ ¬IsZero (P.factor i)) (f := f)).symm
            _ = ∑ i ∈ s, f i := by rw [hz, add_zero]
        rw [hsum]
        exact sum_mem_semiClosedUpperHalfPlane hs hterm }

@[simp]
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_charge
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory) :
    @StabilityFunction.charge _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E = σ.charge E.obj := by
  simp [observableStabilityFunctionOnHeart, StabilityFunction.charge,
    PreStabilityCondition.WithClassMap.charge_def, classOf]

/-- On a nonzero heart object already lying in a slice, the phase of the
restricted owner stability function is that slice parameter. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E = φ := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  obtain ⟨m, hm, hZ⟩ := σ.compat φ E.obj hP hEobj
  have harg : Complex.arg
      ((m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) =
      Real.pi * φ := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    constructor
    · nlinarith [Real.pi_pos, hφ.1]
    · nlinarith [Real.pi_pos, hφ.2]
  change Complex.arg (σ.charge E.obj) / Real.pi = φ
  rw [hZ, harg]
  field_simp [Real.pi_ne_zero]

/-- The heart phase is bounded by the highest ambient HN phase.  The
non-boundary case is the owner weak-charge argument bound; at phase one the
claim follows from the intrinsic range of an abelian stability phase. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_le_phiPlus
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory) (hE : ¬IsZero E) :
    @StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E ≤
      σ.slicing.phiPlus C E.obj (fun hZ ↦ hE <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := σ.slicing.toTStructure.heart) (X := E) hZ) := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  by_cases hplus : σ.slicing.phiPlus C E.obj hEobj < 1
  · let τ := CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ofPre
      σ.observable.toWithClassMap
    have hbound := τ.charge_mem_upperHalfPlane_and_arg_le_phiPlus
      E.obj E.property hEobj hplus
    have harg : Complex.arg (σ.charge E.obj) ≤
        Real.pi * σ.slicing.phiPlus C E.obj hEobj := by
      simpa [τ,
        WeakPreStabilityCondition.weakStabilityFunctionOnHeart_charge,
        StabilityCondition.WithClassMap.observable,
        PreStabilityCondition.WithClassMap.charge_def] using hbound.2
    change Complex.arg (σ.charge E.obj) / Real.pi ≤ _
    exact (div_le_iff₀ Real.pi_pos).2 (by simpa [mul_comm] using harg)
  · have hheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
    have hle : σ.slicing.phiPlus C E.obj hEobj ≤ 1 :=
      σ.slicing.phiPlus_le_of_leProp C hEobj hheart.2
    have heq : σ.slicing.phiPlus C E.obj hEobj = 1 :=
      le_antisymm hle (le_of_not_gt hplus)
    rw [heq]
    exact σ.observableStabilityFunctionOnHeart.phase_le_one E

/-- Ambient slice semistability implies semistability for the restricted
owner stability function on the canonical heart. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
    (σ : StabilityCondition.WithClassMap C v) {φ : ℝ}
    (hφ : φ ∈ Set.Ioc (0 : ℝ) 1)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hP : σ.slicing.P φ E.obj) (hE : ¬IsZero E) :
    @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  refine ⟨hE, ?_⟩
  intro B hB
  let B' : t.heart.FullSubcategory := (B : t.heart.FullSubcategory)
  have hBobj : ¬IsZero B'.obj := fun hZ ↦ hB <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := B') hZ
  have hphiPlus_le : σ.slicing.phiPlus C B'.obj hBobj ≤ φ := by
    by_contra hle
    have hgt : φ < σ.slicing.phiPlus C B'.obj hBobj := lt_of_not_ge hle
    have hBheart := (σ.slicing.toTStructure_heart_iff C B'.obj).mp B'.property
    obtain ⟨F, hn, hfirst⟩ := σ.slicing.exists_hn_nonzero_first C hBobj
    have htop : σ.slicing.phiPlus C B'.obj hBobj = F.φ ⟨0, hn⟩ := by
      simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
        σ.slicing.phiPlus_eq C B'.obj hBobj F hn hfirst
    have hphase_gt : φ < F.φ ⟨0, hn⟩ := by simpa [htop] using hgt
    have hphase_mem : F.φ ⟨0, hn⟩ ∈ Set.Ioc (0 : ℝ) 1 := by
      exact ⟨hφ.1.trans hphase_gt,
        (by rw [← htop]; exact σ.slicing.phiPlus_le_of_leProp C hBobj hBheart.2)⟩
    have hAheart : t.heart (F.factor ⟨0, hn⟩) := by
      rw [σ.slicing.toTStructure_heart_iff C]
      exact ⟨σ.slicing.gtProp_of_semistable C (F.semistable ⟨0, hn⟩)
          hphase_mem.1,
        σ.slicing.leProp_of_semistable C (F.semistable ⟨0, hn⟩)
          hphase_mem.2⟩
    obtain ⟨α, hα⟩ : ∃ α : F.factor ⟨0, hn⟩ ⟶ B'.obj, α ≠ 0 := by
      by_contra hzero
      push Not at hzero
      exact hfirst (F.firstFactor_isZero_of_hom_eq_zero C σ.slicing hn hzero)
    let A : t.heart.FullSubcategory := ⟨F.factor ⟨0, hn⟩, hAheart⟩
    let αH : A ⟶ B' := ObjectProperty.homMk α
    have hcomp : α ≫ B.arrow.hom ≠ 0 := by
      intro hzero
      have hz : αH ≫ B.arrow = 0 := by ext; exact hzero
      have : αH = 0 := (cancel_mono B.arrow).mp (by simpa using hz)
      exact hα (by simpa [αH] using congrArg (fun f ↦ f.hom) this)
    exact hcomp <| σ.slicing.hom_vanishing _ _ _ _ hphase_gt
      (F.semistable ⟨0, hn⟩) hP (α ≫ B.arrow.hom)
  calc
    σ.observableStabilityFunctionOnHeart.phase B' ≤
        σ.slicing.phiPlus C B'.obj hBobj :=
      σ.observableStabilityFunctionOnHeart_phase_le_phiPlus B' hB
    _ ≤ φ := hphiPlus_le
    _ = σ.observableStabilityFunctionOnHeart.phase E :=
      (σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P hφ E hP hE).symm

/-- The observable heart stability function has Harder--Narasimhan
filtrations. -/
theorem StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
    (σ : StabilityCondition.WithClassMap C v) :
    @StabilityFunction.HasHNProperty
      (σ.slicing.toTStructure.heart.FullSubcategory) _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let Z := σ.observableStabilityFunctionOnHeart
  intro E hE
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hE <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  suffices hmain :
      ∀ (m : ℕ) {X : t.heart.FullSubcategory} (hXobj : ¬IsZero X.obj)
        (F : HNFiltration C σ.slicing.P X.obj) (hnF : 0 < F.n)
        (hFm : F.n ≤ m) (hfirst : ¬IsZero (F.factor ⟨0, hnF⟩)),
        ∃ G : AbelianHNFiltration Z X,
          G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ =
            σ.slicing.phiMinus C X.obj hXobj by
    obtain ⟨F, hnF, hfirst, -⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hEobj
    exact ⟨(hmain F.n hEobj F hnF le_rfl hfirst).choose⟩
  intro m
  induction m with
  | zero =>
      intro X hXobj F hnF hFm
      omega
  | succ m ih =>
      intro X hXobj F hnF hFm hfirst
      have hX : ¬IsZero X := fun hZ ↦ hXobj ((t.heart).ι.map_isZero hZ)
      have hXheart := (σ.slicing.toTStructure_heart_iff C X.obj).mp X.property
      by_cases h1 : F.n = 1
      · let φ := F.φ ⟨0, hnF⟩
        have hlast : ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) := by
          have hidx : (⟨F.n - 1, by omega⟩ : Fin F.n) = ⟨0, hnF⟩ :=
            Fin.ext (by omega)
          simpa [hidx] using hfirst
        have hall : ∀ i : Fin F.n, F.φ i = φ := by
          intro i
          have hi : i = ⟨0, hnF⟩ := Fin.ext (by omega)
          subst i
          rfl
        have hP : σ.slicing.P φ X.obj :=
          σ.slicing.semistable_of_HN_all_eq C F hall
        have hφm : σ.slicing.phiMinus C X.obj hXobj = φ := by
          rw [σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast]
          simp only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
          congr 1
          exact Fin.ext (by omega)
        have hφp : σ.slicing.phiPlus C X.obj hXobj = φ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using
            σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst
        have hφ : φ ∈ Set.Ioc (0 : ℝ) 1 := by
          constructor
          · exact (by
              have := σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1
              linarith)
          · exact (by
              have := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
              linarith)
        have hss : @StabilityFunction.IsSemistable _ _
            t.heartFullSubcategoryAbelian Z X :=
          σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
            hφ X hP hX
        obtain ⟨G, hG⟩ :=
          CategoryTheory.Triangulated.StabilityFunction.exists_hn_with_last_phase_of_semistable
            Z hss
        refine ⟨G, ?_⟩
        calc
          G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase X := hG
          _ = φ :=
            σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P hφ X hP hX
          _ = σ.slicing.phiMinus C X.obj hXobj := hφm.symm
      · have htwo : 2 ≤ F.n := by omega
        by_cases hlast : IsZero (F.factor ⟨F.n - 1, by omega⟩)
        · let F' := F.dropLast C (by omega) hlast
          have hnF' : 0 < F'.n := F'.n_pos C hXobj
          have hF'm : F'.n ≤ m := by
            change F.n - 1 ≤ m
            omega
          have hfirst' : ¬IsZero (F'.factor ⟨0, hnF'⟩) := by
            change ¬IsZero (F.factor ⟨0, by omega⟩)
            simpa using hfirst
          exact ih hXobj F' hnF' hF'm hfirst'
        · have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
            intro i
            constructor
            · calc
                0 < σ.slicing.phiMinus C X.obj hXobj :=
                  σ.slicing.phiMinus_gt_of_gtProp C hXobj hXheart.1
                _ = F.φ ⟨F.n - 1, by omega⟩ := by
                  simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
                    using σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast
                _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
            · calc
                F.φ i ≤ F.φ ⟨0, hnF⟩ :=
                  F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
                _ = σ.slicing.phiPlus C X.obj hXobj := by
                  simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus]
                    using (σ.slicing.phiPlus_eq C X.obj hXobj F hnF hfirst).symm
                _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hXobj hXheart.2
          let FX : HNFiltration C σ.slicing.P
              (F.chain.obj ⟨F.n - 1, by omega⟩) :=
            F.prefix C (F.n - 1) (by omega)
          have hFXn : 0 < FX.n := by change 0 < F.n - 1; omega
          have hFXheart : t.heart (F.chain.obj ⟨F.n - 1, by omega⟩) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨
              CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
                C σ.slicing F (F.n - 1) (by omega) (by omega) 0
                (fun j ↦ (hall_mem ⟨j, by omega⟩).1),
              CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
                C σ.slicing F (F.n - 1) (by omega) (by omega) 1
                (fun j ↦ (hall_mem ⟨j, by omega⟩).2)⟩
          let X' : t.heart.FullSubcategory :=
            ⟨F.chain.obj ⟨F.n - 1, by omega⟩, hFXheart⟩
          have hfirstFX : ¬IsZero (FX.factor ⟨0, hFXn⟩) := by
            change ¬IsZero (F.factor ⟨0, by omega⟩)
            simpa using hfirst
          have hX'obj : ¬IsZero X'.obj := by
            intro hZ
            have hz : ∀ f : FX.factor ⟨0, hFXn⟩ ⟶ X'.obj, f = 0 :=
              fun f ↦ hZ.eq_of_tgt _ _
            exact hfirstFX <| FX.firstFactor_isZero_of_hom_eq_zero
              C σ.slicing hFXn hz
          obtain ⟨GX, hGX⟩ := ih hX'obj FX hFXn (by
            change F.n - 1 ≤ m
            omega) hfirstFX
          let jLast : Fin F.n := ⟨F.n - 1, by omega⟩
          have hBheart : t.heart (F.factor jLast) := by
            rw [σ.slicing.toTStructure_heart_iff C]
            exact ⟨σ.slicing.gtProp_of_semistable C (F.semistable jLast)
                (hall_mem jLast).1,
              σ.slicing.leProp_of_semistable C (F.semistable jLast)
                (hall_mem jLast).2⟩
          let B : t.heart.FullSubcategory := ⟨F.factor jLast, hBheart⟩
          have hB : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
          have hBss : @StabilityFunction.IsSemistable _ _
              t.heartFullSubcategoryAbelian Z B :=
            σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
              (hall_mem jLast) B (F.semistable jLast) hB
          have hBphase : Z.phase B = F.φ jLast :=
            σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
              (hall_mem jLast) B (F.semistable jLast) hB
          have hX'gt : σ.slicing.gtProp C (F.φ jLast) X'.obj :=
            CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
              C σ.slicing F (F.n - 1) (by omega) (by omega) (F.φ jLast) <|
                fun j ↦ F.hφ (Fin.mk_lt_mk.mpr (by omega))
          have hphase_lt : Z.phase B < GX.phase ⟨GX.n - 1, by
              have := GX.nonempty; omega⟩ := by
            calc
              Z.phase B = F.φ jLast := hBphase
              _ < σ.slicing.phiMinus C X'.obj hX'obj :=
                σ.slicing.phiMinus_gt_of_gtProp C hX'obj hX'gt
              _ = GX.phase ⟨GX.n - 1, by have := GX.nonempty; omega⟩ := hGX.symm
          let Tlast := F.triangle jLast
          let e₁ := Classical.choice (F.triangle_obj₁ jLast)
          let e₂ := Classical.choice (F.triangle_obj₂ jLast)
          have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by omega) =
              F.chain.right := by
            simp only [ComposableArrows.obj']
            congr 1
            ext
            simp
            omega
          let e₂X : Tlast.obj₂ ≅ X.obj :=
            e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
          let i : X' ⟶ X :=
            ObjectProperty.homMk (e₁.inv ≫ Tlast.mor₁ ≫ e₂X.hom)
          let q : X ⟶ B := ObjectProperty.homMk (e₂X.inv ≫ Tlast.mor₂)
          let δ : B.obj ⟶ X'.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
          have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
            refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
            exact Triangle.isoMk _ _ e₁.symm e₂X.symm (Iso.refl _)
              (by simp [Tlast, i, e₂X]) (by simp [Tlast, q, e₂X])
              (by simp [Tlast, δ])
          have hiq : i ≫ q = 0 := by
            ext
            simpa using comp_distTriang_mor_zero₁₂ _ hTlast
          have hKer : IsLimit (KernelFork.ofι i hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
            simpa [hiq] using
              Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
                (CategoryTheory.Triangulated.TStructure.heart_hι t)
                i q δ hTlast
          let eB : cokernel i ≅ B :=
            IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel i) hCok
          haveI : Mono i := Fork.IsLimit.mono hKer
          obtain ⟨G, hG⟩ :=
            CategoryTheory.Triangulated.StabilityFunction.append_hn_filtration_of_mono
              Z i GX eB hBss hphase_lt
          refine ⟨G, ?_⟩
          calc
            G.phase ⟨G.n - 1, by have := G.nonempty; omega⟩ = Z.phase B := hG
            _ = F.φ jLast := hBphase
            _ = σ.slicing.phiMinus C X.obj hXobj := by
              symm
              simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus]
                using σ.slicing.phiMinus_eq C X.obj hXobj F hnF hlast

/-- The converse half of the heart/slicing semistability comparison.  A
nonzero object that is semistable for the stability function on the canonical
heart is semistable in the ambient slicing, at the same phase. -/
theorem StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
    (σ : StabilityCondition.WithClassMap C v)
    (E : σ.slicing.toTStructure.heart.FullSubcategory)
    (hE : @StabilityFunction.IsSemistable _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    σ.slicing.P (@StabilityFunction.phase _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) E.obj := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  have hEnz : ¬IsZero E := hE.1
  have hEobj : ¬IsZero E.obj := fun hZ ↦ hEnz <|
    ObjectProperty.FullSubcategory.isZero_of_obj_isZero
      (C := C) (P := t.heart) (X := E) hZ
  have hEheart := (σ.slicing.toTStructure_heart_iff C E.obj).mp E.property
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    σ.slicing.exists_hn_nonzero_boundaries C hEobj
  have hall_mem : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    constructor
    · calc
        0 < σ.slicing.phiMinus C E.obj hEobj :=
          σ.slicing.phiMinus_gt_of_gtProp C hEobj hEheart.1
        _ = F.φ ⟨F.n - 1, by lia⟩ :=
          σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ = σ.slicing.phiPlus C E.obj hEobj := by
          symm
          exact σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst
        _ ≤ 1 := σ.slicing.phiPlus_le_of_leProp C hEobj hEheart.2
  let iFirst : Fin F.n := ⟨0, hn⟩
  have hAheart : t.heart (F.triangle iFirst).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C
        (F.semistable iFirst) (hall_mem iFirst).1,
      σ.slicing.leProp_of_semistable C
        (F.semistable iFirst) (hall_mem iFirst).2⟩
  let A : t.heart.FullSubcategory := ⟨(F.triangle iFirst).obj₃, hAheart⟩
  have hAnz : ¬IsZero A := fun hZ ↦ hfirst ((t.heart).ι.map_isZero hZ)
  have hAss : @StabilityFunction.IsSemistable _ _
      t.heartFullSubcategoryAbelian Z A :=
    σ.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hAphase : Z.phase A = F.φ iFirst :=
    σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
      (hall_mem iFirst) A (F.semistable iFirst) hAnz
  have hα : ∃ α : A.obj ⟶ E.obj, α ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hfirst <|
      F.isZero_factor_zero_of_hom_eq_zero C σ.slicing hn hzero
  obtain ⟨α, hα⟩ := hα
  let αH : A ⟶ E := ObjectProperty.homMk α
  have hIm : ¬IsZero (Limits.image αH) := by
    intro hZ
    apply hα
    have hι : Limits.image.ι αH = 0 := zero_of_source_iso_zero _ hZ.isoZero
    have hαH : αH = 0 := by rw [← Limits.image.fac αH, hι, comp_zero]
    exact congr_arg (·.hom) hαH
  have hImSub : ¬IsZero (imageSubobject αH : t.heart.FullSubcategory) := by
    intro hZ
    exact hIm (hZ.of_iso (imageSubobjectIso αH).symm)
  have hfirst_le : F.φ iFirst ≤ Z.phase E := by
    rw [← hAphase]
    calc
      Z.phase A ≤ Z.phase (Limits.image αH) :=
        Z.phase_le_of_epi (factorThruImage αH) hAss hIm
      _ = Z.phase (imageSubobject αH : t.heart.FullSubcategory) :=
        Z.phase_eq_of_iso (imageSubobjectIso αH).symm
      _ ≤ Z.phase E := hE.2 (imageSubobject αH) hImSub
  have hplus_le : σ.slicing.phiPlus C E.obj hEobj ≤ Z.phase E := by
    rw [σ.slicing.phiPlus_eq C E.obj hEobj F hn hfirst]
    exact hfirst_le

  let jLast : Fin F.n := ⟨F.n - 1, by lia⟩
  have hXheart : t.heart (F.chain.obj ⟨F.n - 1, by lia⟩) := by
    by_cases hk : F.n - 1 = 0
    · rw [σ.slicing.toTStructure_heart_iff C]
      have hidx : (⟨F.n - 1, by lia⟩ : Fin (F.n + 1)) = 0 :=
        Fin.ext (by simpa using hk)
      have hzero : IsZero (F.chain.obj ⟨F.n - 1, by lia⟩) := by
        rw [hidx]
        simpa [ComposableArrows.left] using F.base_isZero
      exact ⟨Or.inl hzero, Or.inl hzero⟩
    · rw [σ.slicing.toTStructure_heart_iff C]
      constructor
      · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
          C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 0
          (fun j ↦ (hall_mem ⟨j, by lia⟩).1)
      · exact CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
          C σ.slicing F (F.n - 1)
          (by lia) (Nat.pos_of_ne_zero hk) 1
          (fun j ↦ (hall_mem ⟨j, by lia⟩).2)
  let X : t.heart.FullSubcategory :=
    ⟨F.chain.obj ⟨F.n - 1, by lia⟩, hXheart⟩
  have hBheart : t.heart (F.triangle jLast).obj₃ := by
    rw [σ.slicing.toTStructure_heart_iff C]
    exact ⟨σ.slicing.gtProp_of_semistable C
        (F.semistable jLast) (hall_mem jLast).1,
      σ.slicing.leProp_of_semistable C
        (F.semistable jLast) (hall_mem jLast).2⟩
  let B : t.heart.FullSubcategory := ⟨(F.triangle jLast).obj₃, hBheart⟩
  have hBnz : ¬IsZero B := fun hZ ↦ hlast ((t.heart).ι.map_isZero hZ)
  have hBphase : Z.phase B = F.φ jLast :=
    σ.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
      (hall_mem jLast) B (F.semistable jLast) hBnz
  let Tlast := F.triangle jLast
  let e₁ := Classical.choice (F.triangle_obj₁ jLast)
  let e₂ := Classical.choice (F.triangle_obj₂ jLast)
  have hobj₂_eq : F.chain.obj' (F.n - 1 + 1) (by lia) = F.chain.right := by
    simp only [ComposableArrows.obj']
    congr 1
    ext
    simp
    lia
  let e₂E : Tlast.obj₂ ≅ E.obj :=
    e₂.trans ((eqToIso hobj₂_eq).trans (Classical.choice F.top_iso))
  let i : X ⟶ E := ObjectProperty.homMk
    (e₁.inv ≫ Tlast.mor₁ ≫ e₂E.hom)
  let q : E ⟶ B := ObjectProperty.homMk (e₂E.inv ≫ Tlast.mor₂)
  let δ : B.obj ⟶ X.obj⟦(1 : ℤ)⟧ := Tlast.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  have hTlast : Triangle.mk i.hom q.hom δ ∈ distTriang C := by
    refine isomorphic_distinguished _ (F.triangle_dist jLast) _ ?_
    exact Triangle.isoMk _ _ e₁.symm e₂E.symm (Iso.refl _)
      (by simp [Tlast, i, e₂E]) (by simp [Tlast, q, e₂E])
      (by simp [Tlast, δ])
  have hiq_hom : i.hom ≫ q.hom = 0 := by
    simpa using comp_distTriang_mor_zero₁₂ _ hTlast
  have hiq : i ≫ q = 0 := by
    ext
    exact hiq_hom
  have hCok : IsColimit (CokernelCofork.ofπ q hiq) := by
    simpa [hiq] using
      Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
        (CategoryTheory.Triangulated.TStructure.heart_hι t)
        i q δ hTlast
  letI : Epi q := Cofork.IsColimit.epi hCok
  have hlast_ge : Z.phase E ≤ F.φ jLast := by
    rw [← hBphase]
    exact Z.phase_le_of_epi q hE hBnz
  have hminus_ge : Z.phase E ≤ σ.slicing.phiMinus C E.obj hEobj := by
    rw [σ.slicing.phiMinus_eq C E.obj hEobj F hn hlast]
    exact hlast_ge
  have hextreme : σ.slicing.phiPlus C E.obj hEobj =
      σ.slicing.phiMinus C E.obj hEobj := by
    apply le_antisymm
    · exact hplus_le.trans hminus_ge
    · exact σ.slicing.phiMinus_le_phiPlus C E.obj hEobj
  have hP := σ.slicing.semistable_of_phiPlus_eq_phiMinus (C := C) hEobj hextreme
  rwa [show σ.slicing.phiPlus C E.obj hEobj = Z.phase E from
    le_antisymm hplus_le
      (σ.observableStabilityFunctionOnHeart_phase_le_phiPlus E hEnz)] at hP

end

end CategoryTheory.Triangulated
