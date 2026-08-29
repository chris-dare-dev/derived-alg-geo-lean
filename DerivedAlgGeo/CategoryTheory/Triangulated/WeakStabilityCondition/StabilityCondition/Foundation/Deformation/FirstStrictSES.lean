/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.SkewedStability
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Slicing.IntervalStrictness
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge

/-!
# First strict short exact sequence in an owner thin interval

Failure of skewed semistability produces a proper strict subobject of larger
phase.  Strict-Artinian descent then terminates at a semistable strict
subobject, yielding the first strict short exact sequence used by the owner
maximal-destabilizing-quotient construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.Deformation

open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace Slicing.IntervalCat

variable {s : Slicing C} {a b : ℝ}

omit [IsTriangulated C] in
/-- An interval subobject is zero exactly when it is the bottom subobject. -/
@[simp]
theorem subobject_isZero_iff_eq_bot {X : s.IntervalCat C a b}
    (B : Subobject X) : IsZero (B : s.IntervalCat C a b) ↔ B = ⊥ := by
  constructor
  · intro hB
    have hArrow : B.arrow = 0 := zero_of_source_iso_zero _ hB.isoZero
    rwa [← Subobject.mk_arrow B, Subobject.mk_eq_bot_iff_zero]
  · intro hB
    subst hB
    exact (isZero_zero (s.IntervalCat C a b)).of_iso Subobject.botCoeIsoZero

omit [IsTriangulated C] in
/-- A non-bottom interval subobject is nonzero. -/
theorem subobject_not_isZero_of_ne_bot {X : s.IntervalCat C a b}
    {B : Subobject X} (hB : B ≠ ⊥) : ¬IsZero (B : s.IntervalCat C a b) :=
  fun hZero => hB ((subobject_isZero_iff_eq_bot (C := C) B).mp hZero)

section

variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The canonical arrow of the subobject represented by a strict mono is
strict. -/
theorem subobject_arrow_strictMono {X Y : s.IntervalCat C a b}
    (f : Y ⟶ X) (hf : IsStrictMono f) :
    letI : Mono f := hf.mono
    IsStrictMono (Subobject.mk f).arrow := by
  letI : Mono f := hf.mono
  let e := Subobject.underlyingIso f
  have he : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ f) :=
    Slicing.IntervalCat.comp_strictMono C s e.hom f he hf
  simpa [e] using hcomp

/-- A strict mono and its canonical cokernel projection form a strict short
exact sequence. -/
theorem strictShortExact_cokernel {X Y : s.IntervalCat C a b}
    (f : Y ⟶ X) (hf : IsStrictMono f) :
    StrictShortExact
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    categoryWithHomology_of_abelian
  let FL := Slicing.IntervalCat.toLeftHeart C s a b
    (Fact.out : b - a ≤ 1)
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S, KernelFork.ofι] using hf.isLimitKernelFork
  have hEpi : Epi ((S.map FL).g) := by
    change Epi (FL.map (cokernel.π f))
    exact Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s
      (cokernel.π f) (isStrictEpi_cokernel f)
  have hKer : IsLimit
      (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hKer
  have hShortExact : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_shortExact_toLeftHeart
      C s hShortExact
  exact Slicing.IntervalCat.strictShortExact_of_distinguished C s hT

/-- Every owner strict subobject of a thin slicing interval is intrinsically
admissible. Together with
`Slicing.IntervalCat.isStrictSubobject_of_isAdmissible`, this identifies the
two subobject orders used by local finiteness and strict HN recursion. -/
theorem isAdmissibleSubobject_of_isStrictSubobject
    {E : s.IntervalCat C a b} (A : Subobject E)
    (hA : IsStrictSubobject A) : s.IsAdmissibleSubobject C A := by
  letI : Mono A.arrow := hA.mono
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk A.arrow (cokernel.π A.arrow)
      (cokernel.condition A.arrow)
  have hS : StrictShortExact S :=
    Slicing.IntervalCat.strictShortExact_cokernel C A.arrow hA
  obtain ⟨δ, hδ⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s hS
  exact ⟨(A : s.IntervalCat C a b), cokernel A.arrow, A.arrow,
    inferInstance, cokernel.π A.arrow, Subobject.mk_arrow A, δ, hδ⟩

/-- Intrinsic admissible subobjects and owner strict subobjects are the same
ordered type in a thin slicing interval. -/
def admissibleStrictSubobjectOrderIso (E : s.IntervalCat C a b) :
    s.AdmissibleSubobject C E ≃o StrictSubobject E where
  toFun A := ⟨A.1,
    Slicing.IntervalCat.isStrictSubobject_of_isAdmissible C s A.1 A.2⟩
  invFun A := ⟨A.1,
    Slicing.IntervalCat.isAdmissibleSubobject_of_isStrictSubobject C A.1 A.2⟩
  left_inv A := rfl
  right_inv A := rfl
  map_rel_iff' := Iff.rfl

/-- Intrinsic local finite length supplies the strict finite length required
by owner HN recursion. -/
theorem isStrictFiniteLength_of_isFiniteLength
    {E : s.IntervalCat C a b} (hE : s.IsFiniteLength C E) :
    IsStrictFiniteLengthObject E := by
  let e := Slicing.IntervalCat.admissibleStrictSubobjectOrderIso
    (C := C) (s := s) E
  have hArt : WellFoundedLT (StrictSubobject E) := by
    letI : WellFoundedLT (s.AdmissibleSubobject C E) := hE.1
    exact e.symm.toOrderEmbedding.wellFoundedLT
  have hNoeth : WellFoundedGT (StrictSubobject E) := by
    letI : WellFoundedGT (s.AdmissibleSubobject C E) := hE.2
    exact e.symm.toOrderEmbedding.wellFoundedGT
  exact ⟨ObjectProperty.is_of_prop _ hArt,
    ObjectProperty.is_of_prop _ hNoeth⟩

/-- Lift a subobject of an interval subobject back to the ambient interval
object by composing the two canonical arrows. -/
def liftSub {X : s.IntervalCat C a b} (M : Subobject X)
    (A : Subobject (M : s.IntervalCat C a b)) : Subobject X :=
  Subobject.mk (A.arrow ≫ M.arrow)

omit [IsTriangulated C] [Fact (a < b)] [Fact (b - a ≤ 1)] in
theorem liftSub_le {X : s.IntervalCat C a b} (M : Subobject X)
    (A : Subobject (M : s.IntervalCat C a b)) : liftSub C M A ≤ M := by
  have h := Subobject.mk_le_mk_of_comm A.arrow
    (show A.arrow ≫ M.arrow = A.arrow ≫ M.arrow from rfl)
  rwa [Subobject.mk_arrow] at h

omit [IsTriangulated C] [Fact (a < b)] [Fact (b - a ≤ 1)] in
theorem liftSub_ne_bot {X : s.IntervalCat C a b} (M : Subobject X)
    {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊥) :
    liftSub C M A ≠ ⊥ := by
  intro h
  apply hA
  rw [← Subobject.mk_arrow A]
  apply (Subobject.mk_eq_bot_iff_zero).mpr
  apply (cancel_mono M.arrow).1
  simpa [liftSub, Subobject.mk_arrow] using
    (Subobject.mk_eq_bot_iff_zero.mp h)

omit [IsTriangulated C] [Fact (a < b)] [Fact (b - a ≤ 1)] in
theorem liftSub_lt {X : s.IntervalCat C a b} (M : Subobject X)
    {A : Subobject (M : s.IntervalCat C a b)} (hA : A ≠ ⊤) :
    liftSub C M A < M := by
  refine lt_of_le_of_ne (liftSub_le C M A) ?_
  intro hEq
  apply hA
  apply (Subobject.map_obj_injective M.arrow)
  rw [show (Subobject.map M.arrow).obj A = liftSub C M A by
    simpa [liftSub] using (Subobject.map_mk A.arrow M.arrow)]
  rw [show (Subobject.map M.arrow).obj
      (⊤ : Subobject (M : s.IntervalCat C a b)) = M by simp]
  exact hEq

/-- Strictness is preserved when a strict subobject of a strict subobject is
lifted to the ambient interval object. -/
theorem liftSub_arrow_strictMono {X : s.IntervalCat C a b}
    {M : Subobject X} (hM : IsStrictMono M.arrow)
    {A : Subobject (M : s.IntervalCat C a b)}
    (hA : IsStrictMono A.arrow) : IsStrictMono (liftSub C M A).arrow := by
  have hcomp : IsStrictMono (A.arrow ≫ M.arrow) :=
    Slicing.IntervalCat.comp_strictMono C s A.arrow M.arrow hA hM
  simpa [liftSub] using subobject_arrow_strictMono C (A.arrow ≫ M.arrow) hcomp

omit [IsTriangulated C] [Fact (a < b)] [Fact (b - a ≤ 1)] in
/-- Lifting a subobject does not change the underlying skewed phase. -/
theorem phase_liftSub {F : SkewedStabilityFunction C κ s a b}
    {X : s.IntervalCat C a b} (M : Subobject X)
    (A : Subobject (M : s.IntervalCat C a b)) :
    F.phase (liftSub C M A : s.IntervalCat C a b).obj =
      F.phase (A : s.IntervalCat C a b).obj := by
  let eI : (liftSub C M A : s.IntervalCat C a b) ≅
      (A : s.IntervalCat C a b) := Subobject.underlyingIso (A.arrow ≫ M.arrow)
  let eC : (liftSub C M A : s.IntervalCat C a b).obj ≅
      (A : s.IntervalCat C a b).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := s) a b).mapIso eI
  exact F.phase_iso eC

end

end Slicing.IntervalCat

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Failure of skewed semistability supplies a proper strict subobject of
strictly larger skewed phase. -/
theorem exists_phase_gt_strictSubobject_of_not_semistable
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    (hns : ¬F.IsSemistable X.obj (F.phase X.obj)) :
    ∃ B : Subobject X, B ≠ ⊥ ∧ B ≠ ⊤ ∧ IsStrictMono B.arrow ∧
      F.phase X.obj < F.phase (B : σ.slicing.IntervalCat C a b).obj := by
  have hXObj : ¬IsZero X.obj := fun h =>
    hX (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have htriangle :
      ¬∀ ⦃K Q : C⦄ ⦃i : K ⟶ X.obj⦄ ⦃q : X.obj ⟶ Q⦄
        ⦃δ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
        Triangle.mk i q δ ∈ distTriang C →
        σ.slicing.intervalProp C a b K →
        σ.slicing.intervalProp C a b Q →
        ¬IsZero K → F.phase K ≤ F.phase X.obj := by
    intro h
    exact hns ⟨X.property, hXObj, hCharge X.property hXObj, rfl, h⟩
  push Not at htriangle
  obtain ⟨K, Q, i, q, δ, hT, hK, hQ, hKne, hphase⟩ := htriangle
  let KI : σ.slicing.IntervalCat C a b := ⟨K, hK⟩
  let QI : σ.slicing.IntervalCat C a b := ⟨Q, hQ⟩
  let iI : KI ⟶ X := ObjectProperty.homMk i
  let qI : X ⟶ QI := ObjectProperty.homMk q
  let S : ShortComplex (σ.slicing.IntervalCat C a b) :=
    ShortComplex.mk iI qI (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)
  have hS : StrictShortExact S :=
    Slicing.IntervalCat.strictShortExact_of_distinguished C σ.slicing
      (by simpa [S, iI, qI] using hT)
  have hi : IsStrictMono iI := ⟨hS.shortExact.mono_f, hS.strict_f⟩
  letI : Mono iI := hi.mono
  let B : Subobject X := Subobject.mk iI
  have hBne : B ≠ ⊥ := by
    intro hB
    have hBZ : IsZero (B : σ.slicing.IntervalCat C a b) :=
      (Slicing.IntervalCat.subobject_isZero_iff_eq_bot (C := C) B).mpr hB
    exact hKne (((σ.slicing.intervalProp C a b).ι).map_isZero
      (hBZ.of_iso (Subobject.underlyingIso iI).symm))
  have hBstrict : IsStrictMono B.arrow := by
    simpa [B] using Slicing.IntervalCat.subobject_arrow_strictMono C iI hi
  have hBphase : F.phase (B : σ.slicing.IntervalCat C a b).obj =
      F.phase K := by
    let eC : (B : σ.slicing.IntervalCat C a b).obj ≅ K :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
        (Subobject.underlyingIso iI)
    exact F.phase_iso eC
  have hBtop : B ≠ ⊤ := by
    intro hB
    have hTop : F.phase
        ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj =
        F.phase X.obj := by
      let eC : ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj ≅
          X.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
          (asIso (⊤ : Subobject X).arrow)
      exact F.phase_iso eC
    have hBphaseTop : F.phase
        ((⊤ : Subobject X) : σ.slicing.IntervalCat C a b).obj =
        F.phase K := by simpa only [hB] using hBphase
    have hEq : F.phase K = F.phase X.obj := hBphaseTop.symm.trans hTop
    exact (lt_irrefl _ (hphase.trans_eq hEq))
  exact ⟨B, hBne, hBtop, hBstrict, hphase.trans_eq hBphase.symm⟩

/-- Strict-Artinian descent terminates at a proper nonzero semistable strict
subobject of strictly larger phase, together with its canonical strict short
exact sequence. -/
theorem exists_first_strictShortExact_of_not_semistable
    {X : σ.slicing.IntervalCat C a b} [IsStrictArtinianObject X]
    (hX : ¬IsZero X)
    (hns : ¬F.IsSemistable X.obj (F.phase X.obj))
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E) :
    ∃ M : Subobject X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      F.IsSemistable (M : σ.slicing.IntervalCat C a b).obj
        (F.phase (M : σ.slicing.IntervalCat C a b).obj) ∧
      F.phase X.obj < F.phase (M : σ.slicing.IntervalCat C a b).obj ∧
      StrictShortExact
        (ShortComplex.mk M.arrow (cokernel.π M.arrow)
          (cokernel.condition M.arrow)) := by
  let phaseSub : StrictSubobject X → ℝ := fun B =>
    F.phase (B.1 : σ.slicing.IntervalCat C a b).obj
  let P : StrictSubobject X → Prop := fun B =>
    ∀ hBne : ¬IsZero (B.1 : σ.slicing.IntervalCat C a b),
      ¬F.IsSemistable (B.1 : σ.slicing.IntervalCat C a b).obj (phaseSub B) →
      ∃ D : StrictSubobject X, D < B ∧
        F.IsSemistable (D.1 : σ.slicing.IntervalCat C a b).obj (phaseSub D) ∧
        phaseSub B < phaseSub D
  have hP : ∀ B : StrictSubobject X, P B := by
    intro B
    refine (wellFounded_lt.induction B ?_)
    intro B ih hBne hBns
    obtain ⟨A, hAne, hAtop, hAstrict, hphase⟩ :=
      exists_phase_gt_strictSubobject_of_not_semistable C hBne hCharge hBns
    let Dsub : Subobject X := Slicing.IntervalCat.liftSub C B.1 A
    have hDne : Dsub ≠ ⊥ := Slicing.IntervalCat.liftSub_ne_bot C B.1 hAne
    have hDstrict : IsStrictMono Dsub.arrow :=
      Slicing.IntervalCat.liftSub_arrow_strictMono C B.2 hAstrict
    let D : StrictSubobject X := ⟨Dsub, hDstrict⟩
    have hDlt : D < B := Slicing.IntervalCat.liftSub_lt C B.1 hAtop
    have hDnonzero : ¬IsZero (D.1 : σ.slicing.IntervalCat C a b) :=
      Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hDne
    have hphaseBD : phaseSub B < phaseSub D := by
      exact hphase.trans_eq (Slicing.IntervalCat.phase_liftSub C B.1 A).symm
    by_cases hDss : F.IsSemistable
        (D.1 : σ.slicing.IntervalCat C a b).obj (phaseSub D)
    · exact ⟨D, hDlt, hDss, hphaseBD⟩
    · obtain ⟨E, hElt, hEss, hphaseDE⟩ := ih D hDlt hDnonzero hDss
      exact ⟨E, hElt.trans hDlt, hEss, hphaseBD.trans hphaseDE⟩
  obtain ⟨B, hBne, hBtop, hBstrict, hphaseXB⟩ :=
    exists_phase_gt_strictSubobject_of_not_semistable C hX hCharge hns
  let Bstr : StrictSubobject X := ⟨B, hBstrict⟩
  have hBnonzero : ¬IsZero (Bstr.1 : σ.slicing.IntervalCat C a b) :=
    Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hBne
  by_cases hBss : F.IsSemistable
      (Bstr.1 : σ.slicing.IntervalCat C a b).obj (phaseSub Bstr)
  · exact ⟨B, hBne, hBtop, hBstrict, hBss, hphaseXB,
      Slicing.IntervalCat.strictShortExact_cokernel C B.arrow hBstrict⟩
  · obtain ⟨D, hDlt, hDss, hphaseBD⟩ := hP Bstr hBnonzero hBss
    have hDtop : D.1 ≠ ⊤ := by
      intro h
      have hle : D.1 ≤ B := hDlt.le
      rw [h] at hle
      exact hBtop (top_le_iff.mp hle)
    have hDne : D.1 ≠ ⊥ := by
      intro h
      exact hDss.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero
        ((Slicing.IntervalCat.subobject_isZero_iff_eq_bot C D.1).mpr h))
    exact ⟨D.1, hDne, hDtop, D.2, hDss,
      hphaseXB.trans hphaseBD,
      Slicing.IntervalCat.strictShortExact_cokernel C D.1.arrow D.2⟩

end SkewedStabilityFunction

end CategoryTheory.Triangulated.Deformation
