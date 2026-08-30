/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.PullbackCokernel
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Strict maximal destabilizing quotients in owner thin intervals

This module introduces the strict finite-length hypothesis and the witness
structure used by the owner Harder--Narasimhan recursion. It remains on the
Mathlib-only side of the ownership boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- Every object of an owner thin interval is strict Artinian and strict
Noetherian. This is the chain-condition hypothesis used by strict MDQ
selection and the finite-length HN recursion. -/
def ThinStrictFiniteLength (σ : StabilityCondition.WithClassMap C κ)
    (a b : ℝ) [Fact (a < b)] [Fact (b - a ≤ 1)] : Prop :=
  ∀ Y : σ.slicing.IntervalCat C a b,
    IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y

/-- Ordinary finite length of every thin-interval object implies owner strict
finite length. -/
theorem ThinStrictFiniteLength.of_finiteLength
    (σ : StabilityCondition.WithClassMap C κ) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (h : ∀ Y : σ.slicing.IntervalCat C a b,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ThinStrictFiniteLength C σ a b := by
  intro Y
  letI : IsArtinianObject Y := (h Y).1
  letI : IsNoetherianObject Y := (h Y).2
  exact ⟨isStrictArtinianObject_of_isArtinianObject,
    isStrictNoetherianObject_of_isNoetherianObject⟩

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Strict-Noetherian induction selects a semistable strict quotient whose
phase is no greater than that of the original nonzero object. -/
theorem exists_semistable_strictQuotient_le_phase
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      F.IsSemistable (cokernel M.arrow).obj
        (F.phase (cokernel M.arrow).obj) ∧
      F.phase (cokernel M.arrow).obj ≤ F.phase X.obj := by
  let phaseQ : Subobject X → ℝ := fun M =>
    F.phase (cokernel M.arrow).obj
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  have h : ∀ S : StrictSubobject X, ¬IsZero (cokernel S.1.arrow) →
      ∃ T : StrictSubobject X, S.1 ≤ T.1 ∧
        F.IsSemistable (cokernel T.1.arrow).obj (phaseQ T.1) ∧
        phaseQ T.1 ≤ phaseQ S.1 := by
    intro S hQS
    revert hQS
    induction S using IsWellFounded.induction
        (· > · : StrictSubobject X → StrictSubobject X → Prop) with
    | ind S ih =>
        intro hQS
        have hStop : S.1 ≠ ⊤ := by
          intro htop
          haveI : IsIso S.1.arrow := by
            apply (Subobject.isIso_iff_mk_eq_top S.1.arrow).2
            simpa [Subobject.mk_arrow] using htop
          exact hQS (isZero_cokernel_of_epi S.1.arrow)
        let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
        letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
        by_cases hss : F.IsSemistable QS.obj (phaseQ S.1)
        · exact ⟨S, le_rfl, hss, le_rfl⟩
        · obtain ⟨A, hAne, hAtop, hAstrict, _, hAphase, _⟩ :=
            exists_first_strictShortExact_of_not_semistable C
              (X := QS) hQS hss hCharge
          let pbA : Subobject X :=
            (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hpbStrict : IsStrictMono pbA.arrow :=
            Slicing.IntervalCat.pullbackArrow_strictMono C
              (cokernel.π S.1.arrow) A hAstrict
          let T : StrictSubobject X := ⟨pbA, hpbStrict⟩
          have hST : S < T :=
            Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot C hAne
          have hpbTop : pbA ≠ ⊤ :=
            Slicing.IntervalCat.pullbackCokernel_ne_top C hAtop hAstrict
          have hQT : ¬IsZero (cokernel pbA.arrow) :=
            Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hpbTop hpbStrict
          obtain ⟨R, hTR, hRss, hRphase⟩ := ih T hST hQT
          have hpbPhase : phaseQ pbA = F.phase (cokernel A.arrow).obj :=
            F.phase_cokernelPullback C S.1 hAstrict
          have hphaseDrop : phaseQ pbA < phaseQ S.1 := by
            rw [hpbPhase]
            exact F.phase_cokernel_lt_of_phase_gt_strictSubobject C
              hAne hAtop hAstrict hAphase hCharge hWindow hWidth
          exact ⟨R, hST.le.trans hTR, hRss,
            hRphase.trans hphaseDrop.le⟩
  let S0 : StrictSubobject X :=
    ⟨⊥, Slicing.IntervalCat.bot_arrow_strictMono C⟩
  have hS0 : ¬IsZero (cokernel S0.1.arrow) := by
    let e : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    intro hzero
    exact hX (hzero.of_iso e.symm)
  obtain ⟨T, _, hTss, hTphase⟩ := h S0 hS0
  have hTtop : T.1 ≠ ⊤ := by
    intro htop
    haveI : IsIso T.1.arrow := by
      apply (Subobject.isIso_iff_mk_eq_top T.1.arrow).2
      simpa [Subobject.mk_arrow] using htop
    have hzero : IsZero (cokernel T.1.arrow).obj :=
      ((σ.slicing.intervalProp C a b).ι).map_isZero
        (isZero_cokernel_of_epi T.1.arrow)
    exact hTss.nonzero hzero
  have hphase0 : phaseQ S0.1 = F.phase X.obj := by
    let eI : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    let eC : (cokernel ((⊥ : Subobject X).arrow)).obj ≅ X.obj :=
      (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
    simpa [phaseQ, S0] using F.phase_iso eC
  exact ⟨T.1, hTtop, T.2, hTss, hTphase.trans_eq hphase0⟩

end SkewedStabilityFunction

/-- A strict maximal destabilizing quotient in an owner thin interval. Its
phase is minimal among nonzero semistable strict quotients, and equality
forces the competing quotient to factor through it. -/
structure IsStrictMDQ
    (σ : StabilityCondition.WithClassMap C κ) {a b : ℝ}
    (F : SkewedStabilityFunction C κ σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} (q : X ⟶ B) : Prop where
  /-- The quotient map is a strict epimorphism. -/
  strictEpi : IsStrictEpi q
  /-- The quotient is nonzero as an ambient object. -/
  nonzero : ¬IsZero B.obj
  /-- The quotient is semistable at its skewed phase. -/
  semistable : F.IsSemistable B.obj (F.phase B.obj)
  /-- The quotient has minimal phase, with the expected rigidity at equal
  phase. -/
  minimal :
    ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'), IsStrictEpi q' →
      ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
      F.phase B.obj ≤ F.phase B'.obj ∧
        (F.phase B'.obj = F.phase B.obj → ∃ t : B ⟶ B', q' = q ≫ t)

namespace IsStrictMDQ

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]
variable {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}

/-- A semistable interval object is its own strict MDQ when every nonzero
interval object has phase in a common window of width less than one. -/
theorem id_of_semistable {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    (hss : F.IsSemistable X.obj (F.phase X.obj)) :
    IsStrictMDQ C σ F (𝟙 X) where
  strictEpi := isStrictEpi_of_isIso
  nonzero := hss.nonzero
  semistable := hss
  minimal := by
    intro B' q' hq' hB' hssB'
    let S := ShortComplex.mk (kernel.ι q') q' (kernel.condition q')
    have hS : StrictShortExact S := hq'.strictShortExact_kernel q'
    obtain ⟨δ, hT⟩ :=
      Slicing.IntervalCat.exists_distinguished_of_strictShortExact
        C σ.slicing hS
    have hXWindow := hWindow X hss.nonzero
    have hB'Window := hWindow B' hB'
    have hB'Range : F.phase B'.obj ∈
        Set.Ioo (F.phase X.obj - 1) (F.phase X.obj + 1) := by
      constructor <;> linarith
    have hphase : F.phase X.obj ≤ F.phase B'.obj :=
      hss.phase_le_of_quotient_triangle hT hssB'.charge_ne hB'Range
        (fun hK ↦ by
          have hKWindow := hWindow (kernel q') hK
          refine ⟨?_, hss.phase_le_of_triangle hT
            (kernel q').property B'.property hK⟩
          linarith)
    refine ⟨hphase, fun _ ↦ ⟨q', ?_⟩⟩
    simp

/-- A strict MDQ is epic. -/
theorem epi (hq : IsStrictMDQ C σ F q) : Epi q := hq.strictEpi.epi

/-- A strict MDQ is strict. -/
theorem strict (hq : IsStrictMDQ C σ F q) : IsStrict q := hq.strictEpi.strict

/-- The minimal-phase part of the strict MDQ universal property. -/
theorem phase_le (hq : IsStrictMDQ C σ F q)
    {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B')
    (hq' : IsStrictEpi q') (hB' : ¬IsZero B'.obj)
    (hss : F.IsSemistable B'.obj (F.phase B'.obj)) :
    F.phase B.obj ≤ F.phase B'.obj :=
  (hq.minimal q' hq' hB' hss).1

/-- Equal phase forces a semistable strict quotient to factor through a
strict MDQ. -/
theorem factor_of_phase_eq (hq : IsStrictMDQ C σ F q)
    {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B')
    (hq' : IsStrictEpi q') (hB' : ¬IsZero B'.obj)
    (hss : F.IsSemistable B'.obj (F.phase B'.obj))
    (hphase : F.phase B'.obj = F.phase B.obj) :
    ∃ t : B ⟶ B', q' = q ≫ t :=
  (hq.minimal q' hq' hB' hss).2 hphase

/-- Precomposing a strict MDQ by an isomorphism of source interval objects
preserves its universal property. -/
theorem precomposeIso (hq : IsStrictMDQ C σ F q)
    {X' : σ.slicing.IntervalCat C a b} (e : X' ≅ X) :
    IsStrictMDQ C σ F (e.hom ≫ q) where
  strictEpi := Slicing.IntervalCat.comp_strictEpi
    (C := C) (s := σ.slicing) (a := a) (b := b) e.hom q
    (isStrictEpi_of_isIso (f := e.hom)) hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB' hss
    let q'' : X ⟶ B' := e.inv ≫ q'
    have hq'' : IsStrictEpi q'' := Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) e.inv q'
      (isStrictEpi_of_isIso (f := e.inv)) hq'
    refine ⟨(hq.minimal q'' hq'' hB' hss).1, ?_⟩
    intro hphase
    obtain ⟨t, ht⟩ := (hq.minimal q'' hq'' hB' hss).2 hphase
    refine ⟨t, ?_⟩
    calc
      q' = e.hom ≫ (e.inv ≫ q') := by simp
      _ = e.hom ≫ (q ≫ t) := by
        simpa [q''] using congrArg (fun f : X ⟶ B' => e.hom ≫ f) ht
      _ = (e.hom ≫ q) ≫ t := by rw [Category.assoc]

/-- If a strict MDQ factors through a strict epimorphism, then the induced
quotient of the intermediate object is again a strict MDQ. -/
theorem of_strictEpi_factor (hq : IsStrictMDQ C σ F q)
    {Q : σ.slicing.IntervalCat C a b} {p : X ⟶ Q} (hp : IsStrictEpi p)
    {π : Q ⟶ B} (hfac : p ≫ π = q) : IsStrictMDQ C σ F π where
  strictEpi := by
    apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p π
    simpa [hfac] using hq.strictEpi
  nonzero := hq.nonzero
  semistable := hq.semistable
  minimal := by
    intro B' q' hq' hB' hss
    have hpq' : IsStrictEpi (p ≫ q') := Slicing.IntervalCat.comp_strictEpi
      (C := C) (s := σ.slicing) (a := a) (b := b) p q' hp hq'
    refine ⟨(hq.minimal (p ≫ q') hpq' hB' hss).1, ?_⟩
    intro hphase
    obtain ⟨t, ht⟩ := (hq.minimal (p ≫ q') hpq' hB' hss).2 hphase
    refine ⟨t, ?_⟩
    haveI : Epi p := hp.epi
    apply (cancel_epi p).1
    calc
      p ≫ q' = q ≫ t := ht
      _ = (p ≫ π) ≫ t := by rw [hfac]
      _ = p ≫ (π ≫ t) := by rw [Category.assoc]

/-- The phase of a strict MDQ is bounded above by the phase of every nonzero
strict quotient, whether or not that quotient is already semistable. -/
theorem phase_le_of_strictQuotient (hq : IsStrictMDQ C σ F q)
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {Q : σ.slicing.IntervalCat C a b} (p : X ⟶ Q)
    (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj) :
    F.phase B.obj ≤ F.phase Q.obj := by
  have hQI : ¬IsZero Q := fun h =>
    hQ (((σ.slicing.intervalProp C a b).ι).map_isZero h)
  obtain ⟨M, hMtop, hMstrict, hMss, hMphase⟩ :=
    F.exists_semistable_strictQuotient_le_phase C hFiniteLength
      hCharge hWindow hWidth hQI
  have hcomp : IsStrictEpi (p ≫ cokernel.π M.arrow) :=
    Slicing.IntervalCat.comp_strictEpi C σ.slicing p
      (cokernel.π M.arrow) hp (isStrictEpi_cokernel M.arrow)
  have hCokI : ¬IsZero (cokernel M.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hMtop hMstrict
  have hCok : ¬IsZero (cokernel M.arrow).obj := fun h =>
    hCokI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  exact (phase_le (C := C) hq (p ≫ cokernel.π M.arrow) hcomp hCok
    hMss).trans hMphase

/-- A nonzero strict quotient having the same phase as a strict MDQ is
semistable. -/
theorem isSemistable_of_strictQuotient_phase_eq
    (hq : IsStrictMDQ C σ F q)
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {Q : σ.slicing.IntervalCat C a b} (p : X ⟶ Q)
    (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hphase : F.phase Q.obj = F.phase B.obj) :
    F.IsSemistable Q.obj (F.phase Q.obj) := by
  letI : IsStrictArtinianObject Q := (hFiniteLength Q).1
  by_contra hns
  have hQI : ¬IsZero Q := fun h =>
    hQ (((σ.slicing.intervalProp C a b).ι).map_isZero h)
  obtain ⟨A, hAne, hAtop, hAstrict, _, hAphase, _⟩ :=
    F.exists_first_strictShortExact_of_not_semistable C hQI hns hCharge
  have hcomp : IsStrictEpi (p ≫ cokernel.π A.arrow) :=
    Slicing.IntervalCat.comp_strictEpi C σ.slicing p
      (cokernel.π A.arrow) hp (isStrictEpi_cokernel A.arrow)
  have hCokI : ¬IsZero (cokernel A.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
  have hCok : ¬IsZero (cokernel A.arrow).obj := fun h =>
    hCokI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hmin : F.phase B.obj ≤ F.phase (cokernel A.arrow).obj :=
    phase_le_of_strictQuotient (C := C) hq hFiniteLength hCharge
      hWindow hWidth (p ≫ cokernel.π A.arrow) hcomp hCok
  have hdrop : F.phase (cokernel A.arrow).obj < F.phase B.obj := by
    calc
      F.phase (cokernel A.arrow).obj < F.phase Q.obj :=
        F.phase_cokernel_lt_of_phase_gt_strictSubobject C hAne hAtop
          hAstrict hAphase hCharge hWindow hWidth
      _ = F.phase B.obj := hphase
  exact (not_lt_of_ge hmin) hdrop

/-- Equal phase forces every nonzero strict quotient to factor through the
strict MDQ; semistability follows from the preceding theorem. -/
theorem factor_of_strictQuotient_phase_eq
    (hq : IsStrictMDQ C σ F q)
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {Q : σ.slicing.IntervalCat C a b} (p : X ⟶ Q)
    (hp : IsStrictEpi p) (hQ : ¬IsZero Q.obj)
    (hphase : F.phase Q.obj = F.phase B.obj) :
    ∃ t : B ⟶ Q, p = q ≫ t := by
  have hQss := isSemistable_of_strictQuotient_phase_eq (C := C) hq
    hFiniteLength hCharge hWindow hWidth p hp hQ hphase
  exact factor_of_phase_eq (C := C) hq p hp hQ hQss hphase

/-- An MDQ of the quotient by a destabilizing semistable strict subobject
composes to an MDQ of the original object. -/
theorem comp_of_destabilizing_semistable_subobject
    {A : Subobject X}
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {V : ℝ}
    (hHom : ∀ {E G : σ.slicing.IntervalCat C a b},
      F.IsSemistable E.obj (F.phase E.obj) →
      F.IsSemistable G.obj (F.phase G.obj) →
      F.phase G.obj < F.phase E.obj → F.phase E.obj < V →
      ∀ f : E ⟶ G, f = 0)
    (hAss : F.IsSemistable
      (A : σ.slicing.IntervalCat C a b).obj
      (F.phase (A : σ.slicing.IntervalCat C a b).obj))
    (hAstrict : IsStrictMono A.arrow)
    (hAphase : F.phase X.obj <
      F.phase (A : σ.slicing.IntervalCat C a b).obj)
    (hAtop : A ≠ ⊤)
    (hAupper : F.phase (A : σ.slicing.IntervalCat C a b).obj < V)
    {Q : σ.slicing.IntervalCat C a b}
    {r : cokernel A.arrow ⟶ Q}
    (hr : IsStrictMDQ C σ F r) :
    IsStrictMDQ C σ F (cokernel.π A.arrow ≫ r) where
  strictEpi := Slicing.IntervalCat.comp_strictEpi C σ.slicing
    (cokernel.π A.arrow) r (isStrictEpi_cokernel A.arrow) hr.strictEpi
  nonzero := hr.nonzero
  semistable := hr.semistable
  minimal := by
    intro Q' p hp hQ' hQ'ss
    have hCokI : ¬IsZero (cokernel A.arrow) :=
      Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
    have hCok : ¬IsZero (cokernel A.arrow).obj := fun h =>
      hCokI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
    have hRle : F.phase Q.obj ≤ F.phase (cokernel A.arrow).obj :=
      phase_le_of_strictQuotient (C := C) hr hFiniteLength hCharge
        hWindow hWidth (𝟙 _) isStrictEpi_of_isIso hCok
    have hAne : A ≠ ⊥ := by
      intro hbot
      have hAI : IsZero (A : σ.slicing.IntervalCat C a b) :=
        (Slicing.IntervalCat.subobject_isZero_iff_eq_bot C A).2 hbot
      exact hAss.nonzero (((σ.slicing.intervalProp C a b).ι).map_isZero hAI)
    have hCokA : F.phase (cokernel A.arrow).obj <
        F.phase (A : σ.slicing.IntervalCat C a b).obj :=
      (F.phase_cokernel_lt_of_phase_gt_strictSubobject C hAne hAtop
        hAstrict hAphase hCharge hWindow hWidth).trans hAphase
    have hRlt : F.phase Q.obj <
        F.phase (A : σ.slicing.IntervalCat C a b).obj :=
      hRle.trans_lt hCokA
    by_cases hle : F.phase Q.obj ≤ F.phase Q'.obj
    · refine ⟨hle, ?_⟩
      intro heq
      have hQ'lt : F.phase Q'.obj <
          F.phase (A : σ.slicing.IntervalCat C a b).obj := by
        rw [heq]
        exact hRlt
      have hzero : A.arrow ≫ p = 0 :=
        hHom hAss hQ'ss hQ'lt hAupper (A.arrow ≫ p)
      let p' : cokernel A.arrow ⟶ Q' := cokernel.desc A.arrow p hzero
      have hp' : IsStrictEpi p' := by
        apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
          (cokernel.π A.arrow) p'
        simpa [p'] using hp
      obtain ⟨t, ht⟩ :=
        factor_of_phase_eq (C := C) hr p' hp' hQ' hQ'ss heq
      refine ⟨t, ?_⟩
      calc
        p = cokernel.π A.arrow ≫ p' :=
          (cokernel.π_desc A.arrow p hzero).symm
        _ = cokernel.π A.arrow ≫ (r ≫ t) := by rw [ht]
        _ = (cokernel.π A.arrow ≫ r) ≫ t := by rw [Category.assoc]
    · have hlt : F.phase Q'.obj < F.phase Q.obj := lt_of_not_ge hle
      have hQ'lt : F.phase Q'.obj <
          F.phase (A : σ.slicing.IntervalCat C a b).obj := hlt.trans hRlt
      have hzero : A.arrow ≫ p = 0 :=
        hHom hAss hQ'ss hQ'lt hAupper (A.arrow ≫ p)
      let p' : cokernel A.arrow ⟶ Q' := cokernel.desc A.arrow p hzero
      have hp' : IsStrictEpi p' := by
        apply Slicing.IntervalCat.strictEpi_of_comp_strictEpi C σ.slicing
          (cokernel.π A.arrow) p'
        simpa [p'] using hp
      exact False.elim ((not_lt_of_ge
        (phase_le (C := C) hr p' hp' hQ' hQ'ss)) hlt)

end IsStrictMDQ

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Every nonzero owner thin-interval object admits a strict maximal
destabilizing quotient under strict finite length, a common phase window,
and the semistable Hom-vanishing used in the recursive transport step. -/
theorem exists_strictMDQ
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {V : ℝ}
    (hHom : ∀ {E G : σ.slicing.IntervalCat C a b},
      F.IsSemistable E.obj (F.phase E.obj) →
      F.IsSemistable G.obj (F.phase G.obj) →
      F.phase G.obj < F.phase E.obj → F.phase E.obj < V →
      ∀ f : E ⟶ G, f = 0)
    (hDestabBound : ∀ {Y : σ.slicing.IntervalCat C a b}, ¬IsZero Y →
      ∀ {A : Subobject Y},
      F.IsSemistable (A : σ.slicing.IntervalCat C a b).obj
        (F.phase (A : σ.slicing.IntervalCat C a b).obj) →
      IsStrictMono A.arrow →
      F.phase Y.obj < F.phase (A : σ.slicing.IntervalCat C a b).obj →
      F.phase (A : σ.slicing.IntervalCat C a b).obj < V)
    {X : σ.slicing.IntervalCat C a b} (hX : ¬IsZero X) :
    ∃ (B : σ.slicing.IntervalCat C a b) (q : X ⟶ B),
      IsStrictMDQ C σ F q := by
  letI : IsStrictNoetherianObject X := (hFiniteLength X).2
  suffices h : ∀ S : StrictSubobject X,
      ¬IsZero (cokernel S.1.arrow) →
      ∃ (B : σ.slicing.IntervalCat C a b)
        (q : cokernel S.1.arrow ⟶ B), IsStrictMDQ C σ F q by
    let S0 : StrictSubobject X :=
      ⟨⊥, Slicing.IntervalCat.bot_arrow_strictMono C⟩
    have hS0 : ¬IsZero (cokernel S0.1.arrow) := by
      let e : cokernel ((⊥ : Subobject X).arrow) ≅ X := by
        rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      intro hzero
      exact hX (hzero.of_iso e.symm)
    obtain ⟨B, q, hq⟩ := h S0 hS0
    let e : cokernel S0.1.arrow ≅ X := by
      rw [show ((⊥ : Subobject X).arrow) = 0 by simp [Subobject.bot_arrow]]
      exact cokernelZeroIsoTarget
    exact ⟨B, e.inv ≫ q, IsStrictMDQ.precomposeIso C hq e.symm⟩
  intro S
  induction S using IsWellFounded.induction
      (· > · : StrictSubobject X → StrictSubobject X → Prop) with
  | ind S ih =>
      intro hQS
      let QS : σ.slicing.IntervalCat C a b := cokernel S.1.arrow
      letI : IsStrictArtinianObject QS := (hFiniteLength QS).1
      letI : IsStrictNoetherianObject QS := (hFiniteLength QS).2
      by_cases hss : F.IsSemistable QS.obj (F.phase QS.obj)
      · exact ⟨QS, 𝟙 _, IsStrictMDQ.id_of_semistable C
          hWindow hWidth hss⟩
      · obtain ⟨A, hAne, hAtop, hAstrict, hAss, hAphase, _⟩ :=
          F.exists_first_strictShortExact_of_not_semistable C
            (X := QS) hQS hss hCharge
        let Tsub : Subobject X :=
          (Subobject.pullback (cokernel.π S.1.arrow)).obj A
        have hTstrict : IsStrictMono Tsub.arrow :=
          Slicing.IntervalCat.pullbackArrow_strictMono C
            (cokernel.π S.1.arrow) A hAstrict
        let T : StrictSubobject X := ⟨Tsub, hTstrict⟩
        have hST : S < T :=
          Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot C hAne
        have hTtop : Tsub ≠ ⊤ :=
          Slicing.IntervalCat.pullbackCokernel_ne_top C hAtop hAstrict
        have hQT : ¬IsZero (cokernel Tsub.arrow) :=
          Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hTtop hTstrict
        obtain ⟨B, qT, hqT⟩ := ih T hST hQT
        let eT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
          Slicing.IntervalCat.cokernelPullbackIso C S.1 hAstrict
        let qA : cokernel A.arrow ⟶ B := eT.inv ≫ qT
        have hqA : IsStrictMDQ C σ F qA :=
          IsStrictMDQ.precomposeIso C hqT eT.symm
        exact ⟨B, cokernel.π A.arrow ≫ qA,
          IsStrictMDQ.comp_of_destabilizing_semistable_subobject C
            hFiniteLength hCharge hWindow hWidth hHom hAss hAstrict
            hAphase hAtop (hDestabBound hQS hAss hAstrict hAphase) hqA⟩

end SkewedStabilityFunction

namespace IsStrictMDQ

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]
variable {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}

/-- A strict MDQ of a non-semistable source has a genuinely nonzero kernel
subobject. -/
theorem kernelSubobject_ne_bot_of_not_semistable
    (hq : IsStrictMDQ C σ F q)
    (hns : ¬F.IsSemistable X.obj (F.phase X.obj)) :
    kernelSubobject q ≠ ⊥ := by
  intro hK
  have hkerZero : IsZero (kernelSubobject q : σ.slicing.IntervalCat C a b) := by
    rw [hK]
    exact (isZero_zero (σ.slicing.IntervalCat C a b)).of_iso
      Subobject.botCoeIsoZero
  haveI : Mono q := Preadditive.mono_of_kernel_zero <|
    zero_of_source_iso_zero _ (hkerZero.of_iso (kernelSubobjectIso q).symm).isoZero
  haveI : IsIso q := IsStrictEpi.isIso hq.strictEpi
  let e : X.obj ≅ B.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso q)
  have hphase : F.phase B.obj = F.phase X.obj := F.phase_iso e.symm
  exact hns (hphase ▸ hq.semistable.ofIso e.symm)

end IsStrictMDQ

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
