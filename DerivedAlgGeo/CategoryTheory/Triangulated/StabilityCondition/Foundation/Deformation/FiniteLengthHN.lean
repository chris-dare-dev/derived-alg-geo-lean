/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.StrictMDQ
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations

/-!
# Finite-length Harder--Narasimhan recursion in owner thin intervals

Strict maximal destabilizing quotients have kernels whose proper strict
quotients have larger phase.  Strict-Artinian induction on those kernels then
constructs finite Harder--Narasimhan filtrations without importing the frozen
external implementation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace Slicing.IntervalCat

variable {s : Slicing C} {a b : ℝ}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The interval kernel subobject represents the categorical kernel. -/
@[nolint defsWithUnderscore]
def kernelSubobject_isLimitKernelFork {X Y : s.IntervalCat C a b}
    (q : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelSubobject q).arrow
      (kernelSubobject_arrow_comp (f := q))) := by
  refine KernelFork.IsLimit.ofι' (kernelSubobject q).arrow
    (kernelSubobject_arrow_comp (f := q)) (fun {W} g hg ↦ ?_)
  let u : W ⟶ kernel q := kernel.lift q g hg
  refine ⟨u ≫ (kernelSubobjectIso q).inv, ?_⟩
  calc
    (u ≫ (kernelSubobjectIso q).inv) ≫ (kernelSubobject q).arrow =
        u ≫ kernel.ι q := by simp [Category.assoc]
    _ = g := kernel.lift_ι q g hg

/-- A strict epimorphism and its interval kernel subobject form a strict
short exact sequence. -/
theorem strictShortExact_kernelSubobject {X Y : s.IntervalCat C a b}
    (q : X ⟶ Y) (hq : IsStrictEpi q) :
    StrictShortExact
      (ShortComplex.mk (kernelSubobject q).arrow q
        (kernelSubobject_arrow_comp (f := q))) := by
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk (kernelSubobject q).arrow q
      (kernelSubobject_arrow_comp (f := q))
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  letI : CategoryWithHomology t.heart.FullSubcategory :=
    categoryWithHomology_of_abelian
  let FL := Slicing.IntervalCat.toLeftHeart C s a b
    (Fact.out : b - a ≤ 1)
  have hKer : IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero
      (kernelSubobject_isLimitKernelFork C q)
  have hEpi : Epi ((S.map FL).g) := by
    change Epi (FL.map q)
    exact Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s q hq
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

/-- The kernel subobject of a strict epimorphism to a nonzero target is
proper. -/
theorem kernelSubobject_ne_top_of_strictEpi_nonzero
    {X Y : s.IntervalCat C a b} {q : X ⟶ Y}
    (hq : IsStrictEpi q) (hY : ¬IsZero Y.obj) : kernelSubobject q ≠ ⊤ := by
  intro hK
  haveI : Epi q := hq.epi
  haveI : IsIso (kernelSubobject q).arrow :=
    (Subobject.isIso_iff_mk_eq_top _).2 (by
      simpa [Subobject.mk_arrow] using hK)
  have hq0 : q = 0 := by
    apply (cancel_epi (kernelSubobject q).arrow).1
    simp [kernelSubobject_arrow_comp (f := q)]
  have hY0 : IsZero Y := IsZero.of_epi_eq_zero q hq0
  exact hY (((s.intervalProp C a b).ι).map_isZero hY0)

end Slicing.IntervalCat

namespace Subobject

variable {D : Type*} [Category D]

/-- Owner spelling of the standard description of a mapped subobject. -/
theorem map_eq_mk_comp {X Y : D} (e : X ≅ Y) (A : Subobject X) :
    (Subobject.map e.hom).obj A = Subobject.mk (A.arrow ≫ e.hom) := by
  calc
    (Subobject.map e.hom).obj A =
        (Subobject.map e.hom).obj (Subobject.mk A.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (A.arrow ≫ e.hom) := by
      simpa using Subobject.map_mk A.arrow e.hom

/-- Mapping a subobject along an isomorphism identifies the mapped
representative canonically with the original subobject. -/
def mapUnderlyingIso {X Y : D} (e : X ≅ Y) (A : Subobject X) :
    ((Subobject.map e.hom).obj A : D) ≅ (A : D) :=
  Subobject.isoOfEqMk _ (A.arrow ≫ e.hom) (map_eq_mk_comp e A)

end Subobject

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The canonical cokernel of the interval kernel subobject of a strict
epimorphism has the same skewed phase as its target. -/
theorem phase_cokernel_kernelSubobject
    {X B : σ.slicing.IntervalCat C a b} (q : X ⟶ B)
    (hq : IsStrictEpi q) :
    F.phase (cokernel (kernelSubobject q).arrow).obj = F.phase B.obj := by
  let M : Subobject X := kernelSubobject q
  have hMstrict : IsStrictMono M.arrow := by
    simpa [M] using Slicing.IntervalCat.subobject_arrow_strictMono C
      (kernel.ι q) (isStrictMono_kernel q)
  have hXB : F.charge X.obj =
      F.charge (M : σ.slicing.IntervalCat C a b).obj + F.charge B.obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq)
    simpa only [charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  have hXM : F.charge X.obj =
      F.charge (M : σ.slicing.IntervalCat C a b).obj +
        F.charge (cokernel M.arrow).obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_cokernel C M.arrow hMstrict)
    simpa only [charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  apply F.phase_congr
  apply add_left_cancel (a :=
    F.charge (M : σ.slicing.IntervalCat C a b).obj)
  exact hXM.symm.trans hXB

end SkewedStabilityFunction

namespace IsStrictMDQ

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]
variable {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}

/-- Every proper strict quotient of the kernel of a strict MDQ has phase
strictly larger than the MDQ factor. -/
theorem phase_lt_of_strictQuotient_of_kernel
    (hq : IsStrictMDQ C σ F q)
    (hFiniteLength : ThinStrictFiniteLength C σ a b)
    (hCharge : ∀ {E : C}, σ.slicing.intervalProp C a b E →
      ¬IsZero E → F.ChargeNe E)
    {L U : ℝ}
    (hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      L < F.phase Y.obj ∧ F.phase Y.obj < U)
    (hWidth : U - L < 1)
    {A : Subobject (kernelSubobject q : σ.slicing.IntervalCat C a b)}
    (hAtop : A ≠ ⊤) (hAstrict : IsStrictMono A.arrow) :
    F.phase B.obj < F.phase (cokernel A.arrow).obj := by
  let M : Subobject X := kernelSubobject q
  have hMstrict : IsStrictMono M.arrow := by
    simpa [M] using Slicing.IntervalCat.subobject_arrow_strictMono C
      (kernel.ι q) (isStrictMono_kernel q)
  let liftA : Subobject X := Slicing.IntervalCat.liftSub C M A
  have hLiftStrict : IsStrictMono liftA.arrow := by
    simpa [liftA, M] using
      Slicing.IntervalCat.liftSub_arrow_strictMono C hMstrict hAstrict
  have hLiftLt : liftA < M := by
    simpa [liftA, M] using Slicing.IntervalCat.liftSub_lt C M hAtop
  have hLiftTop : liftA ≠ ⊤ := ne_top_of_lt (hLiftLt.trans_le le_top)
  have hCokLiftI : ¬IsZero (cokernel liftA.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hLiftTop hLiftStrict
  have hCokLift : ¬IsZero (cokernel liftA.arrow).obj := fun h ↦
    hCokLiftI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hPhaseGe : F.phase B.obj ≤ F.phase (cokernel liftA.arrow).obj :=
    hq.phase_le_of_strictQuotient C hFiniteLength hCharge hWindow hWidth
      (cokernel.π liftA.arrow) (isStrictEpi_cokernel liftA.arrow) hCokLift
  have hMp : M.arrow ≫ cokernel.π liftA.arrow ≠ 0 := by
    intro hzero
    let hKer := hLiftStrict.isLimitKernelFork
    let u : (M : σ.slicing.IntervalCat C a b) ⟶
        (liftA : σ.slicing.IntervalCat C a b) :=
      hKer.lift (KernelFork.ofι M.arrow hzero)
    have hu : u ≫ liftA.arrow = M.arrow :=
      hKer.fac _ WalkingParallelPair.zero
    have hle : M ≤ liftA := Subobject.le_of_comm u hu
    exact (not_le_of_gt hLiftLt) hle
  have hLiftPhase :
      F.phase B.obj < F.phase (cokernel liftA.arrow).obj := by
    refine lt_of_le_of_ne hPhaseGe ?_
    intro heq
    obtain ⟨t, ht⟩ := hq.factor_of_strictQuotient_phase_eq C
      hFiniteLength hCharge hWindow hWidth (cokernel.π liftA.arrow)
      (isStrictEpi_cokernel liftA.arrow) hCokLift heq.symm
    apply hMp
    calc
      M.arrow ≫ cokernel.π liftA.arrow = M.arrow ≫ (q ≫ t) := by rw [ht]
      _ = (M.arrow ≫ q) ≫ t := by simp [Category.assoc]
      _ = 0 := by simp [M]
  have hMtop : M ≠ ⊤ :=
    Slicing.IntervalCat.kernelSubobject_ne_top_of_strictEpi_nonzero C
      hq.strictEpi hq.nonzero
  have hCokMI : ¬IsZero (cokernel M.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hMtop hMstrict
  have hCokM : ¬IsZero (cokernel M.arrow).obj := fun h ↦
    hCokMI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hCokAI : ¬IsZero (cokernel A.arrow) :=
    Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
  have hCokA : ¬IsZero (cokernel A.arrow).obj := fun h ↦
    hCokAI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hBWindow := hWindow B hq.nonzero
  have hLiftWindow := hWindow (cokernel liftA.arrow) hCokLift
  have hAWindow := hWindow (cokernel A.arrow) hCokA
  have hBRange : F.phase B.obj ∈
      Set.Ioo (F.phase (cokernel liftA.arrow).obj - 1)
        (F.phase (cokernel liftA.arrow).obj + 1) := by
    constructor <;> linarith
  have hARange : F.phase (cokernel A.arrow).obj ∈
      Set.Ioo (F.phase (cokernel liftA.arrow).obj - 1)
        (F.phase (cokernel liftA.arrow).obj + 1) := by
    constructor <;> linarith
  have hXB : F.charge X.obj =
      F.charge (M : σ.slicing.IntervalCat C a b).obj + F.charge B.obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq.strictEpi)
    simpa only [SkewedStabilityFunction.charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  have hXM : F.charge X.obj =
      F.charge (M : σ.slicing.IntervalCat C a b).obj +
        F.charge (cokernel M.arrow).obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_cokernel C M.arrow hMstrict)
    simpa only [SkewedStabilityFunction.charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  have hBCharge : F.charge B.obj = F.charge (cokernel M.arrow).obj := by
    apply add_left_cancel
    exact hXB.symm.trans hXM
  have hMChargeNe : F.ChargeNe (cokernel M.arrow).obj := fun h ↦
    hq.semistable.charge_ne (hBCharge.trans h)
  have hBPhase : F.phase B.obj = F.phase (cokernel M.arrow).obj :=
    F.phase_congr hBCharge
  have hMRange : F.phase (cokernel M.arrow).obj ∈
      Set.Ioo (F.phase (cokernel liftA.arrow).obj - 1)
        (F.phase (cokernel liftA.arrow).obj + 1) := by
    simpa [hBPhase] using hBRange
  have hMPhase : F.phase (cokernel M.arrow).obj <
      F.phase (cokernel liftA.arrow).obj := by
    simpa [hBPhase] using hLiftPhase
  have hMA : F.charge (M : σ.slicing.IntervalCat C a b).obj =
      F.charge (A : σ.slicing.IntervalCat C a b).obj +
        F.charge (cokernel A.arrow).obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_cokernel C A.arrow hAstrict)
    simpa only [SkewedStabilityFunction.charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  have hXLift : F.charge X.obj =
      F.charge (liftA : σ.slicing.IntervalCat C a b).obj +
      F.charge (cokernel liftA.arrow).obj := by
    have hK := Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Slicing.IntervalCat.strictShortExact_cokernel C liftA.arrow hLiftStrict)
    simpa only [SkewedStabilityFunction.charge, classOf, map_add] using
      congrArg (fun z : K₀ C ↦ F.W (κ z)) hK
  let eLift : (liftA : σ.slicing.IntervalCat C a b).obj ≅
      (A : σ.slicing.IntervalCat C a b).obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (Subobject.underlyingIso (A.arrow ≫ M.arrow))
  have hLiftCharge : F.charge (liftA : σ.slicing.IntervalCat C a b).obj =
      F.charge (A : σ.slicing.IntervalCat C a b).obj :=
    congrArg F.W (classOf_iso C κ eLift)
  have hsum : F.charge (cokernel liftA.arrow).obj =
      F.charge (cokernel A.arrow).obj +
        F.charge (cokernel M.arrow).obj := by
    apply add_left_cancel
    calc
      F.charge (A : σ.slicing.IntervalCat C a b).obj +
          F.charge (cokernel liftA.arrow).obj = F.charge X.obj := by
        rw [← hLiftCharge]
        exact hXLift.symm
      _ = F.charge (M : σ.slicing.IntervalCat C a b).obj +
          F.charge (cokernel M.arrow).obj := hXM
      _ = (F.charge (A : σ.slicing.IntervalCat C a b).obj +
          F.charge (cokernel A.arrow).obj) +
            F.charge (cokernel M.arrow).obj := by rw [hMA]
      _ = F.charge (A : σ.slicing.IntervalCat C a b).obj +
          (F.charge (cokernel A.arrow).obj +
            F.charge (cokernel M.arrow).obj) := by abel
  have hAgt : F.phase (cokernel liftA.arrow).obj <
      F.phase (cokernel A.arrow).obj :=
    F.phase_seesaw_strict hsum.symm rfl hMPhase hMChargeNe hMRange hARange
  exact hLiftPhase.trans hAgt

end IsStrictMDQ

namespace SkewedStabilityFunction

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Strict-Artinian recursion on kernel subobjects constructs an owner HN
filtration.  The explicit lower quotient bound is the induction invariant
propagated from a strict MDQ to its kernel. -/
theorem hn_exists_of_quotientLowerBound
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
    (t : ℝ) (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X)
    (hquot : ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
      t < F.phase (cokernel A.arrow).obj) :
    let Psem : ℝ → ObjectProperty C := fun ψ E ↦ F.IsSemistable E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, t < G.φ j ∧ G.φ j < U := by
  let Psem : ℝ → ObjectProperty C := fun ψ E ↦ F.IsSemistable E ψ
  letI : IsStrictArtinianObject X := (hFiniteLength X).1
  let S₀ : StrictSubobject X := ⟨⊤, isStrictMono_of_isIso⟩
  let Psub : StrictSubobject X → Prop := fun S ↦
    ¬IsZero (S.1 : σ.slicing.IntervalCat C a b) →
      ∀ t : ℝ,
        (∀ A : Subobject (S.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
          IsStrictMono A.arrow →
          t < F.phase (cokernel A.arrow).obj) →
        ∃ G : HNFiltration C Psem
            (S.1 : σ.slicing.IntervalCat C a b).obj,
          ∀ j, t < G.φ j ∧ G.φ j < U
  have recurse : ∀ S : StrictSubobject X, Psub S := by
    intro S
    refine (show WellFounded
      ((· < ·) : StrictSubobject X → StrictSubobject X → Prop) from
        wellFounded_lt).induction S ?_
    intro S ih hS t hquotS
    let Y : σ.slicing.IntervalCat C a b := S.1
    have hYobj : ¬IsZero Y.obj := fun h ↦
      hS (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
    let ψY : ℝ := F.phase Y.obj
    by_cases hss : F.IsSemistable Y.obj ψY
    · let G : HNFiltration C Psem Y.obj := HNFiltration.single C Y.obj ψY hss
      refine ⟨G, ?_⟩
      intro j
      have hbotTop : (⊥ : Subobject Y) ≠ ⊤ := by
        intro hEq
        have hzero : IsZero Y := by
          have hbot : IsZero ((⊥ : Subobject Y) : σ.slicing.IntervalCat C a b) :=
            (isZero_zero (σ.slicing.IntervalCat C a b)).of_iso
              Subobject.botCoeIsoZero
          have htop : IsZero ((⊤ : Subobject Y) : σ.slicing.IntervalCat C a b) :=
            hbot.of_iso (eqToIso (congrArg Subobject.underlying.obj hEq)).symm
          exact htop.of_iso (asIso (⊤ : Subobject Y).arrow).symm
        exact hS hzero
      have hbotStrict : IsStrictMono ((⊥ : Subobject Y).arrow) :=
        Slicing.IntervalCat.bot_arrow_strictMono C
      have hbotPhase := hquotS ⊥ hbotTop hbotStrict
      let eI : cokernel ((⊥ : Subobject Y).arrow) ≅ Y := by
        rw [show ((⊥ : Subobject Y).arrow) = 0 by
          simp [Subobject.bot_arrow]]
        exact cokernelZeroIsoTarget
      let eC : (cokernel ((⊥ : Subobject Y).arrow)).obj ≅ Y.obj :=
        (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eI
      have hψ : t < ψY := hbotPhase.trans_eq (F.phase_iso eC)
      have hψU : ψY < U := (hWindow Y hYobj).2
      have hj0 : j.val = 0 := by
        have : j.val < 1 := by simp [G, HNFiltration.single] at j ⊢
        omega
      have hj : j = ⟨0, by simp [G, HNFiltration.single]⟩ := Fin.ext hj0
      subst j
      simpa [G, HNFiltration.single] using And.intro hψ hψU
    · letI : IsStrictArtinianObject Y := (hFiniteLength Y).1
      letI : IsStrictNoetherianObject Y := (hFiniteLength Y).2
      obtain ⟨B, q, hq⟩ := F.exists_strictMDQ C hFiniteLength hCharge
        hWindow hWidth hHom hDestabBound hS
      let K : Subobject Y := kernelSubobject q
      have hKbot : K ≠ ⊥ := hq.kernelSubobject_ne_bot_of_not_semistable C hss
      have hKtop : K ≠ ⊤ :=
        Slicing.IntervalCat.kernelSubobject_ne_top_of_strictEpi_nonzero C
          hq.strictEpi hq.nonzero
      have hKstrict : IsStrictMono K.arrow := by
        simpa [K] using Slicing.IntervalCat.subobject_arrow_strictMono C
          (kernel.ι q) (isStrictMono_kernel q)
      let T : Subobject X := Slicing.IntervalCat.liftSub C S.1 K
      have hTbot : T ≠ ⊥ := Slicing.IntervalCat.liftSub_ne_bot C S.1 hKbot
      have hTstrict : IsStrictMono T.arrow :=
        Slicing.IntervalCat.liftSub_arrow_strictMono C S.2 hKstrict
      let Tstr : StrictSubobject X := ⟨T, hTstrict⟩
      have hTlt : Tstr < S := by
        change T < S.1
        exact Slicing.IntervalCat.liftSub_lt C S.1 hKtop
      have hTne : ¬IsZero (T : σ.slicing.IntervalCat C a b) :=
        Slicing.IntervalCat.subobject_not_isZero_of_ne_bot C hTbot
      let ψB : ℝ := F.phase B.obj
      have hψB : t < ψB := by
        have hgt := hquotS K hKtop hKstrict
        exact hgt.trans_eq (F.phase_cokernel_kernelSubobject C q hq.strictEpi)
      have hψBU : ψB < U := (hWindow B hq.nonzero).2
      let eK : (T : σ.slicing.IntervalCat C a b) ≅
          (K : σ.slicing.IntervalCat C a b) := by
        dsimp [T, Slicing.IntervalCat.liftSub]
        exact Subobject.underlyingIso (K.arrow ≫ S.1.arrow)
      have hquotT : ∀ A : Subobject (T : σ.slicing.IntervalCat C a b),
          A ≠ ⊤ → IsStrictMono A.arrow →
          ψB < F.phase (cokernel A.arrow).obj := by
        intro A hAtop hAstrict
        let A' : Subobject (K : σ.slicing.IntervalCat C a b) :=
          (Subobject.map eK.hom).obj A
        have hA'top : A' ≠ ⊤ := by
          intro htop
          apply hAtop
          apply (Subobject.map_obj_injective eK.hom)
          calc
            (Subobject.map eK.hom).obj A = A' := rfl
            _ = ⊤ := htop
            _ = (Subobject.map eK.hom).obj
                (⊤ : Subobject (T : σ.slicing.IntervalCat C a b)) := by
              rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso eK.hom]
        have hA'strict : IsStrictMono A'.arrow := by
          have hcomp : IsStrictMono (A.arrow ≫ eK.hom) :=
            Slicing.IntervalCat.comp_strictMono C σ.slicing A.arrow eK.hom
              hAstrict isStrictMono_of_isIso
          have hEq : A' = Subobject.mk (A.arrow ≫ eK.hom) := by
            simpa [A'] using Subobject.map_eq_mk_comp eK A
          rw [hEq]
          exact Slicing.IntervalCat.subobject_arrow_strictMono C
            (A.arrow ≫ eK.hom) hcomp
        have hphase : F.phase (cokernel A.arrow).obj =
            F.phase (cokernel A'.arrow).obj := by
          let eA : (A : σ.slicing.IntervalCat C a b) ≅
              (A' : σ.slicing.IntervalCat C a b) :=
            (Subobject.mapUnderlyingIso eK A).symm
          have hw : A.arrow ≫ eK.hom = eA.hom ≫ A'.arrow := by
            simp [eA, A', Subobject.mapUnderlyingIso]
          let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
            cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA eK hw
          exact F.phase_iso
            ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC)
        rw [hphase]
        exact hq.phase_lt_of_strictQuotient_of_kernel C hFiniteLength
          hCharge hWindow hWidth hA'top hA'strict
      obtain ⟨GT, hGT⟩ := ih Tstr hTlt hTne ψB hquotT
      let GK : HNFiltration C Psem
          (K : σ.slicing.IntervalCat C a b).obj :=
        GT.ofIso C ((Slicing.IntervalCat.ι
          (C := C) (s := σ.slicing) a b).mapIso eK)
      have hGK : ∀ j, ψB < GK.φ j ∧ GK.φ j < U := by
        change ∀ j : Fin GT.n, ψB < GT.φ j ∧ GT.φ j < U
        exact hGT
      let SQ : ShortComplex (σ.slicing.IntervalCat C a b) :=
        ShortComplex.mk K.arrow q (kernelSubobject_arrow_comp (f := q))
      have hSQ : StrictShortExact SQ :=
        Slicing.IntervalCat.strictShortExact_kernelSubobject C q hq.strictEpi
      let H : HNFiltration C Psem Y.obj :=
        HNFiltration.appendStrictFactor C GK hSQ ψB hq.semistable
          (fun j ↦ (hGK j).1)
      refine ⟨H, ?_⟩
      intro j
      by_cases hj : j.val < GK.n
      · have hGj := hGK ⟨j.val, hj⟩
        have hGj' : t < GK.φ ⟨j.val, hj⟩ ∧
            GK.φ ⟨j.val, hj⟩ < U := ⟨hψB.trans hGj.1, hGj.2⟩
        simpa [H, GK, HNFiltration.appendStrictFactor,
          HNFiltration.appendFactor, hj] using hGj'
      · have hjlt : j.val < GK.n + 1 := by
          simpa [H, GK, HNFiltration.appendStrictFactor,
            HNFiltration.appendFactor] using j.is_lt
        have hjEq : j.val = GK.n := by omega
        have hlast : GK.n < H.n := by
          simp [H, GK, HNFiltration.appendStrictFactor,
            HNFiltration.appendFactor]
        have hjLast : j = ⟨GK.n, hlast⟩ := Fin.ext hjEq
        subst j
        have hfalse : ¬GK.n < GK.n := lt_irrefl _
        simpa [H, GK, HNFiltration.appendStrictFactor,
          HNFiltration.appendFactor, hfalse, ψB] using And.intro hψB hψBU
  have hS₀ : ¬IsZero (S₀.1 : σ.slicing.IntervalCat C a b) := by
    intro hzero
    exact hX (hzero.of_iso (asIso S₀.1.arrow).symm)
  have hquot₀ : ∀ A : Subobject
      (S₀.1 : σ.slicing.IntervalCat C a b), A ≠ ⊤ →
      IsStrictMono A.arrow → t < F.phase (cokernel A.arrow).obj := by
    intro A hAtop hAstrict
    let e₀ : (S₀.1 : σ.slicing.IntervalCat C a b) ≅ X := asIso S₀.1.arrow
    let A' : Subobject X := (Subobject.map e₀.hom).obj A
    have hA'top : A' ≠ ⊤ := by
      intro htop
      apply hAtop
      apply (Subobject.map_obj_injective e₀.hom)
      calc
        (Subobject.map e₀.hom).obj A = A' := rfl
        _ = ⊤ := htop
        _ = (Subobject.map e₀.hom).obj
            (⊤ : Subobject (S₀.1 : σ.slicing.IntervalCat C a b)) := by
          rw [Subobject.map_top, Subobject.mk_eq_top_of_isIso e₀.hom]
    have hA'strict : IsStrictMono A'.arrow := by
      have hcomp : IsStrictMono (A.arrow ≫ e₀.hom) :=
        Slicing.IntervalCat.comp_strictMono C σ.slicing A.arrow e₀.hom
          hAstrict isStrictMono_of_isIso
      have hEq : A' = Subobject.mk (A.arrow ≫ e₀.hom) := by
        simpa [A'] using Subobject.map_eq_mk_comp e₀ A
      rw [hEq]
      exact Slicing.IntervalCat.subobject_arrow_strictMono C
        (A.arrow ≫ e₀.hom) hcomp
    have hphase : F.phase (cokernel A.arrow).obj =
        F.phase (cokernel A'.arrow).obj := by
      let eA : (A : σ.slicing.IntervalCat C a b) ≅
          (A' : σ.slicing.IntervalCat C a b) :=
        (Subobject.mapUnderlyingIso e₀ A).symm
      have hw : A.arrow ≫ e₀.hom = eA.hom ≫ A'.arrow := by
        simp [eA, A', Subobject.mapUnderlyingIso]
      let eC : cokernel A.arrow ≅ cokernel A'.arrow :=
        cokernel.mapIso (f := A.arrow) (f' := A'.arrow) eA e₀ hw
      exact F.phase_iso
        ((Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso eC)
    rw [hphase]
    exact hquot A' hA'top hA'strict
  obtain ⟨G₀, hG₀⟩ := recurse S₀ hS₀ t hquot₀
  let eTop : (S₀.1 : σ.slicing.IntervalCat C a b).obj ≅ X.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso
      (asIso S₀.1.arrow)
  refine ⟨G₀.ofIso C eTop, ?_⟩
  intro j
  change t < G₀.φ j ∧ G₀.φ j < U
  exact hG₀ j

/-- Every nonzero object in an owner strict finite-length thin interval has
an HN filtration whose phases remain in the common phase window. -/
theorem hn_exists
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
    (X : σ.slicing.IntervalCat C a b) (hX : ¬IsZero X) :
    let Psem : ℝ → ObjectProperty C := fun ψ E ↦ F.IsSemistable E ψ
    ∃ G : HNFiltration C Psem X.obj,
      ∀ j, L < G.φ j ∧ G.φ j < U := by
  have hquot : ∀ A : Subobject X, A ≠ ⊤ → IsStrictMono A.arrow →
      L < F.phase (cokernel A.arrow).obj := by
    intro A hAtop hAstrict
    have hQI : ¬IsZero (cokernel A.arrow) :=
      Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict
    have hQ : ¬IsZero (cokernel A.arrow).obj := fun h ↦
      hQI (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
    exact (hWindow (cokernel A.arrow) hQ).1
  exact F.hn_exists_of_quotientLowerBound C hFiniteLength hCharge
    hWindow hWidth hHom hDestabBound L X hX hquot

end SkewedStabilityFunction

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
