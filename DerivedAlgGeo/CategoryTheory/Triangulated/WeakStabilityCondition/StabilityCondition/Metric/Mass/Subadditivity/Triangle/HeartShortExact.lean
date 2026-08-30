/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Subadditivity.Triangle.HeartObservable

/-!
# Named inequality targets and the heart short-exact bridge

This file owns the statement-level interface of the subadditivity milestone --
the `Prop`-valued named targets -- together with the bridge between a short
exact sequence in the canonical heart and the distinguished triangle it
generates.  It converts an abelian Harder--Narasimhan filtration into an
ambient tower of the same mass and proves the phase-one boundary-heart
inequality.

Definitions of the targets are kept above their proofs so that a consumer may
depend on the statement without the proof's import surface.
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

/-- The first major mass-triangle milestone, in its phase-one boundary-heart
form.  For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in the
canonical heart with `C ∈ P(1)`, the mass of `A` is at most the combined
mass of `B` and `C`.

This is a named proof target, not an installed premise. -/
def StabilityMassBoundaryHeartInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact → σ.slicing.P 1 S.X₃.obj →
      (stabilityMass σ S.X₁.obj).toReal ≤
        (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

/-- The second paper-level mass-triangle milestone: subadditivity for a
distinguished triangle whose first object is semistable. -/
def StabilityMassSemistableLeftTriangleInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v) (T : Triangle C),
    T ∈ distTriang C →
    ∀ (φ : ℝ), σ.slicing.P φ T.obj₁ →
      (stabilityMass σ T.obj₂).toReal ≤
        (stabilityMass σ T.obj₁).toReal +
          (stabilityMass σ T.obj₃).toReal

/-- The arbitrary-left octahedral milestone.  Once the triangle inequality is
known for semistable first objects, split an HN filtration of the first object
into its head and tail.  The octahedron produces one semistable-left triangle
and a shorter arbitrary-left triangle, so induction proves the unrestricted
statement. -/
theorem stabilityMassTriangleInequality_of_semistable_obj₁
    (hsemistable :
      StabilityMassSemistableLeftTriangleInequality (C := C) (v := v)) :
    StabilityMassTriangleInequality (C := C) (v := v) := by
  intro σ T hT
  obtain ⟨F⟩ := σ.slicing.hn_exists T.obj₁
  suffices hmain :
      ∀ (m : ℕ) (U : Triangle C), U ∈ distTriang C →
        ∀ G : HNFiltration C σ.slicing.P U.obj₁, G.n ≤ m →
          (stabilityMass σ U.obj₂).toReal ≤
            (stabilityMass σ U.obj₁).toReal +
              (stabilityMass σ U.obj₃).toReal by
    exact hmain F.n T hT F le_rfl
  intro m
  induction m with
  | zero =>
      intro U hU G hG
      have hn : G.n = 0 := by omega
      have hzero : IsZero U.obj₁ := G.isZero_of_length_zero hn
      haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
      rw [stabilityMass_congr σ (asIso U.mor₂)]
      simp [show stabilityMass σ U.obj₁ = 0 from
        (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
  | succ m ih =>
      intro U hU G hG
      by_cases hn0 : G.n = 0
      · have hzero : IsZero U.obj₁ := G.isZero_of_length_zero hn0
        haveI : IsIso U.mor₂ := (Triangle.isZero₁_iff_isIso₂ U hU).mp hzero
        rw [stabilityMass_congr σ (asIso U.mor₂)]
        simp [show stabilityMass σ U.obj₁ = 0 from
          (stabilityMass_eq_zero_iff σ U.obj₁).2 hzero]
      · have hn : 0 < G.n := Nat.pos_of_ne_zero hn0
        obtain ⟨Y, Gtail, f, _g, _δ, hhead, hmass, hnTail, _hφ⟩ :=
          G.exists_headTail_mass σ hn
        obtain ⟨Z, v₁₃, w₁₃, h₁₃⟩ :=
          distinguished_cocone_triangle (f ≫ U.mor₁)
        let oct := Triangulated.someOctahedron rfl hhead hU h₁₃
        have hfirst := hsemistable σ
          (Triangle.mk (f ≫ U.mor₁) v₁₃ w₁₃) h₁₃
          (G.φ ⟨0, hn⟩) (G.semistable ⟨0, hn⟩)
        have hheadMass :
            (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal =
              ‖σ.charge (G.factor ⟨0, hn⟩)‖ :=
          stabilityMass_toReal_eq_norm_charge σ (G.semistable ⟨0, hn⟩)
        change (stabilityMass σ U.obj₂).toReal ≤
          (stabilityMass σ (G.factor ⟨0, hn⟩)).toReal +
            (stabilityMass σ Z).toReal at hfirst
        rw [hheadMass] at hfirst
        have htail :
            (stabilityMass σ Z).toReal ≤
              (stabilityMass σ Y).toReal +
                (stabilityMass σ U.obj₃).toReal := by
          simpa [oct] using ih oct.triangle oct.mem Gtail (by
            rw [hnTail]
            omega)
        linarith

/-- The first remaining polygonal milestone: mass subadditivity for every
short exact sequence in the canonical heart `P((0, 1])`. -/
def StabilityMassHeartShortExactInequality : Prop :=
  ∀ (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory),
    S.ShortExact →
      (stabilityMass σ S.X₂.obj).toReal ≤
        (stabilityMass σ S.X₁.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal

/-- A short exact sequence in the canonical heart is induced by a
distinguished triangle on its underlying ambient objects. -/
theorem heartShortExact_exists_distinguished_triangle
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧,
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := σ.slicing.toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  letI : IsNormalMonoCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalEpiCategory
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  haveI := hS.mono_f
  haveI := hS.epi_g
  exact TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t S.f S.g S.zero (fun {W} α hα ↦ by
      have hker : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
      exact ⟨hker.lift (KernelFork.ofι α hα),
        hker.fac _ WalkingParallelPair.zero⟩)

/-- In a short exact sequence in the canonical heart, if the middle object
lies on the phase-one boundary ray, then both endpoint objects do as well.
This is the boundary-specific kernel/image closure used in the six-term
cohomology argument; it does not assert the false general closure of
`P(φ)` under arbitrary heart subobjects. -/
theorem phaseOne_endpoints_of_heart_shortExact
    (σ : StabilityCondition.WithClassMap C v)
    (S : ShortComplex σ.slicing.toTStructure.heart.FullSubcategory)
    (hS : S.ShortExact) (h₂ : σ.slicing.P 1 S.X₂.obj) :
    σ.slicing.P 1 S.X₁.obj ∧ σ.slicing.P 1 S.X₃.obj := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  by_cases h₁ : IsZero S.X₁
  · have h₁obj := (t.heart).ι.map_isZero h₁
    haveI : IsIso S.g := hS.isIso_g_iff.mpr h₁
    exact ⟨σ.slicing.zero_mem_of_isZero C 1 _ h₁obj,
      (σ.slicing.P 1).prop_of_iso ((t.heart).ι.mapIso (asIso S.g)) h₂⟩
  · by_cases h₃ : IsZero S.X₃
    · have h₃obj := (t.heart).ι.map_isZero h₃
      haveI : IsIso S.f := hS.isIso_f_iff.mpr h₃
      exact ⟨(σ.slicing.P 1).prop_of_iso
          ((t.heart).ι.mapIso (asIso S.f)).symm h₂,
        σ.slicing.zero_mem_of_isZero C 1 _ h₃obj⟩
    · have h₁obj : ¬IsZero S.X₁.obj := fun hz ↦ h₁ <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₁) hz
      have h₃obj : ¬IsZero S.X₃.obj := fun hz ↦ h₃ <|
        ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₃) hz
      have h₂obj : ¬IsZero S.X₂.obj := by
        intro hz
        have hz' := ObjectProperty.FullSubcategory.isZero_of_obj_isZero
          (C := C) (P := t.heart) (X := S.X₂) hz
        haveI := hS.mono_f
        exact h₁ (IsZero.of_mono S.f hz')
      obtain ⟨m, hm, hcharge⟩ := σ.compat 1 S.X₂.obj h₂ h₂obj
      have him₂ : (Z.charge S.X₂).im = 0 := by
        change (σ.charge S.X₂.obj).im = 0
        rw [hcharge]
        simp [Complex.exp_mul_I]
      have hadd := Z.additive S hS
      have himadd : (Z.charge S.X₂).im =
          (Z.charge S.X₁).im + (Z.charge S.X₃).im := by
        simpa using congrArg Complex.im hadd
      have him₁_nonneg : 0 ≤ (Z.charge S.X₁).im := by
        rcases Z.nonzero_mem S.X₁ h₁ with h | ⟨h, -⟩
        · exact h.le
        · exact h.ge
      have him₃_nonneg : 0 ≤ (Z.charge S.X₃).im := by
        rcases Z.nonzero_mem S.X₃ h₃ with h | ⟨h, -⟩
        · exact h.le
        · exact h.ge
      have him₁ : (Z.charge S.X₁).im = 0 := by linarith
      have him₃ : (Z.charge S.X₃).im = 0 := by linarith
      have hre₁ : (Z.charge S.X₁).re < 0 := by
        rcases Z.nonzero_mem S.X₁ h₁ with h | h
        · exfalso
          simpa [him₁] using h
        · exact h.2
      have hre₃ : (Z.charge S.X₃).re < 0 := by
        rcases Z.nonzero_mem S.X₃ h₃ with h | h
        · exfalso
          simpa [him₃] using h
        · exact h.2
      have hphase₁ : Z.phase S.X₁ = 1 := by
        rw [StabilityFunction.phase]
        have hz : Z.charge S.X₁ = ((Z.charge S.X₁).re : ℂ) :=
          Complex.ext rfl (by simpa using him₁)
        rw [hz, Complex.arg_ofReal_of_neg hre₁]
        field_simp [Real.pi_ne_zero]
      have hphase₃ : Z.phase S.X₃ = 1 := by
        rw [StabilityFunction.phase]
        have hz : Z.charge S.X₃ = ((Z.charge S.X₃).re : ℂ) :=
          Complex.ext rfl (by simpa using him₃)
        rw [hz, Complex.arg_ofReal_of_neg hre₃]
        field_simp [Real.pi_ne_zero]
      have hss₁ : Z.IsSemistable S.X₁ := ⟨h₁, fun B _ ↦ by
        rw [hphase₁]
        exact Z.phase_le_one B⟩
      have hss₃ : Z.IsSemistable S.X₃ := ⟨h₃, fun B _ ↦ by
        rw [hphase₃]
        exact Z.phase_le_one B⟩
      have hP₁ := σ.mem_slicing_of_heart_isSemistable S.X₁ hss₁
      have hP₃ := σ.mem_slicing_of_heart_isSemistable S.X₃ hss₃
      rw [hphase₁] at hP₁
      rw [hphase₃] at hP₃
      exact ⟨hP₁, hP₃⟩

/-- An abelian HN filtration in the canonical heart is also an ambient HN
filtration after replacing each short exact successive quotient by its
distinguished triangle.  Consequently its factor-norm mass is exactly the
ambient `stabilityMass`. -/
theorem AbelianHNFiltration.mass_eq_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v)
    {E : σ.slicing.toTStructure.heart.FullSubcategory}
    (F : @AbelianHNFiltration _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E) :
    @AbelianHNFiltration.mass _ _
      ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
      σ.observableStabilityFunctionOnHeart E F =
        (stabilityMass σ E.obj).toReal := by
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let fH (i : Fin F.n) :
      (F.chain i.castSucc : t.heart.FullSubcategory) ⟶
        (F.chain i.succ : t.heart.FullSubcategory) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI hmono (i : Fin F.n) : Mono (fH i) := by
    dsimp [fH]
    infer_instance
  let S (i : Fin F.n) : ShortComplex t.heart.FullSubcategory :=
    ShortComplex.mk (fH i) (cokernel.π (fH i)) (cokernel.condition (fH i))
  have hS (i : Fin F.n) : (S i).ShortExact := by
    exact StabilityFunction.shortExact_of_mono (fH i)
  let δ (i : Fin F.n) :
      (cokernel (fH i)).obj ⟶ (F.chain i.castSucc : t.heart.FullSubcategory).obj⟦(1 : ℤ)⟧ :=
    Classical.choose (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  have hδ (i : Fin F.n) :
      Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i) ∈ distTriang C := by
    exact Classical.choose_spec
      (heartShortExact_exists_distinguished_triangle σ (S i) (hS i))
  let objFn : Fin (F.n + 1) → C := fun j ↦ (F.chain j : t.heart.FullSubcategory).obj
  let mapSuccFn : ∀ i : Fin F.n, objFn i.castSucc ⟶ objFn i.succ :=
    fun i ↦ (fH i).hom
  let T (i : Fin F.n) : Triangle C :=
    Triangle.mk (fH i).hom (cokernel.π (fH i)).hom (δ i)
  let G : HNFiltration C σ.slicing.P E.obj :=
    { n := F.n
      chain := ComposableArrows.mkOfObjOfMapSucc objFn mapSuccFn
      triangle := T
      triangle_dist := fun i ↦ hδ i
      triangle_obj₁ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      triangle_obj₂ := fun i ↦ ⟨eqToIso (by
        simp only [T, ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj,
          objFn]
        rfl)⟩
      base_isZero := by
        change IsZero (objFn 0)
        have hzero : IsZero (F.chain 0 : t.heart.FullSubcategory) :=
          (StabilityFunction.subobject_isZero_iff_eq_bot (F.chain 0)).2 F.chain_bot
        exact (t.heart).ι.map_isZero hzero
      top_iso := by
        have htop : F.chain (Fin.last F.n) = ⊤ := F.chain_top
        let eEq : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅
            ((⊤ : Subobject E) : t.heart.FullSubcategory) :=
          eqToIso (congrArg (fun S : Subobject E ↦
            (S : t.heart.FullSubcategory)) htop)
        let eTop : (F.chain (Fin.last F.n) : t.heart.FullSubcategory) ≅ E :=
          eEq.trans (asIso (⊤ : Subobject E).arrow)
        exact ⟨(t.heart).ι.mapIso eTop⟩
      φ := F.phase
      hφ := F.phase_strictAnti
      semistable := fun i ↦ by
        have hP := σ.mem_slicing_of_heart_isSemistable
          (cokernel (fH i)) (by simpa [Z, fH] using F.factor_semistable i)
        rw [show Z.phase (cokernel (fH i)) = F.phase i by
          simpa [Z, fH] using F.factor_phase i] at hP
        exact hP }
  rw [stabilityMass_toReal_eq_sum σ G]
  unfold AbelianHNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- The phase-one boundary-heart mass inequality.  The nonzero case is the
boundary-cut comparison for abelian HN polygons, transported to ambient mass
by `AbelianHNFiltration.mass_eq_stabilityMass_toReal`; the zero source case is
handled directly. -/
theorem stabilityMassBoundaryHeartInequality :
    StabilityMassBoundaryHeartInequality (C := C) (v := v) := by
  intro σ S hS h₃
  let t := σ.slicing.toTStructure
  let Z := σ.observableStabilityFunctionOnHeart
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  by_cases h₁ : IsZero S.X₁
  · have h₁obj : IsZero S.X₁.obj := (t.heart).ι.map_isZero h₁
    rw [show stabilityMass σ S.X₁.obj = 0 from
      (stabilityMass_eq_zero_iff σ S.X₁.obj).2 h₁obj]
    positivity
  · haveI := hS.mono_f
    have h₂ : ¬IsZero S.X₂ := by
      intro h₂
      exact h₁ (IsZero.of_mono S.f h₂)
    obtain ⟨F⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₁ h₁
    obtain ⟨G⟩ := σ.observableStabilityFunctionOnHeart_hasHN S.X₂ h₂
    have hmass := AbelianHNFiltration.mass_le_add_norm_of_shortExact
      S hS F G σ.observableStabilityFunctionOnHeart_hasHN
    calc
      (stabilityMass σ S.X₁.obj).toReal =
          @AbelianHNFiltration.mass _ _
            ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
            σ.observableStabilityFunctionOnHeart S.X₁ F :=
        (AbelianHNFiltration.mass_eq_stabilityMass_toReal σ F).symm
      _ ≤ @AbelianHNFiltration.mass _ _
            ((σ.slicing.toTStructure).heartFullSubcategoryAbelian)
            σ.observableStabilityFunctionOnHeart S.X₂ G + ‖Z.charge S.X₃‖ := hmass
      _ = (stabilityMass σ S.X₂.obj).toReal +
          (stabilityMass σ S.X₃.obj).toReal := by
        rw [AbelianHNFiltration.mass_eq_stabilityMass_toReal σ G,
          stabilityMass_toReal_eq_norm_charge σ h₃]
        rfl

end

end CategoryTheory.Triangulated
