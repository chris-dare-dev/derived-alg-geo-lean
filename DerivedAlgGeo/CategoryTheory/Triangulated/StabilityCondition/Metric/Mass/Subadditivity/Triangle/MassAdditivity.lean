/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Subadditivity.Triangle.MassTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Separation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Cohomology.Sequence

/-!
# Exact mass splitting across a distinguished triangle

This file owns the cases in which Harder--Narasimhan mass is exactly additive
along a distinguished triangle: when the two filtrations are phase separated,
when the endpoints are cut by a `gtProp`/`leProp` boundary, and when both
endpoints are semistable of a common phase.  The easy triangle inequalities
that follow directly from additivity are proved here too.

The hard arbitrary-left case is developed in `PhaseOne` and `Consequences`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction Matrix
open CategoryTheory.Triangulated
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- HN mass is exactly additive across a distinguished triangle when every
phase of the right-hand HN filtration is strictly below every phase of the
left-hand filtration.  The proof peels the right filtration from its head
and uses the octahedral axiom to append that factor to the left filtration. -/
theorem stabilityMass_toReal_triangle_eq_add_of_hn_separated
    (σ : StabilityCondition.WithClassMap C v)
    {X E Y : C}
    (GX : HNFiltration C σ.slicing.P X)
    (GY : HNFiltration C σ.slicing.P Y)
    (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C)
    (hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal := by
  suffices hmain :
      ∀ (m : ℕ) {X Y : C}
        (GX : HNFiltration C σ.slicing.P X)
        (GY : HNFiltration C σ.slicing.P Y), GY.n ≤ m →
        ∀ {E : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C →
          (∀ i : Fin GY.n, ∀ j : Fin GX.n, GY.φ i < GX.φ j) →
          (stabilityMass σ E).toReal =
            (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal by
    exact hmain GY.n GX GY le_rfl f g h hT hsep
  intro m
  induction m with
  | zero =>
      intro X Y GX GY hn E f g h hT _hsep
      have hYn : GY.n = 0 := by omega
      have hYz : IsZero Y := GY.isZero_of_length_zero hYn
      haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
      rw [stabilityMass_congr σ (asIso f)]
      rw [show stabilityMass σ Y = 0 from
        (stabilityMass_eq_zero_iff σ Y).2 hYz]
      simp
  | succ m ih =>
      intro X Y GX GY hn E f g h hT hsep
      by_cases hYn : GY.n = 0
      · have hYz : IsZero Y := GY.isZero_of_length_zero hYn
        haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYz
        rw [stabilityMass_congr σ (asIso f)]
        rw [show stabilityMass σ Y = 0 from
          (stabilityMass_eq_zero_iff σ Y).2 hYz]
        simp
      · have hYpos : 0 < GY.n := Nat.pos_of_ne_zero hYn
        obtain ⟨Ytail, Gtail, a, b, c, hHead, hmassY, hnTail, hφTail⟩ :=
          GY.exists_headTail_mass σ hYpos
        obtain ⟨Z, fZE, hYZ, hZE⟩ := distinguished_cocone_triangle₁ (g ≫ b)
        let oct := Triangulated.someOctahedron'
          (show g ≫ b = g ≫ b by rfl) hT hHead hZE
        let iHead : Fin GY.n := ⟨0, hYpos⟩
        have hsepHead : ∀ j : Fin GX.n, GY.φ iHead < GX.φ j :=
          fun j ↦ hsep iHead j
        let GZ := GX.appendFactor C oct.triangle oct.mem
          (Iso.refl _) (Iso.refl _) (GY.φ iHead) (GY.semistable iHead) hsepHead
        have hmassZ :
            (stabilityMass σ Z).toReal =
              (stabilityMass σ X).toReal +
                ‖σ.charge (GY.factor iHead)‖ := by
          simpa [GZ, iHead, oct] using
            stabilityMass_toReal_appendFactor σ GX oct.triangle oct.mem
              (Iso.refl _) (Iso.refl _) (GY.φ iHead)
              (GY.semistable iHead) hsepHead
        have hsepTail :
            ∀ i : Fin Gtail.n, ∀ j : Fin GZ.n, Gtail.φ i < GZ.φ j := by
          intro i j
          obtain ⟨k, hkval, hkφ⟩ := hφTail i
          change Gtail.φ i <
            (GX.appendFactor C oct.triangle oct.mem
              (Iso.refl _) (Iso.refl _) (GY.φ iHead)
              (GY.semistable iHead) hsepHead).φ j
          simp only [HNFiltration.appendFactor]
          split_ifs with hj
          · rw [hkφ]
            exact hsep k ⟨j.val, hj⟩
          · rw [hkφ]
            exact GY.hφ (show iHead < k by
              apply Fin.mk_lt_mk.mpr
              omega)
        have hmassE := ih GZ Gtail (by rw [hnTail]; omega)
          fZE (g ≫ b) hYZ hZE hsepTail
        change (stabilityMass σ E).toReal =
          (stabilityMass σ Z).toReal +
            (stabilityMass σ Ytail).toReal at hmassE
        linarith

/-- Intrinsic cutoff form of exact mass splitting.  If the left endpoint has
all HN phases strictly above `t` and the right endpoint has all phases at
most `t`, the middle mass is the sum of the endpoint masses. -/
theorem stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    (σ : StabilityCondition.WithClassMap C v)
    {X E Y : C} (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (t : ℝ)
    (hX : σ.slicing.gtProp C t X) (hY : σ.slicing.leProp C t Y) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + (stabilityMass σ Y).toReal := by
  rcases hX with hXzero | ⟨GX, hGX, hXgt⟩
  · haveI : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ hT).mp hXzero
    rw [stabilityMass_congr σ (asIso g)]
    rw [show stabilityMass σ X = 0 from
      (stabilityMass_eq_zero_iff σ X).2 hXzero]
    simp
  · rcases hY with hYzero | ⟨GY, hGY, hYle⟩
    · haveI : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYzero
      rw [stabilityMass_congr σ (asIso f)]
      rw [show stabilityMass σ Y = 0 from
        (stabilityMass_eq_zero_iff σ Y).2 hYzero]
      simp
    · apply stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GX GY f g h hT
      intro i j
      calc
        GY.φ i ≤ GY.φ ⟨0, hGY⟩ :=
          GY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        _ ≤ t := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using hYle
        _ < GX.φ ⟨GX.n - 1, by lia⟩ := by
          simpa only [CategoryTheory.Triangulated.HNFiltration.phiMinus] using hXgt
        _ ≤ GX.φ j :=
          GX.hφ.antitone (Fin.mk_le_mk.mpr (by lia))

/-- On the amplitude window with phases in `(0, 2]`, mass is the sum of the
masses of the only two possibly nonzero heart-cohomology objects. -/
theorem stabilityMass_toReal_eq_heartCoh_negOne_add_zero
    (σ : StabilityCondition.WithClassMap C v) (X : C)
    (hgt : σ.slicing.gtProp C 0 X) (hle : σ.slicing.leProp C 2 X) :
    (stabilityMass σ X).toReal =
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure (-1) X).obj).toReal +
      (stabilityMass σ
        (CategoryTheory.Triangulated.Tilting.originalHeartCoh
          σ.slicing.toTStructure 0 X).obj).toReal := by
  let t := σ.slicing.toTStructure
  letI hXLE : t.IsLE X 0 := by
    refine ⟨?_⟩
    dsimp [t, Slicing.toTStructure]
    simpa using hgt
  letI hXGE : t.IsGE X (-1) := by
    refine ⟨?_⟩
    dsimp [t, Slicing.toTStructure]
    norm_num
    exact hle
  let T := (t.triangleLTGE 0).obj X
  have hT : T ∈ distTriang C := t.triangleLTGE_distinguished 0 X
  letI hT₁LE : t.IsLE T.obj₁ (-1) := by
    dsimp [T]
    exact t.isLE_truncLT_obj X 0 (-1) (by lia)
  letI hT₁GE : t.IsGE T.obj₁ (-1) := by
    dsimp [T]
    infer_instance
  letI hT₂LE : t.IsLE T.obj₂ 0 := by
    dsimp [T]
    exact hXLE
  letI hT₂GE : t.IsGE T.obj₂ (-1) := by
    dsimp [T]
    exact hXGE
  have hKLE : t.IsLE (T.obj₁⟦(-1 : ℤ)⟧) 0 :=
    t.isLE_shift (X := T.obj₁) (-1) (-1) 0 (by lia)
  have hKGE : t.IsGE (T.obj₁⟦(-1 : ℤ)⟧) 0 :=
    t.isGE_shift (X := T.obj₁) (-1) (-1) 0 (by lia)
  have hKheart : t.heart (T.obj₁⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).2 ⟨hKLE, hKGE⟩
  let K : t.heart.FullSubcategory := ⟨T.obj₁⟦(-1 : ℤ)⟧, hKheart⟩
  have hQLE : t.IsLE T.obj₃ 0 := by
    dsimp [T]
    infer_instance
  have hQGE : t.IsGE T.obj₃ 0 := by
    dsimp [T]
    infer_instance
  have hQheart : t.heart T.obj₃ := (t.mem_heart_iff _).2 ⟨hQLE, hQGE⟩
  let Q : t.heart.FullSubcategory := ⟨T.obj₃, hQheart⟩
  let eK : K.obj⟦(1 : ℤ)⟧ ≅ T.obj₁ := shiftNegShift T.obj₁ (1 : ℤ)
  let TK : Triangle C := Triangle.mk
    (eK.hom ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map eK.inv)
  have hTK : TK ∈ distTriang C := by
    refine isomorphic_distinguished _ hT TK ?_
    exact (Triangle.isoMk T TK eK.symm (Iso.refl _) (Iso.refl _)
      (by simp [TK]) (by simp [TK]) (by simp [TK])).symm
  have hKgt : σ.slicing.gtProp C 1 TK.obj₁ := by
    have hK0 : σ.slicing.gtProp C 0 K.obj :=
      (σ.slicing.toTStructure_heart_iff C K.obj).mp K.property |>.1
    simpa [TK, K] using σ.slicing.gtProp_shift C 0 K.obj 1 hK0
  have hQle : σ.slicing.leProp C 1 TK.obj₃ :=
    (σ.slicing.toTStructure_heart_iff C Q.obj).mp Q.property |>.2
  have hmass := stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
    σ TK.mor₁ TK.mor₂ TK.mor₃ hTK 1 hKgt hQle
  have eNeg := CategoryTheory.Triangulated.Tilting.originalHeartCohNegOneIsoOfAmplitude
    t K.property Q.property hTK
  have eZero := CategoryTheory.Triangulated.Tilting.originalHeartCohZeroIsoOfAmplitude
    t K.property Q.property hTK
  change (stabilityMass σ X).toReal =
    (stabilityMass σ (K.obj⟦(1 : ℤ)⟧)).toReal +
      (stabilityMass σ Q.obj).toReal at hmass
  rw [stabilityMass_shift_one] at hmass
  have hNegMass := stabilityMass_congr σ ((t.heart).ι.mapIso eNeg)
  have hZeroMass := stabilityMass_congr σ ((t.heart).ι.mapIso eZero)
  change stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t (-1) X).obj =
    stabilityMass σ K.obj at hNegMass
  change stabilityMass σ
      (CategoryTheory.Triangulated.Tilting.originalHeartCoh t 0 X).obj =
    stabilityMass σ Q.obj at hZeroMass
  rw [hNegMass, hZeroMass]
  exact hmass

omit [IsTriangulated C] in
/-- The charge of the middle object in a distinguished triangle is the sum
of the endpoint charges. -/
theorem StabilityCondition.WithClassMap.charge_triangle
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) :
    σ.charge T.obj₂ = σ.charge T.obj₁ + σ.charge T.obj₃ := by
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_triangle C v T hT, map_add]

/-- Mass is subadditive along a distinguished triangle whose middle object is
semistable. -/
theorem stabilityMass_triangle_le_of_obj₂_semistable
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) {φ : ℝ} (h₂ : σ.slicing.P φ T.obj₂) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  rw [stabilityMass_toReal_eq_norm_charge σ h₂,
    σ.charge_triangle T hT]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_charge_le_stabilityMass_toReal σ T.obj₁)
      (norm_charge_le_stabilityMass_toReal σ T.obj₃))

/-- Mass is subadditive when both endpoints of a distinguished triangle are
semistable of the same phase. -/
theorem stabilityMass_triangle_le_of_same_phase
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (φ : ℝ)
    (h₁ : σ.slicing.P φ T.obj₁) (h₃ : σ.slicing.P φ T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  exact stabilityMass_triangle_le_of_obj₂_semistable σ T hT
    (σ.slicing.semistable_of_triangle C φ h₁ h₃ hT)

/-- Mass is exactly additive when both endpoints of a distinguished triangle
lie in one semistable slice.  The middle object is in the same slice by
extension closure, and all three charges lie on the same ray. -/
theorem stabilityMass_toReal_triangle_eq_add_of_same_phase
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C) (φ : ℝ)
    (h₁ : σ.slicing.P φ T.obj₁) (h₃ : σ.slicing.P φ T.obj₃) :
    (stabilityMass σ T.obj₂).toReal =
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  have h₂ := σ.slicing.semistable_of_triangle C φ h₁ h₃ hT
  by_cases h₁z : IsZero T.obj₁
  · haveI : IsIso T.mor₂ := (Triangle.isZero₁_iff_isIso₂ T hT).mp h₁z
    rw [stabilityMass_congr σ (asIso T.mor₂)]
    rw [show stabilityMass σ T.obj₁ = 0 from
      (stabilityMass_eq_zero_iff σ T.obj₁).2 h₁z]
    simp
  · by_cases h₃z : IsZero T.obj₃
    · haveI : IsIso T.mor₁ := (Triangle.isZero₃_iff_isIso₁ T hT).mp h₃z
      rw [stabilityMass_congr σ (asIso T.mor₁)]
      rw [show stabilityMass σ T.obj₃ = 0 from
        (stabilityMass_eq_zero_iff σ T.obj₃).2 h₃z]
      simp
    · obtain ⟨m₁, hm₁, hZ₁⟩ := σ.compat φ T.obj₁ h₁ h₁z
      obtain ⟨m₃, hm₃, hZ₃⟩ := σ.compat φ T.obj₃ h₃ h₃z
      rw [stabilityMass_toReal_eq_norm_charge σ h₂,
        stabilityMass_toReal_eq_norm_charge σ h₁,
        stabilityMass_toReal_eq_norm_charge σ h₃,
        σ.charge_triangle T hT, hZ₁, hZ₃, ← add_mul]
      rw [norm_mul, norm_mul, norm_mul]
      rw [show ‖(m₁ : ℂ) + (m₃ : ℂ)‖ = m₁ + m₃ by
        simpa [abs_of_pos (add_pos hm₁ hm₃)] using
          Complex.norm_real (m₁ + m₃)]
      simp only [Complex.norm_real, Real.norm_of_nonneg hm₁.le,
        Real.norm_of_nonneg hm₃.le]
      ring

/-- At the upper boundary of the canonical heart, a semistable left endpoint
can be prepended to an arbitrary heart object without increasing mass beyond
the sum of the endpoint masses.

If the right endpoint has no phase-one HN factor, the two endpoint
filtrations are strictly separated.  Otherwise its unique phase-one head is
first combined with the left endpoint; that extension remains in `P(1)`, and
the remaining HN tail is strictly lower.  This is the precise mass comparison
behind the "easy to check" phase-one extension step in Ikeda's proof of
Proposition 3.3. -/
theorem stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
    (σ : StabilityCondition.WithClassMap C v) (T : Triangle C)
    (hT : T ∈ distTriang C)
    (h₁ : σ.slicing.P 1 T.obj₁)
    (h₃ : σ.slicing.leProp C 1 T.obj₃) :
    (stabilityMass σ T.obj₂).toReal ≤
      (stabilityMass σ T.obj₁).toReal +
        (stabilityMass σ T.obj₃).toReal := by
  rcases h₃ with hYzero | ⟨GY, hGYpos, hGYle⟩
  · haveI : IsIso T.mor₁ :=
      (Triangle.isZero₃_iff_isIso₁ T hT).mp hYzero
    rw [stabilityMass_congr σ (asIso T.mor₁)]
    rw [show stabilityMass σ T.obj₃ = 0 from
      (stabilityMass_eq_zero_iff σ T.obj₃).2 hYzero]
    simp
  · let iHead : Fin GY.n := ⟨0, hGYpos⟩
    have htop_le : GY.φ iHead ≤ 1 := by
      simpa only [CategoryTheory.Triangulated.HNFiltration.phiPlus] using hGYle
    by_cases htop : GY.φ iHead = 1
    · obtain ⟨Ytail, Gtail, a, b, c, hHead, hmassY, hnTail, hφTail⟩ :=
        CategoryTheory.Triangulated.HNFiltration.exists_headTail_mass σ GY hGYpos
      obtain ⟨Z, fZE, hYZ, hZE⟩ :=
        distinguished_cocone_triangle₁ (T.mor₂ ≫ b)
      let oct := Triangulated.someOctahedron'
        (show T.mor₂ ≫ b = T.mor₂ ≫ b by rfl) hT hHead hZE
      have hHeadP : σ.slicing.P 1 (GY.factor iHead) := by
        simpa [htop] using GY.semistable iHead
      have hZP : σ.slicing.P 1 Z := by
        exact σ.slicing.semistable_of_triangle C 1 h₁ hHeadP oct.mem
      have hmassZ :
          (stabilityMass σ Z).toReal ≤
            (stabilityMass σ T.obj₁).toReal +
              (stabilityMass σ (GY.factor iHead)).toReal := by
        simpa [oct] using stabilityMass_triangle_le_of_same_phase
          σ oct.triangle oct.mem 1 h₁ hHeadP
      let GZ := HNFiltration.single C Z 1 hZP
      have hsep : ∀ i : Fin Gtail.n, ∀ j : Fin GZ.n,
          Gtail.φ i < GZ.φ j := by
        intro i j
        obtain ⟨k, hkval, hkφ⟩ := hφTail i
        have hkpos : iHead < k := by
          apply Fin.mk_lt_mk.mpr
          omega
        rw [hkφ]
        rw [show GZ.φ j = 1 by rfl, ← htop]
        exact GY.hφ hkpos
      have hmassE := stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GZ Gtail fZE (T.mor₂ ≫ b) hYZ hZE hsep
      have hHeadMass := stabilityMass_toReal_eq_norm_charge σ hHeadP
      change (stabilityMass σ T.obj₂).toReal =
        (stabilityMass σ Z).toReal +
          (stabilityMass σ Ytail).toReal at hmassE
      change (stabilityMass σ T.obj₃).toReal =
        ‖σ.charge (GY.factor iHead)‖ +
          (stabilityMass σ Ytail).toReal at hmassY
      linarith
    · have htop_lt : GY.φ iHead < 1 := lt_of_le_of_ne htop_le htop
      let GX := HNFiltration.single C T.obj₁ 1 h₁
      have hsep : ∀ i : Fin GY.n, ∀ j : Fin GX.n,
          GY.φ i < GX.φ j := by
        intro i j
        have hi : GY.φ i ≤ GY.φ iHead :=
          GY.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        change GY.φ i < 1
        exact hi.trans_lt htop_lt
      exact le_of_eq (stabilityMass_toReal_triangle_eq_add_of_hn_separated
        σ GX GY T.mor₁ T.mor₂ T.mor₃ hT hsep)

end

end CategoryTheory.Triangulated
