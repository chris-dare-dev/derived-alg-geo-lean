/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.PullbackCokernel
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Stable

/-!
# Jordan--Hölder filtrations from local finiteness

The local-finiteness axiom controls intrinsic admissible subobjects in a
normalized thin interval.  In such an interval, admissible subobjects are
exactly owner strict subobjects.  Strict-Noetherian induction therefore finds
a stable quotient of every nonzero same-phase object, and strict-Artinian
induction iterates these quotients into an owner extension filtration.

No ordinary subobject is treated as admissible: every subobject constructed
below carries an explicit `IsStrictMono` witness, and all recursive steps use
the order on `StrictSubobject`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.TStructure
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

namespace Slicing

variable {s : Slicing C}

omit [IsTriangulated C] in
private theorem intervalProp_of_semistable {a b φ : ℝ} {E : C}
    (ha : a < φ) (hb : φ < b) (hE : s.P φ E) :
    s.intervalProp C a b E := by
  refine Or.inr ⟨HNFiltration.single C E φ hE, ?_⟩
  intro i
  simpa [HNFiltration.single] using And.intro ha hb

private def cokernelIso_of_distinguished
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (S : ShortComplex (s.IntervalCat C a b))
    {d : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom d ∈ distTriang C) :
    cokernel S.f ≅ S.X₃ := by
  let tR := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := heartFullSubcategoryAbelian tR
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hR : (S.map FR).ShortExact := by
    change (ShortComplex.mk (FR.map S.f) (FR.map S.g) _).ShortExact
    exact heartFullSubcategory_shortExact_of_distTriang tR hT
  have hCokR : IsColimit
      (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) :=
    hR.gIsCokernel
  have hCokMap : IsColimit
      (FR.mapCocone (CokernelCofork.ofπ S.g S.zero)) :=
    (isColimitMapCoconeCoforkEquiv' FR S.zero).symm hCokR
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitOfReflects FR hCokMap
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok

private theorem exists_nontrivial_strictSubobject_of_not_stable
    {a b φ : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (ha : a < φ) (hb : φ < b)
    {E : s.IntervalCat C a b} (hEφ : s.P φ E.obj)
    (hE : ¬IsZero E) (hnstable : ¬s.IsStableAt φ E.obj) :
    ∃ A : Subobject E, A ≠ ⊥ ∧ A ≠ ⊤ ∧
      IsStrictMono A.arrow ∧
      s.P φ (A : s.IntervalCat C a b).obj ∧
      s.P φ (cokernel A.arrow).obj := by
  have hEobj : ¬IsZero E.obj := fun h ↦
    hE (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have htriangle :
      ¬∀ {X Y : C}, s.P φ X → s.P φ Y →
        ∀ (f : X ⟶ E.obj) (g : E.obj ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang C → IsZero X ∨ IsZero Y := by
    intro h
    apply hnstable
    refine ⟨hEφ, hEobj, ?_⟩
    intro X Y hX hY f g h' hT'
    exact h hX hY f g h' hT'
  push Not at htriangle
  obtain ⟨X, Y, hXφ, hYφ, f, g, h, hT, hX, hY⟩ := htriangle
  let XI : s.IntervalCat C a b :=
    ⟨X, intervalProp_of_semistable C ha hb hXφ⟩
  let YI : s.IntervalCat C a b :=
    ⟨Y, intervalProp_of_semistable C ha hb hYφ⟩
  let fI : XI ⟶ E := ObjectProperty.homMk f
  let gI : E ⟶ YI := ObjectProperty.homMk g
  let S : ShortComplex (s.IntervalCat C a b) :=
    ShortComplex.mk fI gI (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)
  have hS : StrictShortExact S :=
    CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distinguished
      C s (by simpa [S, fI, gI] using hT)
  have hfstrict : IsStrictMono fI := ⟨hS.shortExact.mono_f, hS.strict_f⟩
  letI : Mono fI := hfstrict.mono
  let A : Subobject E := Subobject.mk fI
  have hAstrict : IsStrictMono A.arrow := by
    simpa [A] using
      CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.subobject_arrow_strictMono
        C fI hfstrict
  have hAbot : A ≠ ⊥ := by
    intro hAbot
    have hAZ : IsZero (A : s.IntervalCat C a b) :=
      (CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.subobject_isZero_iff_eq_bot
        (C := C) A).mpr hAbot
    exact hX (((s.intervalProp C a b).ι).map_isZero
      (hAZ.of_iso (Subobject.underlyingIso fI).symm))
  have hAtop : A ≠ ⊤ := by
    intro hAtop
    haveI : IsIso A.arrow := (Subobject.isIso_arrow_iff_eq_top A).2 hAtop
    haveI : IsIso fI := (Subobject.isIso_iff_mk_eq_top fI).2 (by
      simpa [A] using hAtop)
    haveI : IsIso f := by
      change IsIso fI.hom
      infer_instance
    letI : IsIso (Triangle.mk f g h).mor₁ := by
      change IsIso f
      infer_instance
    have hYZ : IsZero Y :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).mpr inferInstance
    exact hY hYZ
  let eA : (A : s.IntervalCat C a b) ≅ XI := Subobject.underlyingIso fI
  have hAφ : s.P φ (A : s.IntervalCat C a b).obj :=
    (s.P φ).prop_of_iso
      (((s.intervalProp C a b).ι).mapIso eA).symm hXφ
  let eCokEq : cokernel A.arrow ≅
      cokernel ((Subobject.underlyingIso fI).hom ≫ fI) :=
    cokernelIsoOfEq (by
      exact (Subobject.underlyingIso_hom_comp_eq_mk fI).symm)
  let eCokI : cokernel A.arrow ≅ cokernel fI :=
    eCokEq ≪≫ cokernelEpiComp (Subobject.underlyingIso fI).hom fI
  let eCokY : cokernel fI ≅ YI :=
    cokernelIso_of_distinguished C S (by simpa [S, fI, gI] using hT)
  let eQ : (cokernel A.arrow).obj ≅ Y :=
    ((s.intervalProp C a b).ι).mapIso (eCokI ≪≫ eCokY)
  have hQφ : s.P φ (cokernel A.arrow).obj :=
    (s.P φ).prop_of_iso eQ.symm hYφ
  exact ⟨A, hAbot, hAtop, hAstrict, hAφ, hQφ⟩

private theorem exists_stable_strictQuotient
    {a b φ : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (ha : a < φ) (hb : φ < b)
    (hfinite : ∀ Y : s.IntervalCat C a b, IsStrictFiniteLengthObject Y)
    {X : s.IntervalCat C a b} (hXφ : s.P φ X.obj)
    (hX : ¬IsZero X) :
    ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
      s.P φ (M : s.IntervalCat C a b).obj ∧
      s.IsStableAt φ (cokernel M.arrow).obj := by
  letI : IsStrictNoetherianObject X := (hfinite X).isStrictNoetherianObject
  have recurse : ∀ S : StrictSubobject X,
      s.P φ (S.1 : s.IntervalCat C a b).obj →
      s.P φ (cokernel S.1.arrow).obj →
      ¬IsZero (cokernel S.1.arrow) →
      ∃ M : Subobject X, M ≠ ⊤ ∧ IsStrictMono M.arrow ∧
        s.P φ (M : s.IntervalCat C a b).obj ∧
        s.IsStableAt φ (cokernel M.arrow).obj := by
    intro S
    induction S using IsWellFounded.induction
        (· > · : StrictSubobject X → StrictSubobject X → Prop) with
    | ind S ih =>
        intro hSφ hQSφ hQS
        have hStop : S.1 ≠ ⊤ := by
          intro htop
          haveI : IsIso S.1.arrow :=
            (Subobject.isIso_arrow_iff_eq_top S.1).2 htop
          exact hQS (isZero_cokernel_of_epi S.1.arrow)
        by_cases hstable : s.IsStableAt φ (cokernel S.1.arrow).obj
        · exact ⟨S.1, hStop, S.2, hSφ, hstable⟩
        · let QS : s.IntervalCat C a b := cokernel S.1.arrow
          have hQSI : ¬IsZero QS := hQS
          obtain ⟨A, hAbot, hAtop, hAstrict, hAφ, hQAφ⟩ :=
            exists_nontrivial_strictSubobject_of_not_stable C ha hb hQSφ hQSI hstable
          let Tsub : Subobject X :=
            (Subobject.pullback (cokernel.π S.1.arrow)).obj A
          have hTstrict : IsStrictMono Tsub.arrow :=
            CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.pullbackArrow_strictMono
              C (cokernel.π S.1.arrow) A hAstrict
          let T : StrictSubobject X := ⟨Tsub, hTstrict⟩
          have hST : S < T :=
            CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot
              C hAbot
          have hTtop : Tsub ≠ ⊤ :=
            CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.pullbackCokernel_ne_top
              C hAtop hAstrict
          have hQT : ¬IsZero (cokernel Tsub.arrow) :=
            CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.cokernel_not_isZero_of_ne_top
              C hTtop hTstrict
          have hTφ : s.P φ (Tsub : s.IntervalCat C a b).obj := by
            have hleft :=
              CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.strictShortExact_pullback_left
                C (cokernel.condition S.1.arrow)
                  (S.2.isLimitKernelFork) (isStrictEpi_cokernel S.1.arrow) A
            obtain ⟨δ, htri⟩ :=
              CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distinguished_of_strictShortExact
                C s hleft
            exact s.semistable_of_triangle C φ hSφ hAφ htri
          let eQT : cokernel Tsub.arrow ≅ cokernel A.arrow :=
            CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.cokernelPullbackIso
              C S.1 hAstrict
          have hQTφ : s.P φ (cokernel Tsub.arrow).obj :=
            (s.P φ).prop_of_iso
              (((s.intervalProp C a b).ι).mapIso eQT).symm hQAφ
          exact ih T hST hTφ hQTφ hQT
  let S₀ : StrictSubobject X :=
    ⟨⊥, CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.bot_arrow_strictMono C⟩
  have hS₀φ : s.P φ (S₀.1 : s.IntervalCat C a b).obj := by
    apply s.zero_mem_of_isZero C
    exact ((s.intervalProp C a b).ι).map_isZero
      ((CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.subobject_isZero_iff_eq_bot
        (C := C) S₀.1).mpr rfl)
  let e₀ : cokernel S₀.1.arrow ≅ X := by
    rw [show S₀.1.arrow = 0 by simp [S₀, Subobject.bot_arrow]]
    exact cokernelZeroIsoTarget
  have hQ₀φ : s.P φ (cokernel S₀.1.arrow).obj :=
    (s.P φ).prop_of_iso (((s.intervalProp C a b).ι).mapIso e₀).symm hXφ
  have hQ₀ : ¬IsZero (cokernel S₀.1.arrow) := fun h ↦
    hX (h.of_iso e₀.symm)
  exact recurse S₀ hS₀φ hQ₀φ hQ₀

/-- Local finiteness supplies the same-phase Jordan--Hölder filtrations
used by stable-object mass--Hom reduction. -/
theorem IsLocallyFinite.hasJordanHolderFiltrations
    (hlocal : s.IsLocallyFinite C) : s.HasJordanHolderFiltrations := by
  intro φ E hEφ
  obtain ⟨η, hη, hηhalf, hfinite⟩ := hlocal.intervalFinite
  letI : Fact (φ - η < φ + η) := ⟨by linarith⟩
  letI : Fact ((φ + η) - (φ - η) ≤ 1) := ⟨by linarith⟩
  let EI : s.IntervalCat C (φ - η) (φ + η) :=
    ⟨E, intervalProp_of_semistable C (by linarith) (by linarith) hEφ⟩
  have hstrict : ∀ Y : s.IntervalCat C (φ - η) (φ + η),
      IsStrictFiniteLengthObject Y := fun Y ↦
    CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength
      C (hfinite φ Y)
  letI : IsStrictArtinianObject EI := (hstrict EI).isStrictArtinianObject
  let topS : StrictSubobject EI := ⟨⊤, isStrictMono_of_isIso⟩
  let Psub : StrictSubobject EI → Prop := fun S ↦
      s.P φ (S.1 : s.IntervalCat C (φ - η) (φ + η)).obj →
      ExtensionClosure (s.IsStableAt φ)
        (S.1 : s.IntervalCat C (φ - η) (φ + η)).obj
  have recurse : ∀ S : StrictSubobject EI, Psub S := by
    intro S
    refine (wellFounded_lt.induction S ?_)
    intro S ih hSφ
    by_cases hSzero : IsZero (S.1 : s.IntervalCat C (φ - η) (φ + η))
    · exact .zero (((s.intervalProp C (φ - η) (φ + η)).ι).map_isZero hSzero)
    · obtain ⟨M, hMtop, hMstrict, hMφ, hstable⟩ :=
        exists_stable_strictQuotient C (by linarith) (by linarith)
          hstrict hSφ hSzero
      let Tsub : Subobject EI :=
        CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.liftSub
          C S.1 M
      have hTstrict : IsStrictMono Tsub.arrow :=
        CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.liftSub_arrow_strictMono
          C S.2 hMstrict
      let T : StrictSubobject EI := ⟨Tsub, hTstrict⟩
      have hTS : T < S :=
        CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.liftSub_lt
          C S.1 hMtop
      let eM : (Tsub : s.IntervalCat C (φ - η) (φ + η)) ≅
          (M : s.IntervalCat C (φ - η) (φ + η)) :=
        Subobject.underlyingIso (M.arrow ≫ S.1.arrow)
      have hTφ : s.P φ
          (Tsub : s.IntervalCat C (φ - η) (φ + η)).obj :=
        (s.P φ).prop_of_iso
          (((s.intervalProp C (φ - η) (φ + η)).ι).mapIso eM).symm hMφ
      have hTclosure := ih T hTS hTφ
      have hMclosure : ExtensionClosure (s.IsStableAt φ)
          (M : s.IntervalCat C (φ - η) (φ + η)).obj :=
        ExtensionClosure.ofIso
          (((s.intervalProp C (φ - η) (φ + η)).ι).mapIso eM) hTclosure
      have hshort :=
        CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat.strictShortExact_cokernel
          C M.arrow hMstrict
      obtain ⟨δ, htri⟩ :=
        CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distinguished_of_strictShortExact
          C s hshort
      exact ExtensionClosure.ext htri hMclosure (.mem hstable)
  have htopφ : s.P φ
      (topS.1 : s.IntervalCat C (φ - η) (φ + η)).obj := by
    let eTop : (topS.1 : s.IntervalCat C (φ - η) (φ + η)) ≅ EI :=
      asIso topS.1.arrow
    exact (s.P φ).prop_of_iso
      (((s.intervalProp C (φ - η) (φ + η)).ι).mapIso eTop).symm hEφ
  have htop := recurse topS htopφ
  let eTop : (topS.1 : s.IntervalCat C (φ - η) (φ + η)) ≅ EI :=
    asIso topS.1.arrow
  exact ExtensionClosure.ofIso
    (((s.intervalProp C (φ - η) (φ + η)).ι).mapIso eTop) htop

end Slicing

end CategoryTheory.Triangulated
