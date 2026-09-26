/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Rouquier

/-!
# Composition of generation in triangulated envelopes

This file proves the composition law for Mathlib's existing triangEnvelopeIter tower. If Q is
reached from P in m extension steps and R from Q in n, then R is reached from P in m * n + m + n
steps. In Rouquier's indexing this is multiplication of the indices, and it gives
submultiplicativity for generation time after adding one.

The proof works with Mathlib's existing shifts, binary-product, retract, and extension-product
closures. It adds no closure operation. The auxiliary product-closure arguments are local to
this proof module.

The Stacks 0FXA result is stated in a form with a uniform finite bound for the objects of the
strong-generating property. Its classical-generator corollary uses a single strong generator,
for which such a bound is available. An arbitrary strong-generating property need not have one
uniform bound over all its objects, so that argument does not prove the fully general
object-property form of Mathlib's TODO.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

private noncomputable def retractBinaryProduct [HasBinaryProducts C]
    {X X' Y Y' : C} (rX : Retract X X') (rY : Retract Y Y') :
    Retract (X ⨯ Y) (X' ⨯ Y') where
  i := Limits.prod.map rX.i rY.i
  r := Limits.prod.map rX.r rY.r
  retract := by
    rw [Limits.prod.map_map, rX.retract, rY.retract, Limits.prod.map_id_id]

private lemma retractClosure_isClosedUnderBinaryProducts (Q : ObjectProperty C)
    [HasBinaryProducts C] [Q.IsClosedUnderBinaryProducts] :
    Q.retractClosure.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    intro X hX
    rcases hX with ⟨p⟩
    let X₁ := p.diag.obj ⟨WalkingPair.left⟩
    let X₂ := p.diag.obj ⟨WalkingPair.right⟩
    have hdiag : p.diag = Limits.pair X₁ X₂ := by
      ext j
      cases j <;> rfl
    have hprod : Q.retractClosure (X₁ ⨯ X₂) := by
      rcases p.prop_diag_obj ⟨WalkingPair.left⟩ with ⟨A, hA, ⟨rA⟩⟩
      rcases p.prop_diag_obj ⟨WalkingPair.right⟩ with ⟨B, hB, ⟨rB⟩⟩
      exact ⟨A ⨯ B, Q.prop_prod A B hA hB, ⟨retractBinaryProduct rA rB⟩⟩
    let e : X ≅ X₁ ⨯ X₂ :=
      p.isLimit.conePointUniqueUpToIso (Limits.limit.isLimit p.diag) ≪≫
        eqToIso (congrArg (fun F : Discrete WalkingPair ⥤ C => limit F) hdiag)
    exact Q.retractClosure.prop_of_iso e.symm hprod

private lemma extensionProduct_prop_prod (Q R : ObjectProperty C)
    [HasBinaryProducts C] [Q.IsClosedUnderBinaryProducts] [R.IsClosedUnderBinaryProducts]
    {X Y : C} (hX : extensionProduct Q R X) (hY : extensionProduct Q R Y) :
    extensionProduct Q R (X ⨯ Y) := by
  rcases hX with ⟨A₁, B₁, f₁, g₁, k₁, hT₁, hQ₁, hR₁⟩
  rcases hY with ⟨A₂, B₂, f₂, g₂, k₂, hT₂, hQ₂, hR₂⟩
  let T₁ : Triangle C := Triangle.mk f₁ g₁ k₁
  let T₂ : Triangle C := Triangle.mk f₂ g₂ k₂
  let T : WalkingPair → Triangle C := fun j => j.casesOn T₁ T₂
  have hT : ∀ j, T j ∈ distTriang C := by
    intro j
    cases j with
    | left => exact hT₁
    | right => exact hT₂
  let U := productTriangle T
  have hU : U ∈ distTriang C := productTriangle_distinguished T hT
  have hQA : Q U.obj₁ := by
    simpa [U] using Q.prop_pi (fun j : WalkingPair => (T j).obj₁) (by
      intro j
      cases j with
      | left => exact hQ₁
      | right => exact hQ₂)
  have hRB : R U.obj₃ := by
    simpa [U] using R.prop_pi (fun j : WalkingPair => (T j).obj₃) (by
      intro j
      cases j with
      | left => exact hR₁
      | right => exact hR₂)
  have hUmem : extensionProduct Q R U.obj₂ :=
    ⟨U.obj₁, U.obj₃, U.mor₁, U.mor₂, U.mor₃, hU, hQA, hRB⟩
  let F : WalkingPair → C := fun j => (T j).obj₂
  let A := (Discrete.functor F).obj ⟨WalkingPair.left⟩
  let B := (Discrete.functor F).obj ⟨WalkingPair.right⟩
  have hFan : IsLimit (Fan.mk U.obj₂ (Pi.π F)) := productIsProduct F
  let α := diagramIsoPair (Discrete.functor F)
  let c : Fan F := Fan.mk U.obj₂ (Pi.π F)
  let d := (Cone.postcompose α.hom).obj c
  have hMid : IsLimit d :=
    (IsLimit.equivOfNatIsoOfIso α c d (Iso.refl d)).toFun hFan
  let e : U.obj₂ ≅ A ⨯ B :=
    IsLimit.conePointUniqueUpToIso hMid (Limits.limit.isLimit (Limits.pair A B))
  have hA : A = X := by dsimp [A, F, T, T₁, T₂]; rfl
  have hB : B = Y := by dsimp [B, F, T, T₁, T₂]; rfl
  exact (extensionProduct Q R).prop_of_iso (e ≪≫ eqToIso (by rw [hA, hB])) hUmem

private lemma extensionProduct_isClosedUnderBinaryProducts (Q R : ObjectProperty C)
    [HasBinaryProducts C] [Q.IsClosedUnderBinaryProducts] [R.IsClosedUnderBinaryProducts] :
    (extensionProduct Q R).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    intro X hX
    rcases hX with ⟨p⟩
    let X₁ := p.diag.obj ⟨WalkingPair.left⟩
    let X₂ := p.diag.obj ⟨WalkingPair.right⟩
    have hdiag : p.diag = Limits.pair X₁ X₂ := by
      ext j
      cases j <;> rfl
    have hprod : extensionProduct Q R (X₁ ⨯ X₂) :=
      extensionProduct_prop_prod Q R (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩)
    let e : X ≅ X₁ ⨯ X₂ :=
      p.isLimit.conePointUniqueUpToIso (Limits.limit.isLimit p.diag) ≪≫
        eqToIso (congrArg (fun F : Discrete WalkingPair ⥤ C => limit F) hdiag)
    exact (extensionProduct Q R).prop_of_iso e.symm hprod

private lemma triangEnvelopeIter_isClosedUnderBinaryProducts (P : ObjectProperty C)
    [IsTriangulated C] (n : ℕ) :
    (P.triangEnvelopeIter n).IsClosedUnderBinaryProducts := by
  induction n with
  | zero =>
    rw [triangEnvelopeIter_zero]
    letI : ((P.shiftClosure ℤ).binaryProductsClosure).IsClosedUnderBinaryProducts := by
      infer_instance
    exact retractClosure_isClosedUnderBinaryProducts _
  | succ n ih =>
    rw [triangEnvelopeIter_succ' P n]
    letI : (P.triangEnvelopeIter n).IsClosedUnderBinaryProducts := ih
    letI : ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure).IsClosedUnderBinaryProducts :=
      retractClosure_isClosedUnderBinaryProducts _
    letI : (extensionProduct (P.triangEnvelopeIter n)
        ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure)).IsClosedUnderBinaryProducts :=
      extensionProduct_isClosedUnderBinaryProducts _ _
    exact retractClosure_isClosedUnderBinaryProducts _

/-- The zeroth envelope of an iterated envelope is contained in that stage. The nonemptiness
hypothesis supplies the zero object needed for the terminal-object condition in binary-product
closure. -/
theorem triangEnvelopeIter_zero_le [IsTriangulated C] (P : ObjectProperty C)
    [P.Nonempty] (n : ℕ) :
    (P.triangEnvelopeIter n).triangEnvelopeIter 0 ≤ P.triangEnvelopeIter n := by
  rw [triangEnvelopeIter_zero]
  let E := P.triangEnvelopeIter n
  letI : E.IsClosedUnderBinaryProducts := triangEnvelopeIter_isClosedUnderBinaryProducts P n
  letI : E.ContainsZero := by
    dsimp [E, triangEnvelopeIter]
    infer_instance
  rw [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure_le_iff]

/-- Composition of two finite generation stages has the multiplicative bound
m * n + m + n. In Rouquier's indexing, where stage n is ⟨P⟩_(n+1), this is the
composition law ⟨⟨P⟩_a⟩_b ⊆ ⟨P⟩_(a*b). -/
theorem triangEnvelopeIter_compose [IsTriangulated C] (P : ObjectProperty C)
    [P.Nonempty] (m n : ℕ) :
    (P.triangEnvelopeIter m).triangEnvelopeIter n ≤
      P.triangEnvelopeIter (m * n + m + n) := by
  induction n with
  | zero =>
    simpa using triangEnvelopeIter_zero_le P m
  | succ n ih =>
    let k := m * n + m + n
    let Q0 :=
      ((P.triangEnvelopeIter m).shiftClosure ℤ).binaryProductsClosure.retractClosure
    have hbase :
        Q0 ≤ P.triangEnvelopeIter m := by
      have hfixed := triangEnvelopeIter_zero_le P m
      rw [triangEnvelopeIter_zero (P.triangEnvelopeIter m)] at hfixed
      simpa [Q0] using hfixed
    rw [triangEnvelopeIter_succ' (P.triangEnvelopeIter m) n]
    calc
      _ ≤ (extensionProduct (P.triangEnvelopeIter k) (P.triangEnvelopeIter m)).retractClosure := by
        apply monotone_retractClosure
        calc
          extensionProduct ((P.triangEnvelopeIter m).triangEnvelopeIter n)
              Q0
              ≤ extensionProduct (P.triangEnvelopeIter k)
                  Q0 :=
                monotone_extensionProduct_left _ ih
          _ ≤ extensionProduct (P.triangEnvelopeIter k) (P.triangEnvelopeIter m) :=
                monotone_extensionProduct_right _ hbase
      _ ≤ P.triangEnvelopeIter (m * (n + 1) + m + (n + 1)) := by
        have hk : m * (n + 1) + m + (n + 1) = k + (m + 1) := by
          simp only [Nat.mul_succ]
          dsimp [k]
          omega
        rw [hk, P.triangEnvelopeIter_add' (n := k) (m := m + 1) (m' := m) rfl]

/-- Transfer finite generation through an intermediate property: if Q is reached from P
in m steps and R is reached from Q in n, then R is reached from P in m * n + m + n steps. -/
theorem le_triangEnvelopeIter_of_le_triangEnvelopeIter [IsTriangulated C]
    {P Q R : ObjectProperty C} [P.Nonempty] {m n : ℕ}
    (hQP : Q ≤ P.triangEnvelopeIter m) (hRQ : R ≤ Q.triangEnvelopeIter n) :
    R ≤ P.triangEnvelopeIter (m * n + m + n) := by
  calc
    R ≤ Q.triangEnvelopeIter n := hRQ
    _ ≤ (P.triangEnvelopeIter m).triangEnvelopeIter n := monotone_triangEnvelopeIter hQP n
    _ ≤ P.triangEnvelopeIter (m * n + m + n) := triangEnvelopeIter_compose P m n

private lemma triangEnvelopeIter_bot_of_not_nonempty (P : ObjectProperty C) (n : ℕ)
    (hP : ¬ P.Nonempty) : P.triangEnvelopeIter n = ⊥ := by
  have hbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
  subst P
  simp [triangEnvelopeIter]

private lemma generationTime_top_of_bot_left_of_nonempty_right (Q : ObjectProperty C)
    (hQ : Q.Nonempty) : (⊥ : ObjectProperty C).generationTime Q = ⊤ := by
  apply (generationTime_eq_top_iff ⊥ Q).2
  intro n hn
  rw [triangEnvelopeIter_bot_of_not_nonempty ⊥ n
    ((ObjectProperty.not_nonempty_iff_eq_bot (⊥ : ObjectProperty C)).mpr rfl)] at hn
  exact ((ObjectProperty.not_nonempty_iff_eq_bot Q).mpr (le_antisymm hn bot_le)) hQ

private lemma generationTime_zero_of_bot_right (P : ObjectProperty C) :
    P.generationTime ⊥ = 0 := by
  apply (generationTime_eq_zero_iff P ⊥).2
  exact bot_le

variable [IsTriangulated C]

/-- Generation time plus one is submultiplicative:
generationTime P R + 1 ≤ (generationTime P Q + 1) * (generationTime Q R + 1).

The unshifted additive law generationTime P R ≤ generationTime P Q + generationTime Q R is
false. For example, the iter 2 then iter 1 composition bound lands in iter 5, not the iter 4
an additive law would predict (⟨P⟩_3 ⋆ ⟨P⟩_3 ⊆ ⟨P⟩_6 in Rouquier's indexing). The +1 form
also avoids the junk case 0 * ⊤ = 0 in ℕ∞. -/
theorem generationTime_add_one_submultiplicative (P Q R : ObjectProperty C) :
    P.generationTime R + 1 ≤ (P.generationTime Q + 1) * (Q.generationTime R + 1) := by
  by_cases hP : P.Nonempty
  · letI := hP
    set a := P.generationTime Q
    set b := Q.generationTime R
    set c := P.generationTime R
    by_cases ha : a = ⊤
    · simp [a, ha]
    by_cases hb : b = ⊤
    · simp [a, b, hb]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ha
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hb
    have hQ : Q ≤ P.triangEnvelopeIter m := by
      apply (generationTime_le_coe_iff P Q m).1
      simp [a, hm]
    have hR : R ≤ Q.triangEnvelopeIter n := by
      apply (generationTime_le_coe_iff Q R n).1
      simp [b, hn]
    have hcomp : (P.triangEnvelopeIter m).triangEnvelopeIter n ≤
        P.triangEnvelopeIter (m * n + m + n) := triangEnvelopeIter_compose P m n
    have hreach : R ≤ P.triangEnvelopeIter (m * n + m + n) := by
      exact hR.trans ((monotone_triangEnvelopeIter hQ n).trans hcomp)
    have hc : c ≤ (m * n + m + n : ℕ∞) := by
      apply (generationTime_le_coe_iff P R (m * n + m + n)).2 hreach
    calc
      c + 1 ≤ (m * n + m + n : ℕ∞) + 1 := by
        simpa [add_comm] using add_le_add_right hc 1
      _ = ((m + 1 : ℕ) : ℕ∞) * ((n + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast (show m * n + m + n + 1 = (m + 1) * (n + 1) by
          rw [Nat.mul_succ, Nat.add_mul, Nat.one_mul]
          omega)
      _ = (a + 1) * (b + 1) := by rw [← hm, ← hn]; simp
  · have hPbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
    subst P
    by_cases hQ : Q.Nonempty
    · have ha : (⊥ : ObjectProperty C).generationTime Q = ⊤ :=
        generationTime_top_of_bot_left_of_nonempty_right Q hQ
      simp [ha]
    · have hQbot : Q = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot Q).mp hQ
      subst Q
      by_cases hR : R.Nonempty
      · have hb : (⊥ : ObjectProperty C).generationTime R = ⊤ :=
          generationTime_top_of_bot_left_of_nonempty_right R hR
        simp [hb]
      · have hRbot : R = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot R).mp hR
        subst R
        simp [generationTime_zero_of_bot_right]

omit [IsTriangulated C] in
private lemma nonempty_of_triangEnvelopeIter_nonempty (P : ObjectProperty C) (n : ℕ)
    (hT : (P.triangEnvelopeIter n).Nonempty) : P.Nonempty := by
  by_contra hP
  have hbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
  subst P
  simp [triangEnvelopeIter] at hT
  letI : (⊥ : ObjectProperty C).Nonempty := hT
  rcases exists_prop_of_nonempty (⊥ : ObjectProperty C) with ⟨x, hx⟩
  exact hx

omit [IsTriangulated C] in
private lemma nonempty_of_strong (Q : ObjectProperty C)
    (hQ : Q.IsStrongTriangulatedGenerator) : Q.Nonempty := by
  obtain ⟨n, hn⟩ := hQ
  apply nonempty_of_triangEnvelopeIter_nonempty Q n
  rw [hn]
  infer_instance

/-- Stacks 0FXA in the bounded form proved by composition: a strong-generating property Q
whose objects all lie in one finite stage of P makes P a strong generator. -/
theorem isStrongTriangulatedGenerator_of_strong_le_iter
    (P Q : ObjectProperty C) (k : ℕ)
    (hQ : Q.IsStrongTriangulatedGenerator) (hQP : Q ≤ P.triangEnvelopeIter k) :
    P.IsStrongTriangulatedGenerator := by
  have hQne : Q.Nonempty := nonempty_of_strong Q hQ
  obtain ⟨n, hn⟩ := hQ
  letI : P.Nonempty := nonempty_of_triangEnvelopeIter_nonempty P k (hQne.mono hQP)
  apply (isStrongTriangulatedGenerator_iff P).2
  refine ⟨k * n + k + n, top_le_iff.1 ?_⟩
  calc
    ⊤ = Q.triangEnvelopeIter n := hn.symm
    _ ≤ (P.triangEnvelopeIter k).triangEnvelopeIter n := monotone_triangEnvelopeIter hQP n
    _ ≤ P.triangEnvelopeIter (k * n + k + n) := triangEnvelopeIter_compose P k n

/-- A single strong generator and a classical generator have the same finite-generation
property. The singleton inclusion supplies the uniform finite stage required by
isStrongTriangulatedGenerator_of_strong_le_iter. -/
theorem isStrongTriangulatedGenerator_of_singleton_strong_of_isClassical
    (P : ObjectProperty C) (G : C)
    (hP : P.IsClassicalTriangulatedGenerator)
    (hG : (singleton G).IsStrongTriangulatedGenerator) :
    P.IsStrongTriangulatedGenerator := by
  have hGmem : P.triangEnvelope G := by
    rw [isClassicalTriangulatedGenerator_iff] at hP
    rw [hP]
    trivial
  obtain ⟨k, hk⟩ := (P.prop_triangEnvelope_iff G).1 hGmem
  apply isStrongTriangulatedGenerator_of_strong_le_iter P (singleton G) k hG
  exact singleton_le_iff.2 hk

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Finite Rouquier dimension makes every classical generator a strong generator. -/
theorem isStrongTriangulatedGenerator_of_classical_of_rouquierDim_ne_top
    (P : ObjectProperty C) (hP : P.IsClassicalTriangulatedGenerator)
    (hD : rouquierDim C ≠ ⊤) : P.IsStrongTriangulatedGenerator := by
  obtain ⟨G, hG⟩ := (rouquierDim_ne_top_iff_exists_strong C).mp hD
  exact ObjectProperty.isStrongTriangulatedGenerator_of_singleton_strong_of_isClassical
    P G hP hG

/-- If Rouquier dimension is finite, each classical generator has finite generation time. -/
theorem generationTime_ne_top_of_classical_of_rouquierDim_ne_top
    (P : ObjectProperty C) (hP : P.IsClassicalTriangulatedGenerator)
    (hD : rouquierDim C ≠ ⊤) : P.generationTime ⊤ ≠ ⊤ :=
  (ObjectProperty.isStrongTriangulatedGenerator_iff_generationTime_ne_top P).1
    (isStrongTriangulatedGenerator_of_classical_of_rouquierDim_ne_top P hP hD)

end CategoryTheory.Triangulated
