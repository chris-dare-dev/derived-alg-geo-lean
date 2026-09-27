/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Generators

/-! # Composition of triangulated envelope stages

This file extends Mathlib's existing `CategoryTheory.ObjectProperty.triangEnvelopeIter` tower.
It proves a fixed-point property for its iterates, a composition law, transfer through an
intermediate property, and the bounded object-property form of Stacks 0FXA.

## Main definitions

This file introduces no definitions. It reuses Mathlib's
`CategoryTheory.ObjectProperty.triangEnvelopeIter`,
`CategoryTheory.ObjectProperty.extensionProduct`,
`CategoryTheory.ObjectProperty.IsStrongTriangulatedGenerator`, and
`CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator`.

## Main results

* `CategoryTheory.ObjectProperty.triangEnvelopeIter_zero_le`: each iterate is fixed by stage zero.
* `CategoryTheory.ObjectProperty.triangEnvelopeIter_compose`: composes two finite stages.
* `CategoryTheory.ObjectProperty.le_triangEnvelopeIter_of_le_triangEnvelopeIter`: transfers a
  bound through an intermediate property.
* `CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_of_strong_le_iter`: bounded
  strong generation implies strong generation.
* `CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_of_isClassical_of_singleton_strong`:
  a classical generator containing a strong singleton is strong.

## Implementation notes

The product-closure proof uses products of retracts and the product of two distinguished triangles.
It keeps the existing closure operations and uses
`CategoryTheory.ObjectProperty.triangEnvelopeIter_succ`, so the fixed-point lemma needs no
triangulated-category hypothesis. The empty property has empty iterates; the
nonempty branch supplies the zero object required by the finite-product closure argument.

## References

* The Stacks Project, Section 13.36, Lemma 13.36.6,
  [tag 0FXA](https://stacks.math.columbia.edu/tag/0FXA).
* `Mathlib.CategoryTheory.Triangulated.Generators`
* `Mathlib.CategoryTheory.Triangulated.Subcategory`

## Tags

triangulated category, envelope composition, strong generator, Stacks 0FXA
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
    (n : ℕ) :
    (P.triangEnvelopeIter n).IsClosedUnderBinaryProducts := by
  induction n with
  | zero =>
    rw [triangEnvelopeIter_zero]
    letI : ((P.shiftClosure ℤ).binaryProductsClosure).IsClosedUnderBinaryProducts := by
      infer_instance
    exact retractClosure_isClosedUnderBinaryProducts _
  | succ n ih =>
    rw [triangEnvelopeIter_succ P n]
    letI : (P.triangEnvelopeIter n).IsClosedUnderBinaryProducts := ih
    letI : ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure).IsClosedUnderBinaryProducts :=
      retractClosure_isClosedUnderBinaryProducts _
    letI : (extensionProduct ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure)
        (P.triangEnvelopeIter n)).IsClosedUnderBinaryProducts :=
      extensionProduct_isClosedUnderBinaryProducts _ _
    exact retractClosure_isClosedUnderBinaryProducts _

private lemma triangEnvelopeIter_bot_of_not_nonempty (P : ObjectProperty C) (n : ℕ)
    (hP : ¬ P.Nonempty) : P.triangEnvelopeIter n = ⊥ := by
  have hbot : P = ⊥ := (ObjectProperty.not_nonempty_iff_eq_bot P).mp hP
  subst P
  simp [triangEnvelopeIter]


/-- The zeroth envelope of an iterated envelope is contained in that stage. For a
nonempty generator property its iterates contain zero; an empty property has empty iterates. -/
theorem triangEnvelopeIter_zero_le (P : ObjectProperty C) (n : ℕ) :
    (P.triangEnvelopeIter n).triangEnvelopeIter 0 ≤ P.triangEnvelopeIter n := by
  by_cases hP : P.Nonempty
  · letI := hP
    rw [triangEnvelopeIter_zero]
    let E := P.triangEnvelopeIter n
    letI : E.IsClosedUnderBinaryProducts := triangEnvelopeIter_isClosedUnderBinaryProducts P n
    letI : E.ContainsZero := by
      dsimp [E, triangEnvelopeIter]
      infer_instance
    rw [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure_le_iff]
  · rw [triangEnvelopeIter_bot_of_not_nonempty P n hP]
    simp [triangEnvelopeIter]

variable [IsTriangulated C]

/-- Composition of two finite generation stages has the multiplicative bound
m * n + m + n. In Rouquier's indexing, where stage n is ⟨P⟩_(n+1), this is the
composition law ⟨⟨P⟩_a⟩_b ⊆ ⟨P⟩_(a*b). -/
theorem triangEnvelopeIter_compose (P : ObjectProperty C) (m n : ℕ) :
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

/-- Monotonicity replaces the intermediate property by the `P`-stage at `m`; the composition
lemma then gives the stated bound. -/
theorem le_triangEnvelopeIter_of_le_triangEnvelopeIter
    {P Q R : ObjectProperty C} {m n : ℕ}
    (hQP : Q ≤ P.triangEnvelopeIter m) (hRQ : R ≤ Q.triangEnvelopeIter n) :
    R ≤ P.triangEnvelopeIter (m * n + m + n) := by
  calc
    R ≤ Q.triangEnvelopeIter n := hRQ
    _ ≤ (P.triangEnvelopeIter m).triangEnvelopeIter n := monotone_triangEnvelopeIter hQP n
    _ ≤ P.triangEnvelopeIter (m * n + m + n) := triangEnvelopeIter_compose P m n

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
private lemma nonempty_of_isStrongTriangulatedGenerator (Q : ObjectProperty C)
    (hQ : Q.IsStrongTriangulatedGenerator) : Q.Nonempty := by
  obtain ⟨n, hn⟩ := hQ
  apply nonempty_of_triangEnvelopeIter_nonempty Q n
  rw [hn]
  infer_instance

/-- A uniformly bounded stage reduces strong generation to the composition lemma. The pointwise
condition `Q ≤ CategoryTheory.ObjectProperty.triangEnvelope P` does not provide such a `k`: the
stage may vary with the object of `Q`, so this argument does not establish the unrestricted
object-property analogue. -/
theorem isStrongTriangulatedGenerator_of_strong_le_iter
    (P Q : ObjectProperty C) (k : ℕ)
    (hQ : Q.IsStrongTriangulatedGenerator) (hQP : Q ≤ P.triangEnvelopeIter k) :
    P.IsStrongTriangulatedGenerator := by
  have hQne : Q.Nonempty := nonempty_of_isStrongTriangulatedGenerator Q hQ
  obtain ⟨n, hn⟩ := hQ
  letI : P.Nonempty := nonempty_of_triangEnvelopeIter_nonempty P k (hQne.mono hQP)
  apply (isStrongTriangulatedGenerator_iff P).2
  refine ⟨k * n + k + n, top_le_iff.1 ?_⟩
  calc
    ⊤ = Q.triangEnvelopeIter n := hn.symm
    _ ≤ (P.triangEnvelopeIter k).triangEnvelopeIter n := monotone_triangEnvelopeIter hQP n
    _ ≤ P.triangEnvelopeIter (k * n + k + n) := triangEnvelopeIter_compose P k n

/-- The classical property places the singleton in one finite stage, so the bounded
strong-generation theorem applies. -/
theorem isStrongTriangulatedGenerator_of_isClassical_of_singleton_strong
    (P : ObjectProperty C) (G : C)
    (hP : P.IsClassicalTriangulatedGenerator)
    (hG : (singleton G).IsStrongTriangulatedGenerator) :
    P.IsStrongTriangulatedGenerator := by
  have hGmem : P.triangEnvelope G := by
    rw [isClassicalTriangulatedGenerator_iff] at hP
    rw [hP]
    trivial
  obtain ⟨k, hk⟩ := (P.prop_triangEnvelope_iff G).1 hGmem
  apply CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_of_strong_le_iter
    P (singleton G) k hG
  exact singleton_le_iff.2 hk

end CategoryTheory.ObjectProperty
