/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Opposite.Linear
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `k`-linear Yoneda functor is homological

Mathlib proves that `preadditiveYoneda.obj B : Cᵒᵖ ⥤ AddCommGrpCat` is
homological. This file proves the same for `(linearYoneda k C).obj B`, which
lands in `ModuleCat k` instead.

The distinction is not cosmetic. A categorical Euler form
`χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])` needs `Module.finrank k` of each `Hom`,
and `finrank k` is not statable in `AddCommGrpCat` — the objects carry no
`k`-action to take dimensions over (`finrank ℤ` is statable, but `ℤ`-rank is
not the dimension count `χ` needs). `preadditiveYoneda` therefore cannot feed
that construction and `linearYoneda` can.

## Why the proof is short

The argument never mentions the target category. `Triangle.yoneda_exact₂` is a
statement about morphisms in `C`, and `ShortComplex.moduleCat_exact_iff` has the
*same shape* as the `ShortComplex.ab_exact_iff` Mathlib's proof uses:

`S.Exact ↔ ∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂`.

So Mathlib's proof transplants with one lemma name changed. An earlier draft
reflected exactness along `forget₂ (ModuleCat k) Ab` instead; that works, but it
is strictly more plumbing for the same result.

## The shift sequence, and what it cost

`ShiftSequence ℤ` **is** here now (#469), so the shifted Hom-groups
`Hom(E, F⟦i⟧)` are assembled and the long exact sequence below is available.
Three Mathlib-level gaps blocked it and all three are closed:

* `Linear R Cᵒᵖ` did not exist in Mathlib. `Preadditive Cᵒᵖ` does, by
  transporting `AddCommGroup` along `opEquiv`, but there was no `k`-linear
  counterpart — and morphisms in `Cᵒᵖ` are `Opposite`-wrapped
  (`(X ⟶ Y)` is `(unop Y ⟶ unop X)ᵒᵖ`), so nothing was definitionally available.
* `ShiftedHom.opEquiv_symm_smul` and `opEquiv'_symm_smul` did not exist, though
  the additive versions did.
* The instance itself, mirroring Mathlib's `preadditiveYoneda` version with
  `LinearEquiv.toModuleIso` in place of `AddEquiv.toAddCommGrpIso`.

The first two are general-purpose and belong upstream, so they live next door
in `CategoryTheory/Triangulated/LinearOpposite.lean`, written in the
`ForMathlib` pattern this repository uses for Mathlib gaps. Only the third is
here.

## What this file still does not provide

**No Euler form here.** Having the long exact sequence is not having
`Σᵢ (-1)ⁱ dim_k Hom(E, F⟦i⟧)`: that needs each term finite-dimensional and the
sum finitely supported, which is supplied data. The form is built in
`Triangulated/GrothendieckGroup/EulerForm.lean` from this file's sequence
together with `LinearCoyoneda.lean`'s — this one gives the sequence in the
*first* variable only, and biadditivity needs both.

**The shift functors on `C` are not shown `k`-linear.** `(shiftFunctor C n).Linear k`
is a hypothesis of this file, not a consequence of `Linear k C`, and it cannot
be: additivity of a functor between `k`-linear categories does not give
`k`-linearity. It is Mathlib's own standing hypothesis wherever the two
interact — `Triangulated/Basic.lean`, `Shift/ShiftedHom.lean`,
`Shift/Linear.lean` all carry it verbatim — and Mathlib discharges it only for
concrete categories, `CochainComplex` directly and their localizations through
`Shift.linear_of_localization`. The *opposite* shift is a different matter and
is not assumed: `LinearOpposite.shiftFunctorOppositeLinear` derives
`(shiftFunctor Cᵒᵖ n).Linear k` from the hypothesis on `C`.
-/

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Pretriangulated.Opposite

variable {k : Type*} [Ring k] {C : Type*} [Category C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! Linearity of the shift, in Mathlib's spelling and at the file's top level
rather than tucked into the section that happens to need it.

It is a genuine hypothesis: additivity does not imply `k`-linearity, and nothing
here or in Mathlib derives it from `Linear k C`. `Triangulated/Basic.lean`,
`Shift/ShiftedHom.lean` and `Shift/Linear.lean` all carry the same binder. -/

variable [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- **The `k`-linear Yoneda functor is homological.**

The `ModuleCat k` counterpart of Mathlib's instance for `preadditiveYoneda`, and
the one a `k`-dimension count can use. The proof is Mathlib's, with
`ShortComplex.ab_exact_iff` replaced by `ShortComplex.moduleCat_exact_iff`; the
`k`-action plays no part, because `Triangle.yoneda_exact₂` is about morphisms in
`C`. -/
instance linearYoneda_isHomological (B : C) :
    ((linearYoneda k C).obj B).IsHomological where
  exact T hT := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x₂ : T.obj₂.unop ⟶ B) (hx₂ : T.mor₂.unop ≫ x₂ = 0)
    obtain ⟨x₃, hx₃⟩ := Triangle.yoneda_exact₂ _ (unop_distinguished T hT) x₂ hx₂
    exact ⟨x₃, hx₃.symm⟩

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- The short complex of a distinguished triangle stays exact after applying the
`k`-linear Yoneda functor. The `ModuleCat k` counterpart of
`preadditiveYoneda_map_distinguished`. -/
lemma linearYoneda_map_distinguished (T : Triangle C) (hT : T ∈ distTriang C)
    (B : C) :
    ((shortComplexOfDistTriangle T hT).op.map ((linearYoneda k C).obj B)).Exact :=
  ((linearYoneda k C).obj B).map_distinguished_op_exact T hT

section ShiftSequence

/-- **The shifted Hom-groups, assembled.**

The `ModuleCat k` counterpart of Mathlib's `ShiftSequence ℤ` instance for
`preadditiveYoneda`, and the last piece a Hom-built Euler form needs: without
it there is no sequence `i ↦ Hom(E, F⟦i⟧)` for an alternating sum to run over.

The construction is Mathlib's with two substitutions — `LinearEquiv.toModuleIso`
for `AddEquiv.toAddCommGrpIso`, and the `smul` half supplied alongside the
`map_add'` half. The `map_smul'` field is `LinearOpposite`'s
`ShiftedHom.opEquiv'_symm_smul`, which is why that file exists.

`(shiftFunctor C n).Linear k` is the one hypothesis this needs beyond the
additive version, and it is not decorative: `opEquiv'_symm_smul` needs the
shift to commute with scalars, exactly where the additive proof needs
`Additive`. -/
noncomputable instance linearYonedaShiftSequence (B : C) :
    ((linearYoneda k C).obj B).ShiftSequence ℤ where
  sequence n := (linearYoneda k C).obj (B⟦n⟧)
  isoZero := (linearYoneda k C).mapIso ((shiftFunctorZero C ℤ).app B)
  shiftIso n a a' h := NatIso.ofComponents (fun A ↦ LinearEquiv.toModuleIso
    { toEquiv := Quiver.Hom.opEquiv.trans (ShiftedHom.opEquiv' n a a' h).symm
      map_add' := fun _ _ ↦ ShiftedHom.opEquiv'_symm_add _ _ _ h
      map_smul' := fun _ _ ↦ ShiftedHom.opEquiv'_symm_smul _ _ _ h })
        (by intros; ext; apply ShiftedHom.opEquiv'_symm_comp _ _ _ h)
  shiftIso_zero a := by ext; apply ShiftedHom.opEquiv'_zero_add_symm
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext _ x
    exact ShiftedHom.opEquiv'_add_symm n m a a' a'' ha' ha'' x.op

/-! ### The long exact sequence

With `IsHomological` and `ShiftSequence ℤ` both in place, Mathlib's homology
sequence API applies verbatim — `ModuleCat k` is abelian, so nothing else is
needed. The three lemmas below are named specializations, not new content: each
is the generic lemma with the functor fixed.

They are stated for a triangle in `Cᵒᵖ` because that is where the linear Yoneda
functor's source lives. A triangle in `C` reaches them through
`(triangleOpEquivalence _).functor.obj (op T)`, exactly as Mathlib's
`preadditiveYoneda` lemmas do.

This is the sequence an alternating sum `Σᵢ (-1)ⁱ dim_k Hom(E, F⟦i⟧)` runs
over. What is still missing before that sum can be *defined* is finiteness:
`FiniteDimensional k` of each term and a bound making the sum finite. Both are
genuine supplied data at this level of generality, and neither is asserted
here. -/

/-- Exactness in the middle. -/
lemma linearYoneda_homologySequence_exact₂ (B : C) (T : Triangle Cᵒᵖ)
    (hT : T ∈ distTriang Cᵒᵖ) (n₀ : ℤ) :
    (ShortComplex.mk _ _
      (((linearYoneda k C).obj B).homologySequence_comp T hT n₀)).Exact :=
  ((linearYoneda k C).obj B).homologySequence_exact₂ T hT n₀

/-- Exactness at the connecting map's source. -/
lemma linearYoneda_homologySequence_exact₃ (B : C) (T : Triangle Cᵒᵖ)
    (hT : T ∈ distTriang Cᵒᵖ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (((linearYoneda k C).obj B).comp_homologySequenceδ T hT n₀ n₁ h)).Exact :=
  ((linearYoneda k C).obj B).homologySequence_exact₃ T hT n₀ n₁ h

/-- Exactness at the connecting map's target. -/
lemma linearYoneda_homologySequence_exact₁ (B : C) (T : Triangle Cᵒᵖ)
    (hT : T ∈ distTriang Cᵒᵖ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (((linearYoneda k C).obj B).homologySequenceδ_comp T hT n₀ n₁ h)).Exact :=
  ((linearYoneda k C).obj B).homologySequence_exact₁ T hT n₀ n₁ h

end ShiftSequence

end CategoryTheory.Triangulated
