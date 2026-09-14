/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Restriction
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Finite cohomological amplitude and the bounded restriction

`SemiorthogonalDecomposition/Strong.lean` records Definition 3.7 of
arXiv:1902.08184 -- a functor has cohomological amplitude `[a, b]` when it
carries the t-cohomological window `[p, q]` into `[p + a, q + b]` -- and the
amplitude of a chosen family of component projections. This file draws the
consequence that a bounded restriction needs: a functor of finite amplitude
carries `t`-bounded objects to `t'`-bounded objects, so chosen projections of
finite amplitude preserve the bounded object property and therefore restrict
along its inclusion, and the restricted sequence is again strong.

Finiteness is recorded twice. `Functor.HasFiniteCohomologicalAmplitude`
existentially quantifies the interval, and the projection-data version
quantifies it separately at each index. The interval is deliberately not
uniform over the index: preserving boundedness never needs one interval to
work for every component at once, and a uniform demand would exclude an
infinite sequence whose component amplitudes grow.

Nothing here asserts that any projection has finite amplitude. That is a
geometric input. What is formal is only the passage from amplitude to
preservation, to restriction, and to strongness of the restricted sequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v₁ u₁ v₂ u₂ v₃ u₃ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- The bounded-below half of an amplitude bound. -/
theorem HasCohomologicalAmplitude.isGE {F : C ⥤ D} {t : TStructure C}
    {t' : TStructure D} {a b : ℤ} (hF : F.HasCohomologicalAmplitude t t' a b)
    (p q : ℤ) (X : C) (hGE : t.IsGE X p) (hLE : t.IsLE X q) :
    t'.IsGE (F.obj X) (p + a) :=
  (hF p q X hGE hLE).1

/-- The bounded-above half of an amplitude bound. -/
theorem HasCohomologicalAmplitude.isLE {F : C ⥤ D} {t : TStructure C}
    {t' : TStructure D} {a b : ℤ} (hF : F.HasCohomologicalAmplitude t t' a b)
    (p q : ℤ) (X : C) (hGE : t.IsGE X p) (hLE : t.IsLE X q) :
    t'.IsLE (F.obj X) (q + b) :=
  (hF p q X hGE hLE).2

/-- Amplitudes add along a composite. -/
theorem HasCohomologicalAmplitude.comp {F : C ⥤ D} {G : D ⥤ E}
    {t : TStructure C} {t' : TStructure D} {t'' : TStructure E}
    {a b a' b' : ℤ}
    (hF : F.HasCohomologicalAmplitude t t' a b)
    (hG : G.HasCohomologicalAmplitude t' t'' a' b') :
    (F ⋙ G).HasCohomologicalAmplitude t t'' (a + a') (b + b') := by
  intro p q X hGE hLE
  obtain ⟨hGE', hLE'⟩ := hF p q X hGE hLE
  obtain ⟨hGE'', hLE''⟩ := hG (p + a) (q + b) (F.obj X) hGE' hLE'
  constructor
  · rw [← add_assoc]
    exact hGE''
  · rw [← add_assoc]
    exact hLE''

/-- A functor with an amplitude bound carries `t`-bounded objects to
`t'`-bounded objects. The witnessing integers move, so the conclusion is
membership in the bounded locus and not a bound on a fixed window. -/
theorem HasCohomologicalAmplitude.bounded_le {F : C ⥤ D} {t : TStructure C}
    {t' : TStructure D} {a b : ℤ}
    (hF : F.HasCohomologicalAmplitude t t' a b) :
    t.bounded ≤ t'.bounded.inverseImage F := by
  intro X hX
  obtain ⟨p, hp⟩ := hX.1
  obtain ⟨q, hq⟩ := hX.2
  exact ⟨⟨p + a, hF.isGE p q X hp hq⟩, ⟨q + b, hF.isLE p q X hp hq⟩⟩

/-- A functor has finite cohomological amplitude when some interval bounds it.
The interval is not retained: every consequence drawn here is insensitive to
which one works. -/
def HasFiniteCohomologicalAmplitude (F : C ⥤ D) (t : TStructure C)
    (t' : TStructure D) : Prop :=
  ∃ a b : ℤ, F.HasCohomologicalAmplitude t t' a b

/-- A named amplitude interval is in particular a finite one. -/
theorem HasCohomologicalAmplitude.hasFinite {F : C ⥤ D} {t : TStructure C}
    {t' : TStructure D} {a b : ℤ} (hF : F.HasCohomologicalAmplitude t t' a b) :
    F.HasFiniteCohomologicalAmplitude t t' :=
  ⟨a, b, hF⟩

/-- A t-exact functor has finite cohomological amplitude. -/
theorem hasFiniteCohomologicalAmplitude_of_isTExact (F : C ⥤ D)
    (t : TStructure C) (t' : TStructure D) [F.IsTExact t t'] :
    F.HasFiniteCohomologicalAmplitude t t' :=
  (hasCohomologicalAmplitude_zero F t t').hasFinite

/-- Finite amplitude is enough to carry bounded objects to bounded objects. -/
theorem HasFiniteCohomologicalAmplitude.bounded_le {F : C ⥤ D}
    {t : TStructure C} {t' : TStructure D}
    (hF : F.HasFiniteCohomologicalAmplitude t t') :
    t.bounded ≤ t'.bounded.inverseImage F := by
  obtain ⟨_, _, hF⟩ := hF
  exact hF.bounded_le

/-- Finite amplitude is closed under composition. -/
theorem HasFiniteCohomologicalAmplitude.comp {F : C ⥤ D} {G : D ⥤ E}
    {t : TStructure C} {t' : TStructure D} {t'' : TStructure E}
    (hF : F.HasFiniteCohomologicalAmplitude t t')
    (hG : G.HasFiniteCohomologicalAmplitude t' t'') :
    (F ⋙ G).HasFiniteCohomologicalAmplitude t t'' := by
  obtain ⟨a, b, hF⟩ := hF
  obtain ⟨a', b', hG⟩ := hG
  exact ⟨a + a', b + b', hF.comp hG⟩

end CategoryTheory.Functor

namespace CategoryTheory.Triangulated.SemiorthogonalSequence.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {ι : Type w} [Preorder ι]
  {S : SemiorthogonalSequence C ι} (Q : S.RightProjectionData)

/-- Every chosen component projection has finite cohomological amplitude, by
an interval that may depend on the index. -/
def HasFiniteCohomologicalAmplitude (t : TStructure C) : Prop :=
  ∀ i, (Q.ambientProjection i).HasFiniteCohomologicalAmplitude t t

/-- A uniform amplitude interval is in particular a finite one at each
index. -/
theorem HasCohomologicalAmplitude.hasFinite {Q : S.RightProjectionData}
    {t : TStructure C} {a b : ℤ} (h : Q.HasCohomologicalAmplitude t a b) :
    Q.HasFiniteCohomologicalAmplitude t :=
  fun i ↦ (h i).hasFinite

/-- Projections of finite amplitude preserve the bounded object property. This
is the whole formal content of the bounded restriction: the obligation
`Preserves` records is discharged by an amplitude bound and by nothing else
about the projection. -/
theorem HasFiniteCohomologicalAmplitude.preserves_bounded
    {Q : S.RightProjectionData} {t : TStructure C}
    (h : Q.HasFiniteCohomologicalAmplitude t) : Q.Preserves t.bounded :=
  fun i ↦ (h i).bounded_le

/-- The chosen projections restricted to the `t`-bounded locus. -/
def HasFiniteCohomologicalAmplitude.boundedProjections
    {Q : S.RightProjectionData} {t : TStructure C}
    (h : Q.HasFiniteCohomologicalAmplitude t) :
    (S.inverseImage t.bounded.ι).RightProjectionData :=
  Q.restrict t.bounded h.preserves_bounded

/-- The bounded restriction of a sequence whose chosen projections have finite
amplitude is again strong in the sense of Definition 3.5. -/
theorem HasFiniteCohomologicalAmplitude.inverseImage_bounded_isStrong
    {Q : S.RightProjectionData} {t : TStructure C}
    (hS : S.HasTriangulatedComponents)
    (hIso : ∀ i, (S.component i).IsClosedUnderIsomorphisms)
    (h : Q.HasFiniteCohomologicalAmplitude t) :
    (S.inverseImage t.bounded.ι).IsStrong :=
  Q.inverseImage_isStrong t.bounded hS hIso h.preserves_bounded

end CategoryTheory.Triangulated.SemiorthogonalSequence.RightProjectionData
