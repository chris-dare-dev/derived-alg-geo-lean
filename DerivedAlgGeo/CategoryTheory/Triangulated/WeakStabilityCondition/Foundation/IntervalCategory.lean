/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.

Portions adapted from mattrobball/BridgelandStability, revision 9e48f23
(Apache-2.0, Copyright (c) 2026 Mathlib Contributors); see LICENSE.md.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Thin interval categories and admissible subobjects

For a slicing `s`, `s.IntervalCat C a b` is the full subcategory of objects
whose Harder--Narasimhan factors have phase in `(a, b)`. An admissible
subobject is one whose inclusion is the first map of a distinguished triangle
whose quotient also lies in the same interval. This intrinsic triangulated
description is independent of any retained quasi-abelian implementation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The predicate defining the thin interval category `P((a,b))`. -/
def Slicing.intervalProp (s : Slicing C) (a b : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ F : HNFiltration C s.P E, ∀ i, a < F.φ i ∧ F.φ i < b

/-- The thin interval category `P((a,b))`. -/
abbrev Slicing.IntervalCat (s : Slicing C) (a b : ℝ) :=
  (s.intervalProp C a b).FullSubcategory

/-- The inclusion of a thin interval category into the ambient category. -/
abbrev Slicing.IntervalCat.ι (s : Slicing C) (a b : ℝ) : s.IntervalCat C a b ⥤ C :=
  (s.intervalProp C a b).ι

/-- A zero object belongs to every thin interval. -/
theorem Slicing.intervalProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E)
    (a b : ℝ) : s.intervalProp C a b E :=
  Or.inl hE

instance Slicing.intervalProp_containsZero (s : Slicing C) (a b : ℝ) :
    (s.intervalProp C a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, s.intervalProp_of_isZero C (isZero_zero C) a b⟩

/-- An admissible subobject in a thin interval is represented by a
distinguished triangle whose third vertex also lies in that interval. -/
def Slicing.IsAdmissibleSubobject (s : Slicing C) {a b : ℝ}
    {E : s.IntervalCat C a b} (A : Subobject E) : Prop :=
  ∃ (X Q : s.IntervalCat C a b) (i : X ⟶ E) (_ : Mono i) (q : E ⟶ Q)
    (_ : Subobject.mk i = A) (δ : Q.obj ⟶ X.obj⟦(1 : ℤ)⟧),
    Triangle.mk i.hom q.hom δ ∈ distTriang C

/-- The ordered type of admissible subobjects of an interval object. -/
abbrev Slicing.AdmissibleSubobject (s : Slicing C) {a b : ℝ}
    (E : s.IntervalCat C a b) :=
  {A : Subobject E // s.IsAdmissibleSubobject C A}

/-- An interval object is admissibly Artinian if descending chains of
admissible subobjects terminate. -/
def Slicing.IsAdmissiblyArtinian (s : Slicing C) {a b : ℝ}
    (E : s.IntervalCat C a b) : Prop :=
  WellFoundedLT (s.AdmissibleSubobject C E)

/-- An interval object is admissibly Noetherian if ascending chains of
admissible subobjects terminate. -/
def Slicing.IsAdmissiblyNoetherian (s : Slicing C) {a b : ℝ}
    (E : s.IntervalCat C a b) : Prop :=
  WellFoundedGT (s.AdmissibleSubobject C E)

/-- Finite length in a thin interval, expressed intrinsically through
admissible subobjects. -/
def Slicing.IsFiniteLength (s : Slicing C) {a b : ℝ}
    (E : s.IntervalCat C a b) : Prop :=
  s.IsAdmissiblyArtinian C E ∧ s.IsAdmissiblyNoetherian C E

/-- An order isomorphism restricts to an order isomorphism of subtypes when
the two predicates correspond. -/
def admissibleSubobjectOrderIso {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (e x)) : {x // p x} ≃o {y // q y} where
  toFun x := ⟨e x, (h x).1 x.2⟩
  invFun y := ⟨e.symm y, (h (e.symm y)).2 (by simpa using y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_rel_iff' := e.le_iff_le

theorem admissibleSubobjectOrderIso_wellFoundedLT_iff
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (e x)) :
    WellFoundedLT {x // p x} ↔ WellFoundedLT {y // q y} := by
  constructor
  · intro hwf
    letI : WellFoundedLT {x // p x} := hwf
    exact (admissibleSubobjectOrderIso e h).symm.toOrderEmbedding.wellFoundedLT
  · intro hwf
    letI : WellFoundedLT {y // q y} := hwf
    exact (admissibleSubobjectOrderIso e h).toOrderEmbedding.wellFoundedLT

theorem admissibleSubobjectOrderIso_wellFoundedGT_iff
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {p : α → Prop} {q : β → Prop}
    (h : ∀ x, p x ↔ q (e x)) :
    WellFoundedGT {x // p x} ↔ WellFoundedGT {y // q y} := by
  rw [← wellFoundedLT_dual_iff, ← wellFoundedLT_dual_iff]
  constructor
  · intro hwf
    letI : WellFoundedLT {x // p x}ᵒᵈ := hwf
    exact ((admissibleSubobjectOrderIso e h).symm.dual).toOrderEmbedding.wellFoundedLT
  · intro hwf
    letI : WellFoundedLT {y // q y}ᵒᵈ := hwf
    exact ((admissibleSubobjectOrderIso e h).dual).toOrderEmbedding.wellFoundedLT

end CategoryTheory.Triangulated
