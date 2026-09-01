/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.IntervalCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Basic
import MathFormalContract

/-!
# The lifted linear action on slicings

A normalized shift `f` acts on a slicing by relabelling phases:

```
(f • s).P φ = s.P (f⁻¹ φ)
```

`f⁻¹` rather than `f` is what makes this a *left* action, and `mul_smul`
below is the test that pins it down — with `f` in place of `f⁻¹` the
definition still typechecks and `mul_smul` fails.

Only the `NormalizedShift` factor is involved: the matrix factor of
`G̃L⁺(2, ℝ)` acts on the central charge, not on the slicing. So the action is
defined for `NormalizedShift` and `GLTilde` inherits it through
`GLTilde.toShiftHom`.

## Why the axioms survive

The axiom with content is `shift_iff`, which needs
`f⁻¹ (φ + 1) = f⁻¹ φ + 1` — i.e. exactly
`NormalizedShift.symm_map_add_one`, here reached through the group structure
as `f⁻¹.map_add_one`.

`hn_exists` reuses the Postnikov tower untouched — `PostnikovTower` carries no
phase data, all of it lives in `HNFiltration`'s extra fields — and relabels
the factor phases by `f`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

noncomputable section

universe v u

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Relabel a slicing's phases by `f`: the objects semistable of phase `φ` in
`relabel f s` are those semistable of phase `f⁻¹ φ` in `s`. -/
def relabel (f : NormalizedShift) (s : Slicing C) : Slicing C where
  P φ := s.P (f⁻¹.toOrderIso φ)
  closedUnderIso _ := s.closedUnderIso _
  zero_mem _ := s.zero_mem _
  shift_iff φ X := by
    rw [f⁻¹.map_add_one]
    exact s.shift_iff _ X
  hom_vanishing _ _ A B h hA hB g :=
    s.hom_vanishing _ _ A B (f⁻¹.toOrderIso.lt_iff_lt.mpr h) hA hB g
  hn_exists E := by
    obtain ⟨F⟩ := s.hn_exists E
    refine ⟨{ toPostnikovTower := F.toPostnikovTower
              φ := fun j => f.toOrderIso (F.φ j)
              hφ := fun _ _ hab => f.toOrderIso.lt_iff_lt.mpr (F.hφ hab)
              semistable := fun j => ?_ }⟩
    show s.P (f⁻¹.toOrderIso (f.toOrderIso (F.φ j))) _
    rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
    exact F.semistable j

@[simp]
theorem relabel_P (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (relabel C f s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- Normalized shifts act on slicings by phase relabelling. -/
-- The `show`s are load-bearing: while the instance is still being elaborated
-- `•` stays opaque, so `relabel_P` has nothing to match against and `simp`
-- reports no progress.
instance slicingMulAction : MulAction NormalizedShift (Slicing C) where
  smul := relabel C
  one_smul s := CategoryTheory.Triangulated.Slicing.ext C (by
    funext φ
    show (relabel C 1 s).P φ = s.P φ
    simp)
  mul_smul f g s := CategoryTheory.Triangulated.Slicing.ext C (by
    funext φ
    show (relabel C (f * g) s).P φ = (relabel C f (relabel C g s)).P φ
    simp [mul_inv_rev])

@[simp]
theorem smul_slicing_P (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `G̃L⁺(2, ℝ)` acts on slicings through its phase-relabelling factor.

The matrix factor is not involved — it acts on the central charge, which is
handled by the prestability action. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "A COMPONENT of the Lemma 8.2 action, not a weaker version of it: the paper states an action on Stab(D), and says nothing about GLTilde acting on slicings alone. Neither statement implies the other, so no_claim rather than one_way.")]
instance gltildeSlicingMulAction : MulAction GLTilde (Slicing C) :=
  MulAction.compHom _ GLTilde.toShiftHom

@[simp]
theorem gltilde_smul_slicing_P (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = s.P (x.shift⁻¹.toOrderIso φ) := rfl

/-! ## Interval subcategories are reindexed, not deformed

`Slicing.intervalProp s a b` is "zero, or has an HN filtration with every
phase in `(a, b)`". Relabelling phases by `f` therefore just moves the window:
the objects lying in `(a, b)` for `f • s` are exactly those lying in
`(f⁻¹ a, f⁻¹ b)` for `s`.

The interval subcategories match up on the nose — no equivalence to chase and
no structure to transport — so the remaining obstacle is the *shape* of the
window, which is what `NormalizedShift.exists_radius` addresses.
-/

theorem relabel_intervalProp_iff (f : NormalizedShift) (s : Slicing C) (a b : ℝ)
    (E : C) :
    (relabel C f s).intervalProp C a b E
      ↔ s.intervalProp C (f⁻¹.toOrderIso a) (f⁻¹.toOrderIso b) E := by
  constructor
  · rintro (hz | ⟨F, hF⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨{ toPostnikovTower := F.toPostnikovTower
                       φ := fun i => f⁻¹.toOrderIso (F.φ i)
                       hφ := fun _ _ h => f⁻¹.toOrderIso.lt_iff_lt.mpr (F.hφ h)
                       semistable := F.semistable }, fun i => ?_⟩
      exact ⟨f⁻¹.toOrderIso.lt_iff_lt.mpr (hF i).1,
             f⁻¹.toOrderIso.lt_iff_lt.mpr (hF i).2⟩
  · rintro (hz | ⟨G, hG⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨{ toPostnikovTower := G.toPostnikovTower
                       φ := fun i => f.toOrderIso (G.φ i)
                       hφ := fun _ _ h => f.toOrderIso.lt_iff_lt.mpr (G.hφ h)
                       semistable := fun i => ?_ }, fun i => ?_⟩
      · show s.P (f⁻¹.toOrderIso (f.toOrderIso (G.φ i))) _
        rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
        exact G.semistable i
      · refine ⟨?_, ?_⟩
        · have h := f.toOrderIso.lt_iff_lt.mpr (hG i).1
          rwa [NormalizedShift.inv_apply, OrderIso.apply_symm_apply] at h
        · have h := f.toOrderIso.lt_iff_lt.mpr (hG i).2
          rwa [NormalizedShift.inv_apply, OrderIso.apply_symm_apply] at h

theorem relabel_intervalProp (f : NormalizedShift) (s : Slicing C) (a b : ℝ) :
    (relabel C f s).intervalProp C a b
      = s.intervalProp C (f⁻¹.toOrderIso a) (f⁻¹.toOrderIso b) :=
  funext fun E => propext (relabel_intervalProp_iff C f s a b E)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
