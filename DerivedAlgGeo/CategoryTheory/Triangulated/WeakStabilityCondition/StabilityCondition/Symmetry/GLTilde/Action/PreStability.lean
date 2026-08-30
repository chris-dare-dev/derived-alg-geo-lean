/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.ComplexRepresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.PreStabilityCondition
-- `.Basic`, not just `.Defs`: `PreStabilityCondition.WithClassMap.ext` is
-- declared there, and the auto-generated structure `ext` will not do — it
-- would demand equality of the `compat'` proofs.

/-!
# The lifted linear action on prestability conditions

Both factors of `G̃L⁺(2, ℝ)` act at once:

```
(x • σ).slicing = x.shift • σ.slicing        -- phases relabelled
(x • σ).Z       = actC x.mat ∘ σ.Z           -- charge transformed
```

The whole point of the `Compatible` condition in `GLTilde` is that these two
stay in step. `compat'` demands that a semistable object of phase `φ` have its
charge on the ray `ℝ₊ · exp(i π φ)`; after acting, its phase is `φ` in the new
slicing exactly when it was `f⁻¹ φ` in the old one, and `actC_exp` says `T`
carries the old ray to the new one. The positive scalars multiply, so the
witness `m` is replaced by `m * r`.

This synchronization is precisely the role of `Compatible`.

## Not yet a stability condition

`StabilityCondition.WithClassMap` additionally carries `locallyFinite`, and
preserving it is a genuine analysis argument, not bookkeeping; the sibling
stability-action module supplies it.

Note this file does **not** need `[IsTriangulated C]`:
`PreStabilityCondition.WithClassMap` does not depend on it.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- `x = (T, f)` acting on a prestability condition: `f` relabels the slicing,
`T` transforms the central charge. -/
def actPre (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    PreStabilityCondition.WithClassMap C v :=
  PreStabilityCondition.WithClassMap.ofStrict
    (x • σ.slicing) ((actC x.mat).toAddMonoidHom.comp σ.Z) (by
    intro φ E hP hE
    -- `hP : (x • σ.slicing).P φ E` is *definitionally* `σ.slicing.P (f⁻¹ φ) E`,
    -- which is why it can be handed straight to the old `compat'`.
    obtain ⟨m, hm, hZ⟩ := σ.compatible (x.shift⁻¹.toOrderIso φ) E hP hE
    obtain ⟨r, hr, hr'⟩ := actC_exp x.compat (x.shift⁻¹.toOrderIso φ)
    have hψ : x.shift.toOrderIso (x.shift⁻¹.toOrderIso φ) = φ := by
      rw [NormalizedShift.inv_apply, OrderIso.apply_symm_apply]
    rw [hψ] at hr'
    refine ⟨m * r, mul_pos hm hr, ?_⟩
    show actC x.mat (σ.Z (v (K₀.of C E))) = _
    -- Pull the real scalar out through `actC`, apply `actC_exp`, then drop
    -- back into multiplication. Staying in `•` does not work here: the two
    -- scalar actions sit on different instance paths, so `smul_smul` will not
    -- match `m • r • z`.
    rw [hZ, ← Complex.real_smul, map_smul, hr']
    simp only [Complex.real_smul]
    push_cast
    ring)

@[simp]
theorem actPre_slicing (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (actPre C v x σ).slicing = x • σ.slicing := rfl

@[simp]
theorem actPre_Z (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (actPre C v x σ).Z a = actC x.mat (σ.Z a) := rfl

/-- `G̃L⁺(2, ℝ)` acts on prestability conditions. -/
instance preMulAction : MulAction GLTilde (PreStabilityCondition.WithClassMap C v) where
  smul := actPre C v
  one_smul σ := by
    refine PreStabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actPre C v 1 σ).slicing = σ.slicing
      rw [actPre_slicing]
      exact one_smul _ _
    · ext a
      show (actPre C v 1 σ).Z a = σ.Z a
      rw [actPre_Z]
      simp
  mul_smul x y σ := by
    refine PreStabilityCondition.WithClassMap.ext (C := C) ?_ ?_
    · show (actPre C v (x * y) σ).slicing = (actPre C v x (actPre C v y σ)).slicing
      rw [actPre_slicing, actPre_slicing, actPre_slicing]
      exact mul_smul _ _ _
    · ext a
      show (actPre C v (x * y) σ).Z a = (actPre C v x (actPre C v y σ)).Z a
      rw [actPre_Z, actPre_Z, actPre_Z, GLTilde.mul_mat, actC_mul]

@[simp]
theorem smul_pre_slicing (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

@[simp]
theorem smul_pre_Z (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
