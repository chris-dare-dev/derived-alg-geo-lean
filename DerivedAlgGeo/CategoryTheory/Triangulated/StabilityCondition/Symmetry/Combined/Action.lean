/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action.Stability
import Mathlib.Algebra.Group.Action.Prod

/-!
# The combined symmetry action

The two halves of Bridgeland's section 8 action commute.  `GLTilde` changes
phases and postcomposes the central charge by a real-linear automorphism of
`ℂ`; `AutPairQuot v` changes objects and precomposes the charge by an
automorphism of the class lattice.  These operations are independent:

* phase relabelling commutes with transport of a slicing along an
  autoequivalence;
* postcomposition on `ℂ` commutes with precomposition on `Λ`.

This gives both the `SMulCommClass` recording that independence and the
product action

```
MulAction (GLTilde × AutPairQuot v)
  (StabilityCondition.WithClassMap C v).
```
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Relabelling phases commutes with transporting a slicing along an
autoequivalence. -/
theorem relabel_mapEquiv (x : GLTilde) (Φ : TriEquiv C) (s : Slicing C) :
    x • s.mapEquiv Φ.e = (x • s).mapEquiv Φ.e := by
  refine Slicing.ext C ?_
  funext φ X
  rfl

variable [IsTriangulated C]

/-- A concrete compatible autoequivalence and `GLTilde` commute on stability
conditions.  Quotient descent is handled below. -/
theorem gltilde_autPair_smul_comm (x : GLTilde) (a : AutPair v)
    (σ : StabilityCondition.WithClassMap C v) :
    x • a.act σ = a.act (x • σ) := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · rw [smul_stab_slicing, AutPair.act_slicing, AutPair.act_slicing,
      smul_stab_slicing]
    exact relabel_mapEquiv x a.Φ σ.slicing
  · ext y
    rw [smul_stab_Z, AutPair.act_Z, AutPair.act_Z, smul_stab_Z]

/-- The two section 8 actions commute after quotienting the autoequivalence
component by natural isomorphism. -/
noncomputable instance smulCommClassGLTildeAutPairQuot :
    SMulCommClass GLTilde (AutPairQuot v)
      (StabilityCondition.WithClassMap C v) where
  smul_comm x q σ := by
    induction q using _root_.Quotient.inductionOn with
    | _ a => exact gltilde_autPair_smul_comm x a σ

/-- **The combined section 8 symmetry action.**

The product acts by the autoequivalence first and `GLTilde` second.  The
commutation theorem above makes this a genuine action of the direct product. -/
noncomputable instance combinedMulAction :
    MulAction (GLTilde × AutPairQuot v)
      (StabilityCondition.WithClassMap C v) :=
  MulAction.prodOfSMulCommClass GLTilde (AutPairQuot v)
    (StabilityCondition.WithClassMap C v)

@[simp]
theorem prod_mk_smul_slicing (x : GLTilde) (a : AutPair v)
    (σ : StabilityCondition.WithClassMap C v) :
    ((x, AutPairQuot.mk a) • σ).slicing =
      x • CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing a.Φ.e := rfl

@[simp]
theorem prod_mk_smul_Z (x : GLTilde) (a : AutPair v)
    (σ : StabilityCondition.WithClassMap C v) (y : Λ) :
    ((x, AutPairQuot.mk a) • σ).Z y = actC x.mat (σ.Z (a.lam y)) := rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
