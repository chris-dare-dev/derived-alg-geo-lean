/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Int.Basic

/-!
# Finite free integral lattices

This file records the algebraic notion of a `ℤ`-lattice used throughout the
repository: a finite free abelian group. It is independent of any numerical
Grothendieck group or geometric realization.

This is deliberately distinct from Mathlib's `IsZLattice`, which concerns
discrete subgroups of normed real or complex vector spaces.
-/

universe w

/-- A `ℤ`-lattice is a finite free abelian group. -/
class ZLattice (Λ : Type w) [AddCommGroup Λ] : Prop where
  /-- The lattice is finitely generated over `ℤ`. -/
  toModuleFinite : Module.Finite ℤ Λ
  /-- The lattice is free over `ℤ`. -/
  toModuleFree : Module.Free ℤ Λ

attribute [instance] ZLattice.toModuleFinite ZLattice.toModuleFree

namespace ZLattice

/-- A finitely generated torsion-free abelian group is a `ℤ`-lattice.

Both hypotheses are explicit. Freeness is the structure theorem for finite
modules over the principal ideal domain `ℤ`. -/
theorem ofFiniteTorsionFree (Λ : Type w) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.IsTorsionFree ℤ Λ] : ZLattice Λ := by
  exact
    { toModuleFinite := inferInstance
      toModuleFree := Module.free_of_finite_type_torsion_free' }

end ZLattice
