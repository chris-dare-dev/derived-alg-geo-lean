/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.LineBundleExt
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.RestrictedTwistPresentation
import DerivedAlgGeo.AlgebraicGeometry.Divisors.LineBundleDual

/-!
# Ext-finiteness from restricted projective twists

The restriction of an ambient projective-space twist was already known to be intrinsically
invertible.  `LineBundleData.ofIsInvertible` upgrades that theorem to the explicit inverse data
consumed by the line-bundle Ext/cohomology comparison.  Consequently Ext in `X.Modules` from a
restricted twist to a coherent target is finite-dimensional in every degree and has finite
finrank support.

This file does not compare Ext in `X.Modules` with Ext in `Coh X`.  It only discharges the
restricted-twist finiteness premise in the coherent-source dévissage.
-/

universe u

open CategoryTheory Abelian
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePresentation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.hasExt_of_hasDerivedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

/-- The restriction of the degree-`d` ambient projective twist, packaged with its canonical
sheafified-dual tensor inverse. -/
noncomputable def restrictedTwistLineBundleData
    (P : ProjectivePresentation k X) (d : ℤ) : Scheme.Modules.LineBundleData X := by
  letI := P.restrictedTwist_isInvertible d
  exact Scheme.Modules.LineBundleData.ofIsInvertible
    ((Coh.ι X).obj (P.restrictedTwist d))

@[simp]
theorem restrictedTwistLineBundleData_line
    (P : ProjectivePresentation k X) (d : ℤ) :
    (P.restrictedTwistLineBundleData d).line =
      (Coh.ι X).obj (P.restrictedTwist d) :=
  rfl

/-- Ambient Ext from a restricted projective twist to a coherent sheaf is finite-dimensional
in every nonnegative degree. -/
theorem module_finite_restrictedTwistExt
    (P : ProjectivePresentation k X) [Nontrivial P.index]
    (d : ℤ) (G : Coh X) (n : ℕ) :
    Module.Finite k
      (Ext.{u + 1} ((Coh.ι X).obj (P.restrictedTwist d)) ((Coh.ι X).obj G) n) := by
  letI hExtStandard : HasExt.{u + 1} X.Modules := HasExt.standard X.Modules
  change Module.Finite k
    (Ext.{u + 1} (P.restrictedTwistLineBundleData d).line ((Coh.ι X).obj G) n)
  exact P.module_finite_lineBundleExt (P.restrictedTwistLineBundleData d)
    ((Coh.ι X).obj G) G.property n

variable [IsVariety k X]

/-- Ambient Ext from a restricted twist vanishes above the cohomological bound of the coherent
inverse twist. -/
theorem restrictedTwistExt_subsingleton_of_bound_lt
    (P : ProjectivePresentation k X) [Nontrivial P.index]
    (d : ℤ) (G : Coh X) (n : ℕ)
    (hn : (P.finiteCohomology (k := k)).bound
      ⟨Scheme.Modules.tensorObj (P.restrictedTwistLineBundleData d).inverse
          ((Coh.ι X).obj G),
        Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
          (P.restrictedTwistLineBundleData d).inverse ((Coh.ι X).obj G) G.property⟩ < n) :
    Subsingleton
      (Ext.{u + 1} ((Coh.ι X).obj (P.restrictedTwist d)) ((Coh.ι X).obj G) n) := by
  simpa only [restrictedTwistLineBundleData_line] using
    P.lineBundleExt_subsingleton_of_bound_lt (P.restrictedTwistLineBundleData d)
      ((Coh.ι X).obj G) G.property n hn

/-- Only finitely many ambient Ext degrees from a restricted projective twist to a coherent
target have nonzero finrank. -/
theorem restrictedTwistExt_finrankSupport_finite
    (P : ProjectivePresentation k X) [Nontrivial P.index]
    (d : ℤ) (G : Coh X) :
    (Function.support fun n : ℕ ↦
      (Module.finrank k
        (Ext.{u + 1} ((Coh.ι X).obj (P.restrictedTwist d))
          ((Coh.ι X).obj G) n) : ℤ)).Finite := by
  letI hExtStandard : HasExt.{u + 1} X.Modules := HasExt.standard X.Modules
  change (Function.support fun n : ℕ ↦
    (Module.finrank k
      (Ext.{u + 1} (P.restrictedTwistLineBundleData d).line
        ((Coh.ι X).obj G) n) : ℤ)).Finite
  exact P.lineBundleExt_finrankSupport_finite (P.restrictedTwistLineBundleData d)
    ((Coh.ι X).obj G) G.property

end AlgebraicGeometry.ProjectivePresentation
