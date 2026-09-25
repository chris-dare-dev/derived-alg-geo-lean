/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Linear
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors

/-!
# Denominator scalars on relative bounded-coherent pullback

Let `X` be any scheme over `Spec R`, with no affineness requirement on `X` or
its fibre product with `Spec A`. When `A` localizes `R`, a denominator acts
invertibly on the target of a bounded-coherent derived pullback. The action
is the explicit affine-base action on bounded-coherent Dqc, installed only in
the theorem's scope. Bounded-coherent preservation remains an input.

This is the denominator-isomorphism premise of the categorical fixed-target
arrow mechanism. It does not prove linearity of derived pullback, localization
of Homs, coherent object descent, or arrow extension.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

/-- The scheme `Spec A` over `Spec R` for an `R`-algebra `A`. This is an
abbreviation of the existing `Over` object, not a new base-change carrier. -/
abbrev affineAlgebraBaseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] :
    SchemeBaseChange (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- Localized denominators act invertibly on the image of relative
bounded-coherent pullback. The total space `X ×_Spec R Spec A` may be
non-affine. The scalar action is the one induced by the second projection
to `Spec A`, not an arbitrary `R`-module instance. -/
theorem boundedFunctor_isIso_smul_denominator
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : SchemeBaseChange (Spec (CommRingCat.of R)))
    (pull : DqcLeftDerivedPullback
      (baseChangeMap X
        (toIdentityBaseChange (affineAlgebraBaseChange (R := R) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent)
    (s : M)
    (E : Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ identityBaseChange (Spec (CommRingCat.of R))).left) :
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
        (X ⨯ affineAlgebraBaseChange (R := R) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
        (baseChangeSnd X (affineAlgebraBaseChange (R := R) (A := A))).left
    IsIso ((s : R) • 𝟙 ((pull.boundedFunctor hBounded).obj E)) := by
  exact Dqc.isIso_smul_id_of_isLocalization M
    (baseChangeSnd X (affineAlgebraBaseChange (R := R) (A := A))).left
    s ((pull.boundedFunctor hBounded).obj E)

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
