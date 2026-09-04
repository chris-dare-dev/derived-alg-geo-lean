/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques.Collection
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Exceptional

/-!
# Exceptional line bundles on an Enriques surface

Li--Nuer--Stellari--Zhao, arXiv:1912.04332v2, Proposition 3.5, use
`Extⁿ(L,L) ≅ Hⁿ(Y,O_Y)` and the vanishing of `H¹(Y,O_Y)` and `H²(Y,O_Y)`
to show that every line bundle on an Enriques surface is exceptional.

This file formalizes that reduction against the APIs available at the current
pin. `IsEnriquesSurface` already contains the degree-one vanishing. The
degree-two vanishing, the self-Ext/cohomology comparisons, the endomorphism
comparison, and the out-of-range Ext vanishing are supplied as explicit
`Prop`-valued data: Serre duality and the required derived Ext comparison are
not theorems in the repository yet. From those inputs, exceptionality is
proved rather than stored.

No Enriques surface, line bundle, comparison, or exceptional collection is
constructed here.

## Main definitions

* `DerivedCat` -- `Dᵇ(Coh Y)` in the Enriques namespace.
* `ExtComparison` -- the precise self-Ext comparison boundary for one line
  bundle.
* `IsotropicCollection.ExceptionalityData` -- the common degree-two
  vanishing and the ten comparison witnesses.

## Main results

* `isExceptional_of_extComparison` -- the exceptionality reduction.
* `IsotropicCollection.ExceptionalityData.bundle_isExceptional` -- every
  member of a supplied isotropic collection is exceptional.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.EnriquesSurface

open Scheme.Modules

variable {k : Type u} [Field k]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k Y]
variable {C : SmoothProperVariety.CanonicalSheafData k Y 2}
  [hY : SmoothProperVariety.IsEnriquesSurface k Y C]

/-- The bounded derived category of coherent sheaves on an Enriques surface.
This is an abbreviation only; it introduces no new category. -/
abbrev DerivedCat (Y : Scheme.{u}) [IsLocallyNoetherian Y] : Type _ :=
  SchemeBoundedCoherentDerivedCategory Y

/-- Supplied comparison data reducing exceptionality of a line bundle to
coherent cohomology of the structure sheaf.

The first field is the degree-zero comparison together with
`H⁰(Y,O_Y) = k`. The next two fields are the degree-one and degree-two
self-Ext comparisons. The last field packages negative Ext vanishing and
cohomological-dimension vanishing above degree two. These are fields because
the requisite Ext/cohomology and cohomological-dimension theorems are not
available at the current pin. -/
structure ExtComparison (L : LineBundleData Y) : Prop where
  /-- Scalar multiplication identifies `k` with the endomorphism ring of the
  bounded derived line bundle. -/
  endomorphisms :
    Function.Bijective (algebraMap k (End L.boundedDerivedObject))
  /-- The degree-one self-Ext group is the first coherent cohomology of the
  structure sheaf. -/
  ext_one : Nonempty
    ((L.boundedDerivedObject ⟶ L.boundedDerivedObject⟦(1 : ℤ)⟧) ≃+
      ((Cohomology.coherentH Y 1).obj (Scheme.structureSheafCoh Y)))
  /-- The degree-two self-Ext group is the second coherent cohomology of the
  structure sheaf. -/
  ext_two : Nonempty
    ((L.boundedDerivedObject ⟶ L.boundedDerivedObject⟦(2 : ℤ)⟧) ≃+
      ((Cohomology.coherentH Y 2).obj (Scheme.structureSheafCoh Y)))
  /-- Self-Ext vanishes in negative degrees and above the surface range. -/
  outside_surface_range : ∀ n : ℤ, n < 0 ∨ 2 < n →
    ∀ f : L.boundedDerivedObject ⟶ L.boundedDerivedObject⟦n⟧, f = 0

include C

/-- A line bundle on an Enriques surface is exceptional once the available
`H¹` vanishing, a supplied `H²` vanishing, and the explicit self-Ext
comparison boundary are assembled. -/
theorem isExceptional_of_extComparison (L : LineBundleData Y)
    (comparison : ExtComparison (k := k) L)
    (hTwo : IsZero
      ((Cohomology.coherentH Y 2).obj (Scheme.structureSheafCoh Y))) :
    IsExceptional k L.boundedDerivedObject := by
  let hEnriques : SmoothProperVariety.IsEnriquesSurface k Y C := inferInstance
  constructor
  · intro n hn f
    by_cases hOne : n = 1
    · subst n
      letI : Subsingleton
          ((Cohomology.coherentH Y 1).obj (Scheme.structureSheafCoh Y)) :=
        AddCommGrpCat.subsingleton_of_isZero hEnriques.h1_vanishing
      apply comparison.ext_one.some.injective
      exact Subsingleton.elim _ _
    by_cases hTwoDegree : n = 2
    · subst n
      letI : Subsingleton
          ((Cohomology.coherentH Y 2).obj (Scheme.structureSheafCoh Y)) :=
        AddCommGrpCat.subsingleton_of_isZero hTwo
      apply comparison.ext_two.some.injective
      exact Subsingleton.elim _ _
    exact comparison.outside_surface_range n (by omega) f
  · exact comparison.endomorphisms

namespace IsotropicCollection

variable {D : Cohomology.FiniteCohomology k Y} {S : D.LinearConnectingSystem}
variable (T : IsotropicCollection (Y := Y) (C := C) D S)

/-- The supplied cohomological input needed to prove exceptionality of all
ten line bundles in an isotropic collection. The common `H²` vanishing is
stored once; each bundle has its own self-Ext comparison. -/
structure ExceptionalityData : Prop where
  /-- `H²(Y,O_Y) = 0`, pending the Serre-duality realization described in
  `Enriques.Basic`. -/
  h_two_vanishing : IsZero
    ((Cohomology.coherentH Y 2).obj (Scheme.structureSheafCoh Y))
  /-- The self-Ext comparison for each selected line bundle. -/
  comparison : ∀ i : Fin 10, ExtComparison (k := k) (T.bundles i)

/-- Every member of an isotropic collection is exceptional from the shared
degree-two vanishing and its supplied self-Ext comparison. -/
theorem ExceptionalityData.bundle_isExceptional
    (data : T.ExceptionalityData) (i : Fin 10) :
    IsExceptional k (T.bundles i).boundedDerivedObject :=
  isExceptional_of_extComparison (C := C) (T.bundles i) (data.comparison i)
    data.h_two_vanishing

end IsotropicCollection

end AlgebraicGeometry.EnriquesSurface
