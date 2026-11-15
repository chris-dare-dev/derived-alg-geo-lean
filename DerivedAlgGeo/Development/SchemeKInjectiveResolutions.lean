/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.LocallySmall
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.DerivedSeam

/-!
# K-injective resolutions of module sheaves on a scheme

This compile-only probe checks that the category `X.Modules` of module sheaves on a
scheme `X` has K-injective resolutions by instance search alone, through
`CategoryTheory.Cdg.hasKInjectiveResolutions_of_isGrothendieckAbelian`, and that
`HasDerivedCategory.ofIsGrothendieckAbelian` supplies a derived category with Hom types in
the morphism universe of `X.Modules`. So the derived seam
`H⁰(D^dg X.Modules) ≌ D(X.Modules)` takes no input at all. It adds no mathematical
declarations. `DerivedAlgGeo.Development` imports this module so the
verification sweep and emitter cover the probe; the stable `DerivedAlgGeo` root does
not import it.

## Main definitions

This verification module introduces no public definitions.

## Main results

The anonymous examples check that `CategoryTheory.Cdg.HasKInjectiveResolutions X.Modules`
is found by instance search, that `D(X.Modules)` has `u`-small Hom types for any choice of
derived category, and that `CategoryTheory.Cdg.derivedSeam` elaborates for `X.Modules`
with `HasDerivedCategory.ofIsGrothendieckAbelian` as a local instance.

## Implementation notes

The probe lives under `Development/` because the stable dg subtree may not import
algebraic geometry. The instance needs `IsGrothendieckAbelian` at the morphism universe
`u` of `X.Modules`, which is Mathlib's instance for module sheaves on `X : Scheme.{u}`.
`derivedSeam` needs a derived category with Hom types in that same universe `u`, while
`HasDerivedCategory.standard` has them in `u + 1`; the local instance supplies the former.

## References

* [The Stacks project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)

## Tags

K-injective resolution, module sheaf, scheme, dg enhancement
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

variable (X : Scheme.{u})

example : Cdg.HasKInjectiveResolutions X.Modules := inferInstance

example [HasDerivedCategory X.Modules] : LocallySmall.{u} (DerivedCategory X.Modules) :=
  inferInstance

attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian in
noncomputable example : H0 (Cdg.Ddg X.Modules) ≌ DerivedCategory X.Modules :=
  Cdg.derivedSeam
