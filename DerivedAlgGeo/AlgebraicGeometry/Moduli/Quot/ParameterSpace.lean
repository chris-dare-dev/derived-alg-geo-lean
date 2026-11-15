/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Yoneda
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic

/-!
# Represented presheaves over a base and the zero parameter space

A `RepresentedPresheafOver S` is a presheaf of types on schemes over `S`
together with a representing `S`-scheme and its Yoneda isomorphism.  Nothing
ties the presheaf to quotients of a module sheaf, so this is not a Quot
functor, and no Quot functor is claimed representable here.

At the current Mathlib pin no general Quot-scheme or Grassmannian
representability theorem is available.  The supported construction here is
the zero quotient: its functor has exactly one point over every test scheme
and is represented by the terminal object `S ⟶ S` of `Over S`.  The parameter
is finite type and its zero complex realizes the pointwise finite-type cover
`zeroPointwiseFiniteTypeCover`.

## Main definitions

* `RepresentedPresheafOver` — a presheaf on schemes over `S` with a
  representing scheme and the full Yoneda universal property;
  `RepresentedPresheafOver.universal` is its universal element.
* `FiniteTypeRepresentedPresheafOver` — a represented presheaf whose
  representing morphism is of finite type.
* `zeroQuotientProblem`, `zeroQuotientRepresentation`,
  `zeroFiniteTypeQuotientParameterSpace` — the zero quotient functor, its
  representation by the identity scheme over `S`, and the resulting finite-type
  represented presheaf.
* `zeroQuotientToRelativePerfect`, `zeroQuotientRelativePerfectModuliProblem`,
  `zeroQuotientPointwiseFiniteTypeCover` — the zero quotient mapped to the
  relative-perfect moduli fiber, problem and pointwise finite-type cover.

## Main results

* `zeroQuotient_universal_eq` — the universal element of the zero parameter
  space is the unique zero-quotient point.
* `zeroQuotient_hasPointwiseCover` — the zero Quot construction has a
  pointwise finite-type cover.

## Implementation notes

Only the zero quotient is constructed. Representability of a general Quot
functor is not claimed: a `RepresentedPresheafOver` must be supplied with its
Yoneda isomorphism, and the zero problem is the one case where that
isomorphism is built here.

## References

This file builds on `Mathlib.CategoryTheory.Yoneda`, on `ModuleQuotient` of
`Moduli/Quot/Basic.lean`, and on `relativePerfectPointwiseCoverProblem` and
`PointwiseFiniteTypeCover` of `Moduli/PerfectComplex/Boundedness.lean`.

## Tags

Quot scheme, representable functor, Yoneda, parameter space, boundedness, moduli
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open scoped ZeroObject

noncomputable section

universe u

/-- A presheaf of types on schemes over `S` with a chosen representing
`S`-scheme and the full Yoneda universal property.

Nothing ties `problem` to quotients of a module sheaf (`ModuleQuotient`), so
this is not a Quot functor; the Quot functor of flat, finitely presented
quotients is not defined here. -/
structure RepresentedPresheafOver (S : Scheme.{u}) where
  /-- The represented presheaf. -/
  problem : (SchemeBaseChange S)ᵒᵖ ⥤ Type u
  /-- The representing scheme over `S`. -/
  parameter : SchemeBaseChange S
  /-- The universal property of the representing scheme. -/
  representation : yoneda.obj parameter ≅ problem

namespace RepresentedPresheafOver

variable {S : Scheme.{u}}

/-- The universal element, obtained from the identity of the representing
scheme by Yoneda. -/
def universal (Q : RepresentedPresheafOver S) :
    Q.problem.obj (Opposite.op Q.parameter) :=
  Q.representation.hom.app (Opposite.op Q.parameter) (𝟙 Q.parameter)

end RepresentedPresheafOver

/-- A represented presheaf over `S` whose representing morphism is of finite
type.

Like `RepresentedPresheafOver`, this is unrelated to quotients of a module
sheaf: no Quot functor is claimed representable. -/
structure FiniteTypeRepresentedPresheafOver (S : Scheme.{u})
    extends RepresentedPresheafOver S where
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange parameter

/-- The functor with one supported zero quotient over every test scheme. -/
def zeroQuotientProblem (S : Scheme.{u}) :
    (SchemeBaseChange S)ᵒᵖ ⥤ Type u :=
  (Functor.const (SchemeBaseChange S)ᵒᵖ).obj PUnit

private def homToIdentityEquiv (S : Scheme.{u}) (T : SchemeBaseChange S) :
    (T ⟶ Over.mk (𝟙 S)) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Over.homMk T.hom (Category.comp_id _)
  left_inv f := by
    apply CostructuredArrow.hom_ext
    change T.hom = f.left
    exact f.w.symm.trans (Category.comp_id _)
  right_inv _ := rfl

/-- The zero quotient functor is represented by the terminal identity scheme
over `S`. -/
def zeroQuotientRepresentation (S : Scheme.{u}) :
    yoneda.obj (identityRelativePerfectBaseChange S) ≅
      zeroQuotientProblem S :=
  NatIso.ofComponents
    (fun T ↦ (homToIdentityEquiv S T.unop).toIso)
    (by
      intro T U f
      ext
      rfl)

/-- The finite-type represented presheaf of the zero quotient problem. -/
def zeroFiniteTypeQuotientParameterSpace (S : Scheme.{u}) :
    FiniteTypeRepresentedPresheafOver S where
  problem := zeroQuotientProblem S
  parameter := identityRelativePerfectBaseChange S
  representation := zeroQuotientRepresentation S
  finiteType := by
    change LocallyOfFiniteType (𝟙 S) ∧ QuasiCompact (𝟙 S)
    exact ⟨by infer_instance, by infer_instance⟩

/-- Realize the unique supported zero quotient over an actual test scheme. -/
def zeroQuotientRealization {S : Scheme.{u}} (T : SchemeBaseChange S)
    (_ : (zeroQuotientProblem S).obj (Opposite.op T)) :
    ModuleQuotient (0 : T.left.Modules) :=
  ModuleQuotient.zero T.left

/-- The universal element classified by the representing identity scheme is
the unique zero-quotient point. -/
theorem zeroQuotient_universal_eq (S : Scheme.{u}) :
    (zeroFiniteTypeQuotientParameterSpace S).toRepresentedPresheafOver.universal =
      PUnit.unit :=
  rfl

/-- The supported zero quotient maps to the actual relative-perfect moduli
fiber by the zero complex. -/
def zeroQuotientToRelativePerfect {S : Scheme.{u}}
    (T : SchemeBaseChange S) :
    (zeroQuotientProblem S).obj (Opposite.op T) →
      RelativePerfectModuliFiber T :=
  fun _ ↦ relativePerfectZeroObject T

/-- On the identity parameter scheme, the zero quotient produces the
concrete relative-perfect moduli problem `identityRelativePerfectModuliProblem`. -/
def zeroQuotientRelativePerfectModuliProblem
    (S : Scheme.{u}) :
    RelativePerfectModuliProblem S PUnit :=
  identityRelativePerfectModuliProblem (identityRelativePerfectBaseChange S)

/-- The finite-type zero Quot parameter realizes the pointwise finite-type
cover `zeroPointwiseFiniteTypeCover`. -/
def zeroQuotientPointwiseFiniteTypeCover
    (S : Scheme.{u}) :
    PointwiseFiniteTypeCover (zeroRelativePerfectModuliSelector S) :=
  zeroPointwiseFiniteTypeCover S

/-- Consequently the supported zero Quot construction inhabits the pointwise
cover predicate of `relativePerfectPointwiseCoverProblem`. -/
theorem zeroQuotient_hasPointwiseCover
    (S : Scheme.{u}) :
    (relativePerfectPointwiseCoverProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S) :=
  ⟨zeroQuotientPointwiseFiniteTypeCover S⟩

end

end AlgebraicGeometry
