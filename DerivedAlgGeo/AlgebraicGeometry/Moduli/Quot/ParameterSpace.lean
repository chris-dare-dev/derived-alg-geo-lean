/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Yoneda
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Boundedness
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic

/-!
# Representable quotient problems and the zero parameter space

A quotient problem is represented only when its functor of points is
isomorphic to a Yoneda functor.  This is the universal property that prevents
an arbitrary scheme from being called a Quot scheme.

At the current Mathlib pin no general Quot-scheme or Grassmannian
representability theorem is available.  The supported construction here is
the zero quotient: its functor has exactly one quotient over every test
scheme and is represented by the terminal object `S ⟶ S` of `Over S`.  The
parameter is finite type and its zero complex realizes the boundedness witness
from SF8.3.
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

/-- A quotient problem on schemes over `S`, together with a representing
scheme and the full Yoneda universal property. -/
structure RepresentableQuotientProblem (S : Scheme.{u}) where
  /-- The functor of quotient families. -/
  problem : (SchemeBaseChange S)ᵒᵖ ⥤ Type u
  /-- The representing parameter scheme over `S`. -/
  parameter : SchemeBaseChange S
  /-- The universal property of the parameter scheme. -/
  representation : yoneda.obj parameter ≅ problem

namespace RepresentableQuotientProblem

variable {S : Scheme.{u}}

/-- The universal quotient-family element, obtained from the identity of the
representing scheme by Yoneda. -/
def universal (Q : RepresentableQuotientProblem S) :
    Q.problem.obj (Opposite.op Q.parameter) :=
  Q.representation.hom.app (Opposite.op Q.parameter) (𝟙 Q.parameter)

end RepresentableQuotientProblem

/-- A representable quotient problem whose actual parameter morphism is of
finite type. -/
structure FiniteTypeQuotientParameterSpace (S : Scheme.{u})
    extends RepresentableQuotientProblem S where
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

/-- The finite-type parameter space representing the zero quotient problem. -/
def zeroFiniteTypeQuotientParameterSpace (S : Scheme.{u}) :
    FiniteTypeQuotientParameterSpace S where
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
    (zeroFiniteTypeQuotientParameterSpace S).toRepresentableQuotientProblem.universal =
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
concrete relative-perfect moduli problem from SF8.2. -/
def zeroQuotientRelativePerfectModuliProblem
    (S : Scheme.{u}) :
    RelativePerfectModuliProblem S PUnit :=
  identityRelativePerfectModuliProblem (identityRelativePerfectBaseChange S)

/-- The finite-type zero Quot parameter realizes the honest boundedness
witness from SF8.3, including geometric-point coverage. -/
def zeroQuotientFiniteTypeBoundednessWitness
    (S : Scheme.{u}) :
    FiniteTypeBoundednessWitness (zeroRelativePerfectModuliSelector S) :=
  zeroFiniteTypeBoundednessWitness S

/-- Consequently the supported zero Quot construction inhabits the SF8.3
geometric boundedness predicate. -/
theorem zeroQuotient_isGeometricallyBounded
    (S : Scheme.{u}) :
    (relativePerfectGeometricBoundednessProblem S).IsBounded
      (zeroRelativePerfectModuliSelector S) :=
  ⟨zeroQuotientFiniteTypeBoundednessWitness S⟩

end

end AlgebraicGeometry
