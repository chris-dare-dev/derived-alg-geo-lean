import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Action
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # SF11 pushforward top-section scalar audit and direct clients -/

open CategoryTheory AlgebraicGeometry

universe u

#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj_top
#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_smul_appTop

-- Only the owner leaf is needed for the theorem; the second import supplies
-- `IsAffineHom` solely to test the caller with its negation.
example {Z Y : Scheme.{u}} (f : Z ⟶ Y) (M : Z.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M, (⊤ : Y.Opens)) =
      Γ(M, (⊤ : Z.Opens)) :=
  Scheme.Modules.pushforward_obj_obj_top f M

example {Z Y : Scheme.{u}} (f : Z ⟶ Y) (_hNonaffine : ¬ IsAffineHom f)
    (M : Z.Modules) (a : Γ(Y, ⊤))
    (m : Γ((Scheme.Modules.pushforward f).obj M, ⊤)) :
    a • m = f.appTop.hom a • (show Γ(M, ⊤) from m) :=
  Scheme.Modules.pushforward_smul_appTop f M a m
