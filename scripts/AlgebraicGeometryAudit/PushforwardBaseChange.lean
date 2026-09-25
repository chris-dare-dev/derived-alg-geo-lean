/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.BaseChange

/-!
Audit and direct client for the independent open-square comparison of module
sheaf pushforward and restriction. No coherence or affine hypothesis is used.
-/

#print axioms AlgebraicGeometry.restrictSquareOpensIso
#print axioms AlgebraicGeometry.restrictSquareSections
#print axioms AlgebraicGeometry.restrictSquareSectionsInv
#print axioms AlgebraicGeometry.restrictSquareSectionsInv_restrictSquareSections
#print axioms AlgebraicGeometry.restrictSquareSections_restrictSquareSectionsInv
#print axioms AlgebraicGeometry.restrictSquareSections_smul
#print axioms AlgebraicGeometry.Scheme.Modules.presheaf_map_square_eq
#print axioms AlgebraicGeometry.restrictSquareSectionsEquiv
#print axioms AlgebraicGeometry.pushforwardRestrictIso
#print axioms AlgebraicGeometry.pushforwardRestrictNatIso
#print axioms AlgebraicGeometry.pullbackRestrictNatIso
#print axioms AlgebraicGeometry.squarePushforwardIso
#print axioms AlgebraicGeometry.pushforwardRestrictNatIso_mate
#print axioms AlgebraicGeometry.pullbackRestrictNatIso_conjugate
#print axioms AlgebraicGeometry.pullbackRestrictNatIso_mate

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

example :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (f ∣_ U) :=
  pushforwardRestrictNatIso f U

example :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  pullbackRestrictNatIso f U

example :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  squarePushforwardIso f U

example :
    mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
      (Scheme.Modules.restrictAdjunction U.ι) (pushforwardRestrictNatIso f U).hom =
        (squarePushforwardIso f U).hom :=
  pushforwardRestrictNatIso_mate f U

example :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
      (pullbackRestrictNatIso f U).inv = (squarePushforwardIso f U).hom :=
  pullbackRestrictNatIso_conjugate f U

example :
    mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (pullbackRestrictNatIso f U).inv = (pushforwardRestrictNatIso f U).hom :=
  pullbackRestrictNatIso_mate f U

example (M : X.Modules) :
    (pushforwardRestrictNatIso f U).hom.app M = (pushforwardRestrictIso f U M).hom :=
  rfl

example (M : X.Modules) (W : U.toScheme.Opens)
    (x : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, W)) :
    ((pushforwardRestrictNatIso f U).hom.app M).app W x =
      (restrictSquareSections f U M W).hom x :=
  rfl

end AlgebraicGeometry
