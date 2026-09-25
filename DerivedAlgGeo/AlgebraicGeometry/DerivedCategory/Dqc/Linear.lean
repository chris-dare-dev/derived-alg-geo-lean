/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import Mathlib.Algebra.Module.RingHom
import Mathlib.RingTheory.Localization.Basic

/-!
# Affine-base scalars on intrinsic bounded-coherent Dqc

A map `Y ⟶ Spec A` acts on module sheaves through global sections of `Y`.
Restriction along `R → A` gives an `R`-linear structure on the intrinsic
bounded-coherent Dqc category of `Y`. It is returned as a value, not installed
as an instance: a category can carry several base-ring actions.

For a localization `R → A`, every localized denominator acts invertibly on
every object. This uses no affineness of `Y`, object descent, or Hom localization.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w v t

namespace AlgebraicGeometry.DerivedCategory.Dqc

@[reducible] private def restrictLinear
    {R : Type u} [CommRing R] {B : Type w} [CommRing B]
    (φ : R →+* B) (C : Type t) [Category.{v} C] [Preadditive C]
    [Linear B C] : Linear R C where
  homModule X Y := Module.compHom (X ⟶ Y) φ
  smul_comp X Y Z r f g := by
    letI : Module R (X ⟶ Y) := Module.compHom (X ⟶ Y) φ
    letI : Module R (X ⟶ Z) := Module.compHom (X ⟶ Z) φ
    change ((φ r) • f) ≫ g = (φ r) • (f ≫ g)
    exact Linear.smul_comp X Y Z (φ r) f g
  comp_smul X Y Z f r g := by
    letI : Module R (Y ⟶ Z) := Module.compHom (Y ⟶ Z) φ
    letI : Module R (X ⟶ Z) := Module.compHom (X ⟶ Z) φ
    change f ≫ ((φ r) • g) = (φ r) • (f ≫ g)
    exact Linear.comp_smul X Y Z f (φ r) g

private def affineBaseToGlobal
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) : R →+* Γ(Y, ⊤) :=
  p.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp φ)

/-- The canonical `R`-action on bounded-coherent Dqc over an affine base,
obtained from `R → A → Γ(Y, 𝒪_Y)`. Use it with `letI`; it is not a global
instance. -/
@[reducible] def boundedCoherentLinearOfAffineMap
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A)) :
    Linear R (SchemeBoundedCoherentDqcCategory Y) :=
  restrictLinear (affineBaseToGlobal φ p) _

/-- The chosen `R`-action is multiplication by the pulled-back global
section. This identifies the action rather than merely asserting its existence. -/
theorem boundedCoherentLinearOfAffineMap_smul
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of A))
    {E F : SchemeBoundedCoherentDqcCategory Y}
    (r : R) (g : E ⟶ F) :
    letI : Linear R (SchemeBoundedCoherentDqcCategory Y) :=
      boundedCoherentLinearOfAffineMap φ p
    r • g = (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ r))) • g :=
  rfl

/-- A denominator of `R → A` acts by an isomorphism on any bounded-coherent
Dqc object over any scheme `Y → Spec A`, including a non-affine `Y`. -/
theorem isIso_smul_id_of_isLocalization
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
    (s : M) (E : SchemeBoundedCoherentDqcCategory Y) :
    letI : Linear R (SchemeBoundedCoherentDqcCategory Y) :=
      boundedCoherentLinearOfAffineMap (algebraMap R A) p
    IsIso ((s : R) • 𝟙 E) := by
  letI : Linear R (SchemeBoundedCoherentDqcCategory Y) :=
    boundedCoherentLinearOfAffineMap (algebraMap R A) p
  have huA : IsUnit ((algebraMap R A) (s : R)) := IsLocalization.map_units A s
  have huΓ : IsUnit ((affineBaseToGlobal (algebraMap R A) p) (s : R)) := by
    dsimp [affineBaseToGlobal]
    exact (huA.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map p.appTop.hom
  have huEnd : IsUnit ((affineBaseToGlobal (algebraMap R A) p) (s : R) •
      (1 : End E)) := by
    convert huΓ.map (algebraMap Γ(Y, (⊤ : Y.Opens)) (End E)) using 1
    simp [Algebra.algebraMap_eq_smul_one]
  change IsIso (((affineBaseToGlobal (algebraMap R A) p) (s : R)) • 𝟙 E)
  exact (isUnit_iff_isIso _).mp huEnd

end AlgebraicGeometry.DerivedCategory.Dqc
