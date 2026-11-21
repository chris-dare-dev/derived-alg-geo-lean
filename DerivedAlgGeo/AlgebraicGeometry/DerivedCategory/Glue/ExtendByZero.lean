/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpenImmersionPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.ExtensionByZero

/-!
# Derived restriction to an open and derived extension by zero

For an open immersion `f : X ⟶ Y` of schemes, restriction `f^*` and extension by zero `f_!` are
exact functors between the abelian categories of module sheaves, so they act on the derived
categories of all module sheaves. Derived restriction is the exact derived pullback of
`Families.ExactPullback`, and `f_!` and `f^*` are adjoint there.

## Main definitions

* `AlgebraicGeometry.Scheme.derivedRestrict`: derived restriction to an open immersion, an
  abbreviation of the exact derived pullback.
* `AlgebraicGeometry.Scheme.derivedExtendByZero`: derived extension by zero, induced by the exact
  functor `Scheme.Modules.extendByZero`.
* `AlgebraicGeometry.Scheme.derivedExtendByZeroAdjunction`: `f_! ⊣ f^*` on derived categories
  (Stacks Tag 08BT).
* `AlgebraicGeometry.Scheme.derivedRestrictComp`, `derivedRestrictCongr` and
  `derivedExtendComp`: restriction and extension by zero along a composite of open immersions.
* `AlgebraicGeometry.Scheme.derivedBaseChange`: `u^* v_! ≅ kU_! kV^*` for a pullback square of
  open immersions.

## Main results

* `AlgebraicGeometry.Scheme.isIso_restrict_counit`: restriction of the counit of
  `f_! ⊣ f^*` is invertible.
* `AlgebraicGeometry.Scheme.isIso_restrict_map_extend_counit`: for a pullback square of open
  immersions, restriction to `U` of `v_!` applied to the counit of `kV_! ⊣ kV^*` is invertible.

## Implementation notes

The adjunction is `Adjunction.mapDerivedCategory` applied to the module-level adjunction of
`Scheme.Modules.extendByZeroPullbackAdjunction`; the unit of the derived adjunction is invertible
because the unit of the module-level one is. The composition isomorphism for extension by zero is
not constructed from a base change: it is the uniqueness of left adjoints, applied to the
composite of the adjunctions along the factors and the composition isomorphism of restriction.

## References

* Stacks Project, Tag 08BT.

## Tags

derived category, extension by zero, open immersion, base change
-/

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits Pretriangulated
open AlgebraicGeometry.DerivedCategory AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

noncomputable section

variable {Y : Scheme.{u}}

/-- An open immersion `f : X ⟶ Y`, as a morphism of schemes over `Y` into `Y` itself. -/
abbrev restrictOver {X : Scheme.{u}} (f : X ⟶ Y) : Over.mk f ⟶ Over.mk (𝟙 Y) :=
  Over.homMk f (Category.comp_id f)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : IsOpenImmersion (restrictOver f).left :=
  inferInstanceAs (IsOpenImmersion f)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Modules.pullback f) :=
  openImmersionModulePullback_preservesFiniteLimits (restrictOver f)

/-- Derived restriction to an open immersion, the exact derived pullback along it. -/
abbrev derivedRestrict {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SchemeDerivedCategory Y ⥤ SchemeDerivedCategory X :=
  derivedPullback (restrictOver f)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : (derivedRestrict f).CommShift ℤ :=
  inferInstanceAs ((derivedPullback (restrictOver f)).CommShift ℤ)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : (derivedRestrict f).IsTriangulated :=
  inferInstanceAs ((derivedPullback (restrictOver f)).IsTriangulated)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : (derivedRestrict f).Additive :=
  inferInstanceAs ((Modules.pullback f).mapDerivedCategory.Additive)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesBinaryBiproducts (derivedRestrict f) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Derived extension by zero along an open immersion, induced by the exact functor
`Scheme.Modules.extendByZero`. -/
def derivedExtendByZero {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SchemeDerivedCategory X ⥤ SchemeDerivedCategory Y :=
  (Modules.extendByZero f).mapDerivedCategory

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : (derivedExtendByZero f).CommShift ℤ :=
  inferInstanceAs ((Modules.extendByZero f).mapDerivedCategory.CommShift ℤ)

instance {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (derivedExtendByZero f).IsTriangulated :=
  inferInstanceAs ((Modules.extendByZero f).mapDerivedCategory.IsTriangulated)

/-- Derived extension by zero is left adjoint to derived restriction (Stacks Tag 08BT). -/
def derivedExtendByZeroAdjunction {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    derivedExtendByZero f ⊣ derivedRestrict f :=
  Adjunction.mapDerivedCategory (Modules.extendByZeroPullbackAdjunction f)

instance derivedExtendByZeroAdjunction_unit_isIso {X : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : IsIso (derivedExtendByZeroAdjunction f).unit :=
  Adjunction.isIso_unit_mapDerivedCategory (Modules.extendByZeroPullbackAdjunction f)

/-- Restriction of the counit of `f_! ⊣ f^*` is invertible: restriction after extension by zero
is the identity. -/
instance isIso_restrict_counit {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (E : SchemeDerivedCategory Y) :
    IsIso ((derivedRestrict f).map ((derivedExtendByZeroAdjunction f).counit.app E)) := by
  have h := (derivedExtendByZeroAdjunction f).right_triangle_components E
  have : IsIso ((derivedExtendByZeroAdjunction f).unit.app ((derivedRestrict f).obj E) ≫
      (derivedRestrict f).map ((derivedExtendByZeroAdjunction f).counit.app E)) := by
    rw [h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_left ((derivedExtendByZeroAdjunction f).unit.app _) _

/-- Restriction along `f` after restriction along `g` is restriction along `g ≫ f`. -/
def derivedRestrictComp {A B C : Scheme.{u}} (k : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion k] [IsOpenImmersion f] :
    derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict (k ≫ f) :=
  Functor.mapDerivedCategoryCompIsoOfIso (Modules.pullbackComp k f)

/-- Derived restriction along equal open immersions is isomorphic. -/
def derivedRestrictCongr {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] : derivedRestrict f ≅ derivedRestrict g := by
  subst h
  exact Iso.refl _

/-- Extension by zero along `k ≫ f` is extension by zero along `k` followed by extension by zero
along `f`, given the composition isomorphism of restriction. -/
def derivedExtendComp {A B C : Scheme.{u}} {k : A ⟶ B} {f : B ⟶ C} {g : A ⟶ C}
    [IsOpenImmersion k] [IsOpenImmersion f] [IsOpenImmersion g]
    (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g) :
    derivedExtendByZero g ≅ derivedExtendByZero k ⋙ derivedExtendByZero f :=
  Adjunction.leftAdjointUniq (derivedExtendByZeroAdjunction g)
    (((derivedExtendByZeroAdjunction k).comp (derivedExtendByZeroAdjunction f)).ofNatIsoRight c)

section Square

variable {W U V : Scheme.{u}} {u : U ⟶ Y} {v : V ⟶ Y} {kU : W ⟶ U} {kV : W ⟶ V}
  [IsOpenImmersion u] [IsOpenImmersion v] [IsOpenImmersion kU] [IsOpenImmersion kV]

/-- Derived base change for a pullback square of open immersions: `u^* v_! ≅ kU_! kV^*`. -/
def derivedBaseChange (hP : IsPullback kU kV u v) :
    derivedExtendByZero v ⋙ derivedRestrict u ≅ derivedRestrict kV ⋙ derivedExtendByZero kU :=
  haveI : PreservesFiniteLimits (Modules.extendByZero v ⋙ Modules.pullback u) :=
    comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (Modules.extendByZero v ⋙ Modules.pullback u) :=
    comp_preservesFiniteColimits _ _
  haveI : (Modules.extendByZero v ⋙ Modules.pullback u).Additive := inferInstance
  haveI : PreservesFiniteLimits (Modules.pullback kV ⋙ Modules.extendByZero kU) :=
    comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (Modules.pullback kV ⋙ Modules.extendByZero kU) :=
    comp_preservesFiniteColimits _ _
  haveI : (Modules.pullback kV ⋙ Modules.extendByZero kU).Additive := inferInstance
  Functor.mapDerivedCategoryCompIsoOfIso
      (Iso.refl (Modules.extendByZero v ⋙ Modules.pullback u)) ≪≫
    NatIso.mapDerivedCategory (Modules.extendByZeroCompPullbackIsoOfIsPullback v u kU kV hP) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfIso
      (Iso.refl (Modules.pullback kV ⋙ Modules.extendByZero kU))).symm

/-- In a pullback square of open immersions, restriction to `U` of `v_!` applied to the counit
of `kV_! ⊣ kV^*` is invertible. -/
lemma isIso_restrict_map_extend_counit (hP : IsPullback kU kV u v) (N : SchemeDerivedCategory V) :
    IsIso ((derivedRestrict u).map ((derivedExtendByZero v).map
      ((derivedExtendByZeroAdjunction kV).counit.app N))) := by
  have hn := (derivedBaseChange hP).hom.naturality ((derivedExtendByZeroAdjunction kV).counit.app N)
  have : (derivedRestrict u).map ((derivedExtendByZero v).map
      ((derivedExtendByZeroAdjunction kV).counit.app N)) =
      (derivedBaseChange hP).hom.app _ ≫
        (derivedExtendByZero kU).map ((derivedRestrict kV).map
          ((derivedExtendByZeroAdjunction kV).counit.app N)) ≫
          (derivedBaseChange hP).inv.app _ := by
    simp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [this]
  infer_instance

end Square

end

end AlgebraicGeometry.Scheme
