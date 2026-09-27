/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.CategoryTheory.Limits.Preserves.Reflective

/-!
# Colimits of tensor products of scheme-module sheaves

Presheaf tensor preserves colimits objectwise. The arbitrary-sheaf tensor/sheafification
comparisons transfer that property to the sheafified tensor in both slots.

The main results are `tensorLeft_preservesColimitsOfShape` and
`tensorRight_preservesColimitsOfShape`. Their index categories have the same universe as
the underlying scheme site, matching the available presheaf tensor instance. The historical
finite-colimit instance for `tensorLeftFunctor` follows without an invertibility hypothesis.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private noncomputable local instance tensorColimits_monoidalCategory :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

private noncomputable def tensorLeftComparisonIso (L : X.Modules) :
    ((MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
        ((toPresheafOfModules X).obj L) ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        tensorLeft (C := X.Modules) L) :=
  NatIso.ofComponents
    (fun P ↦ @asIso _ _ _ _ (tensorSheafificationComparisonLeft L P)
      (isIso_tensorSheafificationComparisonLeft L P))
    (fun {P Q} g ↦ by
      change (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            (((toPresheafOfModules X).obj L) ◁ g) ≫
          tensorSheafificationComparisonLeft L Q =
        tensorSheafificationComparisonLeft L P ≫
          tensorHom (𝟙 L)
            ((PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)).map g)
      have h := tensorSheafificationComparisonLeft_naturality (𝟙 L) g
      have hid : (toPresheafOfModules X).map (𝟙 L) =
          𝟙 ((toPresheafOfModules X).obj L) :=
        (toPresheafOfModules X).map_id L
      rw [hid, MonoidalCategory.id_tensorHom] at h
      exact h)

/-- Objectwise presheaf tensor preserves colimits, and the sheafification comparison
identifies its image with tensoring a module sheaf. The sheafification adjunction
then reflects this preservation back to sheaf modules. -/
theorem tensorLeft_preservesColimitsOfShape (L : X.Modules)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (tensorLeft (C := X.Modules) L) := by
  let a := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let T := (MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
    ((toPresheafOfModules X).obj L)
  have hT : PreservesColimitsOfShape J T := by
    change PreservesColimitsOfShape J
      (tensorLeft (show _root_.PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) from
          (toPresheafOfModules X).obj L))
    infer_instance
  letI : PreservesColimitsOfShape J T := hT
  haveI : PreservesColimitsOfShape J a := inferInstance
  have hsource : PreservesColimitsOfShape J
      (((MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
          ((toPresheafOfModules X).obj L)) ⋙
        PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) := by
    change PreservesColimitsOfShape J (T ⋙ a)
    infer_instance
  have htarget : PreservesColimitsOfShape J
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        tensorLeft (C := X.Modules) L) :=
    (preservesColimitsOfShape_iff_of_natIso
      (J := J) (tensorLeftComparisonIso L)).mp hsource
  letI : PreservesColimitsOfShape J (a ⋙ tensorLeft (C := X.Modules) L) := htarget
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).preservesColimitsOfShape_of_comp_left
      (tensorLeft (C := X.Modules) L)

private noncomputable def tensorRightComparisonIso (L : X.Modules) :
    ((MonoidalCategory.tensoringRight X.PresheafOfModules).obj
        ((toPresheafOfModules X).obj L) ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        tensorRight (C := X.Modules) L) :=
  NatIso.ofComponents
    (fun P ↦ @asIso _ _ _ _ (tensorSheafificationComparisonRight P L)
      (isIso_tensorSheafificationComparisonRight P L))
    (fun {P Q} g ↦ by
      change (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
            (g ▷ ((toPresheafOfModules X).obj L)) ≫
          tensorSheafificationComparisonRight Q L =
        tensorSheafificationComparisonRight P L ≫
          tensorHom
            ((PresheafOfModules.sheafification
              (𝟙 X.ringCatSheaf.obj)).map g) (𝟙 L)
      have h := tensorSheafificationComparisonRight_naturality g (𝟙 L)
      have hid : (toPresheafOfModules X).map (𝟙 L) =
          𝟙 ((toPresheafOfModules X).obj L) :=
        (toPresheafOfModules X).map_id L
      rw [hid, MonoidalCategory.tensorHom_id] at h
      exact h)

/-- The right-hand sheafification comparison gives the same colimit preservation
without assuming a braided structure on module sheaves. -/
theorem tensorRight_preservesColimitsOfShape (L : X.Modules)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (tensorRight (C := X.Modules) L) := by
  let a := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let T := (MonoidalCategory.tensoringRight X.PresheafOfModules).obj
    ((toPresheafOfModules X).obj L)
  have hT : PreservesColimitsOfShape J T := by
    change PreservesColimitsOfShape J
      (tensorRight (show _root_.PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) from
          (toPresheafOfModules X).obj L))
    infer_instance
  letI : PreservesColimitsOfShape J T := hT
  haveI : PreservesColimitsOfShape J a := inferInstance
  have hsource : PreservesColimitsOfShape J
      (((MonoidalCategory.tensoringRight X.PresheafOfModules).obj
          ((toPresheafOfModules X).obj L)) ⋙
        PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) := by
    change PreservesColimitsOfShape J (T ⋙ a)
    infer_instance
  have htarget : PreservesColimitsOfShape J
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        tensorRight (C := X.Modules) L) :=
    (preservesColimitsOfShape_iff_of_natIso
      (J := J) (tensorRightComparisonIso L)).mp hsource
  letI : PreservesColimitsOfShape J (a ⋙ tensorRight (C := X.Modules) L) := htarget
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).preservesColimitsOfShape_of_comp_left
      (tensorRight (C := X.Modules) L)

/-- Finite colimit preservation used by exact tensoring with an invertible sheaf
follows from the all-shapes result, with no invertibility assumption. -/
noncomputable instance tensorLeftFunctor_preservesFiniteColimits (L : X.Modules) :
    PreservesFiniteColimits (tensorLeftFunctor L) := by
  haveI : PreservesColimitsOfSize.{u, u}
      (tensorLeft (C := X.Modules) L) := by
    constructor
    exact tensorLeft_preservesColimitsOfShape L _
  change PreservesFiniteColimits (tensorLeft (C := X.Modules) L)
  infer_instance

/-- Tensoring by any module sheaf is additive, since it preserves finite coproducts. -/
noncomputable instance tensorLeftFunctor_additive (L : X.Modules) :
    (tensorLeftFunctor L).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tensorLeftFunctor L)
  exact Functor.additive_of_preservesBinaryBiproducts (tensorLeftFunctor L)

/-- The finite free sheaf is a coproduct of units. Tensoring with any module sheaf
preserves that coproduct, and the right unitor identifies each summand. -/
noncomputable def tensorLeftFreeIso (L : X.Modules) (I : Type u) [Finite I] :
    tensorObj L (show X.Modules from SheafOfModules.free.{u} I) ≅ ∐ (fun _ : I => L) := by
  classical
  haveI := Fintype.ofFinite I
  exact PreservesCoproduct.iso (tensorLeftFunctor L)
      (fun _ : I => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ≪≫
    Sigma.mapIso (fun _ => tensorUnitRightIso L)

end AlgebraicGeometry.Scheme.Modules
