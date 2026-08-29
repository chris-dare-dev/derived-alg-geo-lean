/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Exact tensoring by an invertible module sheaf

This file is the neutral exact-functor owner for tensoring module sheaves by a line bundle.  The
construction belongs under `Modules/Tensor`: divisor sequences, filtrations, and future moduli
constructions are consumers of the same exact functor rather than separate owners of it.

For an invertible `L`, `tensorLeftFunctor L` is the sheafified tensor product `L ⊗ -`.  It
preserves finite colimits by comparison with objectwise presheaf tensor and sheafification.  Local
rank-one trivializations show that it preserves monomorphisms; hence it preserves homology and all
finite limits as well.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private local instance tensorExact_category : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

private noncomputable local instance tensorExact_monoidalCategory :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- Tensoring on the left by a module sheaf, using the sheafified tensor product. -/
noncomputable def tensorLeftFunctor (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := tensorObj L M
  map f := tensorHom (𝟙 L) f
  map_id M := tensorHom_id_id L M
  map_comp f g := by
    symm
    simpa using tensorHom_comp_tensorHom (𝟙 L) f (𝟙 L) g

private noncomputable def tensorLeftComparisonIso (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    ((MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
        ((toPresheafOfModules X).obj L) ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
        tensorLeftFunctor L) :=
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

/-- Tensoring by an invertible module sheaf preserves finite colimits. -/
noncomputable instance tensorLeftFunctor_preservesFiniteColimits (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    PreservesFiniteColimits (tensorLeftFunctor L) where
  preservesFiniteColimits K _ _ := by
    let a := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let T := (MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
      ((toPresheafOfModules X).obj L)
    have hT : PreservesFiniteColimits T := by
      change PreservesFiniteColimits
        ((MonoidalCategory.tensoringLeft
          (_root_.PresheafOfModules.{u}
            (X.presheaf ⋙ forget₂ CommRingCat RingCat))).obj
          (show _root_.PresheafOfModules.{u}
            (X.presheaf ⋙ forget₂ CommRingCat RingCat) from
              (toPresheafOfModules X).obj L))
      infer_instance
    letI : PreservesFiniteColimits T := hT
    haveI : PreservesFiniteColimits a := inferInstance
    have hsource : PreservesColimitsOfShape K
        (((MonoidalCategory.tensoringLeft X.PresheafOfModules).obj
            ((toPresheafOfModules X).obj L)) ⋙
          PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) := by
      change PreservesColimitsOfShape K (T ⋙ a)
      infer_instance
    have htarget : PreservesColimitsOfShape K
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
          tensorLeftFunctor L) :=
      (preservesColimitsOfShape_iff_of_natIso
        (J := K) (tensorLeftComparisonIso L)).mp hsource
    letI : PreservesColimitsOfShape K (a ⋙ tensorLeftFunctor L) := htarget
    exact (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).preservesColimitsOfShape_of_comp_left
        (tensorLeftFunctor L)

/-- Tensoring by an invertible module sheaf is additive. -/
noncomputable instance tensorLeftFunctor_additive (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (tensorLeftFunctor L).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (tensorLeftFunctor L)
  exact Functor.additive_of_preservesBinaryBiproducts (tensorLeftFunctor L)

private noncomputable instance faithfulToSheaf : (toSheaf X).Faithful := by
  constructor
  intro A B f g h
  apply hom_ext f g
  intro U
  ext x
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.hom.app (.op U)) h) x

set_option maxHeartbeats 800000 in
/-- Tensoring a monomorphism by an invertible module sheaf remains a monomorphism. -/
theorem mono_tensorHom_id_of_invertible (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Mono (tensorHom (𝟙 L) f) := by
  let g := (toPresheafOfModules X).map f
  haveI : Mono g := Functor.map_mono (toPresheafOfModules X) f
  haveI hg : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map g) := by
    apply Presheaf.isLocallyInjective_of_injective
    intro U
    exact PresheafOfModules.injective_of_mono g U
  let hInv : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L) := inferInstance
  obtain ⟨q, hq, hrank⟩ := hInv.exists_rankOneData
  letI : q.IsLocallyFreeData := hq
  have hlocal :=
    SheafOfModules.isLocallyInjective_whiskerLeft_of_rankOneData q hrank g
  let t := tensorHom (𝟙 L) f
  let t' := (toSheaf X).map t
  haveI : Sheaf.IsLocallyInjective t' := by
    change Sheaf.IsLocallyInjective
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (L.val ◁ g)))
    rw [Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    exact hlocal
  haveI : Mono t' := Sheaf.mono_of_isLocallyInjective t'
  exact (toSheaf X).mono_of_mono_map inferInstance

noncomputable instance tensorLeftFunctor_preservesMonomorphisms (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (tensorLeftFunctor L).PreservesMonomorphisms where
  preserves f _ := mono_tensorHom_id_of_invertible L f

noncomputable instance tensorLeftFunctor_preservesHomology (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (tensorLeftFunctor L).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorLeftFunctor L)

/-- Tensoring by an invertible module sheaf preserves finite limits. -/
noncomputable instance tensorLeftFunctor_preservesFiniteLimits (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    PreservesFiniteLimits (tensorLeftFunctor L) :=
  Functor.preservesFiniteLimits_of_preservesHomology (tensorLeftFunctor L)

/-- Tensoring a short exact sequence by an invertible module sheaf remains short exact. -/
theorem shortExact_map_tensorLeft_of_invertible (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor L)).ShortExact :=
  hS.map_of_exact (tensorLeftFunctor L)

end AlgebraicGeometry.Scheme.Modules
