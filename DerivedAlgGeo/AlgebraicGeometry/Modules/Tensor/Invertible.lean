/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Colimits
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Isomorphism
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Locality
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Exact tensoring by an invertible module sheaf

This file is the neutral exact-functor owner for tensoring module sheaves by a line bundle.  The
construction belongs under `Modules/Tensor`: divisor sequences, filtrations, and future moduli
constructions are consumers of the same exact functor rather than separate owners of it.

The generic `tensorLeftFunctor L` and its colimit preservation come from `Monoidal` and
`Colimits`. For an invertible `L`, local rank-one trivializations show that it also preserves
monomorphisms; hence it preserves homology and all finite limits.
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

/-- **Tensoring a finitely presented module sheaf by an invertible one preserves finite
presentation.**

On a rank-one trivializing cover for `L`, the restriction of `L ⊗ M` is isomorphic to the
restriction of `M`: commute the two tensor factors and use the right-factor trivialization.
Finite presentation restricts to each cover member and descends from that cover. -/
theorem isFinitePresentation_tensorObj_left_of_isInvertible (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    (hM : (show SheafOfModules X.ringCatSheaf from M).IsFinitePresentation) :
    (show SheafOfModules X.ringCatSheaf from
      tensorObj L M).IsFinitePresentation := by
  obtain ⟨q, hq, hrank⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from L)
  letI : q.IsLocallyFreeData := hq
  apply SheafOfModules.IsFinitePresentation.of_coversTop
    (show SheafOfModules X.ringCatSheaf from tensorObj L M) q.X q.coversTop
  intro i
  let e : (tensorObj L M).over (q.X i) ≅ M.over (q.X i) :=
    (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso
        (tensorCommIso L M) ≪≫
      tensorOverIsoOfTrivializationRight M L (q.X i)
        (q.rankOneTrivialization hrank i)
  exact SheafOfModules.IsFinitePresentation.of_iso
    (C := Over (q.X i)) e.symm
    (SheafOfModules.IsFinitePresentation.over hM (q.X i))

/-- **Tensoring an epimorphism by an invertible module sheaf remains an epimorphism.**

Finite colimits are preserved, so pushouts are, and a morphism is an epimorphism exactly when
its pushout along itself is the identity square. The companion of
`mono_tensorHom_id_of_invertible`, and the step that carries Serre's surjection `free I ↠ F(N)`
across `O(-N)`. -/
theorem epi_tensorHom_id_of_invertible (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi (tensorHom (𝟙 L) f) :=
  (tensorLeftFunctor L).map_epi f

/-- **Tensoring a finite free sheaf by an invertible sheaf is a finite direct sum of copies of
it.** `free I` is the coproduct of copies of the unit, tensoring by an invertible sheaf preserves
finite coproducts, and `L ⊗ unit ≅ L` by the right unitor. -/
noncomputable def tensorLeftFreeIso (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    (I : Type u) [Finite I] :
    tensorObj L (show X.Modules from SheafOfModules.free.{u} I) ≅ ∐ (fun _ : I => L) := by
  classical
  haveI := Fintype.ofFinite I
  exact PreservesCoproduct.iso (tensorLeftFunctor L)
      (fun _ : I => (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ≪≫
    Sigma.mapIso (fun _ => tensorUnitRightIso L)

/-- Tensoring a short exact sequence by an invertible module sheaf remains short exact. -/
theorem shortExact_map_tensorLeft_of_invertible (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (tensorLeftFunctor L)).ShortExact :=
  hS.map_of_exact (tensorLeftFunctor L)

end AlgebraicGeometry.Scheme.Modules
