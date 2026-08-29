/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Pullback of invertible module sheaves

An arbitrary scheme morphism pulls locally free rank-one module sheaves back to locally free
rank-one module sheaves. The proof pulls a chosen rank-one trivializing cover back along the
underlying continuous map and transports each trivialization through `pullbackOverIso`.

No preservation certificate is stored as data: the result is a theorem about Mathlib's existing
scheme-module pullback functor and the repository's intrinsic `SheafOfModules.IsInvertible` root.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

private noncomputable def overUnitIso (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (SheafOfModules.unit X.ringCatSheaf).over U :=
  Iso.refl _

-- Inverse image on opens is representably flat in Mathlib, hence every structured-arrow
-- category is cofiltered and therefore connected. Keep this derived instance local: its
-- canonical owner is topology, while this module only needs it to invoke pullback of free sheaves.
private instance opensMapFinal (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final where
  out _ := CategoryTheory.IsCofiltered.isConnected _

/-- A trivialization of `M` on `U` pulls back to a trivialization of `f⁺ M` on `f⁻¹ U`. -/
noncomputable def pullbackTrivializationOver (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : SheafOfModules.unit (Y.ringCatSheaf.over U) ≅ M.over U) :
    SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      ((pullback f).obj M).over (f ⁻¹ᵁ U) := by
  let V : X.Opens := f ⁻¹ᵁ U
  let eU : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (overEquiv U).functor.obj (M.over U) :=
    (restrictUnitIso U.ι).symm ≪≫
      ((overFunctorEquiv U).app (SheafOfModules.unit Y.ringCatSheaf)).symm ≪≫
      (overEquiv U).functor.mapIso e
  let eV : (overEquiv V).functor.obj
      (SheafOfModules.unit (X.ringCatSheaf.over V)) ≅
      (pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U)) :=
    (overEquiv V).functor.mapIso (overUnitIso X V) ≪≫
      (overFunctorEquiv V).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      restrictUnitIso V.ι ≪≫
      (asIso (SheafOfModules.pullbackObjUnitToUnit
        (f ∣_ U).toRingCatSheafHom)).symm ≪≫
      (pullback (f ∣_ U)).mapIso eU
  let eOver : SheafOfModules.unit (X.ringCatSheaf.over V) ≅
      (overEquiv V).inverse.obj
        ((pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U))) :=
    (overEquiv V).fullyFaithfulFunctor.preimageIso
      (eV ≪≫ ((overEquiv V).counitIso.app _).symm)
  exact eOver ≪≫ (pullbackOverIso f M U).symm

/-- Pullback along an arbitrary scheme morphism preserves intrinsic invertibility. -/
lemma isInvertible_pullback (f : X ⟶ Y) (M : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) := by
  obtain ⟨q, hq, hrank⟩ := SheafOfModules.IsInvertible.exists_rankOneData
    (M := show SheafOfModules Y.ringCatSheaf from M)
  letI : q.IsLocallyFreeData := hq
  let V : q.I → X.Opens := fun i ↦ f ⁻¹ᵁ q.X i
  have hqTop : ⨆ i, q.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (Y : Type u) q.X).mp q.coversTop
  have hV : (_root_.Opens.grothendieckTopology X).CoversTop V :=
    (_root_.Opens.coversTop_iff (X : Type u) V).mpr
      (f.iSup_preimage_eq_top hqTop)
  apply SheafOfModules.IsInvertible.of_trivializations V hV
  intro i
  exact pullbackTrivializationOver f M (q.X i) (q.rankOneTrivialization hrank i)

attribute [instance] isInvertible_pullback

end

end AlgebraicGeometry.Scheme.Modules
