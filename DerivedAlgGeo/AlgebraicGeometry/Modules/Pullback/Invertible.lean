/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Invertible

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

/-- A trivialization of `M` on `U` pulls back to a trivialization of `f⁺ M` on `f⁻¹ U`: the
structure-sheaf identification `pullbackOverUnitIso`, the trivialization transported by
`pullbackOverFunctor`, and the restriction square `pullbackOverIso`. -/
def pullbackTrivializationOver (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : SheafOfModules.unit (Y.ringCatSheaf.over U) ≅ M.over U) :
    SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      ((pullback f).obj M).over (f ⁻¹ᵁ U) :=
  pullbackOverUnitIso f U ≪≫ (pullbackOverFunctor f U).mapIso e ≪≫ (pullbackOverIso f M U).symm

/-- Pullback along an arbitrary scheme morphism preserves intrinsic invertibility. -/
lemma isInvertible_pullback (f : X ⟶ Y) (M : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) := by
  obtain ⟨q, hq, hrank⟩ := SheafOfModules.IsInvertible.exists_rankOneData
    (M := show SheafOfModules Y.ringCatSheaf from M)
  letI : q.IsLocallyFreeData := hq
  apply SheafOfModules.IsInvertible.of_trivializations (fun i ↦ f ⁻¹ᵁ q.X i)
    (f.coversTop_preimage q.coversTop)
  intro i
  exact pullbackTrivializationOver f M (q.X i) (q.rankOneTrivialization hrank i)

attribute [instance] isInvertible_pullback

end

end AlgebraicGeometry.Scheme.Modules
