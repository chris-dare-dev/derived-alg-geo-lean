/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction

/-!
# Locally free sheaves under pullback

Pullback of module sheaves along any morphism of schemes preserves local freeness, with the
same index type on each chart.  On a chart `U` of `Y` the generating sections of `M.over U`
are transported by Mathlib's `GeneratingSections.map` along pullback on slices,
`pullbackOverFunctor`, which preserves coproducts, being a left adjoint, and sends the
structure sheaf to the structure sheaf (`pullbackOverUnitIso`); the restriction square
`pullbackOverIso` then moves them onto `(f⁺ M).over (f ⁻¹ᵁ U)`.  This is the site-level
`LocalGeneratorsData.transport` applied chart by chart, and a free basis stays a free basis
because `GeneratingSections.map` sends an isomorphism `π` to an isomorphism.  No flatness
enters, exactly as for invertible sheaves in `Pullback/Invertible.lean`, and the transport is
the one `Coherent/Pullback.lean` runs on presentations.

## Main definitions

* `Scheme.Modules.pullbackLocalGeneratorsData`: local generator data pulls back, on the
  preimage cover with the same index types.

## Main results

* `Scheme.Modules.isLocallyFreeData_pullbackLocalGeneratorsData`: locally free data pulls
  back to locally free data;
* `Scheme.Modules.isLocallyFree_pullback`: pullback preserves local freeness.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

/-- Local generator data pulls back along any morphism of schemes: on the preimage of each
chart the generators are `GeneratingSections.map` along pullback on slices, moved onto
`(f⁺ E).over (f ⁻¹ᵁ U)` by the restriction square, with the same index types
(`LocalGeneratorsData.transport`). -/
def pullbackLocalGeneratorsData (f : X ⟶ Y) {E : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} (show SheafOfModules Y.ringCatSheaf from E)) :
    SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj E) :=
  q.transport (N := show SheafOfModules X.ringCatSheaf from (pullback f).obj E)
    (fun i ↦ f ⁻¹ᵁ q.X i) (f.coversTop_preimage q.coversTop)
    (fun i ↦ pullbackOverFunctor f (q.X i)) (fun i ↦ pullbackOverUnitIso f (q.X i))
    (fun i ↦ (pullbackOverIso f E (q.X i)).symm)

/-- The pulled-back generators on the preimage of a chart have the original index type: this
is what lets a fixed-rank atlas pull back with its rank. -/
@[simp]
lemma pullbackLocalGeneratorsData_generators_I (f : X ⟶ Y) {E : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} (show SheafOfModules Y.ringCatSheaf from E))
    (i : q.I) :
    ((pullbackLocalGeneratorsData f q).generators i).I = (q.generators i).I :=
  rfl

/-- Locally free data pulls back to locally free data
(`LocalGeneratorsData.isLocallyFreeData_transport`). -/
instance isLocallyFreeData_pullbackLocalGeneratorsData (f : X ⟶ Y) {E : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} (show SheafOfModules Y.ringCatSheaf from E))
    [q.IsLocallyFreeData] : (pullbackLocalGeneratorsData f q).IsLocallyFreeData := by
  unfold pullbackLocalGeneratorsData
  infer_instance

/-- Pullback preserves local freeness with no flatness hypothesis: chart generators are
transported by `pullbackOverFunctor`, a left adjoint fixing the structure sheaf, exactly as
in `isInvertible_pullback`.  The data is `pullbackLocalGeneratorsData`; this lemma forgets it
to the `Prop` through `LocalGeneratorsData.isLocallyFree`.  It is registered as an instance,
keyed at the `show SheafOfModules _ from _` spelling, so it fires on goals written at that
spelling. -/
lemma isLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules)
    [SheafOfModules.IsLocallyFree.{u, u, u} (show SheafOfModules Y.ringCatSheaf from M)] :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (pullback f).obj M) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData
    (M := show SheafOfModules Y.ringCatSheaf from M)
  letI : q.IsLocallyFreeData := hq
  exact (pullbackLocalGeneratorsData f q).isLocallyFree

attribute [instance] isLocallyFree_pullback

end

end AlgebraicGeometry.Scheme.Modules
