/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# General covering maps

Covering-map lemmas that hold for arbitrary topological spaces and extend
`Mathlib.Topology.Covering.Basic` at the pinned revision.

`isCoveringMap_prodMap_id` was extracted here by MO1.12 (#1323) from the
`GL⁺(2, ℝ)` cover's coordinate argument, where it was stated and proved. Its
statement quantifies over three arbitrary topological spaces and mentions no
matrix, no phase and no stability condition, so the ledger's row 08 places
general covering lemmas with the topology owner rather than beside the group
they were first needed for.

The declaration keeps the fully qualified name it was introduced under, per the
cutover ledger's first standing decision: paths move, namespaces do not. The
namespace therefore reads oddly here, and that is recorded rather than repaired.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

/-- A covering map remains a covering map after taking its product with an
identity map. -/
theorem isCoveringMap_prodMap_id {E X Y : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace Y] {f : E → X} (hf : IsCoveringMap f) :
    IsCoveringMap (Prod.map f (id : Y → Y)) := by
  intro xy
  obtain ⟨hdisc, U, hxU, hU, hfU, H, hH⟩ := hf xy.1
  let I := f ⁻¹' ({xy.1} : Set X)
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I)
  have hpre : Prod.map f (id : Y → Y) ⁻¹' (U ×ˢ Set.univ) =
      (f ⁻¹' U) ×ˢ Set.univ := by
    ext p
    simp [Prod.map]
  let reassoc : ((U × I) × Y) ≃ₜ ((U × Y) × I) :=
    (Homeomorph.prodAssoc U I Y).trans <|
      ((Homeomorph.refl U).prodCongr (Homeomorph.prodComm I Y)).trans <|
        (Homeomorph.prodAssoc U Y I).symm
  let base : (U ×ˢ (Set.univ : Set Y)) ≃ₜ U × Y :=
    (Homeomorph.Set.prod U Set.univ).trans <|
      (Homeomorph.refl U).prodCongr (Homeomorph.Set.univ Y)
  let K : (Prod.map f (id : Y → Y) ⁻¹' (U ×ˢ Set.univ)) ≃ₜ
      (U ×ˢ Set.univ) × I :=
    (Homeomorph.setCongr hpre).trans <|
      (Homeomorph.Set.prod (f ⁻¹' U) Set.univ).trans <|
        (H.prodCongr (Homeomorph.Set.univ Y)).trans <|
          reassoc.trans (base.symm.prodCongr (Homeomorph.refl I))
  refine ⟨hdisc, U ×ˢ Set.univ, ⟨hxU, Set.mem_univ _⟩, hU.prod isOpen_univ,
    hpre ▸ hfU.prod isOpen_univ, K, ?_⟩
  intro e
  change (K e).1.1 = Prod.map f id e
  apply Prod.ext
  · exact hH ⟨e.1.1, e.2.1⟩
  · rfl

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
