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

## Main definitions

This file introduces no new definitions.

## Main results

* `isCoveringMap_prodMap_id` — a covering map remains a covering map after taking its product
  with an identity map. It is in the namespace
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.

## Implementation notes

The statement of `isCoveringMap_prodMap_id` quantifies over three arbitrary
topological spaces and mentions no matrix, no phase and no stability
condition, so it lives with the topology owner rather than beside the
`GL⁺(2, ℝ)` cover whose coordinate argument uses it.

The declaration lives in the namespace of that cover's stability-action
consumer, which keeps its fully qualified name fixed. The namespace therefore
reads oddly here; the divergence between path and namespace is deliberate.

## References

Mathlib's `IsCoveringMap` and `IsEvenlyCovered`.

## Tags

covering map, product, topology
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
