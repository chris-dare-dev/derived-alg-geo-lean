/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Presentation

/-!
# Pullback of quasi-coherent module sheaves

Pullback of module sheaves along any scheme morphism preserves quasi-coherence.
The existing neutral presentation transport applies on inverse-image opens,
which still cover the source scheme.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback` preserves
  quasi-coherence without a flatness, finiteness, or quasi-compactness premise.

## Implementation notes

The proof transports the chosen `SheafOfModules.QuasicoherentData` across each
inverse-image open, then applies `SheafOfModules.QuasicoherentData.isQuasicoherent`.

## References

Pinned Mathlib's `SheafOfModules.IsQuasicoherent` supplies local presentation
data, and `AlgebraicGeometry.Scheme.Hom.coversTop_preimage` supplies the cover.

## Tags

scheme modules, pullback, quasi-coherence
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

noncomputable section

/-- Pullback of a quasi-coherent module sheaf is quasi-coherent along every
scheme morphism. Presentations pull back on each member of the chosen open
cover; no exactness of pullback is needed. -/
theorem isQuasicoherent_pullback (hM : M.IsQuasicoherent) :
    ((pullback f).obj M).IsQuasicoherent := by
  obtain ⟨q⟩ := hM.nonempty_quasicoherentData
  let σ : ((pullback f).obj M).QuasicoherentData :=
    { I := q.I
      X := fun i ↦ f ⁻¹ᵁ q.X i
      coversTop := f.coversTop_preimage q.coversTop
      presentation := fun i ↦ pullbackPresentationOver f M (q.X i) (q.presentation i) }
  exact σ.isQuasicoherent

end

end AlgebraicGeometry.Scheme.Modules
