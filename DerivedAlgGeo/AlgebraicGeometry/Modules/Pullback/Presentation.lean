/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Transport of module-sheaf presentations by scheme pullback

The presentation transport is independent of finite generation or
quasi-coherence. Both quasi-coherent and coherent pullback consume it.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackPresentationOver` transports a
  presentation on an open through pullback on slice sites.

## Main results

The transported presentation has no finiteness requirement and can be used by
both the quasi-coherent and coherent module-sheaf owners.

## Implementation notes

`SheafOfModules.Presentation.map` uses the left-adjoint pullback on slice sites and its unit
comparison; `SheafOfModules.Presentation.ofIsIso` transports across the restriction square.

## References

The construction uses pinned Mathlib's `SheafOfModules.Presentation.map` and
the repository's `AlgebraicGeometry.Scheme.Modules.pullbackOverIso`.

## Tags

scheme modules, pullback, presentations
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

noncomputable section

/-- A presentation of `M` on `U` pulls back to a presentation of `f⁺ M` on
`f⁻¹ U`: transport along pullback on slices, then across the restriction
square `AlgebraicGeometry.Scheme.Modules.pullbackOverIso`. No finiteness premise is needed. -/
def pullbackPresentationOver (P : (M.over U).Presentation) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation :=
  (P.map (pullbackOverFunctor f U) (pullbackOverUnitIso f U)).ofIsIso
    (pullbackOverIso f M U).inv

end

end AlgebraicGeometry.Scheme.Modules
