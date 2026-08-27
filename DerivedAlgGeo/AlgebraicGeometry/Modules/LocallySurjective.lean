/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Epimorphisms of module sheaves, from local preimages

`epi_of_pointwise_preimages` is the criterion the rest of this repository reaches for whenever a
map of module sheaves has to be shown surjective: it is enough that every section, near every
point, has a preimage on some smaller open.

## Why it is worth naming

The chain it packages is four links, and each one is a different library's idea of the same fact:

* `TopCat.Presheaf.isLocallySurjective_iff` — local surjectivity on `Opens X` is exactly the
  pointwise statement, because `Opens.mem_grothendieckTopology` is `rfl`;
* `CategoryTheory.Sheaf.IsLocallySurjective` — the sheaf-level class is that, on the underlying
  presheaf map;
* `epi_of_isLocallySurjective` — which gives `Epi` in `Sheaf J AddCommGrpCat`;
* `Functor.epi_of_epi_map` along `SheafOfModules.toSheaf`, which reflects epimorphisms because it
  is faithful.

`Divisors/Effective.lean` runs precisely this chain inline for one specific quotient map, and
hand-rolls the faithfulness of the forgetful functor while doing so — Mathlib's
`instance : (toSheaf.{v} R).Faithful` already provides it, and `reflectsEpimorphisms_of_faithful`
turns that into the reflection. Extracting the chain here is what stops the next caller rebuilding
it a third time.

## What it is *not*

There is no covering family and no `GrothendieckTopology.over` anywhere. A chart-by-chart argument
does not need `isLocallySurjective_of_coversTop`: the charts enter when the caller *chooses* which
open to work inside, at a point it has already been handed, and the hypothesis below is stated so
that choice is all the caller has to make. That is why the criterion is pointwise rather than
indexed by a cover.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A map of module sheaves with local preimages is an epimorphism.**

If every section `t` of `G` over every open `U`, and every point `x ∈ U`, admits an open
`x ∈ V ≤ U` and a section of `F` over `V` mapping to `t|_V`, then `φ` is epi.

The hypothesis is deliberately pointwise. A caller arguing chart by chart is handed the point
first and picks the chart containing it, so no covering family has to be assembled and no
`GrothendieckTopology.over` appears. -/
theorem epi_of_pointwise_preimages {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ (U : X.Opens) (t : Γ(G, U)) (x : X), x ∈ U →
      ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ ∃ s : Γ(F, V),
        Scheme.Modules.Hom.app φ V s = G.presheaf.map (homOfLE hV).op t) :
    Epi φ := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨V, hV, hxV, s, hs⟩ := h U t x hx
    exact ⟨V, hV, ⟨s, hs⟩, hxV⟩
  have : CategoryTheory.Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := ⟨hls.imageSieve_mem⟩
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance

end AlgebraicGeometry.Scheme.Modules
