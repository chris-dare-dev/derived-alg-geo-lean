/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Inverse image on opens is a final functor

For a continuous map `f : X ⟶ Y`, the inverse-image functor `Opens.map f : Opens Y ⥤ Opens X` is
final.  Mathlib makes it representably flat, so every structured-arrow category under it is
cofiltered, hence connected, which is finality.

## Main results

* `TopologicalSpace.Opens.map_final`: the instance.

## Implementation notes

This is what makes `SheafOfModules.pullbackObjUnitToUnit` an isomorphism along every morphism
of ringed spaces over `f`, in particular along every morphism of schemes: Mathlib states that
isomorphism under a `Final` hypothesis on the underlying functor of opens.  The instance lives
here, with the carrier, rather than in the module-sheaf consumer that first needed it.
-/

open CategoryTheory

namespace TopologicalSpace.Opens

/-- Inverse image on opens is final: it is representably flat, so each structured-arrow category
is cofiltered and therefore connected. -/
instance map_final {X Y : TopCat} (f : X ⟶ Y) : (Opens.map f).Final where
  out _ := IsCofiltered.isConnected _

end TopologicalSpace.Opens
