/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Colimit.Finiteness

/-!
# A module as the filtered colimit of its finitely generated submodules

Mathlib has both halves of this statement and does not join them.
`Module.fgSystem.equiv` identifies a module with the direct limit of its finitely generated
submodules, as a linear equivalence; `ModuleCat.directLimitIsColimit` exhibits an unbundled
direct limit as a categorical colimit. This file is the composite: the cocone whose vertex is
the module itself, and whose legs are the inclusions of its finitely generated submodules, is
a colimit in `ModuleCat R`.

The categorical form is what a sheaf-theoretic consumer needs. Approximating a quasi-coherent
sheaf by its coherent subsheaves is a colimit statement about a diagram of subobjects, and the
comparison maps it has to produce are cocone legs; `Module.fgSystem.equiv` alone cannot supply
those.

## Main definitions

* `ModuleCat.fgSubmoduleDiagram`: the diagram of finitely generated submodules.
* `ModuleCat.fgSubmoduleCocone`: that diagram's cocone with vertex the module itself.

## Main results

* `ModuleCat.fgSubmoduleCoconeIsColimit`: the cocone is a colimit.

## Implementation notes

`DecidableEq (Submodule R M)` is carried rather than obtained from `Classical`, because
`Module.fgSystem.equiv` and `ModuleCat.directLimitDiagram` both carry it; introducing choice
here would make this statement harder to use than the two it is built from, not easier.

## References

* Mathlib's `Algebra/Colimit/Finiteness.lean` and `Algebra/Category/ModuleCat/Limits.lean`.
-/

open CategoryTheory CategoryTheory.Limits Module

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable [DecidableEq (Submodule R M)]

/-- The diagram of finitely generated submodules of `M`, valued in `ModuleCat R`. -/
noncomputable abbrev fgSubmoduleDiagram :
    {N : Submodule R M // N.FG} ⥤ ModuleCat.{u} R :=
  ModuleCat.directLimitDiagram (R := R) (fun N => (N : Submodule R M)) (fgSystem R M)

/-- The cocone on `fgSubmoduleDiagram` whose vertex is `M` itself, with the inclusion of each
finitely generated submodule as its leg. -/
@[simps]
noncomputable def fgSubmoduleCocone : Cocone (fgSubmoduleDiagram R M) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun N => ModuleCat.ofHom (N : Submodule R M).subtype
      naturality := by intros; rfl }

/-- **Every module is the filtered colimit of its finitely generated submodules.**

`Module.fgSystem.equiv` is the same statement as a linear equivalence with a direct limit;
this transports it across `ModuleCat.directLimitIsColimit`, and `Module.fgSystem.equiv_comp_of`
is exactly the compatibility with the cocone legs that the transport needs. -/
noncomputable def fgSubmoduleCoconeIsColimit : IsColimit (fgSubmoduleCocone R M) :=
  IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit _ _)
    (Cocone.ext (fgSystem.equiv R M).toModuleIso fun N =>
      ModuleCat.hom_ext (fgSystem.equiv_comp_of N))

end ModuleCat
