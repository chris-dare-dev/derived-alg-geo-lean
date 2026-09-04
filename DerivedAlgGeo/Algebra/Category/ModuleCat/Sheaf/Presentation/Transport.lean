/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Transporting finite presentations

Mathlib has two ways of moving a `SheafOfModules.Presentation` around — along an isomorphism
(`Presentation.ofIsIso`) and along a colimit-preserving functor (`Presentation.map`). Mathlib
v4.32 supplies anonymous instances proving that both preserve `Presentation.IsFinite`; the
named results in this file retain the stable API used by this project.

That gap is why `SheafOfModules.IsFinitePresentation` has no local-to-global criterion even
though `IsQuasicoherent` does: `QuasicoherentData.bind` builds its presentations as
`(P.map _ _).of_isIso _`, so without these two instances there is no way to conclude that the
glued data is finite.

Both are immediate from the upstream instances.

## Main results

* `Presentation.isFinite_of_isIso`
* `Presentation.isFinite_map`

This is DerivedAlgGeo-owned compatibility infrastructure. It remains in the `SheafOfModules`
namespace because that is the mathematical owner of the declarations, not because the project
is committed to upstreaming it.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Transporting a presentation along an isomorphism keeps it finite: `of_isIso` composes the
generating and relating maps with an iso and leaves both index types alone. -/
theorem Presentation.isFinite_of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (P : M.Presentation) [P.IsFinite] : (P.ofIsIso f).IsFinite := by
  infer_instance

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Transporting a presentation along a colimit-preserving functor keeps it finite:
`Presentation.map` builds the new generators and relations out of the *same* index types
(`map_generators_I`, `map_relations_I`). -/
theorem Presentation.isFinite_map {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
    (η : unit S ≅ F.obj (unit R)) : (P.map F η).IsFinite where
  isFiniteType_generators := by
    constructor
    rw [Presentation.map_generators_I]
    infer_instance
  isFiniteType_relations := by
    constructor
    rw [Presentation.map_relations_I]
    infer_instance

/-! ### What these unblock

`Presentation.quasicoherentData` and `QuasicoherentData.bind` are both built out of exactly
`map` and `of_isIso`, so these two instances are what any statement about finite presentation
has to go through.

The global case is done in the sibling `Presentation/Finite.lean`:
`IsFinitePresentation.of_presentation`. Two things were needed on top of the instances here,
both recorded there — a hand-supplied `preservesColimitsOfSize_shrink`, and pinning `S` when
applying `isFinite_map`, without which `J'` stays a metavariable and instance synthesis fails
with a misleading "missing `HasSheafify`".

The local-to-global case, `IsFinitePresentation.of_coversTop` via `bind`, is implemented in the
sibling `Presentation/Locality.lean`. It needs the same two fixes plus one more:
`QuasicoherentData.I` lives in its own universe `w`, and `bind` returns `Σ i, (D i).I`, so the
covering-family index has to remain universe-polymorphic for the `w` from
`exists_quasicoherentData` to match the `w` `bind` produces.

A practical note for that work: introduce local data with `choose D hD using …`, not
`have D := ….choose`. With `have`, `D i` is opaque and `choose_spec` types against `_.choose`
rather than `D i` — an error with nothing to do with the real problem.
-/

end SheafOfModules
