/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Transport

/-!
# Finite global presentations give finitely presented sheaves

`SheafOfModules.Presentation.quasicoherentData` turns a global presentation into quasicoherent
data on the trivial cover. This file records that the data is *finite* when the presentation
is, and hence that a sheaf of modules with a finite global presentation is of finite
presentation.

Together with `presentationOfIsCokernelFree`, this is what concrete constructions need:
anything exhibited as the cokernel of a map between finitely generated free sheaves is of
finite presentation, hence coherent on a locally noetherian scheme.

## The one non-obvious step

`Presentation.isFinite_map` is stated for a functor into sheaves of modules over a *second*
sheaf of rings `S` on a second site `J'`. Applying it here without pinning `S` leaves `J'` a
metavariable, and Lean then tries to synthesise `HasSheafify J' AddCommGrpCat` against that
metavariable and fails outright rather than postponing. Supplying `(S := R.over x)` makes `J'`
ground and everything resolves.

The failure this produces is thoroughly misleading: it reports a missing
`HasSheafify (J.over x) AddCommGrpCat` even though `[∀ X, HasSheafify (J.over X) AddCommGrpCat]`
is in scope and prints identically under `pp.universes`. It is not a universe problem, not a
`variable`-inclusion problem, and not a limitation on `∀`-quantified instance hypotheses —
those all check out in isolation.

## Main results

* `Presentation.isFinitePresentation_quasicoherentData`
* `IsFinitePresentation.of_presentation`

Destined for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.

## Note for callers

Applying `of_presentation` at a concrete presentation is fiddlier than it looks, and the
symptom is always a universe defaulted to `0`. Both this theorem and Mathlib's
`Presentation.IsFinite` carry universe parameters that a goal phrased in other terms — say
`Scheme.Modules.IsCoherent …` — does not pin, and Lean then elaborates them at `.{0, 0, 0}`
and reports a type mismatch at `Type 1` rather than an ambiguity. `(M := …)` does not fix it,
because the universes bind before `M`; `Presentation.IsFinite.{u, u, u}` does. Expect to
annotate.
-/

universe w u v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Quasicoherent data built from a finite global presentation is finite.

`quasicoherentData` covers by the terminal object alone and sets each local presentation to
`P.map (pushforward (𝟙 _)) _`, so this is `Presentation.isFinite_map`. -/
instance Presentation.isFinitePresentation_quasicoherentData {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] : P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation x := by
    dsimp only [Presentation.quasicoherentData, id_eq]
    -- `pushforward (𝟙 _)` is a left adjoint (`Sheaf/PushforwardContinuous.lean`) and so
    -- preserves colimits, but at its own hom universe. `Presentation.map` wants `.{u, u}`, and
    -- `preservesColimitsOfSize_shrink` is deliberately not a global instance — it loops — so
    -- the bridge is supplied by hand.
    haveI : PreservesColimitsOfSize.{u, u} (pushforward.{u} (𝟙 (R.over x))) :=
      preservesColimitsOfSize_shrink _
    -- `(S := R.over x)` is load-bearing; see the module docstring.
    exact Presentation.isFinite_map (S := R.over x) P _ _

/-- **A sheaf of modules with a finite global presentation is of finite presentation.** -/
theorem IsFinitePresentation.of_presentation {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] : IsFinitePresentation M where
  exists_quasicoherentData := ⟨P.quasicoherentData, inferInstance⟩

end SheafOfModules
