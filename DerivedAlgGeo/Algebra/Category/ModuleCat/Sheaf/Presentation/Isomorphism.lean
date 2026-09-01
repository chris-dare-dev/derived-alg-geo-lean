/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Isomorphism invariance of finite presentation

Finite local presentation data for a sheaf of modules on an arbitrary ringed site transports
across an isomorphism. Consequently, finite presentation defines an isomorphism-closed object
property on the category of module sheaves.

## Main results

* `SheafOfModules.QuasicoherentData.ofIso` transports local presentation data;
* `SheafOfModules.IsFinitePresentation.of_iso` preserves finite presentation;
* `SheafOfModules.isFinitePresentation_isClosedUnderIsomorphisms` packages the result as an
  isomorphism-closed object property.
-/

universe u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] [Limits.HasBinaryProducts C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [hasSheafCompose : ∀ X,
    (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafify : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hasWeakSheafify : ∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [wEqualsLocallyBijective : ∀ X,
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport local presentation data across an isomorphism of sheaves of modules.

This is the project-facing, iso-valued wrapper around Mathlib's `QuasicoherentData.ofIsIso`.
-/
noncomputable def QuasicoherentData.ofIso {M N : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (e : M ≅ N) : N.QuasicoherentData :=
  q.ofIsIso e.hom

instance QuasicoherentData.isFinitePresentation_ofIso
    {M N : SheafOfModules.{u} R} (q : M.QuasicoherentData) (e : M ≅ N)
    [q.IsFinitePresentation] : (q.ofIso e).IsFinitePresentation := by
  dsimp only [QuasicoherentData.ofIso]
  infer_instance

omit hasSheafCompose [Limits.HasBinaryProducts C] in
/-- Finite presentation is preserved by an isomorphism of sheaves of modules. -/
theorem IsFinitePresentation.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (hM : M.IsFinitePresentation) : N.IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  letI := hq
  exact ⟨q.ofIso e, inferInstance⟩

instance isFinitePresentation_isClosedUnderIsomorphisms :
    (isFinitePresentation R).IsClosedUnderIsomorphisms where
  of_iso e hM := hM.of_iso e

end SheafOfModules
