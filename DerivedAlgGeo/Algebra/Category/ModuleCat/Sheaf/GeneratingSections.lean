/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Generating sections from free epimorphisms

A family of generating sections of a module sheaf is equivalently packaged by an epimorphism
from a free module sheaf. Mathlib provides the map from generating sections to such an
epimorphism; this file records the converse construction, its finite-index instance, and the
resulting recovery lemma.

These declarations require only a sheaf of rings on an arbitrary site. Geometric applications,
such as finite generation on an affine chart, import this categorical owner directly.

## Main results

* `SheafOfModules.GeneratingSections.ofFreeEpi`
* `SheafOfModules.GeneratingSections.isFiniteType_ofFreeEpi`
* `SheafOfModules.GeneratingSections.ofFreeEpi_π`
-/

universe u u₁ v₁

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An epimorphism from a free sheaf of modules determines a family of generating sections. -/
noncomputable def GeneratingSections.ofFreeEpi (M : SheafOfModules.{u} R) {I : Type u}
    (p : free I ⟶ M) [Epi p] : M.GeneratingSections where
  I := I
  s := M.freeHomEquiv p
  epi := by simpa using (inferInstance : Epi p)

/-- A finite free source gives a finite family of generating sections. -/
instance GeneratingSections.isFiniteType_ofFreeEpi (M : SheafOfModules.{u} R) {I : Type u}
    [Finite I] (p : free I ⟶ M) [Epi p] :
    (GeneratingSections.ofFreeEpi M p).IsFiniteType where
  finite := inferInstanceAs (Finite I)

/-- `ofFreeEpi` recovers its defining epimorphism under `GeneratingSections.π`. -/
@[simp]
lemma GeneratingSections.ofFreeEpi_π (M : SheafOfModules.{u} R) {I : Type u}
    (p : free I ⟶ M) [Epi p] : (GeneratingSections.ofFreeEpi M p).π = p :=
  M.freeHomEquiv.symm_apply_apply p

/-- Pushing a free presentation forward along an isomorphism keeps it a free presentation:
the presentation of `σ.ofEpi p` is `σ.π ≫ p`.  Stated here, on a general ringed site, because
the rewrite along `ofEpi_π` does not terminate in the default heartbeat budget once the sheaf
carries scheme-level instances. -/
lemma GeneratingSections.isIso_ofEpi_π {M N : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    (p : M ⟶ N) [Epi p] [IsIso σ.π] [IsIso p] : IsIso (σ.ofEpi p).π := by
  rw [GeneratingSections.ofEpi_π]
  exact IsIso.comp_isIso' ‹_› ‹_›

end SheafOfModules
