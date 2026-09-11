/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Free modules of finite rank in `FGModuleCat`

The free module `Fin k → R` is projective among finitely generated modules, and every
finitely generated module is a quotient of one. The first statement is projectivity in all
modules transported along the forgetful functor, which preserves epimorphisms because it
preserves finite colimits; the second is `Module.Finite.exists_fin'` read in the category.

Neither statement needs `R` noetherian, and this file no longer assumes it. Mathlib's
`PreservesFiniteColimits (forget₂ (FGModuleCat k) (ModuleCat k))` holds over any ring,
because a finite colimit of finitely generated modules is a quotient of a finite coproduct.
Noetherian hypotheses enter `FGModuleCat` for finite *limits*, where a kernel of finitely
generated modules need not be finitely generated. The consumers below are noetherian for
their own reasons, not for this one.

These are the "enough acyclic generators" inputs for coherent sheaves on an affine
noetherian scheme, through `Coh.affineEquivalence`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace FGModuleCat

variable {R : Type u} [CommRing R]

/-- Every finitely generated module is a quotient of a free module of finite rank. -/
theorem exists_finFree_epi (M : FGModuleCat.{u} R) :
    ∃ (k : ℕ) (q : FGModuleCat.of R (Fin k → R) ⟶ M), Epi q := by
  haveI : Module.Finite R M.obj := M.property
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' (R := R) (M := M.obj)
  refine ⟨k, ⟨ModuleCat.ofHom f⟩, ?_⟩
  haveI : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).2 hf
  exact Functor.epi_of_epi_map (ModuleCat.isFG R).ι this

/-- Free modules of finite rank are projective among finitely generated modules: the
forgetful functor to all modules preserves epimorphisms, so a lift in all modules is a lift.

No noetherian hypothesis. The epimorphism preservation comes from Mathlib's
`PreservesFiniteColimits` instance for `forget₂ (FGModuleCat R) (ModuleCat R)`, which is
stated over any ring. -/
theorem projective_of_finFree (k : ℕ) :
    Projective (FGModuleCat.of R (Fin k → R)) where
  factors {Y Z} g e he := by
    haveI : Epi e.hom := (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_epi e
    haveI : Projective (ModuleCat.of R (Fin k → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    exact ⟨⟨Projective.factorThru g.hom e.hom⟩,
      ObjectProperty.hom_ext _ (Projective.factorThru_comp g.hom e.hom)⟩

end FGModuleCat
