/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Noetherian
import DerivedAlgGeo.CategoryTheory.Subobject.NoetherianObject
import Mathlib.Algebra.Category.FGModuleCat.Limits

/-!
# Noetherian objects in `FGModuleCat`

Over a Noetherian ring, every finitely generated module is algebraically Noetherian. The
forgetful functor to `ModuleCat` preserves monomorphisms, reflects isomorphisms, and therefore
detects the categorical ascending-chain condition.
-/

universe u

open CategoryTheory

namespace FGModuleCat

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Every finitely generated module over a Noetherian ring is a Noetherian object. -/
instance isNoetherianObject (M : FGModuleCat.{u} R) : IsNoetherianObject M := by
  letI : Module.Finite R M := M.property
  have hM : IsNoetherianObject (ModuleCat.of R M) := inferInstance
  letI : IsNoetherianObject
      ((forget₂ (FGModuleCat R) (ModuleCat R)).obj M) := hM
  exact CategoryTheory.isNoetherianObject_of_reflectsIsomorphisms
    (forget₂ (FGModuleCat R) (ModuleCat R))

end FGModuleCat
