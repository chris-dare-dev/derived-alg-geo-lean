/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional

/-!
# Degree-zero cohomology and linear global sections

For a scheme over a field, global sections of a module sheaf carry the canonical base-field
action obtained from the structure morphism. This file packages that module and proves that
Mathlib's derived-functor `H⁰` comparison is linear for the canonical cohomology action.

The resulting linear equivalence is the transport step needed to turn finite-dimensional
coherent `H⁰` into finite-dimensional global sections. It assumes no projectivity, coherence, or
finiteness theorem itself.

## Main results

* `linearGlobalSectionsObj` packages sections over `⊤` as a `k`-module;
* `coherentHZeroSectionsLinearEquiv` is the canonical linear `H⁰`/sections comparison;
* `module_finite_linearGlobalSectionsObj` transports module-finiteness across it.
-/

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]

/-- The base-field module structure on global sections induced by the structure morphism. -/
@[reducible]
noncomputable def globalSectionsModule (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] (M : Y.Modules) :
    Module k Γ(M, (⊤ : Y.Opens)) :=
  Module.compHom _ (baseFieldToGlobalSections Y)

/-- Global sections over `⊤`, packaged with their canonical base-field module structure. -/
noncomputable def linearGlobalSectionsObj (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] (M : Y.Modules) : ModuleCat.{u} k :=
  letI := globalSectionsModule (k := k) Y M
  ModuleCat.of k Γ(M, (⊤ : Y.Opens))

set_option maxHeartbeats 800000 in
/-- The canonical additive equivalence between coherent `H⁰` and sections over `⊤`. -/
noncomputable def coherentHZeroSectionsAddEquiv (Y : Scheme.{u}) (F : Coh Y) :
    (coherentH Y 0).obj F ≃+ Γ(F.obj, (⊤ : Y.Opens)) :=
  @Sheaf.H.equiv₀ Y.Opens _ (Opens.grothendieckTopology Y) inferInstance
    (HasExt.standard _) ((Scheme.Modules.toSheaf Y).obj ((Coh.ι Y).obj F))
    (⊤ : Y.Opens) isTerminalTop

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero cohomology/sections comparison is natural in the coherent sheaf. -/
theorem coherentHZeroSectionsAddEquiv_naturality (Y : Scheme.{u})
    {F G : Coh Y} (f : F ⟶ G) (x : (coherentH Y 0).obj F) :
    (((Coh.ι Y).map f).val.app (op (⊤ : Y.Opens))).hom
        (coherentHZeroSectionsAddEquiv Y F x) =
      coherentHZeroSectionsAddEquiv Y G ((coherentH Y 0).map f x) := by
  exact @Sheaf.H.equiv₀_naturality Y.Opens _
    (Opens.grothendieckTopology Y) inferInstance (HasExt.standard _)
    (⊤ : Y.Opens) isTerminalTop
    ((Scheme.Modules.toSheaf Y).obj ((Coh.ι Y).obj F))
    ((Scheme.Modules.toSheaf Y).obj ((Coh.ι Y).obj G))
    ((Scheme.Modules.toSheaf Y).map ((Coh.ι Y).map f)) x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero cohomology/sections comparison respects the canonical base-field actions. -/
theorem coherentHZeroSectionsAddEquiv_smul (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] (F : Coh Y) (r : k)
    (x : (linearCoherentH k Y 0).obj F) :
    (show linearGlobalSectionsObj (k := k) Y ((Coh.ι Y).obj F) from
      coherentHZeroSectionsAddEquiv Y F (r • x)) =
      r • (show linearGlobalSectionsObj (k := k) Y ((Coh.ι Y).obj F) from
        coherentHZeroSectionsAddEquiv Y F x) := by
  change coherentHZeroSectionsAddEquiv Y F
      ((coherentH Y 0).map (coherentScalarAction Y F r) x) =
    baseFieldToGlobalSections Y r • coherentHZeroSectionsAddEquiv Y F x
  rw [← coherentHZeroSectionsAddEquiv_naturality Y (coherentScalarAction Y F r) x]
  change ((globalSectionSmul ((Coh.ι Y).obj F) (baseFieldToGlobalSections Y r)).val.app
      (op (⊤ : Y.Opens))).hom (coherentHZeroSectionsAddEquiv Y F x) = _
  rw [globalSectionSmul_app]
  have hres : Y.presheaf.map
      (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top)).op
        (baseFieldToGlobalSections Y r) = baseFieldToGlobalSections Y r := by
    rw [show (homOfLE (show (⊤ : Y.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : Y.Opens)) from Subsingleton.elim _ _]
    simp
  rw [hres]

/-- The canonical `H⁰`/global-sections comparison as a base-field linear equivalence. -/
noncomputable def coherentHZeroSectionsLinearEquiv (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] (F : Coh Y) :
    (linearCoherentH k Y 0).obj F ≃ₗ[k]
      linearGlobalSectionsObj (k := k) Y ((Coh.ι Y).obj F) where
  toFun := coherentHZeroSectionsAddEquiv Y F
  invFun := (coherentHZeroSectionsAddEquiv Y F).symm
  left_inv := (coherentHZeroSectionsAddEquiv Y F).left_inv
  right_inv := (coherentHZeroSectionsAddEquiv Y F).right_inv
  map_add' := (coherentHZeroSectionsAddEquiv Y F).map_add
  map_smul' := coherentHZeroSectionsAddEquiv_smul Y F

/-- Finite-dimensional coherent `H⁰` implies finite-dimensional global sections. -/
theorem module_finite_linearGlobalSectionsObj (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of k))] (F : Coh Y)
    (h : Module.Finite k ((linearCoherentH k Y 0).obj F)) :
    Module.Finite k (linearGlobalSectionsObj (k := k) Y ((Coh.ι Y).obj F)) := by
  letI := h
  exact Module.Finite.equiv (coherentHZeroSectionsLinearEquiv Y F)

end AlgebraicGeometry.Cohomology
