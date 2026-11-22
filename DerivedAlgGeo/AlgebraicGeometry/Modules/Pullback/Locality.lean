/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Locality

/-!
# Zero objects and epimorphisms are local for pullback along open covers

A module sheaf on a scheme is zero when its pullbacks along a jointly surjective family of open
immersions are zero, and a morphism of module sheaves is an epimorphism when its pullbacks along
such a family are. This is `isZero_of_isZero_restrict` with restriction replaced by pullback,
which is how a descent datum sees a module sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_pullback`: zero is local.
* `AlgebraicGeometry.Scheme.Modules.epi_of_epi_pullback`: being an epimorphism is local.

## Implementation notes

Zero is detected on stalks. Pullback along an open immersion `f` is restriction
(`restrictFunctorIsoPullback`), and the stalk of the restriction at `y` is the stalk of the sheaf
at `f y` (`restrictStalkNatIso`). A morphism is an epimorphism when its cokernel is zero, and
pullback preserves the cokernel projection and epimorphisms.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A module sheaf on `X` is zero if its pullbacks along a jointly surjective family of open
immersions are zero. -/
theorem isZero_of_isZero_pullback {X : Scheme.{u}} (M : X.Modules) {ι : Type*}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ x, ∃ i, x ∈ Set.range (f i)) (h : ∀ i, IsZero ((pullback (f i)).obj M)) :
    IsZero M := by
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hSheaf : IsZero M' := by
    refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero M').2 fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := hf x
    have hr : IsZero (M.restrict (f i)) := (h i).of_iso ((restrictFunctorIsoPullback (f i)).app M)
    exact ((toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ y).map_isZero hr).of_iso
      ((restrictStalkNatIso (f i) y).app M).symm
  have hSheaf' : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := hSheaf
  rw [IsZero.iff_id_eq_zero]
  exact (SheafOfModules.toSheaf X.ringCatSheaf).map_injective (hSheaf'.eq_of_src _ _)

/-- A morphism of module sheaves is an epimorphism if its pullbacks along a jointly surjective
family of open immersions are. -/
theorem epi_of_epi_pullback {X : Scheme.{u}} {M N : X.Modules} (π : M ⟶ N) {ι : Type*}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ x, ∃ i, x ∈ Set.range (f i)) (h : ∀ i, Epi ((pullback (f i)).map π)) : Epi π := by
  have hz : IsZero (cokernel π) := by
    refine isZero_of_isZero_pullback _ f hf fun i ↦ ?_
    have := h i
    have h0 : (pullback (f i)).map (cokernel.π π) = 0 := by
      rw [← cancel_epi ((pullback (f i)).map π), ← Functor.map_comp, cokernel.condition,
        Functor.map_zero, comp_zero]
    exact IsZero.of_epi_eq_zero ((pullback (f i)).map (cokernel.π π)) h0
  exact Preadditive.epi_of_isZero_cokernel π hz

end AlgebraicGeometry.Scheme.Modules
