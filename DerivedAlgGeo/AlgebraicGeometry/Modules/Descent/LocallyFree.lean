/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.Zariski
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.LocallyFree
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop

/-!
# Local freeness of a fixed rank is local for the Zariski topology

Local freeness of rank `r` of a module sheaf is stable under pullback along every morphism of
schemes (`isLocallyFreeOfRank_pullback`) and descends along a jointly surjective family of open
immersions. So it is a local property of objects of `modulesPseudofunctor` for the big Zariski
topology.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.locallyFreeOfRankProperty`: local freeness of rank `r`, as a
  property of objects of `modulesPseudofunctor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_of_cover`: a module sheaf is locally
  free of rank `r` when its pullbacks along a jointly surjective family of open immersions are.
* `AlgebraicGeometry.Scheme.Modules.locallyFreeOfRankProperty.IsLocal`: the property is local
  for `zariskiTopology`.

## Implementation notes

The argument is that of `isQuasicoherent_of_cover`: pullback along an open immersion is
restriction (`restrictFunctorIsoPullback`), restriction to the source of an open immersion gives
the slice over its range (`Scheme.Hom.isLocallyFreeOfRank_over_of_restrict`), and slices over
the members of a cover glue (`SheafOfModules.IsLocallyFreeOfRank.of_coversTop`).
-/

open CategoryTheory Bicategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A module sheaf is locally free of rank `r` when its pullbacks along a jointly surjective
family of open immersions are. -/
theorem isLocallyFreeOfRank_of_cover {S : Scheme.{u}} (M : S.Modules) {ι : Type u}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) {r : ℕ}
    (h : ∀ i, SheafOfModules.IsLocallyFreeOfRank.{u, u, u}
      (show SheafOfModules (X i).ringCatSheaf from (pullback (f i)).obj M) r) :
    SheafOfModules.IsLocallyFreeOfRank.{u, u, u}
      (show SheafOfModules S.ringCatSheaf from M) r := by
  refine SheafOfModules.IsLocallyFreeOfRank.of_coversTop M (fun i ↦ (f i).opensRange)
    (TopCat.Opens.grothendieckTopology_coversTop _ hf) fun i ↦ ?_
  exact (f i).isLocallyFreeOfRank_over_of_restrict M
    ((h i).ofIso ((restrictFunctorIsoPullback (f i)).app M).symm)

/-- Local freeness of rank `r`, as a property of objects of `modulesPseudofunctor`. -/
def locallyFreeOfRankProperty (r : ℕ) : modulesPseudofunctor.{u}.ObjectProperty where
  prop _ := fun M ↦ SheafOfModules.IsLocallyFreeOfRank.{u, u, u} M r

instance (r : ℕ) : (locallyFreeOfRankProperty.{u} r).IsClosedUnderMapObj where
  map_obj {_ _} M hM f := isLocallyFreeOfRank_pullback f.as.unop M hM

instance (r : ℕ) : (locallyFreeOfRankProperty.{u} r).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms _ :=
    { of_iso e h := SheafOfModules.IsLocallyFreeOfRank.ofIso.{u, u, u} h e }

instance (r : ℕ) : (locallyFreeOfRankProperty.{u} r).IsLocal zariskiTopology where
  of_sieve {S} M R hR h := by
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, h𝒰⟩ := hR
    have := 𝒰.map_prop
    exact isLocallyFreeOfRank_of_cover M 𝒰.f (OpenCover.iSup_opensRange 𝒰) fun j ↦
      h (𝒰.f j) (h𝒰 _ _ (Presieve.ofArrows.mk j))

end AlgebraicGeometry.Scheme.Modules
