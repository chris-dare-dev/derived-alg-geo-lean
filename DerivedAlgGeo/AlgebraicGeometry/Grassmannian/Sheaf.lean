/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Grassmannian.Functor
import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Descent
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# The Grassmannian functor is a Zariski sheaf

`AlgebraicGeometry.Grassmannian.functor n k` is a sheaf of sets for the big Zariski topology
on schemes: a compatible family of rank-`k` quotients of `𝒪^n` on the members of an open cover
glues to a unique rank-`k` quotient of `𝒪^n` on the base.

## Main results

* `AlgebraicGeometry.Grassmannian.isSheaf`: the Zariski sheaf property.

## Implementation notes

For a cover by open immersions indexed in `Type u`, a point of `functor n k` on a member is the
class of a quotient `𝒪^n ↠ Q` with `Q` locally free of rank `k`. A compatible family of points
is a family of quotients that are isomorphic as quotients on every test object mapping to two
members compatibly (`Presieve.isSheafFor_arrows_iff`). `ModuleQuotient.exists_glue` glues the
quotients, the glued target is locally free of rank `k` because that is local for the Zariski
topology (`Scheme.Modules.isLocallyFreeOfRank_of_cover`), and
`ModuleQuotient.nonempty_iso_of_freePullback_iso` gives uniqueness. Covers are taken indexed in
`Type u` (`Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small`), which
is what products of module sheaves need.

## References

* [Stacks, Tag 089R](https://stacks.math.columbia.edu/tag/089R): the Grassmannian of a module.

## Tags

Grassmannian, Zariski sheaf, descent, quotient
-/

open CategoryTheory Opposite SheafOfModules Limits

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

noncomputable section

variable (n k : ℕ)

/-- **The Grassmannian functor is a Zariski sheaf.** A compatible family of rank-`k` quotients
of `𝒪^n` on the members of an open cover glues uniquely. -/
theorem isSheaf : Presheaf.IsSheaf Scheme.zariskiTopology (functor.{u} n k) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro T (𝒰 : Scheme.OpenCover.{u} T)
  have := 𝒰.map_prop
  have hf : ⨆ i, (𝒰.f i).opensRange = ⊤ := Scheme.OpenCover.iSup_opensRange 𝒰
  rw [PreZeroHypercover.presieve₀, Presieve.isSheafFor_arrows_iff]
  intro x hx
  choose q hq hxq using fun i ↦ exists_eq_point (x i)
  have hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i₁ i₂ : 𝒰.I₀⦄ (g₁ : Y ⟶ 𝒰.X i₁) (g₂ : Y ⟶ 𝒰.X i₂),
      g₁ ≫ 𝒰.f i₁ = g₂ ≫ 𝒰.f i₂ →
      Nonempty (ModuleQuotient.freePullback (ULift.{u} (Fin n)) g₁ (q i₁) ≅
        ModuleQuotient.freePullback (ULift.{u} (Fin n)) g₂ (q i₂)) := by
    intro Y i₁ i₂ g₁ g₂ hg
    have h := hx i₁ i₂ Y g₁ g₂ hg
    rw [hxq i₁, hxq i₂, functor_map_point, functor_map_point, point_eq_point_iff] at h
    exact h
  obtain ⟨Q, hQ⟩ := ModuleQuotient.exists_glue 𝒰.f q hcompat hf
  have hQk : pointProperty n k T Q := isLocallyFreeOfRank_of_cover Q.target 𝒰.f hf fun i ↦
    (hq i).ofIso ((ModuleQuotient.targetFunctor _).mapIso (hQ i).some).symm
  refine ⟨point Q hQk, fun i ↦ ?_, fun y hy ↦ ?_⟩
  · rw [functor_map_point, hxq i, point_eq_point_iff]
    exact hQ i
  · obtain ⟨Q', hQ', rfl⟩ := exists_eq_point y
    rw [point_eq_point_iff]
    refine ModuleQuotient.nonempty_iso_of_freePullback_iso 𝒰.f hf fun i ↦ ?_
    have h := hy i
    rw [functor_map_point, hxq i, point_eq_point_iff] at h
    exact ⟨h.some ≪≫ (hQ i).some.symm⟩

end

end AlgebraicGeometry.Grassmannian
