/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.Zariski
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Pullback
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty

/-!
# Quasi-coherent module sheaves form a Zariski substack

Quasi-coherence is a property of objects of `modulesPseudofunctor` that is stable under
pullback along every morphism of schemes and is local for the big Zariski topology. So the full
sub-pseudofunctor `qcohPseudofunctor` of quasi-coherent module sheaves is a stack for the big
Zariski topology.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.quasicoherentProperty`: quasi-coherence, as a property of
  objects of `modulesPseudofunctor`.
* `AlgebraicGeometry.Scheme.qcohPseudofunctor`: quasi-coherent module sheaves with pullback.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_cover`: a module sheaf is quasi-coherent
  when its pullbacks along a jointly surjective family of open immersions are.
* `AlgebraicGeometry.Scheme.qcohPseudofunctor_isStack_zariskiTopology`: quasi-coherent module
  sheaves glue along Zariski covers.

## Implementation notes

Stability under pullback is `Scheme.Modules.isQuasicoherent_pullback`
([Stacks, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)). Locality passes from pullback to
restriction along each open immersion of the cover by `restrictFunctorIsoPullback`, then to the
slice over its range by `Scheme.Hom.isQuasicoherent_over_of_restrict`, and concludes with
Mathlib's `SheafOfModules.IsQuasicoherent.of_coversTop`. The stack property is then the substack
theorem `Pseudofunctor.ObjectProperty.isStack_fullsubcategory` applied to
`modulesPseudofunctor_isStack`.

## References

* [Stacks, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG): Modules, Lemma 17.10.4.
* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU): substacks cut out by local
  properties.

## Tags

quasi-coherent sheaf, Zariski topology, descent, stack
-/

open CategoryTheory Bicategory

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

/-- Quasi-coherence, as a property of objects of `modulesPseudofunctor`. -/
def quasicoherentProperty : modulesPseudofunctor.{u}.ObjectProperty where
  prop X := SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf

instance : quasicoherentProperty.{u}.IsClosedUnderMapObj where
  map_obj {_ _} M hM f := isQuasicoherent_pullback f.as.unop M hM

instance : quasicoherentProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := inferInstanceAs
    (SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).IsClosedUnderIsomorphisms

/-- A module sheaf is quasi-coherent when its pullbacks along a jointly surjective family of open
immersions are. -/
theorem isQuasicoherent_of_cover {S : Scheme.{u}} (M : S.Modules) {ι : Type u}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (h : ∀ i, ((pullback (f i)).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  have (i : ι) : (M.over (f i).opensRange).IsQuasicoherent :=
    (f i).isQuasicoherent_over_of_restrict M <| by
      have hi : SheafOfModules.isQuasicoherent (X i).ringCatSheaf ((pullback (f i)).obj M) := h i
      exact (SheafOfModules.isQuasicoherent (X i).ringCatSheaf).prop_of_iso
        ((restrictFunctorIsoPullback (f i)).app M).symm hi
  exact SheafOfModules.IsQuasicoherent.of_coversTop M (fun i ↦ (f i).opensRange)
    (TopCat.Opens.grothendieckTopology_coversTop _ hf)

instance : quasicoherentProperty.{u}.IsLocal zariskiTopology where
  of_sieve {S} M R hR h := by
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, h𝒰⟩ := hR
    have := 𝒰.map_prop
    exact isQuasicoherent_of_cover M 𝒰.f (OpenCover.iSup_opensRange 𝒰) fun j ↦
      h (𝒰.f j) (h𝒰 _ _ (Presieve.ofArrows.mk j))

end Modules

/-- Quasi-coherent module sheaves on schemes, with pullback. Its fibre over `X` is
`(SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory`, the codomain of Mathlib's
`tildeEquiv` when `X` is affine. -/
noncomputable abbrev qcohPseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  Modules.quasicoherentProperty.fullsubcategory

/-- Quasi-coherent module sheaves glue along Zariski covers: `qcohPseudofunctor` is a stack for
the big Zariski topology, as a substack of `modulesPseudofunctor` cut out by a local property. -/
instance qcohPseudofunctor_isStack_zariskiTopology :
    qcohPseudofunctor.{u}.IsStack zariskiTopology :=
  Pseudofunctor.ObjectProperty.isStack_fullsubcategory _

end AlgebraicGeometry.Scheme
