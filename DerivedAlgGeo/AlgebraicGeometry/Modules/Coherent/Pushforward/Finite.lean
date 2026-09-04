/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Affine
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Iso
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coherent pushforward along a finite morphism

For a finite morphism `f : X ⟶ Y` into a locally Noetherian scheme, `f_*` sends coherent
sheaves to coherent sheaves and is exact on them.  This file proves both and packages the
result as the functor `Coh.pushforward f : Coh X ⥤ Coh Y`, the `f_*` on coherent sheaves that
the derived direct image on `Dᵇ(Coh)` is built from.  A closed immersion is finite (Mathlib's
instance in `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`), so `#572` step 2, coherence of
`ι_* F` along a closed immersion, is the theorem `isCoherent_pushforward` here.

## Main definitions

* `Coh.pushforward`: the functor `f_* : Coh X ⥤ Coh Y` along a finite morphism, with
  `Coh.pushforwardCompι`, its comparison with module-sheaf pushforward.

## Main results

* `isCoherent_pushforward`: coherence is preserved by pushforward along a finite morphism into
  a locally Noetherian scheme; `isCoherent_pushforward_affine` and `isCoherent_restrict_chart`
  are the affine case and one chart of its globalisation.
* `Coh.pushforward_preservesFiniteLimits`, `Coh.pushforward_preservesEpimorphisms`, and
  `Coh.pushforward_preservesFiniteColimits`: the functor is exact.

## The three inputs to coherence, and what each was missing

Every ingredient existed before the closed-immersion version of this argument; none of them
fitted the next one without a bridge, and the same three bridges serve the finite case.

* `isCoherent_pushforward_of_finite` (`Pushforward/Affine.lean`) is the mathematics, and it is
  stated about `Spec.map φ : Spec S ⟶ Spec R` — a map **of spectra**.  An affine open cover
  supplies affine **schemes**, so it cannot be applied to a cover member directly.
* `pushforwardRestrictIso` (`Pushforward/BaseChange.lean`) compares the two ways round the
  restriction square.  Its own docstring says it is what the chart step *consumes*.
* `isCoherent_pushforward_of_iso` (`Pushforward/Iso.lean`) closes the first gap.

The affine case is a factorisation, not an induction: `Scheme.isoSpec_inv_naturality` gives
`f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv`, and `Modules.pushforward` of a
composite is the composite of pushforwards **by `rfl`**, so the affine case is three steps with no
glue: transport to `Spec Γ(X, ⊤)` along an isomorphism, apply the affine theorem, transport back.
`isAffine_of_isAffineHom` supplies affineness of `X` and `Scheme.Hom.finite_appTop` finiteness of
the coordinate-ring map, the two facts a closed immersion used to supply as affineness and
surjectivity.

The globalisation is by opens, not by an `AffineOpenCover`:
`Modules.isCoherent_iff_restrict_affineOpenCover` is the obvious criterion and is *not* what this
file uses.  Its members are affine schemes mapping in, and the base-change square is stated for an
open `U` and its `U.ι`; going straight to `IsFinitePresentation.of_coversTop` over `Y.affineOpens`
avoids carrying an isomorphism `𝒰.X i ≅ U.toScheme` through every step, with
`Scheme.Opens.opensRange_ι` as the slice-versus-restriction bridge and `iSup_affineOpens_eq_top`
as the covering hypothesis.

`IsLocallyNoetherian Y` is used once per chart, to see that `Γ(U.toScheme, ⊤)` is Noetherian;
`X` is not assumed Noetherian for coherence and does not need to be.  The two spellings
`_of_finite` (a ring map, `RingHom.Finite`) and `IsFinite f` (a morphism of schemes) both occur
in this directory and follow Mathlib's naming of the two notions.

## Exactness

Exactness is where finite morphisms differ from closed immersions.  Pushforward along a closed
immersion is exact on every module sheaf; along a finite morphism it is exact only on
quasi-coherent sheaves, so `Coh.pushforward_preservesFiniteColimits` cannot be reflected from
the ambient functor.  Instead, left exactness is reflected through `Coh.ι` from pushforward
being a right adjoint, and right exactness comes from preservation of epimorphisms, which is
`pushforward_map_epi_of_isAffineHom` on the underlying quasi-coherent sheaves, reflected
through `Coh.ι`; `preservesHomology_of_preservesEpis_and_kernels` then gives finite colimits.

## References

* Hartshorne, *Algebraic Geometry*, Exercise II.5.5(c) (pushforward of a coherent sheaf along a
  finite morphism is coherent) and Exercise II.5.17(b), (e).
* arXiv:2607.28411v1, Definition 3.1 and Proposition 3.3, which use `f_*` along finite
  morphisms.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The affine case.** A finite morphism into an affine scheme with Noetherian coordinate
ring pushes coherent sheaves to coherent sheaves.  `f` is factored through `Spec.map f.appTop`
by `isoSpec_inv_naturality`; the source is affine because `f` is an affine morphism, and
`f.appTop` is a finite ring map because `f` is finite (`Scheme.Hom.finite_appTop`). -/
theorem isCoherent_pushforward_affine [IsAffine Y] [IsFinite f]
    [IsNoetherianRing Γ(Y, ⊤)] (M : X.Modules) (hM : Modules.IsCoherent X M) :
    Modules.IsCoherent Y ((Modules.pushforward f).obj M) := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  have h1 : Modules.IsCoherent (Spec Γ(X, ⊤)) ((Modules.pushforward X.isoSpec.hom).obj M) :=
    Modules.isCoherent_pushforward_of_iso X.isoSpec M hM
  have h2 := isCoherent_pushforward_of_finite f.appTop f.finite_appTop _ h1
  have h3 := Modules.isCoherent_pushforward_of_iso Y.isoSpec.symm _ h2
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.symm.hom = f := by
    rw [Iso.symm_hom, Scheme.isoSpec_inv_naturality f, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [← hf]
  exact h3

/-- **One chart.** Over an affine open `U` of `Y`, the restriction of `f_* M` is finitely
presented: `pushforwardRestrictIso` turns the restriction of a pushforward into the pushforward
of a restriction along `f ∣_ U`, which is again finite, and the affine case applies. -/
theorem isCoherent_restrict_chart [IsLocallyNoetherian Y] [IsFinite f]
    (M : X.Modules) (hM : Modules.IsCoherent X M)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (((Modules.pushforward f).obj M).restrict U.ι) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsNoetherianRing Γ(U.toScheme, ⊤) := by
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact isNoetherianRing_of_ringEquiv _ (U.topIso).commRingCatIsoToRingEquiv.symm
  have hres : Modules.IsCoherent (f ⁻¹ᵁ U).toScheme (M.restrict (f ⁻¹ᵁ U).ι) :=
    Modules.IsCoherent.restrict_of_isOpenImmersion (f ⁻¹ᵁ U).ι M hM
  have hpush := isCoherent_pushforward_affine (f ∣_ U) _ hres
  exact (Scheme.coherent U.toScheme).prop_of_iso
    (AlgebraicGeometry.pushforwardRestrictIso f U M).symm hpush

/-- **Coherence is preserved by pushforward along a finite morphism** into a locally Noetherian
scheme; for a closed immersion this is `#572` step 2.  The affine opens cover `Y`, and finite
presentation descends along a covering family; each chart is `isCoherent_restrict_chart`. -/
theorem isCoherent_pushforward [IsLocallyNoetherian Y] [IsFinite f]
    (M : X.Modules) (hM : Modules.IsCoherent X M) :
    Modules.IsCoherent Y ((Modules.pushforward f).obj M) := by
  refine SheafOfModules.IsFinitePresentation.of_coversTop
    (M := (Modules.pushforward f).obj M)
    (X := fun i : Y.affineOpens => (i : Y.Opens)) ?_ ?_
  · apply TopCat.Opens.grothendieckTopology_coversTop
    exact AlgebraicGeometry.iSup_affineOpens_eq_top Y
  · intro i
    rw [← Scheme.Opens.opensRange_ι (i : Y.Opens)]
    rw [(i : Y.Opens).ι.isFinitePresentation_over_iff_restrict]
    exact isCoherent_restrict_chart f M hM (i : Y.Opens) i.2

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Coh

open Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsFinite f]

/-- Pushforward of coherent sheaves along a finite morphism, `f_* : Coh X ⥤ Coh Y`.

It is module-sheaf pushforward restricted to coherent sheaves, which lands in coherent sheaves
by `Scheme.isCoherent_pushforward`.  Finiteness of `f` buys both coherence of the image and,
through affineness, exactness on quasi-coherent sheaves.  A proper morphism that is not finite
still preserves coherence (Grothendieck's finiteness theorem, Hartshorne III.8.8), but its `f_*`
is not exact, so the functor the paper wants on `Dᵇ(Coh)` is the derived `Rf_*`, which the
repository does not own. -/
noncomputable def pushforward : Coh X ⥤ Coh Y :=
  (Scheme.coherent Y).lift (ι X ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ Scheme.isCoherent_pushforward f M.obj M.property)

/-- Forgetting coherence after coherent pushforward is module-sheaf pushforward after forgetting
coherence.  Definitional, since `ObjectProperty.liftCompιIso` is `Iso.refl`; recorded because a
contract consuming `Coh.pushforward` asks for the comparison as data. -/
noncomputable def pushforwardCompι :
    pushforward f ⋙ ι Y ≅ ι X ⋙ Scheme.Modules.pushforward f :=
  (Scheme.coherent Y).liftCompιIso _ _

/-- Coherent pushforward along a finite morphism preserves finite limits.  Reflected through the
fully faithful `Coh.ι Y` from the composite `Coh.ι X ⋙ Modules.pushforward f`, where pushforward
is a right adjoint; `X` must be locally Noetherian for `Coh.ι X` to be left exact.  The composite
instance is `comp_preservesFiniteLimits`, a lemma rather than an instance, hence supplied by
name. -/
instance pushforward_preservesFiniteLimits [IsLocallyNoetherian X] :
    PreservesFiniteLimits (pushforward f) :=
  haveI : PreservesFiniteLimits (pushforward f ⋙ ι Y) := by
    change PreservesFiniteLimits (ι X ⋙ Scheme.Modules.pushforward f)
    exact comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_reflects_of_preserves (pushforward f) (ι Y)

/-- Coherent pushforward along a finite morphism is additive, reflected through the faithful
additive inclusion `Coh.ι Y`.  Needed by `Functor.mapDerivedCategory`, which asks for additivity
separately from exactness. -/
instance pushforward_additive : (pushforward f).Additive :=
  haveI : (pushforward f ⋙ ι Y).Additive := by
    change (ι X ⋙ Scheme.Modules.pushforward f).Additive
    infer_instance
  Functor.additive_of_comp_faithful (pushforward f) (ι Y)

/-- Coherent pushforward along a finite morphism preserves epimorphisms.  This is where
finiteness, through affineness, is spent on exactness: an epimorphism of coherent sheaves is an
epimorphism of the underlying quasi-coherent sheaves, `pushforward_map_epi_of_isAffineHom`
pushes it forward, and `Coh.ι Y` reflects it.  The finite-presentation instances are stated on
`(ι X).obj M`, the spelling the goal carries, because `Coh.ι` is a `def` that instance search
does not unfold. -/
instance pushforward_preservesEpimorphisms [IsLocallyNoetherian X] :
    (pushforward f).PreservesEpimorphisms where
  preserves {M N} u _ := by
    haveI : (ι X).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape (ι X)
    haveI : Epi ((ι X).map u) := (ι X).map_epi u
    haveI : SheafOfModules.IsFinitePresentation.{u, u, u} ((ι X).obj M) := M.property
    haveI : SheafOfModules.IsFinitePresentation.{u, u, u} ((ι X).obj N) := N.property
    apply (ι Y).epi_of_epi_map
    change Epi ((Scheme.Modules.pushforward f).map ((ι X).map u))
    exact Scheme.Modules.pushforward_map_epi_of_isAffineHom f ((ι X).map u)

/-- Coherent pushforward along a finite morphism preserves finite colimits: it preserves kernels
and epimorphisms, hence homology, hence finite colimits. -/
instance pushforward_preservesFiniteColimits [IsLocallyNoetherian X] :
    PreservesFiniteColimits (pushforward f) :=
  haveI : (pushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  Functor.preservesFiniteColimits_of_preservesHomology _

end AlgebraicGeometry.Coh
