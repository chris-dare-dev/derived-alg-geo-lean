/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Affine
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Iso
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coherent pushforward along a closed immersion

`isCoherent_pushforward` — **`#572` step 2**. For `f : X ⟶ Y` a closed immersion into a locally
Noetherian scheme and `F` coherent on `X`, the pushforward `f_* F` is coherent on `Y`.

## The three inputs, and what each was missing

Every ingredient existed before this file; none of them fitted the next one without a bridge.

* `isCoherent_pushforward_of_surjective` (`Pushforward/Affine.lean`) is the mathematics, and it is
  stated about `Spec.map φ : Spec S ⟶ Spec R` — a map **of spectra**. An affine open cover supplies
  affine **schemes**, so it could not be applied to a cover member directly.
* `pushforwardRestrictIso` (`Pushforward/BaseChange.lean`, `#812`) compares the two ways round the
  restriction square. Its own docstring says it is what step 2 *consumes*; it is not step 2.
* `isCoherent_pushforward_of_iso` (`Pushforward/Iso.lean`) closes the first gap, and is the piece
  that did not exist.

## The affine case is a factorisation, not an induction

`Scheme.isoSpec_inv_naturality` gives `f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv`, and
`Modules.pushforward` of a composite is the composite of pushforwards **by `rfl`**. So the affine
case is three steps with no glue: transport to `Spec Γ(X, ⊤)` along an isomorphism, apply the
affine theorem, transport back. `IsClosedImmersion.isAffine_surjective_of_isAffine` supplies both
the affineness of `X` and the surjectivity of `f.appTop` that the middle step needs — one call,
because for a closed immersion into an affine those two facts come together.

## The globalisation is by opens, not by an `AffineOpenCover`

`Modules.isCoherent_iff_restrict_affineOpenCover` is the obvious criterion and is *not* what this
file uses. Its members are affine schemes mapping in, and the base-change square is stated for an
open `U` and its `U.ι`; bridging the two means carrying an isomorphism `𝒰.X i ≅ U.toScheme` through
every step. Going straight to `IsFinitePresentation.of_coversTop` over `Y.affineOpens` avoids that
entirely — `Scheme.Opens.opensRange_ι` makes the slice-versus-restriction bridge a rewrite, and
`iSup_affineOpens_eq_top` is the covering hypothesis.

## Where Noetherianity enters, and where it does not

`IsLocallyNoetherian Y` is used once per chart, to see that `Γ(U.toScheme, ⊤)` is Noetherian —
through `IsLocallyNoetherian.component_noetherian`, which wants the *affine* open, and then
`U.topIso` to move from `Γ(Y, U)` to `Γ(U.toScheme, ⊤)`. Nothing else in the argument needs a
chain condition; in particular the transports along isomorphisms do not.

`X` is not assumed Noetherian, and does not need to be: a closed immersion into a locally
Noetherian scheme makes it so, but the proof never asks.

## Main definitions

* `Coh.pushforward` — the functor `f_* : Coh X ⥤ Coh Y` that `isCoherent_pushforward` makes
  available, and `Coh.pushforwardCompι`, its comparison with module-sheaf pushforward.

## Main results

* `isCoherent_pushforward_affine` — the affine case.
* `isCoherent_restrict_chart` — one chart of the globalisation.
* `isCoherent_pushforward` — `#572` step 2.
* `Coh.pushforward_preservesFiniteLimits` and `Coh.pushforward_preservesFiniteColimits` — the
  functor is exact.

## The functor, and why its exactness is reflected rather than proved

`Coh.pushforward` is module-sheaf pushforward restricted to coherent sheaves, a lift of
`Coh.ι X ⋙ Modules.pushforward f` through `Coh.ι Y`.  Its exactness is not a new argument: the
composite `Coh.ι X ⋙ Modules.pushforward f` preserves finite limits (pushforward is a right
adjoint) and finite colimits (`pushforward_preservesFiniteColimits_of_isClosedImmersion`, the
closed-embedding argument), and `Coh.ι Y` is fully faithful, so it reflects both.  The same
inclusion is faithful, so additivity is reflected the same way.  The derived direct image on
`Dᵇ(Coh)` in `DerivedCategory/Families/CoherentPushforward.lean` is built from this functor.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The affine case.** A closed immersion into an affine scheme with Noetherian coordinate ring
pushes coherent sheaves to coherent sheaves.

The three factors of `f` are handled in order and the composite is recognised at the end by
`isoSpec_inv_naturality`; `Modules.pushforward` of a composite is the composite of pushforwards by
`rfl`, so no comparison isomorphism appears. -/
theorem isCoherent_pushforward_affine [IsAffine Y] [IsClosedImmersion f]
    [IsNoetherianRing Γ(Y, ⊤)] (M : X.Modules) (hM : Modules.IsCoherent X M) :
    Modules.IsCoherent Y ((Modules.pushforward f).obj M) := by
  obtain ⟨hXaff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  haveI := hXaff
  have h1 : Modules.IsCoherent (Spec Γ(X, ⊤)) ((Modules.pushforward X.isoSpec.hom).obj M) :=
    Modules.isCoherent_pushforward_of_iso X.isoSpec M hM
  have h2 := isCoherent_pushforward_of_surjective f.appTop hsurj _ h1
  have h3 := Modules.isCoherent_pushforward_of_iso Y.isoSpec.symm _ h2
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.symm.hom = f := by
    rw [Iso.symm_hom, Scheme.isoSpec_inv_naturality f, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [← hf]
  exact h3

/-- **One chart.** Over an affine open `U` of `Y`, the restriction of `f_* M` is finitely
presented.

This is where `pushforwardRestrictIso` is spent: it turns the restriction of a pushforward into
the pushforward of a restriction, and the latter is the affine case applied to `f ∣_ U`, which is
again a closed immersion. -/
theorem isCoherent_restrict_chart [IsLocallyNoetherian Y] [IsClosedImmersion f]
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

/-- **`#572` step 2: coherence is preserved by pushforward along a closed immersion.**

The affine opens cover `Y`, and finite presentation descends along a covering family; each chart is
`isCoherent_restrict_chart`. -/
theorem isCoherent_pushforward [IsLocallyNoetherian Y] [IsClosedImmersion f]
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsClosedImmersion f]

/-- Pushforward of coherent sheaves along a closed immersion, `f_* : Coh X ⥤ Coh Y`.

It is module-sheaf pushforward restricted to coherent sheaves, which lands in coherent sheaves by
`Scheme.isCoherent_pushforward`.  The closed-immersion hypothesis buys two things at once:
coherence of the image, and exactness of pushforward on *all* module sheaves.  Along a finite
morphism `f_*` is still exact on coherent sheaves and still coherent, but neither is proved in
this repository yet; a contract on scheme base changes
(`SchemeBaseChange.HasCoherentPushforward`) is where a finite-morphism instance would go. -/
noncomputable def pushforward : Coh X ⥤ Coh Y :=
  (Scheme.coherent Y).lift (ι X ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ Scheme.isCoherent_pushforward f M.obj M.property)

/-- Forgetting coherence after coherent pushforward is module-sheaf pushforward after forgetting
coherence.  Definitional, since `ObjectProperty.liftCompιIso` is `Iso.refl`; recorded because a
contract consuming `Coh.pushforward` asks for the comparison as data. -/
noncomputable def pushforwardCompι :
    pushforward f ⋙ ι Y ≅ ι X ⋙ Scheme.Modules.pushforward f :=
  (Scheme.coherent Y).liftCompιIso _ _

/-- Coherent pushforward along a closed immersion preserves finite limits.  Reflected through the
fully faithful `Coh.ι Y` from the composite `Coh.ι X ⋙ Modules.pushforward f`, where pushforward
is a right adjoint; `X` must be locally Noetherian for `Coh.ι X` to be left exact. -/
instance pushforward_preservesFiniteLimits [IsLocallyNoetherian X] :
    PreservesFiniteLimits (pushforward f) :=
  haveI : PreservesFiniteLimits (pushforward f ⋙ ι Y) := by
    change PreservesFiniteLimits (ι X ⋙ Scheme.Modules.pushforward f)
    infer_instance
  preservesFiniteLimits_of_reflects_of_preserves (pushforward f) (ι Y)

/-- Coherent pushforward along a closed immersion preserves finite colimits.  This is where the
closed-immersion hypothesis is spent: module-sheaf pushforward is right exact along a closed
embedding (`pushforward_preservesFiniteColimits_of_isClosedImmersion`), and `Coh.ι Y` reflects
it. -/
instance pushforward_preservesFiniteColimits [IsLocallyNoetherian X] :
    PreservesFiniteColimits (pushforward f) :=
  haveI : PreservesFiniteColimits (pushforward f ⋙ ι Y) := by
    change PreservesFiniteColimits (ι X ⋙ Scheme.Modules.pushforward f)
    infer_instance
  preservesFiniteColimits_of_reflects_of_preserves (pushforward f) (ι Y)

/-- Coherent pushforward along a closed immersion is additive, reflected through the faithful
additive inclusion `Coh.ι Y`.  Needed by `Functor.mapDerivedCategory`, which asks for additivity
separately from exactness. -/
instance pushforward_additive : (pushforward f).Additive :=
  haveI : (pushforward f ⋙ ι Y).Additive := by
    change (ι X ⋙ Scheme.Modules.pushforward f).Additive
    infer_instance
  Functor.additive_of_comp_faithful (pushforward f) (ι Y)

end AlgebraicGeometry.Coh
