/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Restriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherent pullback along a morphism of schemes

Pullback of module sheaves along any morphism of schemes preserves finite presentation, hence
coherence.  This file proves it and packages the result as the functor
`Coh.pullback f : Coh Y ⥤ Coh X`, with its exactness: right exact always, left exact when
module-sheaf pullback is, which flatness supplies.

## Main definitions

* `Scheme.Modules.pullbackPresentationOver`: a presentation of `M` on `U` pulled back to a
  presentation of `f⁺ M` on `f⁻¹ U`.
* `Coh.pullback`: the functor `f^* : Coh Y ⥤ Coh X`, with `Coh.pullbackCompι`, its comparison
  with module-sheaf pullback.

## Main results

* `Scheme.Modules.isFinitePresentation_pullback` and `Scheme.Modules.isCoherent_pullback`:
  pullback preserves finite presentation and coherence, along every morphism;
  `Scheme.Modules.isFinite_pullbackPresentationOver` is the chart-level statement.
* `Coh.pullback_preservesFiniteColimits`, `Coh.pullback_preservesFiniteLimits`, and
  `Coh.pullback_additive`: the functor is right exact, left exact when module-sheaf pullback is,
  and additive.

## The argument

A finitely presented sheaf is locally the cokernel of a map of finite free sheaves; pullback is
right exact and sends free sheaves to free sheaves, so the cokernel presentation pulls back to a
presentation on the preimage open.  Mathlib's `Presentation.map` does that transport for a
colimit-preserving functor that fixes the structure sheaf; the functor here is pullback on
slices, `pullbackOverFunctor`, whose colimit preservation and structure-sheaf identification
are `pullbackOverFunctor_preservesColimits` and `pullbackOverUnitIso`.  The restriction square
`pullbackOverIso` then moves the presentation onto `(f⁺ M).over (f ⁻¹ᵁ U)`, and the preimages
of a cover of `Y` cover `X` (`Scheme.Hom.coversTop_preimage`).

## Implementation notes

Two things about the proof are deliberate.  Finiteness of the transported presentation is
proved from the index types, which `Presentation.map` and `Presentation.ofIsIso` leave
unchanged.  The designated route, `Presentation.isFinite_map` supplied by `haveI` and the
`ofIsIso` instance asked for by `inferInstanceAs`, fails to synthesize here, for the reason
`Algebra/Category/ModuleCat/Sheaf/Presentation/Finite.lean` records: the universe parameters
of these classes are not pinned by the goal and default to `0`.  And the quasi-coherent data
of the pullback is a local definition inside the one proof that consumes it, with the
universes of its finiteness written out and the class built field by field rather than by an
anonymous constructor: naming the data globally and restating the finiteness of its
projections makes Lean re-check instance arguments of the presentation type at `whnf` and
does not terminate in the default heartbeat budget, and an anonymous constructor for either
finiteness class elaborates it at universe `0` whatever the expected type says.

## References

* Hartshorne, *Algebraic Geometry*, Proposition II.5.8(b) (pullback of a coherent sheaf;
  Hartshorne assumes `X` and `Y` noetherian, which finite presentation does not need) and
  Proposition II.5.2(e), `f^*(M~) ≅ (M ⊗_A B)~`, with II.5.2(a) and (c) for right exactness and
  direct sums, for the local model.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

/-- A presentation of `M` on `U` pulls back to a presentation of `f⁺ M` on `f⁻¹ U`: transport
along pullback on slices with its structure-sheaf identification, then across the restriction
square `pullbackOverIso`. -/
noncomputable def pullbackPresentationOver (P : (M.over U).Presentation) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation :=
  (P.map (pullbackOverFunctor f U) (pullbackOverUnitIso f U)).ofIsIso (pullbackOverIso f M U).inv

/-- The pulled-back presentation of a finite presentation is finite: neither `Presentation.map`
nor `Presentation.ofIsIso` changes the index types of generators and relations. -/
theorem isFinite_pullbackPresentationOver (P : (M.over U).Presentation)
    [hP : P.IsFinite.{u, u, u}] :
    (pullbackPresentationOver f M U P).IsFinite.{u, u, u} where
  isFiniteType_generators := ⟨by
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite⟩
  isFiniteType_relations := ⟨by
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite⟩

/-- **Pullback preserves finite presentation**, along every morphism of schemes: the cover
chosen for `M` pulls back to a cover of `X`, and each chart's presentation to
`pullbackPresentationOver`, which is finite. -/
theorem isFinitePresentation_pullback
    (hM : SheafOfModules.IsFinitePresentation.{u, u, u} M) :
    SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback f).obj M) where
  exists_quasicoherentData := by
    obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
    let σ : ((pullback f).obj M).QuasicoherentData :=
      { I := q.I
        X := fun i ↦ f ⁻¹ᵁ q.X i
        coversTop := f.coversTop_preimage q.coversTop
        presentation := fun i ↦ pullbackPresentationOver f M (q.X i) (q.presentation i) }
    have hσ : σ.IsFinitePresentation.{u, u, u, u} := by
      constructor
      intro i
      haveI : (q.presentation i).IsFinite.{u, u, u} := hq.isFinite_presentation i
      exact isFinite_pullbackPresentationOver f M (q.X i) (q.presentation i)
    exact ⟨σ, hσ⟩

/-- **Coherence is preserved by pullback** along every morphism of schemes; no Noetherian or
flatness hypothesis enters, because coherence in this repository is finite presentation. -/
theorem isCoherent_pullback (hM : Modules.IsCoherent Y M) :
    Modules.IsCoherent X ((pullback f).obj M) :=
  isFinitePresentation_pullback f M hM

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Coh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of coherent sheaves along a morphism of schemes, `f^* : Coh Y ⥤ Coh X`: module-sheaf
pullback restricted to coherent sheaves, which lands in coherent sheaves by
`Scheme.Modules.isCoherent_pullback`.  Defined for every morphism; exactness is where a
hypothesis on `f` enters. -/
noncomputable def pullback : Coh Y ⥤ Coh X :=
  (Scheme.coherent X).lift (ι Y ⋙ Scheme.Modules.pullback f)
    (fun M ↦ Scheme.Modules.isCoherent_pullback f M.obj M.property)

/-- Forgetting coherence after coherent pullback is module-sheaf pullback after forgetting
coherence.  Definitional, since `ObjectProperty.liftCompιIso` is `Iso.refl`; recorded because the
contract `HasCoherentPullback` asks for the comparison as data. -/
noncomputable def pullbackCompι : pullback f ⋙ ι X ≅ ι Y ⋙ Scheme.Modules.pullback f :=
  (Scheme.coherent X).liftCompιIso _ _

/-- Coherent pullback preserves finite colimits, for every morphism: module-sheaf pullback is a
left adjoint, `Coh.ι Y` is right exact on a locally Noetherian scheme, and the fully faithful
`Coh.ι X` reflects.  The composite instance is `comp_preservesFiniteColimits`, a lemma rather
than an instance, hence supplied by name. -/
instance pullback_preservesFiniteColimits [IsLocallyNoetherian Y] :
    PreservesFiniteColimits (pullback f) :=
  haveI : PreservesFiniteColimits (pullback f ⋙ ι X) := by
    change PreservesFiniteColimits (ι Y ⋙ Scheme.Modules.pullback f)
    exact comp_preservesFiniteColimits _ _
  preservesFiniteColimits_of_reflects_of_preserves (pullback f) (ι X)

/-- Coherent pullback preserves finite limits when module-sheaf pullback does, which is the
case for a flat morphism (proved in the families layer, `Families/FlatPullback.lean`, from
flatness of the stalk maps); `Coh.ι Y` is left exact on a locally Noetherian scheme and the
fully faithful `Coh.ι X` reflects. -/
instance pullback_preservesFiniteLimits [IsLocallyNoetherian Y]
    [PreservesFiniteLimits (Scheme.Modules.pullback f)] :
    PreservesFiniteLimits (pullback f) :=
  haveI : PreservesFiniteLimits (pullback f ⋙ ι X) := by
    change PreservesFiniteLimits (ι Y ⋙ Scheme.Modules.pullback f)
    exact comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_reflects_of_preserves (pullback f) (ι X)

/-- Coherent pullback is additive, reflected through the faithful additive inclusion `Coh.ι X`.
Needed by `Functor.mapDerivedCategory`, which asks for additivity separately from exactness. -/
instance pullback_additive : (pullback f).Additive :=
  haveI : (pullback f ⋙ ι X).Additive := by
    change (ι Y ⋙ Scheme.Modules.pullback f).Additive
    infer_instance
  Functor.additive_of_comp_faithful (pullback f) (ι X)

end AlgebraicGeometry.Coh
