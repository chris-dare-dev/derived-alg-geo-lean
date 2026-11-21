/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.EssentiallyOfFiniteType
import DerivedAlgGeo.AlgebraicGeometry.ResidueField
import DerivedAlgGeo.RingTheory.Nagata
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Nagata and universally Japanese schemes

A scheme is *universally Japanese* (resp. *Nagata*) if the ring of sections over every affine
open is universally Japanese (resp. Nagata). Both properties are affine-local (Stacks 033W,
033X), and universally Japanese ascends along morphisms locally of finite type.

## Main definitions

* `AlgebraicGeometry.Scheme.IsUniversallyJapanese`: Stacks 033S.
* `AlgebraicGeometry.Scheme.IsNagata`: Stacks 033S.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyJapanese_of_affine_cover`: Stacks 033W.
* `AlgebraicGeometry.Scheme.isNagata_of_affine_cover`: Stacks 033X.
* `AlgebraicGeometry.Scheme.IsUniversallyJapanese.of_locallyOfFiniteType`: universally Japanese
  ascends along morphisms locally of finite type.
* `AlgebraicGeometry.exists_dvr_of_specializes`: BLMNPS Lemma 11.19.

## Implementation notes

Nagata's theorem that a Nagata scheme is universally Japanese (Stacks 033Z) is not proved here,
so statements that need a Nagata base take `[IsLocallyNoetherian Y] [Y.IsUniversallyJapanese]`.
By BLMNPS Lemma 11.13 (arXiv:1902.08184v4, §11.4) this pair is equivalent to being Nagata; only
the easy direction, `Scheme.isNagata_of_isUniversallyJapanese`, is proved here.

The spectrum of a universally Japanese ring is universally Japanese
(`AlgebraicGeometry.isUniversallyJapanese_Spec`), so with
`Scheme.IsUniversallyJapanese.of_locallyOfFiniteType` and `IsUniversallyJapanese.of_charZero`
every scheme locally of finite type over a field of characteristic zero is universally Japanese.

## References

* [Stacks: Nagata schemes](https://stacks.math.columbia.edu/tag/033R)
* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in families*,
  arXiv:1902.08184v4, §11.4

## Tags

Nagata scheme, universally Japanese scheme, valuative criterion, discrete valuation ring
-/

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A scheme is **universally Japanese** if the ring of sections over every affine open is
universally Japanese. Stacks 033S asks this only on an affine open cover;
`Scheme.isUniversallyJapanese_of_affine_cover` (Stacks 033W) shows that the two agree. -/
@[stacks 033S "(2)"]
class Scheme.IsUniversallyJapanese (X : Scheme.{u}) : Prop where
  /-- The ring of sections over an affine open is universally Japanese. -/
  isUniversallyJapanese (U : X.affineOpens) : _root_.IsUniversallyJapanese Γ(X, U)

/-- A scheme is **Nagata** if the ring of sections over every affine open is Nagata. Stacks 033S
asks this only on an affine open cover; `Scheme.isNagata_of_affine_cover` (Stacks 033X) shows that
the two agree.

Nagata's theorem (Stacks 033Z) says that this is equivalent to being locally Noetherian and
universally Japanese. Only the easy direction, `Scheme.isNagata_of_isUniversallyJapanese`, is
proved here, so theorems that need the stronger property assume
`[IsLocallyNoetherian X] [X.IsUniversallyJapanese]` instead. -/
@[stacks 033S "(3)"]
class Scheme.IsNagata (X : Scheme.{u}) : Prop where
  /-- The ring of sections over an affine open is Nagata. -/
  isNagataRing (U : X.affineOpens) : IsNagataRing Γ(X, U)

namespace Scheme

/-- A scheme with an affine open cover by universally Japanese rings is universally Japanese. -/
@[stacks 033W "(3) ⇒ (2)"]
theorem isUniversallyJapanese_of_affine_cover {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) (hS' : ∀ i, _root_.IsUniversallyJapanese Γ(X, S i)) :
    X.IsUniversallyJapanese := by
  refine ⟨fun U ↦ ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hU =>
    have := U.prop.isLocalization_basicOpen f
    have : Algebra.EssFiniteType Γ(X, U) Γ(X, X.basicOpen f) :=
      .of_isLocalization _ (.powers f)
    exact .of_essFiniteType Γ(X, U) Γ(X, X.basicOpen f)
  | openCover U s hs hU =>
    have := fun f : (s : Set Γ(X, U)) ↦ U.prop.isLocalization_basicOpen f.1
    have : ∀ f : (s : Set Γ(X, U)), _root_.IsUniversallyJapanese Γ(X, X.basicOpen f.1) :=
      fun f ↦ hU ⟨f.1, f.2⟩
    exact .of_span_eq_top (s : Set Γ(X, U)) hs fun f ↦ Γ(X, X.basicOpen f.1)
  | hU => exact hS' _

/-- A scheme with an affine open cover by Nagata rings is Nagata. -/
@[stacks 033X "(3) ⇒ (2)"]
theorem isNagata_of_affine_cover {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) (hS' : ∀ i, IsNagataRing Γ(X, S i)) : X.IsNagata := by
  refine ⟨fun U ↦ ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hU =>
    have := U.prop.isLocalization_basicOpen f
    exact .of_isLocalization (.powers f) Γ(X, X.basicOpen f)
  | openCover U s hs hU =>
    have := fun f : (s : Set Γ(X, U)) ↦ U.prop.isLocalization_basicOpen f.1
    have : ∀ f : (s : Set Γ(X, U)), IsNagataRing Γ(X, X.basicOpen f.1) :=
      fun f ↦ hU ⟨f.1, f.2⟩
    exact .of_span_eq_top (s : Set Γ(X, U)) hs fun f ↦ Γ(X, X.basicOpen f.1)
  | hU => exact hS' _

/-- A Nagata scheme is locally Noetherian. -/
@[stacks 033U]
instance IsNagata.isLocallyNoetherian [X.IsNagata] : IsLocallyNoetherian X :=
  ⟨fun U ↦ (IsNagata.isNagataRing U).isNoetherianRing⟩

/-- The easy half of Nagata's theorem for schemes: a locally Noetherian, universally Japanese
scheme is Nagata. The converse (Stacks 033Z) is not proved here. -/
instance isNagata_of_isUniversallyJapanese [IsLocallyNoetherian X] [X.IsUniversallyJapanese] :
    X.IsNagata :=
  ⟨fun U ↦
    have := IsLocallyNoetherian.component_noetherian U
    have := IsUniversallyJapanese.isUniversallyJapanese U
    inferInstance⟩

/-- Universally Japanese ascends along morphisms locally of finite type. This is not an instance:
the conclusion does not determine the target. -/
theorem IsUniversallyJapanese.of_locallyOfFiniteType (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Y.IsUniversallyJapanese] : X.IsUniversallyJapanese := by
  let ι := {p : Y.affineOpens × X.affineOpens // (p.2 : X.Opens) ≤ f ⁻¹ᵁ p.1}
  refine isUniversallyJapanese_of_affine_cover (S := fun i : ι ↦ i.1.2) ?_ fun i ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU)
        (f ⁻¹ᵁ U).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hxV⟩
  · obtain ⟨⟨U, V⟩, e⟩ := i
    have := IsUniversallyJapanese.isUniversallyJapanese U
    let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    have : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) :=
      RingHom.FiniteType.essFiniteType (f.finiteType_appLE U.2 V.2 e)
    exact .of_essFiniteType Γ(Y, U) _

end Scheme

/-- The spectrum of a universally Japanese ring is universally Japanese. -/
instance isUniversallyJapanese_Spec (R : CommRingCat.{u}) [_root_.IsUniversallyJapanese R] :
    (Spec R).IsUniversallyJapanese := by
  refine Scheme.isUniversallyJapanese_of_affine_cover
    (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top _⟩) (by simp) fun _ ↦ ?_
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  let : Algebra R Γ(Spec R, ⊤) := e.symm.toRingHom.toAlgebra
  have : Algebra.EssFiniteType R Γ(Spec R, ⊤) :=
    (RingHom.FiniteType.of_surjective _ e.symm.surjective).essFiniteType
  exact .of_essFiniteType R _

/-- **BLMNPS Lemma 11.19**, universally Japanese form. Let `f : X ⟶ Y` be locally of finite type
over a locally Noetherian, universally Japanese `Y`, let `y ⤳ y'` be a specialization with
`y ≠ y'`, and let `x` be a point over `y`. Then some discrete valuation ring `R` with fraction
field `κ(x)` fits in a square over `f` whose bottom arrow `Spec R ⟶ Y` is essentially of finite
type and sends the closed point to `y'`.

BLMNPS (arXiv:1902.08184v4, §11.4) assume `Y` Nagata, which by their Lemma 11.13 (Stacks 033Z)
is equivalent to `Y` being locally Noetherian and universally Japanese. Only the easy direction is
proved here, so the latter is assumed. -/
theorem exists_dvr_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] [Y.IsUniversallyJapanese]
    {y y' : Y} (h : y ⤳ y') (hne : y ≠ y') {x : X} (hx : f x = y) :
    ∃ (R : Subring (X.residueField x)) (_ : IsDiscreteValuationRing R)
      (_ : IsFractionRing R (X.residueField x)) (g : Spec (.of R) ⟶ Y),
      EssentiallyOfFiniteType g ∧ g (IsLocalRing.closedPoint R) = y' ∧
      X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField x))) ≫ g := by
  subst hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hy'U, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y') isOpen_univ
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : _root_.IsUniversallyJapanese Γ(Y, U) :=
    Scheme.IsUniversallyJapanese.isUniversallyJapanese ⟨U, hU⟩
  have : IsNoetherianRing (Y.residueFieldSubring h) := Scheme.isNoetherianRing_residueFieldSubring h
  let : Algebra Γ(Y, U) (Y.residueFieldSubring h) :=
    ((Scheme.toResidueFieldSubring h).comp (Y.presheaf.germ U y' hy'U).hom).toAlgebra
  have : Algebra.EssFiniteType Γ(Y, U) (Y.residueFieldSubring h) :=
    RingHom.essFiniteType_algebraMap.mp
      (Scheme.essFiniteType_toResidueFieldSubring_comp_germ h hU hy'U)
  have : _root_.IsUniversallyJapanese (Y.residueFieldSubring h) :=
    .of_essFiniteType Γ(Y, U) (Y.residueFieldSubring h)
  -- `κ(x)` is a finitely generated extension of `κ(y)`.
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.residueField (f x)) (X.residueField x) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.essFiniteType_residueFieldMap f x)
  let : Algebra (Y.residueFieldSubring h) (X.residueField x) :=
    ((algebraMap (Y.residueField (f x)) (X.residueField x)).comp
      (algebraMap (Y.residueFieldSubring h) (Y.residueField (f x)))).toAlgebra
  have : IsScalarTower (Y.residueFieldSubring h) (Y.residueField (f x)) (X.residueField x) :=
    .of_algebraMap_eq fun _ ↦ rfl
  -- BLMNPS Lemma 11.15 gives the discrete valuation ring.
  obtain ⟨R, hR, hdvr, hfr, heft⟩ := exists_dvr_dominating_essFiniteType
    (Scheme.not_isField_residueFieldSubring h hne) (Y.residueField (f x)) (X.residueField x)
  obtain ⟨ψ, -, hψK, hcl, hsq⟩ :=
    Scheme.exists_hom_of_le_residueFieldSubring h (f.residueFieldMap x) R hR
  have hψ : (ψ.comp (Y.presheaf.germ U y' hy'U).hom).EssFiniteType := by
    have : ψ.comp (Y.presheaf.germ U y' hy'U).hom =
        ((algebraMap (Y.residueFieldSubring h) (X.residueField x)).codRestrict R.toSubring
          fun a ↦ LocalSubring.toSubring_mono hR ⟨a, rfl⟩).comp
          ((Scheme.toResidueFieldSubring h).comp (Y.presheaf.germ U y' hy'U).hom) :=
      RingHom.ext fun r ↦ Subtype.ext (hψK _)
    rw [this]
    exact (Scheme.essFiniteType_toResidueFieldSubring_comp_germ h hU hy'U).comp heft
  have hg : EssentiallyOfFiniteType (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y') := by
    have : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
    have : LocallyOfFiniteType hU.fromSpec := locallyOfFiniteType_of_isOpenImmersion _
    have := essentiallyOfFiniteType_spec_map_comp
      (Y.presheaf.germ U y' hy'U ≫ CommRingCat.ofHom ψ) hψ hU.fromSpec
    have e1 : Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y' =
        Spec.map (Y.presheaf.germ U y' hy'U ≫ CommRingCat.ofHom ψ) ≫ hU.fromSpec := by
      simp only [← hU.fromSpecStalk_eq_fromSpecStalk hy'U, IsAffineOpen.fromSpecStalk,
        ← Category.assoc]
      congr 1
      exact (Spec.map_comp _ _).symm
    rw [e1]
    exact this
  refine ⟨R.toSubring, hdvr, hfr, _, hg, hcl, ?_⟩
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm.trans hsq.symm

/-- BLMNPS Lemma 11.19 as a valuative commutative square: the top arrow is
`Spec κ(x) ⟶ X`, the valuation ring is a discrete valuation ring, and the bottom arrow is
essentially of finite type and sends the closed point to `y'`. -/
theorem exists_valuativeCommSq_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] [Y.IsUniversallyJapanese]
    {y y' : Y} (h : y ⤳ y') (hne : y ≠ y') {x : X} (hx : f x = y) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧ EssentiallyOfFiniteType sq.i₂ ∧
      sq.i₂ (IsLocalRing.closedPoint sq.R) = y' ∧ Set.range sq.i₁ = {x} := by
  obtain ⟨R, hdvr, hfr, g, hg, hcl, hcomm⟩ := exists_dvr_of_specializes f h hne hx
  let sq : ValuativeCommSq f :=
    { R := R
      K := X.residueField x
      i₁ := X.fromSpecResidueField x
      i₂ := g
      commSq := ⟨hcomm⟩ }
  exact ⟨sq, hdvr, hg, hcl, Scheme.range_fromSpecResidueField x⟩

end AlgebraicGeometry
