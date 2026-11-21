/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.QuasiCompact
import DerivedAlgGeo.AlgebraicGeometry.ResidueField
import DerivedAlgGeo.RingTheory.Valuation.LocalSubring
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Discrete valuation rings realize specializations

Let `f : X ⟶ Y` be a morphism of schemes with `Y` locally Noetherian. This file produces
valuative squares over `f` whose valuation ring is a discrete valuation ring, with no Nagata
hypothesis on `Y`.

## Main results

* `AlgebraicGeometry.IsLocallyNoetherian.exists_dvr_of_specializes`: Stacks 054F (2), relative
  form. If `f` is locally of finite type, `y ⤳ y'` with `y ≠ y'` and `f x = y`, then a discrete
  valuation ring `R ⊆ κ(x)` with fraction field `κ(x)` fits in a square over `f` whose top arrow
  is `Spec κ(x) ⟶ X` and whose closed point maps to `y'`.
* `AlgebraicGeometry.IsLocallyNoetherian.exists_valuativeCommSq_of_specializes`: the same as a
  `ValuativeCommSq`.
* `AlgebraicGeometry.exists_dvr_of_mem_closure_range`: Stacks 0CM2. If `f` is of finite type and
  `y` lies in the closure of the image, some discrete valuation ring square over `f` sends the
  closed point to `y` and its top arrow hits a generic point of an irreducible component of `X`.
* `AlgebraicGeometry.exists_dvr_residueField_of_mem_closure_range`: the "moreover" of 0CM2, for
  `y` outside the image: the fraction field can be taken to be the residue field of that generic
  point.
* `AlgebraicGeometry.IsSeparated.of_dvr_residueField`: Stacks 0207, (4) ⇒ (1). Over a locally
  Noetherian base, a morphism locally of finite type is separated as soon as the squares at generic
  points of irreducible components, with a discrete valuation ring `R ⊆ κ(η)` of fraction field
  `κ(η)`, have at most one lift.
* `AlgebraicGeometry.IsSeparated.iff_dvr`: Stacks 0207, (1) ⇔ (3). Separatedness is equivalent to
  uniqueness of lifts for squares over a discrete valuation ring.

## Implementation notes

Both constructions dominate the image of `𝒪_{Y,y'} ⟶ κ(y)` (`Scheme.residueFieldSubring`) by a
discrete valuation ring of `κ(x)` using Stacks 00PH (`exists_dvr_dominating`), which needs no
Nagata hypothesis. In contrast to `exists_dvr_of_specializes`, the bottom arrow `Spec R ⟶ Y` is
therefore not known to be essentially of finite type: Stacks Tag 09E1 gives a Noetherian local
domain for which it cannot be.

## References

* [Stacks: Tag 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks: Tag 0CM2](https://stacks.math.columbia.edu/tag/0CM2)
* [Stacks: Tag 0207](https://stacks.math.columbia.edu/tag/0207)
* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in families*,
  arXiv:1902.08184v4, Lemma 11.19

## Tags

valuative criterion, discrete valuation ring, specialization
-/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry

/-- **Stacks 054F (2)**, relative form: BLMNPS Lemma 11.19 without the Nagata hypothesis. Let
`f : X ⟶ Y` be locally of finite type over a locally Noetherian `Y`, let `y ⤳ y'` be a
specialization with `y ≠ y'`, and let `x` be a point over `y`. Then some discrete valuation ring
`R ⊆ κ(x)` with fraction field `κ(x)` fits in a square over `f` whose top arrow is
`Spec κ(x) ⟶ X` and whose bottom arrow `Spec R ⟶ Y` sends the closed point to `y'`.

Unlike `AlgebraicGeometry.exists_dvr_of_specializes`, which assumes `Y` universally Japanese, the
bottom arrow need not be essentially of finite type (Stacks Tag 09E1).

The hypothesis `y ≠ y'` is needed: for `X = Y = Spec ℚ` and `f = 𝟙`, a square with `R ⊆ ℚ`
and the top arrow the identity forces `R` to contain `ℚ = Frac R`, so `R` is a field. -/
@[stacks 054F "(2), relative form"]
theorem IsLocallyNoetherian.exists_dvr_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y y' : Y} (h : y ⤳ y') (hne : y ≠ y')
    {x : X} (hx : f x = y) :
    ∃ (R : Subring (X.residueField x)) (_ : IsDiscreteValuationRing R)
      (_ : IsFractionRing R (X.residueField x)) (g : Spec (.of R) ⟶ Y),
      g (IsLocalRing.closedPoint R) = y' ∧
      X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField x))) ≫ g := by
  subst hx
  have : IsNoetherianRing (Y.residueFieldSubring h) := Scheme.isNoetherianRing_residueFieldSubring h
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.residueField (f x)) (X.residueField x) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.essFiniteType_residueFieldMap f x)
  let : Algebra (Y.residueFieldSubring h) (X.residueField x) :=
    ((algebraMap (Y.residueField (f x)) (X.residueField x)).comp
      (algebraMap (Y.residueFieldSubring h) (Y.residueField (f x)))).toAlgebra
  have : IsScalarTower (Y.residueFieldSubring h) (Y.residueField (f x)) (X.residueField x) :=
    .of_algebraMap_eq fun _ ↦ rfl
  -- Stacks 00PH gives the discrete valuation ring.
  obtain ⟨V, hV, hdvr⟩ := exists_dvr_dominating (Scheme.not_isField_residueFieldSubring h hne)
    (Y.residueField (f x)) (X.residueField x)
  obtain ⟨ψ, -, -, hcl, hsq⟩ :=
    Scheme.exists_hom_of_le_residueFieldSubring h (f.residueFieldMap x) V.toLocalSubring hV
  refine ⟨V.toSubring, hdvr, inferInstanceAs (IsFractionRing V (X.residueField x)), _, hcl, ?_⟩
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x).symm.trans hsq.symm

/-- **Stacks 054F (2)**, relative form, as a valuative commutative square: the top arrow is
`Spec κ(x) ⟶ X`, the valuation ring is a discrete valuation ring, and the bottom arrow sends the
closed point to `y'`. See `IsLocallyNoetherian.exists_dvr_of_specializes`. -/
theorem IsLocallyNoetherian.exists_valuativeCommSq_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] {y y' : Y} (h : y ⤳ y') (hne : y ≠ y')
    {x : X} (hx : f x = y) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧
      sq.i₂ (IsLocalRing.closedPoint sq.R) = y' ∧ Set.range sq.i₁ = {x} := by
  obtain ⟨R, hdvr, hfr, g, hcl, hcomm⟩ := IsLocallyNoetherian.exists_dvr_of_specializes f h hne hx
  let sq : ValuativeCommSq f :=
    { R := R
      K := X.residueField x
      i₁ := X.fromSpecResidueField x
      i₂ := g
      commSq := ⟨hcomm⟩ }
  exact ⟨sq, hdvr, hcl, Scheme.range_fromSpecResidueField x⟩

/-- A discrete valuation ring square over `f` at a point `η`, with closed point sent to `f η`:
the valuation ring is the power series ring over `κ(η)` and its fraction field is the field of
Laurent series. -/
private theorem exists_valuativeCommSq_of_residueField {X Y : Scheme.{u}} (f : X ⟶ Y) (η : X) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧
      sq.i₂ (IsLocalRing.closedPoint sq.R) = f η ∧ Set.range sq.i₁ = {η} := by
  let K : Type u := X.residueField η
  let j : Spec (.of (PowerSeries K)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) ≫ X.fromSpecResidueField η
  have hj : ∀ p, j p = η := fun p ↦ by
    change X.fromSpecResidueField η (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) p)
      = η
    rw [Subsingleton.elim (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries K))) p)
      (closedPoint K)]
    exact Scheme.fromSpecResidueField_apply _ _
  let sq : ValuativeCommSq f :=
    { R := PowerSeries K
      K := LaurentSeries K
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (LaurentSeries K))) ≫ j
      i₂ := j ≫ f
      commSq := ⟨by rw [Category.assoc]⟩ }
  refine ⟨sq, inferInstanceAs (IsDiscreteValuationRing (PowerSeries K)), hj _ ▸ rfl, ?_⟩
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun z ⟨p, hp⟩ ↦ ?_⟩
  · exact ⟨closedPoint (LaurentSeries K), hj _⟩
  · rw [← hp]; exact hj _

/-- For a quasi-compact morphism, every point `y` of the closure of the image is a
specialization of `f η` for a generic point `η` of an irreducible component of `X`. -/
private theorem exists_isGenericPoint_specializes_of_mem_closure_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] {y : Y} (hy : y ∈ closure (Set.range f)) :
    ∃ η : X, closure {η} ∈ irreducibleComponents X ∧ f η ⤳ y := by
  obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range f hy
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηZ : closure {η} = Z := hη
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hηZ]
    exact hxZ (subset_closure rfl)
  exact ⟨η, hηZ ▸ hZ, (hηx.map f.continuous).trans hx⟩

/-- **Stacks 0CM2.** Let `f : X ⟶ Y` be of finite type over a locally Noetherian `Y`, and let `y` be
in the closure of the image of `f`. Then some discrete valuation ring square over `f` sends the
closed point to `y`, and its top arrow hits a generic point of an irreducible component of `X`.

Quasi-compactness gives a point of the image specializing to `y` (Stacks 02JQ); the proof
then dominates the image of `𝒪_{Y,y} ⟶ κ(η)` by a discrete valuation ring (Stacks 00PH).
See `exists_dvr_residueField_of_mem_closure_range` for the fraction field.

All three hypotheses are needed:
* `[QuasiCompact f]`: for `X = ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ` and `y` the generic point, `y` is in the closure
  of the image but no square has closed point `↦ y`, since the generic point of the square would
  map into some `Spec 𝔽ₚ`, over `(p) ≠ y`.
* `[IsLocallyNoetherian Y]`: for `V` a valuation ring with value group `ℚ`, `K = V[1/π]` and
  `f : Spec K ⟶ Spec V`, the map `V ⟶ A` of a square with closed point `↦ y` would be local and
  injective, so `A ∩ K` would be a valuation ring dominating `V`, hence `V`, and `ℚ` would embed
  in the value group `ℤ` of `A`.
* `[LocallyOfFiniteType f]`: for `Spec ℚ̄ ⟶ Spec ℤ_(p)` the same argument embeds a nontrivial
  divisible group into `ℤ`. -/
@[stacks 0CM2]
theorem exists_dvr_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsLocallyNoetherian Y] {y : Y} (hy : y ∈ closure (Set.range f)) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧
      sq.i₂ (IsLocalRing.closedPoint sq.R) = y ∧
      ∃ η : X, closure {η} ∈ irreducibleComponents X ∧ Set.range sq.i₁ = {η} := by
  obtain ⟨η, hη, hηy⟩ := exists_isGenericPoint_specializes_of_mem_closure_range f hy
  by_cases hne : f η = y
  · obtain ⟨sq, hdvr, hcl, hr⟩ := exists_valuativeCommSq_of_residueField f η
    exact ⟨sq, hdvr, hcl.trans hne, η, hη, hr⟩
  · obtain ⟨sq, hdvr, hcl, hr⟩ :=
      IsLocallyNoetherian.exists_valuativeCommSq_of_specializes f hηy hne rfl
    exact ⟨sq, hdvr, hcl, η, hη, hr⟩

/-- **Stacks 0CM2**, "moreover", for `y` outside the image. Let `f : X ⟶ Y` be of finite type over a
locally Noetherian `Y`, and let `y` be in the closure of the image of `f` but not in the image.
Then for some generic point `η` of an irreducible component of `X`, a discrete valuation ring
`R ⊆ κ(η)` with fraction field `κ(η)` fits in a square over `f` whose closed point maps to `y`.

The hypothesis `y ∉ range f` is needed. Stacks 0CM2 states the "moreover" without it, and then it
is false: for `X = Y = Spec ℚ`, `f = 𝟙` and `y` the point, a square with `K = κ(η) = ℚ` and top
arrow the canonical one has `ℚ ⟶ A ⟶ ℚ` equal to the identity, so `A ⊇ ℚ = Frac A` is a field,
not a discrete valuation ring. Stacks' proof applies 00PH to the image of `𝒪_{Y,y} ⟶ κ(η)`, which
is the field `κ(y)` when `f η = y`. -/
@[stacks 0CM2 "moreover; needs y ∉ range f"]
theorem exists_dvr_residueField_of_mem_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y] {y : Y}
    (hy : y ∈ closure (Set.range f)) (hy' : y ∉ Set.range f) :
    ∃ (η : X) (_ : closure {η} ∈ irreducibleComponents X) (R : Subring (X.residueField η))
      (_ : IsDiscreteValuationRing R) (_ : IsFractionRing R (X.residueField η))
      (g : Spec (.of R) ⟶ Y), g (IsLocalRing.closedPoint R) = y ∧
      X.fromSpecResidueField η ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η))) ≫ g := by
  obtain ⟨η, hη, hηy⟩ := exists_isGenericPoint_specializes_of_mem_closure_range f hy
  have hne : f η ≠ y := fun h ↦ hy' ⟨η, h⟩
  obtain ⟨R, hdvr, hfr, g, hcl, hcomm⟩ :=
    IsLocallyNoetherian.exists_dvr_of_specializes f hηy hne rfl
  exact ⟨η, hη, R, hdvr, hfr, g, hcl, hcomm⟩

/-- **Stacks 0207**, (4) ⇒ (1). Let `f : X ⟶ S` be locally of finite type over a locally Noetherian
`S`. If for every generic point `η` of an irreducible component of `X`, every discrete valuation
ring `R ⊆ κ(η)` with fraction field `κ(η)` and every bottom arrow `Spec R ⟶ S`, the square with top
arrow `Spec κ(η) ⟶ X` has at most one lift, then `f` is separated.

The proof applies `IsLocallyNoetherian.exists_dvr_of_specializes` to the diagonal `Δ`, which is
a quasi-compact immersion because `X` is locally Noetherian, hence quasi-separated (Stacks 01OY).
A point `z` in the closure of the range of `Δ` specializes from `Δ η` for a generic point `η`
(Stacks 02JQ), and then a square for `Δ` over a discrete valuation ring `R ⊆ κ(η)` sends the closed
point to `z`. The two projections of its bottom arrow are lifts of the same square for `f`,
so they agree, and the bottom arrow factors through `Δ`. -/
@[stacks 0207 "(4) ⇒ (1)"]
theorem IsSeparated.of_dvr_residueField {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f]
    (h : ∀ η : X, closure {η} ∈ irreducibleComponents X →
      ∀ (R : Subring (X.residueField η)) [IsDiscreteValuationRing R]
        [IsFractionRing R (X.residueField η)] (g : Spec (.of R) ⟶ S)
        (w : CommSq (X.fromSpecResidueField η)
          (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f g),
        Subsingleton w.LiftStruct) :
    IsSeparated f where
  isClosedImmersion_diagonal := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : QuasiSeparated f := inferInstance
    refine .of_isPreimmersion _ (closure_subset_iff_isClosed.mp ?_)
    intro z hz
    obtain ⟨η, hη, hηz⟩ :=
      exists_isGenericPoint_specializes_of_mem_closure_range (pullback.diagonal f) hz
    by_cases hne : pullback.diagonal f η = z
    · exact ⟨η, hne⟩
    obtain ⟨R, hdvr, hfr, g, hcl, hcomm⟩ :=
      IsLocallyNoetherian.exists_dvr_of_specializes (pullback.diagonal f) hηz hne rfl
    have hfst : X.fromSpecResidueField η =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η))) ≫ g ≫ pullback.fst f f := by
      rw [← Category.assoc, ← hcomm]; simp
    have hsnd : X.fromSpecResidueField η =
        Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η))) ≫ g ≫ pullback.snd f f := by
      rw [← Category.assoc, ← hcomm]; simp
    have w : CommSq (X.fromSpecResidueField η)
        (Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField η)))) f
        (g ≫ pullback.fst f f ≫ f) := ⟨by
          have := congrArg (· ≫ f) hfst
          simp only [Category.assoc] at this
          exact this⟩
    have := h η hη R (g ≫ pullback.fst f f ≫ f) w
    have h₁₂ : (⟨g ≫ pullback.fst f f, hfst.symm, by simp⟩ : w.LiftStruct) =
        ⟨g ≫ pullback.snd f f, hsnd.symm, by simp [pullback.condition]⟩ :=
      Subsingleton.elim _ _
    have hl : g ≫ pullback.fst f f = g ≫ pullback.snd f f := congrArg CommSq.LiftStruct.l h₁₂
    have hg : (g ≫ pullback.fst f f) ≫ pullback.diagonal f = g := by
      apply pullback.hom_ext <;> simp [hl]
    refine ⟨(g ≫ pullback.fst f f) (closedPoint R), ?_⟩
    exact (congrArg (fun k : Spec ↧R ⟶ _ ↦ k (closedPoint R)) hg).trans hcl

/-- **Stacks 0207**, (1) ⇔ (3). Let `f : X ⟶ S` be locally of finite type over a locally Noetherian
`S`. Then `f` is separated if and only if every valuative square over `f` whose valuation ring is a
discrete valuation ring has at most one lift. By `IsSeparated.of_dvr_residueField` it already
suffices to test the squares at generic points of irreducible components.

The hypothesis is locally of finite type, not finite type: Stacks 0208 and 05JY need finite type.
Both hypotheses are needed.
* `[LocallyOfFiniteType f]`: let `V = ⋃ₙ k[t^{1/n}]_{(t^{1/n})}`, a valuation ring with value group
  `ℚ`, and let `X` be two copies of `Spec V` glued along `Spec (Frac V)`. Then `X ⟶ Spec k` is not
  separated. In a discrete valuation ring square a lift sending the closed point to a doubled point
  would make `V ⟶ A` local and injective, so `A ∩ Frac V = V` would have value group `ℚ ⊆ ℤ`. So
  every lift lands in the separated open `Spec (Frac V)`, and lifts are unique.
* `[IsLocallyNoetherian S]`: for `S = Spec V` with `V` as above and `X` the scheme `S` with its
  closed point doubled, `X ⟶ S` is locally an isomorphism and not separated. A square with closed
  point over the closed point of `S` either makes `V ⟶ A` local and injective, which is impossible
  as above, or lands in the closed fibre, two discrete points, where the lift is determined. -/
@[stacks 0207]
theorem IsSeparated.iff_dvr {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] :
    IsSeparated f ↔ ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      Subsingleton sq.commSq.LiftStruct := by
  refine ⟨fun _ sq _ ↦ IsSeparated.valuativeCriterion f sq, fun h ↦ ?_⟩
  refine IsSeparated.of_dvr_residueField f fun η _ R _ _ g w ↦ ?_
  exact h ⟨R, X.residueField η, X.fromSpecResidueField η, g, w⟩ inferInstance

end AlgebraicGeometry
