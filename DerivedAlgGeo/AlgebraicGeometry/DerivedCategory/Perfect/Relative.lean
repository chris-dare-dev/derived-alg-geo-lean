/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Comparison
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpenImmersionPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Locality

/-!
# Relative-perfect and universally-gluable complexes

Pseudo-coherence, local finite Tor amplitude over a base, relative perfection
and the universally-gluable refinement.  These are properties of *one complex*
over *one morphism*.  Their objects live in the honest
quasi-coherent-cohomology locus `SchemeQuasicoherentDerivedCategory X`, not in
the derived category of all module sheaves under a different name.

## Main definitions

* `AlgebraicGeometry.schemePseudoCoherent` — the locally Noetherian cohomological
  criterion for pseudo-coherence.
* `AlgebraicGeometry.LocalFiniteTorAmplitudeChart` and
  `AlgebraicGeometry.schemeLocallyFiniteTorAmplitudeOver` — bounded stalkwise-flat
  local models, and local finite Tor amplitude over a base witnessed by them.
* `AlgebraicGeometry.LocalRelativePerfectChart` — a bounded local model whose terms are
  finitely presented and flat over the base.
* `AlgebraicGeometry.schemeRelativePerfect` and
  `AlgebraicGeometry.SchemeRelativePerfectCategory` — relative perfection, defined by such
  charts at every point, and its full subcategory.
* `AlgebraicGeometry.GeometricFiberModel` and its `fiberComplex`, `fiberObject` —
  a global flat model and the geometric fiber computed from it.
* `AlgebraicGeometry.UniversallyGluableData`,
  `AlgebraicGeometry.schemeUniversallyGluableRelativePerfect` and
  `AlgebraicGeometry.SchemeUniversallyGluableCategory` — fiberwise negative-Ext
  vanishing and the universally-gluable locus.
* `AlgebraicGeometry.relativeOpenBaseChange` and `relativeOpenTo` — restriction
  of a family to an open subscheme.

## Main results

* `AlgebraicGeometry.schemeRelativePerfect_le_schemeLocallyFiniteTorAmplitudeOver` —
  relative perfection forgets to local finite Tor amplitude.
* `AlgebraicGeometry.minus_of_schemeLocallyFiniteTorAmplitudeOver` — on a quasi-compact
  scheme, local bounded models give a global upper bound.
* `AlgebraicGeometry.isFinitePresentation_homology_of_schemeRelativePerfect` — on a locally
  Noetherian scheme, a relative-perfect object has finitely presented cohomology.
* `AlgebraicGeometry.schemeRelativePerfect_le_schemePseudoCoherent` — on a quasi-compact,
  locally Noetherian scheme, relative perfection implies the cohomological criterion.
* `SchemeRelativePerfectCategory.exists_boundedCoherentRepresentative` — a
  relative-perfect object with bounded coherent cohomology has a `Dᵇ(Coh X)`
  representative, given the bounded-coherent `Dqc` identification.
* `SchemeRelativePerfectCategory.perfect_iff_compact` — given the
  compact/perfect comparison, perfection is compactness in `Dqc(X)`.
* `schemePseudoCoherent_zero`, `schemeLocallyFiniteTorAmplitudeOver_zero`,
  `schemeRelativePerfect_zero` and `schemeUniversallyGluableRelativePerfect_zero` —
  the zero object lies in every locus.

## Implementation notes

### Ownership

These predicates are needed before a moduli functor exists -- base change and
derived operations require them -- so they are owned here, beside the derived
category they are predicates on, and the moduli problem in `Moduli/PerfectComplex/`
consumes them.  That subtree keeps the presheaf, restriction stability,
boundedness, openness, atlas and algebraicity layer, none of which is
mentioned here.

Stalkwise flatness of a module sheaf over a morphism is a further step down
and lives with the module sheaves, in `Modules/Flat.lean`.

### Relative perfection

`schemeRelativePerfect p` is Lieblich's relative perfection in its Zariski form: around every
point the object is represented by a bounded complex of finitely presented module sheaves
that are flat over the base. This is condition (A) of Stacks Remark 36.35.14 (Tag 0DI9); that
remark notes that condition (A) is easier to work with in regards to limits. It asks nothing
of the cohomology sheaves. The cohomological criterion `schemePseudoCoherent` is kept as a
separate predicate, because it is not stable under base change to non-Noetherian schemes; see
the docstring of `schemeRelativePerfect` for a witness. It is recovered on quasi-compact,
locally Noetherian schemes by `schemeRelativePerfect_le_schemePseudoCoherent`.

### Local models instead of a derived tensor product

At the current Mathlib pin there is no general derived tensor product for
module sheaves.  Finite Tor amplitude is therefore expressed by the standard
local model that can be checked without such an API: around every point the
complex is represented by a bounded complex of module sheaves whose stalks
are flat over the base.  The bounds and the representing isomorphism are data,
not an arbitrary proposition supplied by a caller.

For the same reason, a geometric fiber is computed only from an explicit
globally flat model. The repository has an interface characterizing arbitrary
pullback by its left-derived universal property, but does not construct that
interface along arbitrary fiber inclusions. This is enough to define and inhabit
the zero model and to state fiberwise negative-Ext vanishing honestly;
comparison with a K-flat construction is a separate theorem.

## References

* M. Lieblich, *Moduli of complexes on a proper morphism*, J. Algebraic Geom. 15 (2006),
  arXiv:math/0502198, Definition 2.1.1.
* The Stacks Project, Section 36.35 (Tag 0DHZ): Definition 36.35.1 (Tag 0DI0) and
  Remark 36.35.14 (Tag 0DI9).

Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber` and `Module.Flat`, and the
repository's `SchemeQuasicoherentDerivedCategory` and
`Scheme.Modules.IsFlatOver`.

## Tags

perfect complex, pseudo-coherence, Tor amplitude, relative perfection,
universally gluable
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
open scoped ZeroObject

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The locally Noetherian cohomological criterion for pseudo-coherence:
bounded above with finitely presented cohomology in every degree.

Scope: on a locally Noetherian scheme this criterion is pseudo-coherence;
on a general scheme the two notions diverge in both directions. Any theorem that
quantifies over non-Noetherian bases is therefore about THIS predicate, not about
standard pseudo-coherence. Relative perfection, `schemeRelativePerfect`, does not
contain this predicate; it implies it on quasi-compact, locally Noetherian schemes
(`schemeRelativePerfect_le_schemePseudoCoherent`). -/
def schemePseudoCoherent (X : Scheme.{u}) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦
    (DerivedCategory.TStructure.t (C := X.Modules)).minus E.obj ∧
      ∀ n : ℤ, (SheafOfModules.isFinitePresentation X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj)

instance schemePseudoCoherent_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (schemePseudoCoherent X).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    constructor
    · exact (DerivedCategory.TStructure.t (C := X.Modules)).minus.prop_of_iso
        ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE.1
    · intro n
      exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules n).mapIso
          ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)) (hE.2 n)

/-- The object of `Over S` obtained by restricting `p : X ⟶ S` to an open
subscheme of `X`. -/
def relativeOpenBaseChange {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) : SchemeBaseChange S :=
  Over.mk (U.ι ≫ p)

/-- The canonical open-immersion morphism from a restricted family to the
original family over `S`. -/
def relativeOpenTo {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) :
    relativeOpenBaseChange p U ⟶ Over.mk p :=
  Over.homMk U.ι (by rfl)

@[simp]
theorem relativeOpenTo_left {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) : (relativeOpenTo p U).left = U.ι :=
  rfl

instance relativeOpenTo_isOpenImmersion {X S : Scheme.{u}}
    (p : X ⟶ S) (U : X.Opens) :
    IsOpenImmersion (relativeOpenTo p U).left := by
  change IsOpenImmersion U.ι
  infer_instance

/-- A bounded flat local model for one object near one point.  The target of
`represents` is the actual exact derived restriction along the open immersion;
no nonexact derived pullback is used. -/
structure LocalFiniteTorAmplitudeChart {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) (x : X) where
  /-- An open neighbourhood on which the flat model is defined. -/
  openSubset : X.Opens
  /-- The chosen point lies in the neighbourhood. -/
  mem_openSubset : x ∈ openSubset
  /-- Lower cohomological bound for the model. -/
  lower : ℤ
  /-- Upper cohomological bound for the model. -/
  upper : ℤ
  /-- The interval of possible nonzero terms is ordered. -/
  lower_le_upper : lower ≤ upper
  /-- A complex of module sheaves on the open neighbourhood. -/
  model : CochainComplex openSubset.toScheme.Modules ℤ
  /-- The model has no terms below `lower`. -/
  strictlyGE : model.IsStrictlyGE lower
  /-- The model has no terms above `upper`. -/
  strictlyLE : model.IsStrictlyLE upper
  /-- Every term is stalkwise flat over the base. -/
  flatOverBase (i : ℤ) :
    Scheme.Modules.IsFlatOver (openSubset.ι ≫ p) (model.X i)
  /-- The model represents the exact restriction of the original object. -/
  represents : (SchemeDerivedCategory.Q openSubset.toScheme).obj model ≅
    (SchemeBaseChange.derivedPullback (relativeOpenTo p openSubset)).obj E.obj

/-- Local finite Tor amplitude over `S`, witnessed pointwise by bounded
stalkwise-flat models on actual open neighbourhoods. -/
def schemeLocallyFiniteTorAmplitudeOver {X S : Scheme.{u}} (p : X ⟶ S) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ ∀ x : X, Nonempty (LocalFiniteTorAmplitudeChart p E x)

namespace LocalFiniteTorAmplitudeChart

/-- Transport a chart along an isomorphism of objects: the same model represents the
isomorphic object. -/
def ofIso {X S : Scheme.{u}} {p : X ⟶ S} {E F : SchemeQuasicoherentDerivedCategory X}
    (e : E ≅ F) {x : X} (c : LocalFiniteTorAmplitudeChart p E x) :
    LocalFiniteTorAmplitudeChart p F x where
  __ := c
  represents := c.represents ≪≫
    (SchemeBaseChange.derivedPullback (relativeOpenTo p c.openSubset)).mapIso
      ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)

/-- The cohomology of a chart's model is the restriction of the cohomology of the object.
Restriction along an open immersion is exact, so it commutes with derived-category
cohomology. -/
def homologyIso {X S : Scheme.{u}} {p : X ⟶ S}
    {E : SchemeQuasicoherentDerivedCategory X} {x : X}
    (c : LocalFiniteTorAmplitudeChart p E x) (n : ℤ) :
    c.model.homology n ≅
      ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj).restrict c.openSubset.ι :=
  ((DerivedCategory.homologyFunctorFactors _ n).app c.model).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso c.represents ≪≫
    mapDerivedCategoryHomologyIso (modulePullback (relativeOpenTo p c.openSubset))
      inferInstance inferInstance inferInstance E.obj n ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback c.openSubset.ι).symm.app _

end LocalFiniteTorAmplitudeChart

instance schemeLocallyFiniteTorAmplitudeOver_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeLocallyFiniteTorAmplitudeOver p).IsClosedUnderIsomorphisms where
  of_iso e hE x := (hE x).map (LocalFiniteTorAmplitudeChart.ofIso e)

/-- On a quasi-compact scheme, local finite Tor amplitude bounds an object above: finitely
many charts cover the scheme, and the largest of their upper bounds bounds the cohomology.

`CompactSpace X` cannot be dropped. On the disjoint union `X = ∐_{n : ℕ} Spec k` of copies
of the spectrum of a field, over itself, let `E` restrict to `𝒪` placed in degree `n` on the
`n`-th copy. It has a one-term chart at every point, but `Hⁿ(E) ≠ 0` for every `n ≥ 0`, so it
is not bounded above. -/
theorem minus_of_schemeLocallyFiniteTorAmplitudeOver {X S : Scheme.{u}} {p : X ⟶ S}
    [CompactSpace X] {E : SchemeQuasicoherentDerivedCategory X}
    (hE : schemeLocallyFiniteTorAmplitudeOver p E) :
    (DerivedCategory.TStructure.t (C := X.Modules)).minus E.obj := by
  let c := fun x ↦ (hE x).some
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ ((c x).openSubset : Set X)) (fun x ↦ (c x).openSubset.isOpen)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, (c x).mem_openSubset⟩)
  obtain ⟨N, hN⟩ := Finset.exists_le (t.image fun x ↦ (c x).upper)
  refine ⟨N, (DerivedCategory.isLE_iff E.obj N).2 fun i hi ↦ ?_⟩
  refine Scheme.Modules.isZero_of_isZero_restrict _ (fun x : t ↦ (c x).openSubset)
    (fun y ↦ ?_) (fun x ↦ ?_)
  · obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨x, hx⟩, hy⟩
  · have hle : (c x).upper < i :=
      lt_of_le_of_lt (hN _ (Finset.mem_image_of_mem _ x.2)) hi
    have := (c x).strictlyLE
    exact (((c x).model.exactAt_of_isLE (c x).upper i hle).isZero_homology).of_iso
      ((c x).homologyIso i).symm

/-- A bounded local model whose terms are finitely presented and flat over the base: the
local condition in Lieblich's relative perfection (Lieblich, Definition 2.1.1). Finitely
presented module sheaves are quasi-coherent, so the terms are the finitely presented,
quasi-coherent, base-flat modules of that definition. -/
structure LocalRelativePerfectChart {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) (x : X)
    extends LocalFiniteTorAmplitudeChart p E x where
  /-- Every term is of finite presentation. -/
  finitePresentation (i : ℤ) : SheafOfModules.IsFinitePresentation.{u, u, u} (model.X i)

/-- Transport a relative-perfect chart along an isomorphism of objects. -/
def LocalRelativePerfectChart.ofIso {X S : Scheme.{u}} {p : X ⟶ S}
    {E F : SchemeQuasicoherentDerivedCategory X} (e : E ≅ F) {x : X}
    (c : LocalRelativePerfectChart p E x) : LocalRelativePerfectChart p F x where
  toLocalFiniteTorAmplitudeChart := c.toLocalFiniteTorAmplitudeChart.ofIso e
  finitePresentation := c.finitePresentation

/-- On a locally Noetherian scheme, the cohomology of an object restricted to a
relative-perfect chart is finitely presented. There finitely presented module sheaves are
closed under kernels and cokernels (`Scheme.coherent_isClosedUnderKernels`,
`Scheme.coherent_isClosedUnderCokernels`), so the cohomology of the finitely presented model
is finitely presented. -/
theorem LocalRelativePerfectChart.isFinitePresentation_homology_restrict
    {X S : Scheme.{u}} {p : X ⟶ S} [IsLocallyNoetherian X]
    {E : SchemeQuasicoherentDerivedCategory X} {x : X}
    (c : LocalRelativePerfectChart p E x) (n : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      (((DerivedCategory.homologyFunctor X.Modules n).obj E.obj).restrict c.openSubset.ι) := by
  have : IsLocallyNoetherian c.openSubset.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion c.openSubset.ι
  let P := Scheme.coherent c.openSubset.toScheme
  let K := c.model.sc n
  have hK : P (kernel K.g) :=
    P.prop_kernel _ (c.finitePresentation _) (c.finitePresentation _)
  have hH : P (cokernel (kernel.lift K.g K.f K.zero)) :=
    P.prop_cokernel _ (c.finitePresentation _) hK
  exact P.prop_of_iso (K.homologyIsoCokernelLift.symm ≪≫ c.homologyIso n) hH

/-- Relative perfection over `p`: every point of `X` has an open neighbourhood on which
the object is represented by a bounded complex of finitely presented module sheaves that are
flat over `S`.

This is Lieblich's relative perfection (Lieblich, *Moduli of complexes on a proper
morphism*, Definition 2.1.1) for the Zariski topology: Lieblich asks for such a model on a
covering of the final object of a topos. It is condition (A) of Stacks Remark 36.35.14
(Tag 0DI9). For `p` flat and locally of finite presentation, that remark states the agreement
with Stacks Definition 36.35.1 (Tag 0DI0), pseudo-coherence with locally finite Tor dimension
over `p⁻¹𝒪_S`. That agreement is not proved here.

The definition makes no demand on the cohomology sheaves. The cohomological criterion
`schemePseudoCoherent` is not stable under base change to non-Noetherian schemes. Let
`X = S = Spec ℤ[x]` and `p = 𝟙`. The complex `E = [𝒪 --x--> 𝒪]` in degrees `-1` and `0`
is relatively perfect and satisfies `schemePseudoCoherent`. Its derived base change along
`Spec (ℤ[x, y₁, y₂, …] ⧸ (x yᵢ)ᵢ) ⟶ S` is the same two-term complex there, still
relatively perfect, but its `H⁻¹` comes from the annihilator of `x`, the ideal
`(y₁, y₂, …)`, which is not finitely generated. The criterion is recovered on quasi-compact,
locally Noetherian schemes by `schemeRelativePerfect_le_schemePseudoCoherent`.

The definition takes an arbitrary morphism; the intended moduli context is a
flat, locally finitely presented family, and geometric theorems state those
hypotheses where they use them rather than here (see
`SchemeRelativePerfectCategory`). -/
def schemeRelativePerfect {X S : Scheme.{u}} (p : X ⟶ S) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ ∀ x : X, Nonempty (LocalRelativePerfectChart p E x)

instance schemeRelativePerfect_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeRelativePerfect p).IsClosedUnderIsomorphisms where
  of_iso e hE x := (hE x).map (LocalRelativePerfectChart.ofIso e)

/-- Relative perfection forgets to local finite Tor amplitude. -/
theorem schemeRelativePerfect_le_schemeLocallyFiniteTorAmplitudeOver {X S : Scheme.{u}}
    (p : X ⟶ S) : schemeRelativePerfect p ≤ schemeLocallyFiniteTorAmplitudeOver p :=
  fun _ hE x ↦ (hE x).map LocalRelativePerfectChart.toLocalFiniteTorAmplitudeChart

/-- On a locally Noetherian scheme, a relative-perfect object has finitely presented
cohomology in every degree. Finite presentation is local, and on each chart it holds by
`LocalRelativePerfectChart.isFinitePresentation_homology_restrict`.

`IsLocallyNoetherian X` cannot be dropped. Let `X = Spec A` over itself, with
`A = ℤ[x, y₁, y₂, …] ⧸ (x yᵢ)ᵢ`, and let `E = [𝒪 --x--> 𝒪]` in degrees `-1` and `0`. It is
relatively perfect, but `H⁻¹(E)` comes from the annihilator of `x`, the ideal
`(y₁, y₂, …)`, which is not finitely generated. -/
theorem isFinitePresentation_homology_of_schemeRelativePerfect {X S : Scheme.{u}}
    {p : X ⟶ S} [IsLocallyNoetherian X] {E : SchemeQuasicoherentDerivedCategory X}
    (hE : schemeRelativePerfect p E) (n : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u}
      ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj) := by
  let c := fun x ↦ (hE x).some
  have hcover : ⨆ x, (c x).openSubset = ⊤ :=
    eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, (c y).mem_openSubset⟩
  refine SheafOfModules.IsFinitePresentation.of_coversTop
    ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj) (fun x ↦ (c x).openSubset)
    (TopCat.Opens.grothendieckTopology_coversTop _ hcover) fun x ↦ ?_
  have := ((c x).openSubset.ι.isFinitePresentation_over_iff_restrict _).2
    ((c x).isFinitePresentation_homology_restrict n)
  rwa [Scheme.Opens.opensRange_ι] at this

/-- On a quasi-compact, locally Noetherian scheme, relative perfection implies the
cohomological criterion `schemePseudoCoherent`: finitely many charts bound the object above
(`minus_of_schemeLocallyFiniteTorAmplitudeOver`), and its cohomology is finitely presented
(`isFinitePresentation_homology_of_schemeRelativePerfect`).

Neither hypothesis can be dropped.
* `IsLocallyNoetherian X`: on `X = Spec (ℤ[x, y₁, y₂, …] ⧸ (x yᵢ)ᵢ)` over itself,
  `[𝒪 --x--> 𝒪]` is relatively perfect and `X` is quasi-compact, but its `H⁻¹` comes from
  the ideal `(y₁, y₂, …)`, which is not finitely generated.
* `CompactSpace X`: on the disjoint union `∐_{n : ℕ} Spec k` over itself, the object that
  is `𝒪` in degree `n` on the `n`-th copy is relatively perfect and `X` is locally
  Noetherian, but it is not bounded above.

The converse is not proved here. -/
theorem schemeRelativePerfect_le_schemePseudoCoherent {X S : Scheme.{u}} (p : X ⟶ S)
    [IsLocallyNoetherian X] [CompactSpace X] :
    schemeRelativePerfect p ≤ schemePseudoCoherent X := fun _ hE ↦
  ⟨minus_of_schemeLocallyFiniteTorAmplitudeOver
      (schemeRelativePerfect_le_schemeLocallyFiniteTorAmplitudeOver p _ hE),
    isFinitePresentation_homology_of_schemeRelativePerfect hE⟩

/-- The full category cut out by relative perfection over `p`.  Geometric
theorems about this category state flatness, finite-presentation, and
Noetherian hypotheses where they are actually used rather than storing inert
typeclass arguments in the category abbreviation. -/
abbrev SchemeRelativePerfectCategory {X S : Scheme.{u}} (p : X ⟶ S) :=
  (schemeRelativePerfect p).FullSubcategory

namespace SchemeRelativePerfectCategory

/-- A relative-perfect object with bounded coherent cohomology has a
`Dᵇ(Coh X)` representative once the bounded-coherent `Dqc` identification is
supplied explicitly. -/
theorem exists_boundedCoherentRepresentative {X S : Scheme.{u}}
    [IsLocallyNoetherian X] {p : X ⟶ S}
    (h : HasBoundedCoherentDqcIdentification X)
    (E : SchemeRelativePerfectCategory p)
    (hE : schemeBoundedCoherentCohomology X E.obj) :
    ∃ F : SchemeBoundedCoherentDerivedCategory X,
      Nonempty (((boundedCoherentDerivedToDqc X).obj F).obj ≅ E.obj) := by
  let E' : SchemeBoundedCoherentDqcCategory X := ⟨E.obj, hE⟩
  refine ⟨boundedCoherentRepresentative X h E', ⟨?_⟩⟩
  exact (SchemeBoundedCoherentDqcCategory.ι X).mapIso
    (boundedCoherentRepresentativeIso X h E')

/-- For a relative-perfect object, the explicit compact/perfect comparison
identifies membership in the absolute perfect locus with compactness in
`Dqc(X)`. -/
theorem perfect_iff_compact {X S : Scheme.{u}} [IsLocallyNoetherian X]
    {p : X ⟶ S} (h : PerfectObjectsAreCompactInDqc X)
    (E : SchemeRelativePerfectCategory p) :
    schemePerfectInDqc X E.obj ↔ IsCompactObject.{0} E.obj :=
  schemePerfectInDqc_iff_isCompact X h E.obj

end SchemeRelativePerfectCategory

/-- A global stalkwise-flat model computing one geometric fiber. This
does not inhabit the arbitrary left-derived pullback interface: it records the
precise model from which the displayed fiber object is computed. -/
structure GeometricFiberModel {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) (s : S) where
  /-- A complex representing the total object. -/
  totalModel : CochainComplex X.Modules ℤ
  /-- The total model represents `E`. -/
  represents : (SchemeDerivedCategory.Q X).obj totalModel ≅ E.obj
  /-- Every term is stalkwise flat over `S`. -/
  flatOverBase (i : ℤ) : Scheme.Modules.IsFlatOver p (totalModel.X i)

namespace GeometricFiberModel

/-- The degreewise pullback of a chosen flat model to the scheme-theoretic
fiber. -/
def fiberComplex {X S : Scheme.{u}} {p : X ⟶ S}
    {E : SchemeQuasicoherentDerivedCategory X} {s : S}
    (M : GeometricFiberModel p E s) :
    CochainComplex (p.fiber s).Modules ℤ :=
  ((Scheme.Modules.pullback (p.fiberι s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj M.totalModel

/-- The geometric fiber object computed in the ambient derived category.
No claim identifies the ambient category with `Dqc`; quasi-coherence of this
object is a separate comparison theorem once arbitrary left-derived pullback
has been constructed. -/
def fiberObject {X S : Scheme.{u}} {p : X ⟶ S}
    {E : SchemeQuasicoherentDerivedCategory X} {s : S}
    (M : GeometricFiberModel p E s) : SchemeDerivedCategory (p.fiber s) :=
  (SchemeDerivedCategory.Q (p.fiber s)).obj M.fiberComplex

end GeometricFiberModel

/-- Explicit geometric fibers of a relative-perfect object together with
negative self-Ext vanishing on every fiber. -/
structure UniversallyGluableData {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) where
  /-- A flat model computing every geometric fiber. -/
  fiberModel (s : S) : GeometricFiberModel p E s
  /-- Negative self-extensions vanish on every geometric fiber. -/
  negativeExtVanishes (s : S) (n : ℤ) (hn : n < 0)
      (f : (fiberModel s).fiberObject ⟶
        (fiberModel s).fiberObject⟦n⟧) : f = 0

/-- The relative-perfect, universally-gluable locus. -/
def schemeUniversallyGluableRelativePerfect {X S : Scheme.{u}}
    (p : X ⟶ S) : ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ schemeRelativePerfect p E ∧ Nonempty (UniversallyGluableData p E)

namespace UniversallyGluableData

/-- Transport universally-gluable fiber data along an isomorphism of total
objects.  The same flat models compute the fibers; only their representing
isomorphisms change. -/
def ofIso {X S : Scheme.{u}} {p : X ⟶ S}
    {E F : SchemeQuasicoherentDerivedCategory X} (e : E ≅ F)
    (h : UniversallyGluableData p E) : UniversallyGluableData p F where
  fiberModel s := {
    totalModel := (h.fiberModel s).totalModel
    represents := (h.fiberModel s).represents ≪≫
      (SchemeQuasicoherentDerivedCategory.ι X).mapIso e
    flatOverBase := (h.fiberModel s).flatOverBase }
  negativeExtVanishes s n hn f := h.negativeExtVanishes s n hn f

end UniversallyGluableData

instance schemeUniversallyGluableRelativePerfect_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeUniversallyGluableRelativePerfect p).IsClosedUnderIsomorphisms where
  of_iso e hE := ⟨
    (schemeRelativePerfect p).prop_of_iso e hE.1,
    hE.2.map (UniversallyGluableData.ofIso e)⟩

/-- The full category of relative-perfect universally-gluable complexes. -/
abbrev SchemeUniversallyGluableCategory {X S : Scheme.{u}} (p : X ⟶ S) :=
  (schemeUniversallyGluableRelativePerfect p).FullSubcategory

/-! ## Concrete models for the canonical Dqc zero -/

/-- The zero cochain complex of module sheaves, named explicitly because the
object-level `0` notation is not exported by every derived-category import. -/
def zeroModuleComplex (X : Scheme.{u}) : CochainComplex X.Modules ℤ :=
  HomologicalComplex.zero

/-- The zero complex is a zero object. -/
theorem zeroModuleComplex_isZero (X : Scheme.{u}) :
    IsZero (zeroModuleComplex X) :=
  HomologicalComplex.isZero_zero

/-- The zero object is pseudo-coherent. -/
theorem schemePseudoCoherent_zero
    (X : Scheme.{u}) :
    schemePseudoCoherent X (SchemeQuasicoherentDerivedCategory.zero X) := by
  have hZ := SchemeQuasicoherentDerivedCategory.zero_obj_isZero X
  constructor
  · exact ⟨0,
      (DerivedCategory.TStructure.t (C := X.Modules)).isLE_of_isZero hZ 0⟩
  · intro n
    let H := (DerivedCategory.homologyFunctor X.Modules n).obj
      (SchemeQuasicoherentDerivedCategory.zero X).obj
    have hH : IsZero H :=
      (DerivedCategory.homologyFunctor X.Modules n).map_isZero hZ
    obtain ⟨Z, hZ', hP⟩ :=
      (Scheme.coherent X).exists_prop_of_containsZero
    exact (Scheme.coherent X).prop_of_iso
      (IsZero.iso hZ' hH) hP

/-- The zero object has a local finite-Tor-amplitude chart at every point. -/
def zeroLocalFiniteTorAmplitudeChart {X S : Scheme.{u}}
    (p : X ⟶ S) (x : X) :
    LocalFiniteTorAmplitudeChart p
      (SchemeQuasicoherentDerivedCategory.zero X) x where
  openSubset := ⊤
  mem_openSubset := trivial
  lower := 0
  upper := 0
  lower_le_upper := le_rfl
  model := zeroModuleComplex ((⊤ : X.Opens).toScheme)
  strictlyGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact isZero_zero _
  strictlyLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact isZero_zero _
  flatOverBase i y := by
    letI : PreservesFiniteLimits
        (Scheme.Modules.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y) :=
      Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits
        ((⊤ : X.Opens).toScheme) y
    let Z :=
      (ModuleCat.restrictScalars (((⊤ : X.Opens).ι ≫ p).stalkMap y).hom).obj
        ((Scheme.Modules.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y).obj
          ((zeroModuleComplex ((⊤ : X.Opens).toScheme)).X i))
    have hZ : IsZero Z :=
      (ModuleCat.restrictScalars (((⊤ : X.Opens).ι ≫ p).stalkMap y).hom).map_isZero
        ((Scheme.Modules.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y).map_isZero
          (by dsimp [zeroModuleComplex]; exact isZero_zero _))
    letI : Subsingleton Z := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact Module.Flat.of_free
  represents := IsZero.iso
    ((SchemeDerivedCategory.Q ((⊤ : X.Opens).toScheme)).map_isZero
      (zeroModuleComplex_isZero ((⊤ : X.Opens).toScheme)))
    ((SchemeBaseChange.derivedPullback
      (relativeOpenTo p ⊤)).map_isZero
        (SchemeQuasicoherentDerivedCategory.zero_obj_isZero X))

/-- The zero object has locally finite Tor amplitude over every base. -/
theorem schemeLocallyFiniteTorAmplitudeOver_zero {X S : Scheme.{u}}
    (p : X ⟶ S) :
    schemeLocallyFiniteTorAmplitudeOver p
      (SchemeQuasicoherentDerivedCategory.zero X) :=
  fun x ↦ ⟨zeroLocalFiniteTorAmplitudeChart p x⟩

/-- The zero chart is a relative-perfect chart: the zero module sheaf is finitely
presented. -/
def zeroLocalRelativePerfectChart {X S : Scheme.{u}} (p : X ⟶ S) (x : X) :
    LocalRelativePerfectChart p (SchemeQuasicoherentDerivedCategory.zero X) x where
  toLocalFiniteTorAmplitudeChart := zeroLocalFiniteTorAmplitudeChart p x
  finitePresentation i := by
    obtain ⟨Z, hZ, hP⟩ :=
      (Scheme.coherent ((⊤ : X.Opens).toScheme)).exists_prop_of_containsZero
    have h0 : IsZero ((zeroModuleComplex ((⊤ : X.Opens).toScheme)).X i) := by
      dsimp [zeroModuleComplex]
      exact isZero_zero _
    exact (Scheme.coherent ((⊤ : X.Opens).toScheme)).prop_of_iso (IsZero.iso hZ h0) hP

/-- The zero object is relative perfect. -/
theorem schemeRelativePerfect_zero {X S : Scheme.{u}}
    (p : X ⟶ S) :
    schemeRelativePerfect p (SchemeQuasicoherentDerivedCategory.zero X) :=
  fun x ↦ ⟨zeroLocalRelativePerfectChart p x⟩

/-- The zero total complex computes the zero object on every geometric
fiber. -/
def zeroGeometricFiberModel {X S : Scheme.{u}} (p : X ⟶ S) (s : S) :
    GeometricFiberModel p (SchemeQuasicoherentDerivedCategory.zero X) s where
  totalModel := zeroModuleComplex X
  represents := IsZero.iso
    ((SchemeDerivedCategory.Q X).map_isZero (zeroModuleComplex_isZero X))
    (SchemeQuasicoherentDerivedCategory.zero_obj_isZero X)
  flatOverBase i x := by
    letI : PreservesFiniteLimits (Scheme.Modules.moduleStalkFunctor X x) :=
      Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits X x
    let Z := (ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((Scheme.Modules.moduleStalkFunctor X x).obj
        ((zeroModuleComplex X).X i))
    have hZ : IsZero Z :=
      (ModuleCat.restrictScalars (p.stalkMap x).hom).map_isZero
        ((Scheme.Modules.moduleStalkFunctor X x).map_isZero
          (by dsimp [zeroModuleComplex]; exact isZero_zero _))
    letI : Subsingleton Z := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact Module.Flat.of_free

/-- The zero relative-perfect object is universally gluable. -/
def universallyGluableDataZero {X S : Scheme.{u}} (p : X ⟶ S) :
    UniversallyGluableData p
      (SchemeQuasicoherentDerivedCategory.zero X) where
  fiberModel := zeroGeometricFiberModel p
  negativeExtVanishes s n hn f := by
    exact ((SchemeDerivedCategory.Q (p.fiber s)).map_isZero
      (((Scheme.Modules.pullback (p.fiberι s)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map_isZero
          (zeroModuleComplex_isZero X))).eq_of_src f 0

/-- The relative-perfect universally-gluable locus is nonempty: it contains
the zero complex for every flat locally finitely presented family. -/
theorem schemeUniversallyGluableRelativePerfect_zero
    {X S : Scheme.{u}} (p : X ⟶ S) :
    schemeUniversallyGluableRelativePerfect p
      (SchemeQuasicoherentDerivedCategory.zero X) :=
  ⟨schemeRelativePerfect_zero p, ⟨universallyGluableDataZero p⟩⟩

end

end AlgebraicGeometry
