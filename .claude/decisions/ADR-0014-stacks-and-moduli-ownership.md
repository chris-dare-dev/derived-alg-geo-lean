# ADR-0014 — Stacks, algebraic spaces and moduli: one carrier, natural representability, a stability-free core

- **Status:** accepted
- **Date:** 2026-09-27 (America/New_York)
- **Decider:** Chris Dare
- **Recorded:** 2026-11-09 by MO2.1
  ([#1624](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1624)).
  Mathlib paths and line numbers are at the revision pinned in
  `lake-manifest.json` (v4.35.0, `56a005855ea1`); repository paths, line
  numbers and states are at main@7c1c3725.
- **Supersedes:** the path and ownership decisions of
  [ADR-0013](ADR-0013-moduli-infrastructure-ownership.md): its Decision list
  and the SF8/SF9 ownership lines under its Consequences. ADR-0013's choice of
  the monorepo, and its final trust clause, stay in force; the clause is
  restated in §7.
- **Decision:** every stack is a `CategoryTheory.StackInGroupoids`;
  representability is natural in the test object; a moduli problem is a
  prestack in groupoids cut out of a stack of categories; site-generic stacks,
  geometric stacks, algebraic spaces and moduli problems reach no stability
  condition; stability consumers are separate subcomponents.

## Context

ADR-0013 (2026-08-17) brought Quot schemes, stacks and good moduli into the
monorepo and named paths for them. Six weeks of construction showed that both
the paths and several constructions need revising.

- **The paths were not used.** Generic stacks in groupoids moved to
  `CategoryTheory/Sites/Descent/StackInGroupoids/` on 2026-09-01 (commit
  7d862cee), Tier 1 beside Mathlib's `CategoryTheory/Sites/Descent/`. Quot
  lives at `AlgebraicGeometry/Moduli/Quot/`, not `AlgebraicGeometry/Quot`.
  `AlgebraicGeometry/Moduli/GoodModuli` does not exist. The geometric stability
  consumers sit in `AlgebraicGeometry/Moduli/{Semistability,HarderNarasimhan}/`,
  and `AlgebraicGeometry/Moduli.lean` imports both, so importing the moduli
  umbrella imports Bridgeland stability.
- **Representability is pointwise (finding d1).**
  `CategoryTheory.StackMorphism.FiberRepresentation`
  (`DerivedAlgGeo/CategoryTheory/Sites/Descent/StackInGroupoids/Morphism.lean:76`)
  gives each test object `T` its own equivalence
  `Discrete (T ⟶ representing) ≌ f.FiberCategory y T`, with nothing relating
  the equivalences along a map of test objects. Every representability,
  property, diagonal and presentation notion in
  `AlgebraicGeometry/Stacks/{Algebraic,AlgebraicStack}.lean` and
  `AlgebraicGeometry/Moduli/PerfectComplex/Algebraicity.lean` inherits this.
  For an infinite field `k`, `X = Spec k[ε]/(ε²) ×ₖ 𝔸¹` and `R = 𝔸¹` have
  Hom-sets of the same cardinality from every test scheme, so
  `StackMorphism.IsSmoothSurjective` holds for the morphism of representable
  stacks induced by `X ⟶ Spec k`, which is not smooth.
- **The boundedness witness does not bound (finding d2).** In
  `AlgebraicGeometry.FiniteTypeBoundednessWitness`
  (`AlgebraicGeometry/Moduli/PerfectComplex/Boundedness.lean:103`),
  `geometricFiber x` is unrelated to `universalFamily`. The structure does not
  assert boundedness in the sense of arXiv:1902.08184v4, Definition 9.4, which
  requires the selected objects to be fibres of one family on a finite-type
  scheme.
- **Universes are tied (finding d3).** `StackInGroupoids` fixes `Cat.{w, w}`
  (`StackInGroupoids.lean:38`), while Mathlib's `Pseudofunctor.IsStack`
  (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:49`) allows
  `Cat.{v', u'}`.
- **Finite-type openness is vacuous.**
  `AlgebraicGeometry/Moduli/Semistability/FiniteType.lean:80` and the geometric
  base-change witness it consumes assume
  `[∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]`, which is false for
  every nonempty `S`.
- **Some capability classes are unpinned.** `HasDerivedPushforward`,
  `HasDerivedTensor` and `HasCoherentDerivedTensor` ask only for some exact
  functor, and the zero functor satisfies them. They are contracts, not
  constructions.

The stacks-and-moduli plan of 2026-09-27 answers these with milestones MO2
(this boundary), STK1–STK4 (stacks), ASP1 (algebraic spaces), DQ1 (derived
pushforward and base change), GM1–GM2 (good moduli spaces), PJ1 (projective
morphisms over a base), MOD1–MOD3 (moduli problems) and ART1 (Artin's axioms).
SF9 is re-scoped to its stability consumers, and SF13 and SF14 take BLMNPS
Part III and §§20–22. The plan, with the issue behind each milestone, is
`.claude/roadmap/stacks-and-moduli.yaml`.

## Decision

### 1. One carrier

The canonical stack is `CategoryTheory.StackInGroupoids`
(`DerivedAlgGeo/CategoryTheory/Sites/Descent/StackInGroupoids.lean:35`): a
groupoid-valued pseudofunctor on `LocallyDiscrete Cᵒᵖ` satisfying Mathlib's
`Pseudofunctor.IsStack`.

- Categories fibred over a base (Mathlib's `CategoryTheory/FiberedCategory/`:
  `Functor.IsFibered`, `HasFibers`, and the fibred Grothendieck construction
  `Pseudofunctor.CoGrothendieck`) are reached from the carrier only by a proved
  comparison (STK1.6, #1638), never by a second stack root.
- A moduli problem is a prestack in groupoids. No `ModuliProblem` carrier is
  introduced. The existing problem records become `abbrev`s or
  specializations of the carrier when their consumers are next rebuilt.

### 2. Universes

Fibres live in universes independent of the site, `Cat.{v', u'}`, as in
Mathlib's `IsStack`. The carrier's `Cat.{w, w}` is generalized (STK1.1,
#1631). Representable stacks are `ULift`ed into the fibre universe (STK1.7,
#1637).

### 3. The base

A relative stack over a scheme `S` is a stack on `Over S`, the repository's
`SchemeBaseChange S := Over S`
(`AlgebraicGeometry/DerivedCategory/Families/Scheme.lean:27`). One proved
comparison relates these to stacks on `Scheme` over the representable
`yoneda.obj S` (STK2.6, #1645). No second base convention is introduced.

### 4. Representability is natural, and the pointwise notions say what they are

A morphism of stacks is representable when its 2-fibre product with every
representable is representable, naturally in the test object (Stacks Project,
Tag 02Y4, Section 4.42; Tag 02ZW, Definition 94.9.1, for algebraic spaces). On
discrete stacks this agrees with Mathlib's `Functor.relativelyRepresentable`
and `MorphismProperty.presheaf`
(`Mathlib/CategoryTheory/MorphismProperty/Representable.lean:103`, `:330`).

- The existing pointwise notions keep their definitions and gain the
  qualifier `Pointwise` (MO2.4, #1626). A type-valued structure takes it as a
  prefix (`PointwiseFiberRepresentation`); a predicate named `Is…` or `Has…`
  takes it after the verb (`IsPointwiseRepresentable`,
  `HasPointwiseRepresentableProperty`), as Mathlib writes
  `HasPointwiseLeftKanExtension`. The list: `FiberRepresentation`,
  `IsRepresentable`, `FiberRepresentationWithProperty`,
  `HasRepresentableProperty`, the stack-morphism abbreviations
  `IsLocallyOfFinitePresentation`, `IsSmoothSurjective` and `IsOpenImmersion`,
  `DiagonalFiberRepresentation`, `HasRepresentableDiagonal`,
  `ZariskiStackPresentation(Over)`, `FppfStackPresentation(Over)` and the
  `RelativePerfect…ZariskiPresentation`s, together with every declaration and
  field whose name spells one of them.
- `RepresentableQuotientProblem` is an arbitrary represented presheaf, not a
  Quot functor; it becomes `RepresentedPresheafOver`.
  `FiniteTypeBoundednessWitness` does not bound; it becomes
  `PointwiseFiniteTypeCover`.
- The natural notions later take the standard names (STK1.4, #1636; STK3.1,
  #1684), each with a proved projection to its `Pointwise…` predecessor. The
  old names are not kept as library aliases, because the natural notions need
  them.

### 5. Moduli of objects is one construction

A local, pullback-stable, isomorphism-closed object property of a stack of
categories cuts out a substack, and the core of a stack of categories is a
stack in groupoids (STK1.5, #1634; this is the TODO at
`Mathlib/CategoryTheory/Bicategory/Functor/Cat/ObjectProperty.lean:19`).
Coh_{X/S}, vector bundles, flat objects in a heart and M_σ(v) are instances.

- `Dqc` is only a prestack.
- The stack property of Lieblich's M_pug is its own theorem (Stacks Project,
  Tag 0DLH, Lemma 99.16.6; #1736), not an instance of the construction above.

### 6. Order

First come algebraic stacks whose diagonal is representable by schemes
(STK3.1, #1684). They suffice for Coh_{X/S} (Tag 0DLY, Lemma 108.4.1) and for
complexes (Tag 0DPW, Lemma 108.12.1). Algebraic spaces come in parallel:
first as targets (Quot spaces and good moduli spaces), then with the standard
definition (Tag 025Y, Definition 65.6.1; ASP1.1, #1651), and then algebraic
stacks whose diagonal is representable by algebraic spaces (Tag 026O,
Definition 94.12.1; STK3.6, #1690), with STK3.1 as a special case.

### 7. Hard theorems are typed hypotheses over genuine definitions

Algebraicity (Artin, Lieblich; Tag 0DLN, Theorem 99.16.12), the existence of
good moduli spaces (Alper, Halpern-Leistner and Heinloth, arXiv:1812.01128v5,
Theorem A) and the representability of Quot functors enter consumer theorems
as explicit hypotheses whose statements use genuine definitions. The shape is
`(h : IsAlgebraic (Mpug X S))`; both names are illustrative. At main@7c1c3725
there is no `Mpug` and no algebraicity predicate for stacks; the existing
`CategoryTheory.Triangulated.StabilityCondition.WithClassMap.IsAlgebraic`
(an algebraic stability condition) is unrelated.

- Such a hypothesis is never a structure field, a typeclass instance, or an
  arbitrary `Prop` parameter. The former `Theorem22_2DependencyContract` was
  removed for exactly this reason
  (`.claude/roadmap/theorem22-2-dependencies.yaml:41`).
- Discharging such a hypothesis later must not change any consumer's
  statement.
- ADR-0013's clause stands: no structure field, typeclass instance or roadmap
  status may stand in for an unproved algebraicity, boundedness, properness or
  descent theorem.

### 8. Placement

A *target* is a confirmed destination with no module yet. It is never
imported and never documented as implemented.

| What | Path | State at main@7c1c3725 |
|---|---|---|
| Site-generic stacks: the carrier, morphisms, 2-fibre products, representable morphisms, substacks cut out by object properties | `CategoryTheory/Sites/Descent/` (Tier 1 beside Mathlib's `Sites/Descent/`; namespace `CategoryTheory`) | exists (`StackInGroupoids/`) |
| Pseudofunctor-level constructions: object-property loci, cores, transport | `CategoryTheory/Bicategory/Functor/Cat/` (Tier 1) | exists |
| Comparison with categories fibred in groupoids | `CategoryTheory/FiberedCategory/` (Tier 1 beside Mathlib's) | target (STK1.6) |
| Neutral moduli interfaces: the boundedness predicate and the family probes | `CategoryTheory/Moduli/` | `Boundedness.lean` exists; the probes arrive with MO2.5 (#1627) |
| Topologies on schemes and scheme-site descent | `AlgebraicGeometry/Sites/`, `AlgebraicGeometry/Modules/…` | `Sites/Comparison.lean` exists |
| Descent for modules | `Algebra/Category/ModuleCat/Descent/` (Tier 1 beside Mathlib's `Algebra/Category/ModuleCat/Descent.lean`) | target (STK2.3, #1644) |
| Algebraic spaces (a new object directory) | `AlgebraicGeometry/AlgebraicSpace/` | target (ASP1) |
| Algebraic stacks, their properties, valuative criteria | `AlgebraicGeometry/Stacks/` | exists (pointwise presentations only) |
| Test stacks Θ, B𝔾_m, ST_R | `AlgebraicGeometry/Stacks/Test/` | target (STK4.4, #1699) |
| Good, coarse and categorical moduli spaces | `AlgebraicGeometry/Stacks/ModuliSpace/` (not `Moduli/GoodModuli`) | target (GM1) |
| Moduli problems only: `Coherent/`, `Quot/`, `PerfectComplex/`, `Picard/`, `Heart/`, sheaf semistability | `AlgebraicGeometry/Moduli/` | `PerfectComplex/`, `Quot/` exist |
| Scheme realizations of the neutral family probes | `AlgebraicGeometry/Moduli/Probes.lean` | target (MO2.3, after MO2.5) |
| Stability consumers | `AlgebraicGeometry/Moduli/StabilityCondition/` (MO2.3, #1628, regroups `Moduli/Semistability/` and `Moduli/HarderNarasimhan/` there), `AlgebraicGeometry/DerivedCategory/Stability/`, `CategoryTheory/Triangulated/StabilityCondition/Families/` | the last two exist |

Dependencies run from site-generic stacks to geometric stacks and algebraic
spaces, from those to moduli problems, and from moduli problems to stability
consumers. Site-generic stacks, the neutral moduli interfaces, pseudofunctor
constructions, geometric stacks, algebraic spaces and moduli problems reach
neither the stability tree nor a stability-consuming subcomponent, and stacks
and algebraic spaces reach no moduli problem (the MO2.2 layering rule, #1625).
`AlgebraicGeometry/Moduli.lean` omits `Moduli/StabilityCondition/`, which the
top-level `AlgebraicGeometry` umbrella imports directly, as it already does
for `DerivedCategory/Stability/` (MO2.3).

| ADR-0013 said | ADR-0014 says |
|---|---|
| relative-perfect objects and their moduli problem under `AlgebraicGeometry/Moduli/PerfectComplex` | unchanged for the moduli problem; the relative-perfect predicates are at `AlgebraicGeometry/DerivedCategory/Perfect/` since MO1.11 |
| Quot and bounded parameter spaces under `AlgebraicGeometry/Quot` | `AlgebraicGeometry/Moduli/Quot/` (the problem); Quot spaces as algebraic spaces or schemes are MOD3 targets |
| stacks in groupoids and descent under `AlgebraicGeometry/Stacks` | site-generic stacks under `CategoryTheory/Sites/Descent/`; algebraic stacks under `AlgebraicGeometry/Stacks/` |
| good moduli under `AlgebraicGeometry/Moduli/GoodModuli` | `AlgebraicGeometry/Stacks/ModuliSpace/` |
| stability-specific use under `CategoryTheory/Triangulated/StabilityCondition/Families` | the three stability-consumer paths in the table above |

### 9. Adoption

Each new root names two independent consumers, and the first is not a
Bridgeland stability condition. Vector bundles inside Coh_{X/S} test open
substacks; affine GIT quotients test good moduli spaces; quotient stacks test
Θ-reductivity and S-completeness.

## Consequences

- The SF8/SF9 ownership lines of ADR-0013 are replaced. STK1–STK4 own the
  stack substrate, ASP1 algebraic spaces, GM1–GM2 good moduli spaces,
  MOD1–MOD3 the moduli problems, DQ1 derived pushforward and base change on
  `Dqc`, PJ1 projective morphisms over a base, and ART1 the route to
  algebraicity. SF8 keeps relative-perfect objects and arbitrary derived
  pullback (#554). SF9 keeps only its stability consumers, and SF13 and SF14
  own BLMNPS Part III and §§20–22.
- ADR-0013's temporary edge is gone: `AlgebraicGeometry/Moduli/PerfectComplex/`
  reaches no stability module at main@7c1c3725, and the MO1.11 rule holds the
  predicates at `AlgebraicGeometry/DerivedCategory/Perfect/`.
- Paths move and fully qualified names do not
  (`docs/architecture/placement.md`, the agreed owner map), except for the
  owner-approved renames of §4. A historical spelling survives only where an
  immutable review payload needs it, through `exe/RestateHistoricalNames.lean`;
  none of the renamed names occurs in `attest/review.yaml`.
- Every issue in the plan above cites this record for its carrier, universes,
  base, representability, placement and hypothesis policy instead of
  re-deciding them.

## Non-claims

- This record proves nothing. No stack, algebraic space, good moduli space or
  moduli problem named in §8 exists before its issue lands, and a target path
  is not an implemented import.
- It does not assert that any existing presentation is an algebraic stack,
  that any finite-type cover bounds, or that any semistable locus of a genuine
  family is open.
- It does not choose a proof route for algebraicity (ART1.1, #1752 decides) or
  for the existence of good moduli spaces (GM2.5, #1721 decides).
