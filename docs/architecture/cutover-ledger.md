# Structural cutover ledger

This ledger records known ownership defects that have been confirmed by the
signature test in `placement.md`. It is a migration queue, not an allowlist:
new code must use the canonical owner immediately, and touching one of these
blocks should normally move it rather than add more declarations beside it.

## Mathematical ownership review: agreed owners and cutover map (2026-09-13)

The [MO1 execution plan](../reviews/2026-09-13-mathematical-ownership-plan.md)
tracks the [fifteen review findings](../reviews/2026-09-13-mathematical-ownership-review.md)
in [milestone 52](https://github.com/chris-dare-dev/derived-alg-geo-lean/milestone/52).
The standing [ownership policy](mathematical-ownership.md) and matching
`CLAUDE.md`/`AGENTS.md` checklist codify the foundation/application boundary.
This section is the other half MO1.01
([#1312](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/1312))
owes: the agreed destination for each confirmed finding, at declaration
granularity, settled **before** any source moves. The policy decides how to
choose an owner; the map below records the decision already taken for each of
the fifteen findings, so an implementing pull request cites a row instead of
re-deriving it. Codifying the policy moved no Lean declaration, and neither
does this map.

It is a queue of pending cutovers, not a record of completed roots and not a
policy exemption. A path named here is the target even before the move lands,
as the "Confirmed next lanes" convention already says; but nothing here is
built, and none of it discharges a mathematical obligation. CA1--CA3 retain
their charge, pairing and tilt mathematics; SRF1, DG3, DT1 and SF8 retain their
theorem obligations. A new name or directory does not supply a geometric
realization, a support condition, exactness, bounded tensor closure, or
standard pseudo-coherence on an arbitrary base.

### Five standing decisions, applying to every row below

1. **Paths move; namespaces do not.** Every row relocates files and leaves
   fully qualified declaration names untouched. `CLAUDE.md` already blesses the
   divergence -- Mathlib's `MetricSpace/Pseudo/` has namespace and path differ
   too -- and a namespace cutover would invalidate the immutable review
   payloads that `exe/RestateHistoricalNames.lean` exists to protect. Where a
   row's destination makes the retained namespace read oddly
   (`CategoryTheory.SerreFunctor` declarations in a linear Yoneda file is the
   sharpest case), the oddity is accepted and recorded here rather than
   repaired by a rename. A namespace cutover is a separate, separately
   justified change, and MO1 does not authorize one.
2. **A new carrier needs a named independent consumer.** Per
   `docs/architecture/abstraction-tree.md`, a proposed new root is justified
   only by a consumer that is not the module it was extracted from. Rows that
   cannot name one say so, and resolve to a theorem, an `abbrev`, or a move
   into an existing owner instead of a new hierarchy. No row below authorizes
   an empty speculative directory or a mass rename.
3. **Three graphs, not one.** A directory is an index; the Lean import graph is
   the dependency DAG; specialization and comparison maps form a third graph.
   They must be consistent and cannot be identical. Each row therefore names
   the *definition owner*, the *neutral core*, the *application adapter* and
   the *comparison owner* separately, because collapsing them is the defect the
   review found.
4. **No retired-path shims.** A move updates imports, umbrellas, audits and
   declaration-sweep routing in the same pull request; the vacated path is
   added to `RETIRED_PATHS` in `scripts/check_layering.py`. Nothing is left
   behind re-exporting its new owner.
5. **Hypotheses travel with the declaration.** Relocation never strengthens or
   silently discharges a hypothesis. Named cases: Hom-finiteness for Serre full
   faithfulness; the codimension-four bound on `sqrtComp`; the Noetherian
   caveat on the bounded-above finitely-presented-cohomology predicate; the
   `(n, m) = (3, 2)` distinction between variety dimension and truncation
   degree; `Dᵇ(Coh X)` not being closed under arbitrary derived tensor on a
   singular scheme.

### The shared CA path contract

Settled here so MO1.02--MO1.06 and CA1--CA3 cannot drift apart:

- **Neutral paired complex functionals live in linear algebra.** The complex
  functional built from two polar pairings, its additivity, its real linearity
  and the description of its kernel are bilinear algebra and stay under
  `LinearAlgebra/`. The *interpretation* of that kernel theorem as a support
  property is a stability adapter and does not.
- **Stability charge families live upstream of `Walls/`.** `ChargeFamily`,
  `Exp.ofMoments` and the divisorial constructors are inputs to a wall
  question, not consequences of one, so `Walls/` imports them and not the
  reverse. They stay inside the stability subject; they do not move into
  `AlgebraicGeometry/`.
- **Geometric Chern/Todd realizations live under `AlgebraicGeometry/`.** The
  scheme-level characteristic-class realizations and their numerical models
  belong to geometry and import the neutral charge root.
- **Single roots are preserved.** `#1223` and `#1230` keep the single charge
  kernel, the public `Mukai.pairing` root and the weighted/factor-of-two
  comparisons. No row creates a second charge carrier, a second pairing root,
  or a competing graded root; the optional graded root remains CA3's decision
  and may still conclude that none is justified.

### The owner map

Columns are the four relationships of decision 3. "--" means the row has no
declaration of that kind. Paths are below `DerivedAlgGeo/` unless marked
otherwise; issue numbers are the implementing task.

#### 01 -- Complex linear functionals vs. central-charge applications (#1313)

| Relationship | Owner |
| --- | --- |
| Definition owner | `LinearAlgebra/QuadraticForm/ComplexPairing.lean` keeps the paired functional, its additivity, real linearity and kernel description |
| Neutral core | `QuadraticForm/Continuous.lean` owns continuity; `QuadraticForm/Bounds.lean` owns positive-definite coercivity and bounded level sets; `OrthogonalityFiniteness.lean` consumes them |
| Application adapter | `StabilityCondition/CentralCharge/Quadratic.lean` owns the orthogonality-locus and positive-plane readings; `Support/Divisorial.lean` owns the full support-property adapter |
| Comparison owner | unchanged: `Weak/Support/Predicate/Quadratic.lean` already records that negative definiteness on `ker Z` is one part of the quadratic support criterion and that nonnegativity on the relevant semistable classes is a further requirement |

Independent consumer for the extracted neutral modules: the wall-finiteness
argument and the support predicate are two different consumers of the same
coercivity statement, which is what justifies extracting it rather than
inlining it. This is a split, not a move into algebraic geometry: the present
definition mentions no category, heart, Chern character or scheme.

#### 02 -- Positive planes, positive frames and the wall loci (#1314)

| Relationship | Owner |
| --- | --- |
| Definition owner | `QuadraticForm/PositivePlane.lean` owns `IsPositivePlane` and `positivePlanes`; `PositiveFrame.lean` owns `IsPositiveFrame`, `positiveFrames`, `framePlane` and `forgetPositiveFrame` |
| Neutral core | `OrthogonalityLocus.lean` owns `orthogonalityLocus` and `positivePlanesAway`; `OrthogonalityFiniteness.lean`, `OrthogonalityRegion.lean` and `OrthogonalityCutNonempty.lean` retain the arrangement results independently of stability |
| Application adapter | `CentralCharge/Family.lean` owns `zeroLocus`; `Walls/Alignment.lean` owns `alignmentValue`, `alignmentLocus` and the nonzero, positive-sign `positiveRayLocus`; `Walls/Spherical/Basic.lean` owns `nonpositiveRayLocus`; `Chambers/Basic.lean` owns the stability-space `chargeZeroLocus` |
| Comparison owner | `Spherical/WallComparison.lean` makes `chartFrame → chartPlane` explicit and compares orthogonality with the signed-ray locus; `Chambers/Basic.lean` compares stability-space vanishing with `ChargeFamily.zeroLocus`; a K3 identification with a framed geometric domain remains with its realization |

No `RealCodimensionOneSubmanifold` parent is created: `Z(δ) = 0` is generically
two real equations and phase alignment is generically one, still requiring
nonvanishing, a sign and destabilizing objects to describe an actual wall. No
`Walls/Actual/` directory is created until there is destabilization content to
put in it -- an empty speculative hierarchy is exactly what decision 2
forbids. Nothing moves into `Geometry/Manifold`; the plane API supplies no
manifold theorem.

#### 03 -- Hyperbolic extension algebra vs. geometric Mukai (#1315)

| Relationship | Owner |
| --- | --- |
| Definition owner | the `ℤ × N × ℤ` carrier with pairing `b(c,c') - rs' - r's` is an abstract hyperbolic extension and gets a neutral owner beside the bilinear-form API it is built from |
| Neutral core | norm-minus-two reflections and rank-two Gram-determinant identities, restated over an arbitrary ambient lattice rather than this one extension |
| Application adapter | the Mukai vector, integral structure and the actual surface realization stay in `AlgebraicGeometry/Numerical/Mukai/` and the surface modules; the exponential chart goes with numerical central-charge construction, not with the quadratic extension |
| Comparison owner | the Euler-pairing comparison stays where it is and is not absorbed into either side |

`IsSpherical` and `expectedDim = square + 2` are application vocabulary sitting
on a neutral carrier: the neutral statement is a root or square condition, and
spherical-object terminology plus expected moduli dimension stay with the
application. "Lattice" must not silently imply finite free or nondegenerate;
an arbitrary additive group with a form is neither. Native prerequisites
`#1223` and `#1229` are load-bearing here, not procedural.

**Definition owner landed 2026-09-14.** The ring-general carrier and pairing
moved to `LinearAlgebra/BilinearForm/Hyperbolic.lean`, beside the
`LinearMap.BilinMap` API they are built from, and `Lattice/Mukai/Basic.lean`
now imports them. Declaration names and the `Mukai` namespace are unchanged:
this is a change of owner, not of vocabulary, and a namespace cutover would
invalidate the immutable review payloads `exe/RestateHistoricalNames.lean`
exists to protect. `HodgeIndex.lean` is the precedent for a neutral path
keeping its consumer's namespace.

**Reflections landed 2026-09-15.** `BilinearForm/Reflection.lean` states the
norm-minus-two reflection over an arbitrary `(R, M, B)`, and
`Lattice/Mukai/Reflection.lean` specialises it at `pairingBilin b`, keeping
every public name its four `SphericalTwist` consumers spell. `-2` is the
hypothesis rather than an `IsSpherical`-shaped predicate: spherical-class
vocabulary is application vocabulary and stays with the application, which is
also what lets the neutral file be importable without the Mukai extension.

Restating it over an arbitrary form made the hypothesis split visible, and it
is not the expected one: additivity needs neither symmetry nor `B s s = -2`,
involutivity needs `B s s = -2` alone, and only the isometry needs symmetry.

**Rank-two Gram landed 2026-09-15**, completing the neutral core.
`BilinearForm/RankTwo.lean` states the Gram determinant, the change-of-basis
identity, `orthWitness` and the hyperbolic-pair predicate over an arbitrary
`(R, M, B)`, and `Lattice/Mukai/RankTwo.lean` specialises them. The file splits
where order is needed: `gram`, `gram_lincomb` and `orthWitness` need only a
commutative ring, and `apply_orthWitness` needs no symmetry either, while
`IsHyperbolicPair` and everything reading a sign need a linear order and a
strict ordered ring.

`HasSphericalClass` and `HasIsotropicClass` stayed with the Mukai lane, and so
did `IsSpherical` and `expectedDim = square + 2`. That is the application
vocabulary row discharged: all three neutral owners import Mathlib and nothing
else, so the general theory is importable with no Mukai extension in scope, and
the `-2` and `0` conditions appear in the neutral statements as hypotheses
rather than as named predicates.

**The exponential chart row is blocked, and not by effort.** The ledger asks
for the chart to go with the numerical central-charge construction. It cannot
move alone: `Lattice/Mukai/CentralCharge.lean` consumes `expRe`/`expIm`, and
`StabilityCondition/CentralCharge/Quadratic.lean` already imports
`Lattice/Mukai/CentralCharge.lean`, so relocating the chart into the
central-charge tree closes an import cycle. The layering gate does not catch
this -- it passes on a `LinearAlgebra` to `StabilityCondition` edge -- Lean's
module acyclicity does. Discharging the row means moving the whole real-Mukai
to charge bridge (`Mukai/CentralCharge.lean`, `ExponentialOrientation.lean`,
`IntegralBridge.lean`) out of `LinearAlgebra/Lattice/`, which is coupled to
MO1.02's central-charge ownership and is a lane of its own.

The tracker closed #1315 early -- a commit message in #1345 that said it did
*not* close the issue was read by GitHub as a closing keyword -- so the issue
state is not evidence about any of these rows.

#### 04 -- Charge construction upstream of walls (#1313)

| Relationship | Owner |
| --- | --- |
| Definition owner | `StabilityCondition/CentralCharge/` holds the family, exponential, numerical, divisorial and quadratic charge constructors formerly owned by `Walls/` |
| Neutral core | Hodge-signature linear algebra lives in `LinearAlgebra/BilinearForm/HodgeIndex.lean` |
| Application adapter | geometric Chern/Todd realizations stay under `AlgebraicGeometry/Numerical/`; semistable support statements live under `StabilityCondition/Support/` |
| Comparison owner | the existing specialization maps out of `ChargeFamily` and `Exp.ofMoments` are preserved as they stand |

Independent consumer: the surface, threefold, slope and divisorial charge
constructions each consume the family root without asking a wall question,
which is the justification for the root existing upstream of `Walls/`. Rule 8
pins six divisorial charge structures to `CentralCharge/Divisorial/`, three
Hodge structures to their neutral owner, and checks the transitive closures of
the neutral owners and
the entire `CentralCharge/` subtree. No second common central-charge record is
introduced merely to improve names.

**Landed 2026-09-13** in #1313; see "Charge construction upstream of walls"
under Completed roots. Issue #1230 remains open and blocked on its independent
two-consumer obligation, so this cutover retains `PeriodDomain.centralCharge`
and `Mukai.expCharge` with their existing bridges instead of inventing
`Lattice.pairCharge` or a graded pairing.

The exponential-twist extension (#1224) uses this implemented owner:
`CentralCharge/Exponential/Twist.lean` adds `Exp.twist`, its real group law and
the complex charge-translation identity to the existing `HDeg` kernel. The
threefold coordinate equivalence `threefoldVec` now lives with `NumClass` in
`CentralCharge/Numerical/Threefold.lean`, with its name preserved; that consumer
uses `betaTwist_eq_exp` to inherit the root group law. Surface scalar and
`B=βH` full-character comparisons are downstream in `Exponential/Divisorial`.
`Numerical/Stability/ExponentialTwist.lean` compares weighted degrees of the
retained rational twist with the real action for `m ≤ n`. No carrier or
instance is introduced. Arbitrary `B` does not descend to compressed degrees;
the explicit counterexample is recorded in the canonical-root policy.

#### 05 -- Linear Serre duality and Yoneda helpers (#1318)

| Relationship | Owner |
| --- | --- |
| Definition owner | `CategoryTheory/Linear/SerreFunctor/Basic.lean` for the `k`-linear duality data, its Hom-finiteness class, the pairing, the trace and the finrank identity; `CategoryTheory/Linear/SerreFunctor/Uniqueness.lean` for the comparison and its coherence |
| Neutral core | `CategoryTheory/Linear/Yoneda.lean` for the three representability helpers, which are proved without reference to any Serre datum |
| Application adapter | `CategoryTheory/Triangulated/SerreFunctor/` keeps `Objects`, `Enriques`, `Classification`, `Transport`, `ProjectionObjects` and `Matching`, which add shift, Ext profiles and semiorthogonal structure |
| Comparison owner | unchanged; SRF1 `#897`--`#899` keeps full faithfulness, equivalence/shift transport and the geometric Serre-duality obligations |

**Landed 2026-09-13** in #1318; see "Linear Serre duality and representability"
under Completed roots.

Independent consumer for `CategoryTheory/Linear/Yoneda.lean`: a downstream lane
already needs the representability step on a functor that is *not* a Serre
functor, which is why those declarations were made public in the first place.
Per decision 1 the three helpers keep the `CategoryTheory.SerreFunctor`
namespace even in the linear Yoneda file. Hom-finiteness is not added to the
linear core, and essential surjectivity is still not inferred from full
faithfulness: `HasRightSerreFunctor` remains the Reiten--Van den Bergh notion
and `SerreCategoryData` remains the Bondal--Kapranov one.

#### 06 -- Abelian stability foundations and slope vs. Gieseker (#1319)

| Relationship | Owner |
| --- | --- |
| Definition owner | abelian stability functions and their Harder--Narasimhan theory under `CategoryTheory/Abelian/`, with weak variants as children |
| Neutral core | the class datum and additive charge, which need an abelian category and nothing triangulated |
| Application adapter | restriction to hearts and reconstruction of triangulated stability stay in `Triangulated/StabilityCondition/`; under `AlgebraicGeometry/Stability/`, slope and Gieseker become siblings with shared Hilbert-polynomial data |
| Comparison owner | a `Comparison.lean` joining the two geometric theories |

`Weak/` below `StabilityCondition/` is not itself a defect and does not move:
directory nesting names a variant even when the stronger theory imports the
weaker. The defect is the independent abelian subject, and the μ-Harder--
Narasimhan existence theorem, being owned by later consumers. The current
μ-HN theorem must not be relabelled a proof of Gieseker HN existence by virtue
of its new directory.

**Landed 2026-09-15** in #1319. `Weak/Foundation/StabilityFunction/` is now
`CategoryTheory/Abelian/Stability/`, with the fourteen `Weak*` leaves as its
`Weak/` children -- so `Weak/` keeps naming a variant in the new home too, and
`Stability/Slope.lean` still imports `Stability/Weak/Slope.lean` rather than the
reverse. `Weak/Charge.lean` became `Abelian/Stability/Charge.lean`: `ClassDatum`
and the additive charge are the neutral core, and they have two independent
consumers, `abelianDatum` and the heart. Only `HeartDatum.lean` stayed in the
triangulated tree, at `Weak/Foundation/HeartDatum.lean`, because it is the
adapter and the one module of the old directory that mentions a t-structure.
`Weak/Foundation.lean` re-exports the abelian owner, so the triangulated weak
theory offers the same names it did before. The four upper-half-plane facts
moved with `Charge.lean` and remain the upstream candidate the 2026-09-02 entry
below records.

Under `AlgebraicGeometry/Stability/`, `HilbertPolynomial.lean`,
`Coefficients.lean` and a new `Purity.lean` are the shared data; `Slope/` and
`Gieseker/` are siblings over them, reaching neither each other nor the
stability tree; and `Comparison.lean` owns the four statements that mention
both, together with the one-step filtration of a Gieseker-semistable sheaf.
`Purity.lean` exists because `IsPure` mentions only the multiplicity and has two
unrelated consumers -- it is the Gieseker predicate's conjunct, and it is what
gives the μ-HN recursion a finite maximal slope -- so the μ-lane no longer
imports the Gieseker order to reach it.

The μ-HN existence theorem is `Slope/HarderNarasimhan/Existence.lean` and is
still a theorem about the μ-slope: it was not relabelled, its `MuHNInput`
hypotheses are unchanged, and Grothendieck's boundedness lemma is still
supplied rather than proved. The audit slice named `Gieseker.lean` was split
for the same reason, into `SheafStability.lean`, `Gieseker.lean`,
`SheafSlope.lean` and `SheafStabilityComparison.lean`, with all 171 records
preserved.

The layering gate gained rule 13 for the three claims this row makes, and
*lost* the `Stability/Gieseker/` entry in rule 3's exemption list: the
sheaf-stability subtree now reaches no stability condition at all, so the
exemption was removed rather than renamed. Fully qualified declaration names
are unchanged throughout, which leaves the abelian files declaring into
`CategoryTheory.Triangulated` -- the oddity decision 1 accepts rather than
repairs.

#### 07 -- Numerical parent-to-specialization inversions (#1316)

| Relationship | Owner |
| --- | --- |
| Definition owner | square-root algebra, Todd construction and K3 simplification become three owners instead of one file that imports its own specialization |
| Neutral core | generic polarised transport imports only its numerical data, correction and charge kernel |
| Application adapter | K3, abelian and Enriques surface models are built from a shared surface-model constructor rather than from each other |
| Comparison owner | old/new agreement theorems move to a downstream comparison module; the K3/abelian/Enriques comparison witnesses move to a downstream `Models/Surface/Comparison.lean` |

**Landed 2026-09-14** in #1316. `Mukai/SqrtTodd.lean` and
`Mukai/VectorClass.lean` now contain only dimension-general constructions;
their K3 consequences live in `SqrtToddK3.lean` and `VectorClassK3.lean`.
`Stability/Slope.lean` is independent of the K3 worked example, which moved to
`SlopeK3.lean`. `PolarisedWallTransport.lean` owns the generic `(n,m,κ)` root,
while `PolarisedWallTransportComparison.lean` imports the surface and
threefold leaves. Shared rank-one Chern coordinates live in `RankOne.lean`,
and cross-model witnesses live in `Models/Surface/Comparison.lean`, which
MO1.06 moved there from `Examples/Surface/` the next day.

The layering gate checks the transitive closures of the square-root, slope and
polarised-transport roots against K3, named-surface and dimension-specific
consumers. Fully qualified declaration names and the codimension-four bound on
`sqrtComp_convolution` are unchanged.

The present comparisons are good mathematics and all of them survive; what
changes is which module owns them. The explicit codimension-four bound on
`sqrtComp` survives relocation unchanged -- it is not an arbitrary-degree
square-root construction and must not be presented as one.

#### 08 -- The GL⁺(2,ℝ) cover vs. its stability action (#1323)

| Relationship | Owner |
| --- | --- |
| Definition owner | the group construction, deck transformations, covering map, simple connectedness and topological-group laws move beside the general-linear-group API, with general covering lemmas near the topology owner |
| Neutral core | the order automorphism of `ℝ` commuting with unit translation, which mentions no category |
| Application adapter | phase conventions and the action on slicings, charges and stability conditions stay under `Symmetry/GLTilde/Action/` |
| Comparison owner | the existing compatible-pair construction is retained; a complex-coordinate linear-map adapter moves near the complex linear-algebra owner only once its public type is independent of the cover |

The π-normalization is a convention to expose through adapters, not a reason
for covering-space theory to live inside triangulated categories. The proposed
destination is a local extension, not an existing Mathlib module.

#### 09 -- Mass as a sibling of metric; planar convex geometry (#1324)

| Relationship | Owner |
| --- | --- |
| Definition owner | `StabilityCondition/Mass/` becomes a sibling of `Metric/`, since Harder--Narasimhan mass is an invariant of an object and a stability condition |
| Neutral core | the polygonal-path carrier, the real continuous linear functionals on `ℂ` and the Euclidean perimeter comparison leave the mass-subadditivity proof directory |
| Application adapter | the metric construction stays downstream of mass; the HN-polygon and mass adapters stay in stability |
| Comparison owner | unchanged |

Mass has consumers besides the metric -- mass--Hom estimates and dynamical
constructions -- and that is the independent-consumer justification. **Scope
warning:** the neutral destination for the planar lemmas is a subject this
repository does not yet have. Introducing `Analysis/` or `Geometry/` means
adding a name to `KNOWN_SUBJECTS` in `scripts/check_layering.py`, which rule 6
deliberately makes a conscious act. MO1.13 must first check what Mathlib
already provides and prefer reusing it; a new top-level subject is authorized
only if that check comes back empty, and is recorded here when it happens.

**Implemented in #1356.**

##### The Mathlib check, and the subject it authorized

The check the scope warning demanded was run against the pinned revision
(`520045ab14e2`) before any code moved. What Mathlib has, and what was reused:

- `Mathlib.Geometry.Polygon.Basic` supplies `Polygon P n` -- a one-field
  wrapper over `vertices : Fin n → P` in an affine space -- with `edgePath`,
  `edgeSet`, `boundary` and two nondegeneracy predicates. It carries **no
  metric content whatsoever**, so rebasing the carrier on it would import a
  synonym for `Fin (n + 1) → ℂ` and supply none of the theory.
- `InnerProductSpace ℝ ℂ`, `Complex.reCLM` and `Complex.imCLM` exist and are
  already what `dotFunctional` and `crossFunctional` are built from.
- `convexHull` and `convexHull_mono` exist and are already used.

What Mathlib does not have, and what therefore has no owner to reuse: a
polygonal-chain length or a perimeter of any kind -- `grep -ri perimeter`
over all of `Mathlib/` returns zero files -- no `Path.length` and no
arclength, only `eVariationOn`, which is the variation of a function and not
the length of a chain; the perimeter comparison under containment of vertex
hulls; and the support-fan turning-functional discrete integration by parts
the proof runs on.

The check therefore came back empty for the substantive content, and a new
top-level subject is authorized. **The name is `Analysis`, not `Geometry`.**
Mathlib is mid-migration on convexity: at the pinned revision
`Mathlib/Geometry/Convex/Hull.lean` defines a *different* `Convexity.convexHull`
over `ConvexSpace`, while the root-namespace `convexHull` this repository
consumes is owned by `Mathlib/Analysis/Convex/Hull.lean`. Ownership follows the
API actually being extended. The half-plane facts land beside it at
`Analysis/Complex/`, mirroring `Mathlib/Analysis/Complex/UpperHalfPlane/`, so
one subject covers both halves rather than two.

`Analysis` is in `KNOWN_SUBJECTS` with the reason recorded at the constant.

##### What moved, beyond the row's own scope

Two files the owner map does not name had to move, because the acceptance
criterion "the planar core imports no categories and no stability" cannot hold
while the core's own hypotheses are stated with declarations that live inside
the stability tree:

- `semiClosedUpperHalfPlane` and `closedUpperHalfPlane` with their three
  lemmas, out of the file MO1.08 has since renamed
  `CategoryTheory/Abelian/Stability/Charge.lean`, to
  `Analysis/Complex/HalfPlane.lean`. That file's own docstring had already
  recorded this as the intended destination and named the only thing holding
  it back -- a namespace change -- which standing decision 1 settles: the
  namespace does not move.
- The neutral first half of `PhaseGeometry.lean` (`phaseCross` and the
  argument see-saw bounds) and all of `FiniteSums.lean`, to
  `Analysis/Complex/PhaseGeometry.lean` and
  `Analysis/Complex/PhaseFiniteSums.lean`. The `StabilityFunction` half of
  `PhaseGeometry.lean`, which genuinely needs an abelian category, stayed and
  now imports the neutral owner.

  These two rows cross MO1.08 (#1319), which landed first and moved that whole
  directory to `CategoryTheory/Abelian/Stability/`. The two moves agree rather
  than compete: MO1.08's claim is that abelian stability needs no shift and no
  t-structure, and rule 13 checks it; MO1.13's is that these particular
  declarations need no *category*, which is a strictly stronger statement about
  a strictly smaller set of files, and rule 14 checks that. The files MO1.13
  takes are the ones for which the stronger claim holds; everything else stayed
  where MO1.08 put it.

`ComplexPolygonalPath.crossFunctional` and `phaseCross` are the same oriented
determinant under two presentations, one bundled as a `ℂ →L[ℝ] ℝ` and one not.
Putting them in one subject makes that visible; unifying them would rename a
declaration and is not authorized here.

##### The claim, and the gate that keeps it

`scripts/check_layering.py` gained **rule 13**: no module below `Analysis/`
reaches `DerivedAlgGeo.CategoryTheory`, `DerivedAlgGeo.AlgebraicGeometry`,
`DerivedAlgGeo.Development`, `Mathlib.CategoryTheory` or
`Mathlib.AlgebraicGeometry`, transitively. Without it the separation is a
docstring, and one convenience import from a stability consumer erases it with
every other gate still green -- the failure mode rule 9 exists for.

The vacated paths are in `RETIRED_PATHS`:
`StabilityCondition/Metric/Mass`, `StabilityCondition/Weak/Metric` (which held
nothing but mass, so it was not kept as a one-child parent), and
`CategoryTheory/Abelian/Stability/FiniteSums.lean` — the path MO1.08 had just
created for it, vacated one step further because that file mentions no category
at all. MO1.08's own parent entry covers where it lived before. No shims.

`Metric/Mass/Subadditivity/PolygonPerimeter.lean` was named for the shape of
its proof. Its Euclidean half is now
`Analysis/Convex/ComplexPolygonalPath/Perimeter.lean` and its stability half is
`Mass/Subadditivity/HNPolygonComparison.lean`, named for its subject. The
Ikeda Lemma 3.7 and 3.8 citations travel with both halves, and the `t = 0`
strengthenings each file records are restated verbatim where they apply.

Scope guard honoured: the mass--Hom consumer #1185 keeps its theorem and its
moduli input, and `StabilityCondition/MassHom/` is untouched except for the
three import lines that follow mass to its new path.

#### 10 -- Derived tensor and pushforward vs. Fourier--Mukai (#1321)

| Relationship | Owner |
| --- | --- |
| Definition owner | the derived-tensor and derived-pushforward capabilities move to geometry-level owners under `AlgebraicGeometry/DerivedCategory/`; the coherent derived-tensor capability follows them out of the Fourier--Mukai subtree |
| Neutral core | the purely functorial correspondence -- three ordinary categories, a pull functor, a bifunctor and a push functor -- may get a categorical owner; this is explicitly the *less* urgent half |
| Application adapter | Fourier--Mukai keeps correspondences, kernels, convolution, units, adjoints and theorems about transforms |
| Comparison owner | unchanged |

These records are **supplied capabilities, not constructed operations in full
generality**, and the move must not read as construction: `Dᵇ(Coh X)` is not
automatically closed under arbitrary derived tensor on a singular scheme.
"Abstract Fourier--Mukai formalism" is a defensible subject name, so the
categorical rename is optional and may be declined with that reason recorded.

#### 11 -- Flatness and relative perfection out of the moduli consumer (#1322)

| Relationship | Owner |
| --- | --- |
| Definition owner | flatness of a module sheaf over a morphism moves to the relative-module owner under `AlgebraicGeometry/Modules/` |
| Neutral core | the derived-object predicates -- pseudo-coherence and local finite Tor amplitude -- and their local models move to a relative-perfect owner under `AlgebraicGeometry/DerivedCategory/` |
| Application adapter | presheaves, restriction stability, boundedness, openness, atlases and algebraicity stay under `Moduli/PerfectComplex/` |
| Comparison owner | `Moduli/PerfectComplex/Comparison.lean` keeps the one-way adapters; the three-notion ledger in `docs/architecture/placement.md` stands unchanged |

**Landed 2026-09-13** in #1322; see "Relative perfection before moduli" under
Completed roots.

The source's own warning survives the move verbatim: the bounded-above
finitely-presented-cohomology predicate is the **Noetherian** criterion and is
not standard pseudo-coherence on an arbitrary scheme. The move must not promote
it to an unrestricted canonical definition, and must not identify the
repository's three "perfect" notions without their comparison theorems.

#### 12 -- Numerical models, named surface cases and realizations (#1317)

| Relationship | Owner |
| --- | --- |
| Definition owner | explicit algebraic models own `Numerical/Models/`; the reusable constructors moved out of the example leaves |
| Neutral core | the shared surface-model constructor from row 07, now `Models/Surface/RankOne.lean` |
| Application adapter | the two K3-only charge adapters took a visibly K3 filename; dimension specializations have explicit homes at `Models/Threefold/` and `Models/Fourfold/` |
| Comparison owner | an actual scheme and its scheme-level realization stay with the geometric object -- `AlgebraicGeometry/Surface/K3.lean`, `AlgebraicGeometry/Surface/Enriques/` -- and a scheme-level specialization of a *stability* construction stays under `DerivedCategory/Stability/` with a `Scheme` suffix, because its subject is the stability function. That is the convention this row picks; both halves already existed and neither moved |

**Landed 2026-09-15** in #1317.

##### The line that was drawn

`Numerical/Models/` holds formal rank--degree--coordinate models: an
intersection ring, its grading, a degree map, Chern and Todd coefficients, and
Riemann--Roch. `Numerical/Examples/` holds the demonstrations built on them:
the realization map into a real divisor space, the charges, the walls, the
slices and the regions.

The line is not a matter of taste, and it is checked. Every module under
`Numerical/Models/` is stability-neutral and every module under
`Numerical/Examples/` reaches the stability tree, so the rule-3 exemption that
names `Numerical/Examples/{Surface,Threefold,Fourfold}` is now tight. Narrowing
it was named as MO1.06 work by the comment on `STABILITY_CONSUMING_GEOMETRY`
itself; `Numerical.Models` is deliberately absent from that list, and rule 12
rejects any later attempt to add it. Rule 11's specialization list gained
`Numerical.Models` in the same change, so a generic root still cannot import a
named model.

| Classification | Modules | Home |
| --- | --- | --- |
| Reusable model | `MonogenicRing`, `Surface/RankOne`, `Threefold/LinearSection`, `Fourfold/LinearSection` | `Numerical/Models/` |
| Named model | `Surface/{K3,Abelian,Enriques,ProjectivePlane}`, `Surface/K3Mukai`, `{Threefold,Fourfold}/{CalabiYau,ProjectiveSpace}`, `DimensionZero/Point` | `Numerical/Models/` |
| Comparison | `Surface/Comparison`, `Surface/K3MukaiIntegral` | `Numerical/Models/` |
| Demonstration | `Surface/{RankOneRealization,RankOneWalls,K3MukaiComparison,ProjectivePlaneCharge,SmoothQuadric,SmoothQuadricCharge,BlowUpPlane,BlowUpPlaneWalls,BlowUpPlaneSlice}`, `{Threefold,Fourfold}/{CalabiYauWalls,ProjectiveSpaceWalls}` | `Numerical/Examples/` |

`SmoothQuadric.lean` and `BlowUpPlane.lean` construct rings and stay with the
demonstrations because each also carries its divisor realization and its
wall-theoretic certificates in the same module; they are not formal models
alone. Splitting them is not required by this row and is not done here.

##### The maps that reach the common root

An advertised specialization is a declaration, not a directory name. These are
the maps, each one an import away from its root:

| Leaf | Root | Map |
| --- | --- | --- |
| `Models/Surface/{K3,Abelian,Enriques,ProjectivePlane}` | `Models/Surface/RankOne` | `surfaceNumericalRing`, `surfaceCh`, `surfaceCh_mem` -- each model supplies only a Todd class |
| `Models/{Threefold,Fourfold}/{CalabiYau,ProjectiveSpace}` | `Models/MonogenicRing` | `rankOneNumericalVariety` and `rankOneNumericalVariety_satisfiesHRR`, through the dimension's `LinearSection` coordinates |
| `Models/Surface/K3Mukai` | `GrothendieckGroup/MukaiVector` | `k3IntegralMukaiData`, `k3AdditiveMukaiData` |
| `Examples/Surface/RankOneRealization` | `Models/Surface/RankOne` | `Surface.NumericalRealization` from the rational codimension-one piece into a real divisor space |
| `Examples/Surface/K3MukaiComparison` | both presentations | the integral and the real Mukai structure of the same model, imported downstream of each |
| `DerivedCategory/Stability/K3MukaiTiltScheme` | `DerivedCategory/Stability/K3MukaiTilt` | the scheme specialization, which takes an actual `Scheme` and geometric Riemann--Roch |

No map runs from a numerical model to a scheme. `AlgebraicGeometry/Surface/K3.lean`
still records in "What this file does not do" that the bridge
`IsK3Surface k X C -> NumericalVarietyData 2 A N` is Hirzebruch--Riemann--Roch
and does not exist at the pin; nothing in this row supplies it.

##### The two naming defects

Both are fixed rather than carried forward.

`Models/Surface/Enriques.lean` is titled "A polarisation slice of the Enriques
numerical lattice". `Num(Y)` of a genuine Enriques surface is `U + E8(-1)` of
rank ten; the file builds the rank-one sublattice spanned by one polarisation
class with `H^2 = 2d`, which is legitimate because the Enriques lattice is even.
Picard rank one is neither a hypothesis nor a conclusion there.

`Examples/RankOne.lean` became `Models/MonogenicRing.lean`, titled "The
numerical intersection ring generated by one ample class, in every dimension",
because that is the hypothesis every construction in it uses. In dimension two
the two conditions agree, since a surface has `A^0 = A^2 = Q` and `A^1 = Q.H`.
For `n >= 3` the rank of `N^1(X)` says nothing about `N^2(X)`, so Picard rank
one alone does not give `Q[H]/(H^(n+1))`. The `rankOne` prefix on the
declarations is preserved and is historical; the module docstring says so.

No K3 files were collapsed into one folder, and no numerical model is
identified with a scheme.

##### The K3-only charge adapters

`GrothendieckGroup/CentralCharge.lean` and `GrothendieckGroup/CategoricalCharge.lean`
were entirely in namespace `Numerical.K3` behind dimension-general filenames.
They are now `CentralChargeK3.lean` and `CategoricalChargeK3.lean`, matching the
`SqrtToddK3`/`VectorClassK3`/`SlopeK3` convention row 07 established, and the
rule-3 exemption entry moved with the file. `MukaiVector.lean` and
`RadicalKernel.lean` beside them are also `Numerical.K3` but are not charge
adapters, and this row does not rename them.

##### The arbitrary-divisor-rank branch

`Exp.ofMoments` takes a moment sequence, not a vector of `H`-degrees, precisely
so that the multi-divisor charge and the compressed families are **siblings**
under one kernel. `H`-compression is not injective once the Picard rank exceeds
one, so the divisorial charge has no degree vector to hand the kernel and is not
a child of the compressed branch. Rule 12 pins that: both
`CentralCharge/Exponential/Divisorial.lean` and
`CentralCharge/Exponential/Comparison.lean` must reach
`CentralCharge/Exponential/Kernel.lean`, only the second may reach a degree
vector, and the rank-two and rank-three geometry demonstrations
(`SmoothQuadric*`, `BlowUpPlane*`) must not import the rank-one carrier or the
scalar polarised transport to obtain a charge.

##### Where the #1225 fourfold models belong

`Models/Fourfold/LinearSection.lean` owns the reusable Koszul linear-section
coordinates in dimension four, and `Models/Fourfold/CalabiYau.lean` and
`Models/Fourfold/ProjectiveSpace.lean` own the two models over it. The wall
families #1225 added to them are demonstrations and stay at
`Examples/Fourfold/CalabiYauWalls.lean` and
`Examples/Fourfold/ProjectiveSpaceWalls.lean`, which is why the fourfold entry
in the rule-3 exemption list survives the move unchanged.

No charge formula is reproduced here. Inhabiting `Numerical.CalabiYauFourfold`
is a statement about the numerical axioms; it is not a claim that a smooth
sextic fourfold exists as a scheme in this repository, and nothing constructs
one.

#### 13 -- Direct Mathlib-owner mismatches (#1325)

| Old path | New owner |
| --- | --- |
| `CategoryTheory/ModuleCat/LinearDual.lean` | consolidated with the rest of module-category linear duality under `Algebra/Category/ModuleCat/LinearDual/` |
| `Algebra/Category/ModuleCat/Sheaf/ExteriorPower.lean` | `Algebra/Category/ModuleCat/Presheaf/ExteriorPower.lean`, because it constructs exterior powers of a presheaf of modules |
| `AlgebraicGeometry/Cohomology/Quasicoherent/Extensions.lean` | `AlgebraicGeometry/Modules/Quasicoherent/Extensions.lean` |
| `AlgebraicGeometry/Divisors/ExteriorPower.lean` | `AlgebraicGeometry/Modules/ExteriorPower/Restriction.lean` |

**Landed 2026-09-13** in #1325; see "Four Mathlib owners repaired" under
Completed roots.

Divisor-specific determinant and Cartier applications stay under `Divisors/`.
A cohomological *proof* does not make cohomology the theorem's subject, which
is the whole content of the third row. **Check the import graph while splitting
the quasicoherent file**: its affine and cohomological helper declarations may
need separate owners to avoid a cycle, and that check is part of MO1.14 rather
than a follow-up.

Note that `placement.md` already assigns the bare algebraic-dual functor to
`CategoryTheory/ModuleCat/LinearDual.lean` and its exactness to
`Algebra/Category/ModuleCat/LinearDual.lean`. That paragraph is the thing this
row changes; MO1.14 updates it in the same pull request as the move.

#### 14 -- The placement policy itself (#1312, this section)

Implemented here rather than queued. See "What MO1.01 changed" below.

#### 15 -- H⁰ with `DGCategory`; enhancement vs. presentation (#1320)

| Relationship | Owner |
| --- | --- |
| Definition owner | the dg encoding root stays **provisionally** at `Algebra/Homology/DGCategory/`, and the generic H⁰ constructions -- shift, cone triangles, functor exactness -- move below that owner |
| Neutral core | pretriangulated H⁰ results about a dg category, stated before any external category is chosen |
| Application adapter | `Triangulated/DGEnhancement/` is reserved for exact comparisons with a *specified* triangulated category, and their transport |
| Comparison owner | the Mathlib homotopy-category realization stays at `Algebra/Homology/HomotopyCategory/DGEnhancement/`; the existing proved agreement for the complexes model is preserved |

The weaker package -- an equivalence with an ordinary category -- is named as an
underlying **H⁰ presentation**, and an exact enhancement becomes a refinement
carrying the compatibility data. Exactness is necessary to match the standard
enhancement notion; it does **not** imply a general uniqueness-of-enhancements
theorem, and no row here asserts one. "Provisionally" is the existing ADR-0010
/ ADR-0011 position and is unchanged: if the enriched encoding (Option A′) ever
lands, the subtree moves under `CategoryTheory/Enriched/` in that same change.
This is not a request to re-encode the library as enriched categories.

### Component-specific forbidden import edges

Named per review finding 14, replacing the impulse to impose a total order on
top-level subjects. Three are named; one is enforced today and two become
enforceable only after their own cutover lands.

| Edge | Status |
| --- | --- |
| numerical core → no stability constructions | **Enforced.** `scripts/check_layering.py` rule 3 now names exempt subcomponents rather than the whole `Numerical/`, `Moduli/` and `Stability/` subtrees, with a forbidden fixture at `scripts/fixtures/layering/forbidden/AlgebraicGeometry/Numerical/Core/` |
| charge construction → no wall classification | **Enforced.** Rule 8 checks every module below `StabilityCondition/CentralCharge/` transitively against `Walls/` and geometry, and checks the neutral paired-functional, continuity, bounds and Hodge roots against stability and geometry; two forbidden fixtures prove both boundaries fire |
| geometric derived operations → no Fourier--Mukai or moduli consumers | Pending MO1.10 and MO1.11. Same reason: the operations are currently declared inside the consumers |

### Legitimate core-umbrella exceptions

The layout promises every non-leaf directory a complete same-named umbrella,
and an umbrella over a stability-consuming child reaches the stability tree by
re-exporting it. Five umbrellas are therefore exempt from rule 3 **as
umbrellas**, and the exemption is not inherited by their other children:

- `AlgebraicGeometry/Moduli.lean` (over `Moduli/HarderNarasimhan/`, `Moduli/Semistability/`)
- `AlgebraicGeometry/Numerical.lean` (over `Numerical/Stability/`, and transitively `Numerical/Examples/`)
- `AlgebraicGeometry/Numerical/Examples.lean` (over `Examples/Surface/`, `Examples/Threefold/`)
- `AlgebraicGeometry/Numerical/GrothendieckGroup.lean` (over `GrothendieckGroup/CategoricalCharge/`)
- `AlgebraicGeometry/Stability.lean` (over `Stability/Gieseker/`)

The gate derives this list rather than hard-coding it: a module is an umbrella
when a same-named source directory exists, and it is exempt when an exempt
subcomponent lies below it. A fixture names no directory, so no fixture can
acquire the exception.

### What MO1.01 changed, and what it left alone

Changed: this section; the subcomponent-scoped rule 3 and the umbrella
exception in `scripts/check_layering.py`; five layering fixtures; and the
placement, contribution, layering and agent documents where they stated the
blanket exemption or the over-broad Tier 1 rule.

Left alone deliberately: one `DerivedAlgGeo` library; the geometry firewall;
`Development/` as a leaf; generic derived categories beside Mathlib's
`DerivedCategory`; `DGCategory` beside the `HomComplex` it is built on; and
every declaration name in the repository. No Lean source moved in MO1.01.

Measured effect of the narrowing: 302 of 381 geometry modules are now checked
as stability-neutral, against 258 on the review snapshot. The 44-module
difference is code the blanket exemption was not guarding -- `Numerical/Core/`,
`Numerical/Mukai/`, `Numerical/RiemannRoch/`, `Numerical/Specializations/`, the
non-charge `Numerical/GrothendieckGroup/` modules, `Numerical/Examples/`'s
dimension-zero, fourfold and rank-one leaves, `Moduli/PerfectComplex/` and
`Moduli/Quot/`. Narrowing the remaining eight entries further was MO1.05,
MO1.06 and MO1.13 work, since each still mixed modules that reach the stability
tree with modules that do not.

MO1.06 (#1317) closed the three `Numerical/Examples/` entries on 2026-09-15 by
moving the formal models to `Numerical/Models/` rather than by editing the
list: every module still named by those three entries now genuinely reaches the
stability tree, and `Numerical/Models` is held neutral. `Numerical/Stability`,
`DerivedCategory/Stability`, `Moduli/HarderNarasimhan`, `Moduli/Semistability`
and `Stability/Gieseker` remain as they were.

## Completed roots

- Derived base change separated from its K-flat model (2026-09-14): the
  base-change layer of `AlgebraicGeometry/DerivedCategory/Families/` was stated
  on `KFlatBaseChangeData`, a nine-field bundle of K-flat resolutions and their
  acyclicity, quasicoherence and tensor-preservation statements -- 195
  occurrences across 20 modules. That is a *model*, not the concept: it records
  one way to produce derived pullback and tensor, so no second construction
  could reach the API without copying it, and `abstraction-tree.md` forbids a
  leaf copying the carrier of its root. There was no root to reach.

  `Families/BaseChangeData.lean` now owns `DerivedBaseChangeData`: the two
  `DqcLeftDerivedPullback`s and the derived tensor, and nothing else. The
  external product, the perfect generators and their envelope, the
  quasicoherent component `(Dqc)_T`, the bounded component `D_T`, their
  instances and the compactness consequences are all stated there.
  `KFlatBaseChangeData` keeps its resolutions and becomes the producer, through
  `KFlatBaseChangeData.toDerivedBaseChangeData`; its eight former
  constructions are reducible abbreviations through it, so the 195 call sites
  are unchanged and definitionally the same terms.

  Seven duplicated instances and one duplicated theorem were deleted rather
  than delegated: with the abbreviations reducible, the root's instances fire
  directly. `KFlatBaseChangeData.derivedTensor` moved from
  `BaseChangeLinearity.lean` to the structure's own definition site, where a
  projection belongs.

  What this unblocks: the first inhabitant. `KFlatBaseChangeData` is
  constructed nowhere in the tree, and the cheapest case is pullback along an
  open immersion, which `OpenImmersionPullback.lean` already proves *exact* --
  so it needs no resolution at all and could not have inhabited the old carrier
  without manufacturing three it does not use. It can now produce a
  `DerivedBaseChangeData` directly.

  Not done here: `KFlatBaseChangeData.PreservesCompactObjects` remains
  model-level, bridged to the root's by `toDerivedPreservesCompactObjects`; a
  non-K-flat model states the root's version directly.

- Numerical foundations upstream of specializations (2026-09-14, finding 07):
  generic square-root Todd, Mukai-class, slope, and polarised-transport roots
  no longer import K3 or dimension-specific consumers. K3 simplifications,
  surface/threefold transport comparisons, and K3/abelian/Enriques model
  comparisons are downstream modules. The three surface models share the
  rank-one coordinate constructor rather than importing sibling models.

- Positive planes, positive frames and numerical loci (2026-09-14, finding 02):
  `QuadraticForm/PositivePlane.lean` and `PositiveFrame.lean` own distinct
  carriers connected by `framePlane` and `forgetPositiveFrame`.
  `OrthogonalityLocus.lean` and the `Orthogonality*` consumers retain the
  neutral arrangement and finiteness theory. `CentralCharge/Family.lean`,
  `Walls/Alignment.lean`, `Walls/Spherical/Basic.lean` and `Chambers/Basic.lean`
  separately own charge-zero, determinant-alignment, positive-ray,
  nonpositive-ray and stability-space loci. The comparison modules state only
  the maps and inclusions their hypotheses support; no shared codimension-one
  superclass or actual destabilization object was introduced.

- Charge construction upstream of walls (2026-09-13, findings 01 and 04):
  `StabilityCondition/CentralCharge/Family.lean` now owns the unchanged
  additive `ChargeFamily`; `CentralCharge/Exponential/` owns the unchanged
  `Exp.ofMoments` kernel and its surface, threefold and arbitrary-divisor-rank
  comparisons; and `CentralCharge/Divisorial/` owns Chern coordinates, charge
  parameters, slice construction, discriminants and supplied Todd data.
  `CentralCharge/Numerical/` owns the surface and threefold charge
  constructions, while `Walls/` keeps only determinant-alignment loci and
  their circle, nesting and finiteness results. `Support/Divisorial.lean`
  states the support predicates, including both semistable-locus
  nonnegativity and strict kernel negativity.

  The paired complex functional and kernel algebra moved without declaration
  renames to `LinearAlgebra/QuadraticForm/ComplexPairing.lean`; wall and period
  interpretations are downstream in `CentralCharge/Quadratic.lean`.
  `QuadraticForm/Continuous.lean` and `Bounds.lean` extract the arbitrary
  continuity, coercivity and level-set results formerly mixed into
  `OrthogonalityFiniteness.lean`. `LinearAlgebra/BilinearForm/HodgeIndex.lean` owns the
  abstract symmetric divisor space and its Hodge signature theory. Geometric
  Chern and Todd realizations remain under `AlgebraicGeometry/Numerical/`.

  Rule 8 pins these structure owners, rejects transitive wall or geometry
  imports from the central-charge tree, and rejects all stability or geometry
  imports from the neutral roots. The old motivational paths are retired, not
  shimmed. Issue #1230 has not introduced `Lattice.pairCharge`: it remains open
  on a separate two-consumer review obligation, so this delivery deliberately
  retains the existing functional and bridge theorems. Tilt-dependent
  rotation remains downstream and does not enter `CentralCharge/Family.lean`.

- Linear Serre duality and representability (2026-09-13, finding 05):
  `CategoryTheory/Linear/SerreFunctor/` now owns `SerreFunctorData`, the
  `HomFinite` hypothesis, `SerreCategoryData`, the Serre pairing, trace and
  `finrank` identity, and the whole uniqueness development --
  `compareEquiv`, `yonedaIso`, `uniqueIsoApp`, `uniqueIso`, `uniqueIso_unique`
  and the reflexivity, transitivity and symmetry coherence lemmas.
  `CategoryTheory/Linear/Yoneda.lean` owns `isoOfLinearYonedaIso`,
  `map_isoOfLinearYonedaIso` and `hom_ext_of_linearYoneda`, which mention no
  Serre datum and are `Functor.preimageIso`, `Functor.map_preimage` and
  `Functor.map_injective` against Mathlib's `full_linearYoneda` and
  `faithful_linearYoneda`. Neither file mentions a shift or a distinguished
  triangle, and the source said so before the move: the previous owner's own
  docstring recorded that no shift or triangulation is needed.
  `CategoryTheory/Triangulated/SerreFunctor/` keeps exactly the
  shift-dependent half -- `Objects`, `Enriques`, `Classification`, `Matching`,
  `ProjectionObjects`, `Transport` -- and imports the linear root. Its umbrella
  no longer re-exports the moved modules, so the audit slice imports both roots
  by name.
  Every fully qualified declaration name survived unchanged, including the
  three helpers that keep the `CategoryTheory.SerreFunctor` namespace inside a
  linear Yoneda file; that divergence is decision 1 of the owner map, not an
  oversight. No hypothesis moved: full faithfulness still spends
  Hom-finiteness, `HasRightSerreFunctor` is still the Reiten--Van den Bergh
  right Serre functor with essential surjectivity supplied separately by
  `SerreCategoryData.serreIsEquivalence`, and no shift or exactness assumption
  was added to the linear core. SRF1 (#897--#899) keeps its full-faithfulness,
  transport and geometric-duality obligations; this cutover proves none of
  them.
- Relative perfection before moduli (2026-09-13, finding 11):
  `AlgebraicGeometry/DerivedCategory/Perfect/Relative.lean` now owns
  `schemePseudoCoherent`, `LocalFiniteTorAmplitudeChart`,
  `schemeLocallyFiniteTorAmplitudeOver`, `schemeRelativePerfect`,
  `SchemeRelativePerfectCategory` with its bounded-coherent representative and
  compact/perfect theorems, `GeometricFiberModel`, `UniversallyGluableData`,
  `schemeUniversallyGluableRelativePerfect` and the zero models that inhabit
  them.  `AlgebraicGeometry/Modules/Flat.lean` owns
  `Scheme.Modules.IsFlatOver`, which mentions one module sheaf and one
  morphism and no derived category at all.  Both were declared inside
  `Moduli/PerfectComplex/Relative.lean`, whose only remaining role was to be
  their first consumer; that path is retired with no shim.
  `Moduli/PerfectComplex/` keeps the presheaf, restriction-stability,
  boundedness, openness, atlas and algebraicity layer, and
  `Comparison.lean` keeps the one-way adapters between the three uses of
  "perfect".
  Measured, not asserted: the transitive repository closure of
  `DerivedCategory/Perfect` is 117 modules with **no** `Moduli/` dependency and
  **no** stability dependency, and `Modules/Flat` closes over a single module.
  Every fully qualified declaration name is unchanged.
  The scope note survives verbatim: `schemePseudoCoherent` is the locally
  Noetherian cohomological criterion, on a general scheme it diverges from
  standard pseudo-coherence in both directions, and any theorem quantifying
  over non-Noetherian bases is about that predicate.  No global equivalence
  instance relates `schemePerfect`, `schemeRelativePerfect` and
  `TwoTermPerfectDeterminantData`; SF8 (#517/#554/#723) keeps its
  construction, preservation and compact-perfect obligations.
- Four Mathlib owners repaired (2026-09-13, finding 13): each path now agrees
  with the API the file extends.
  `Algebra/Category/ModuleCat/LinearDual/` is one subject in two files,
  `Basic.lean` for the contravariant additive functor and `Exact.lean` for its
  exactness over a field; the split across `CategoryTheory/ModuleCat/` and
  `Algebra/Category/ModuleCat/` had filed the functor by its abstraction level
  rather than by where `ModuleCat` is defined, and `CategoryTheory/ModuleCat/`
  is retired.  `Algebra/Category/ModuleCat/Presheaf/ExteriorPower.lean` is
  where the file always belonged: every declaration in it is in the
  `PresheafOfModules` namespace, and nothing in it was sheaf-specific.
  `AlgebraicGeometry/Modules/Quasicoherent/Extensions.lean` owns closure of
  quasi-coherence under extensions -- a theorem about module sheaves whose
  proof happens to go through affine cohomology, which is why it had been filed
  under `Cohomology/`.  `AlgebraicGeometry/Modules/ExteriorPower/Restriction.lean`
  owns the restriction comparison for module-sheaf exterior powers; the
  divisor-specific determinant and Cartier consumers stay under `Divisors/`.
  The cycle the review warned about does not occur: the two cohomological
  imports of the extensions file reach nothing under `Modules/Quasicoherent/`
  or the `Modules` umbrella, measured before the move, so no helper needed
  splitting out.  Every fully qualified declaration name is unchanged; the one
  audit record that moved slice is `ModuleCat.linearDualFunctor`, rejoining its
  own siblings.  All four vacated paths are retired with no shims.

- `H⁰` dg-functor compositor coherence and adjunction normalization
  (2026-09-13): `DGFunctor.h0CompIso_assoc`, `h0CompIso_comp_id`, and
  `h0CompIso_id_comp` record the associativity and two unit equations for the
  canonical comparison from strict dg composition to ordinary functor
  composition.  `DGAdjunction.h0_whiskerLeft_counit` packages the descended
  left-whiskered counit as ordinary whiskering of `h0Counit`, while the dual
  `h0_whiskerRight_unit` packages the right-whiskered unit through `h0Unit`.
  `CounitConeData.twistAdjointComparisonH0_eq_inverseRotateFirstH0_comp_h0Counit`
  is the twist consumer, and
  `UnitConeData.cotwistAdjointComparisonH0_eq_h0Unit_comp_inrH0` factors the
  unshifted cotwist comparison through that unit law and the descended cone
  inclusion.  The conventional `[-1][1]` cotwist normalization remains in the
  existing shift package.  Mathlib's `Pseudofunctor` remains the
  conceptual owner, but no instance is installed because the repository does
  not yet have a bundled universe-controlled bicategory of dg categories and
  quotient two-cells.  This adds no `IsIso`, exactness, Morita, or sphericality
  conclusion.

- Conditional dg/Fourier--Mukai kernel autoequivalences (2026-09-13):
  a supplied `PresentedCounitComparisonData` or `PresentedUnitComparisonData`
  transports an explicit `H⁰` equivalence hypothesis from the dg twist or
  unshifted unit cone to the selected Fourier--Mukai twist or conventional
  cotwist.  `twistKernelAutoequivalence` and
  `cotwistKernelAutoequivalence` package the already named cone kernels with
  the repository's `KernelAutoequivalence` interface; the cotwist uses the
  existing exact-family shift comparison for its `[-1]` kernel.  The natural
  comparisons also expose the transported dg functors as kernel functors.
  Together with the supplied triangulated endpoint equivalence, the existing
  `ShiftCompatibility` gives the two equivalences Mathlib's canonical
  triangulated-equivalence package.  No comparison data,
  equivalence hypothesis, inverse kernel, dg quasi-equivalence, adjoint
  comparison, or sphericality is constructed.
- Shift-compatible dg/Fourier--Mukai twist and cotwist comparison
  (2026-09-13): the nested `ShiftCompatibility` records refine supplied
  `PresentedCounitComparisonData` and `PresentedUnitComparisonData` with an
  independently selected `CommShift` on the Fourier--Mukai twist or cotwist
  and Mathlib's `NatTrans.CommShift` condition for the corresponding natural
  isomorphism.  `twistIsTriangulated` and `cotwistIsTriangulated` then delegate
  exactness transfer to Mathlib's `Functor.isTriangulated_of_iso`.  The
  cotwist side compares the conventional pointwise `[-1]` functor, whose
  sign-correct shift structure is already packaged.
  `transportedCotwistH0Iso_commShift` derives compatibility of the intermediate
  actual shifted dg cone, and
  `ShiftCompatibility.transportedDGCotwistIso_commShift` composes it with the
  supplied Fourier--Mukai comparison.  Neither compatibility is stored as new
  record data.  The shift-compatibility layer manufactures no target shift
  structure and installs no global instance; it asserts no uniqueness or
  sphericality.
- Supplied natural comparison of dg and Fourier--Mukai adjunction cones
  (2026-09-13): `Triangle.FirstMapNormalizationData.ComparisonData` records the
  remaining data for an endpoint-strict comparison of two normalizations with
  the same first two vertices and first map: a natural third-vertex isomorphism
  and the two remaining map squares.  It fixes the endpoint components to
  identities and delegates the resulting triangle-family isomorphism to
  Mathlib's `Triangle.functorIsoMk'`.  The Fourier--Mukai aliases
  `PresentedUnitComparisonData` and `PresentedCounitComparisonData` specialize
  this contract to the independently chosen dg and kernel cones; they derive
  natural unit/counit and twist/cotwist comparisons, including the actual
  shifted dg cotwist.  The records are supplied and are not inferred from the
  earlier pointwise choices.  By themselves the bare records assert no
  canonicity, `CommShift` compatibility, equivalence of either functor, or
  sphericality; the conditional consumers above require the separate
  equivalence and shift inputs explicitly.
- Objectwise dg/Fourier--Mukai twist comparison (2026-09-13):
  `CounitKernelConeData.presentedCounitTriangleObjIso` applies Mathlib's
  triangle-isomorphism completion theorem to the presented dg and independently
  selected Fourier--Mukai counit triangles at each target object.  Its first
  two components are identities because both triangles use the same presented
  adjunction counit, and its third component gives
  `transportedTwistObjIso` from the actual transported dg twist object to the
  kernel twist object.  This choice is not proved natural in the target object,
  so no functor isomorphism, choice independence, exactness/equivalence
  transfer, kernel presentation of the dg twist, or sphericality is inferred.
- Objectwise dg/Fourier--Mukai cotwist comparison (2026-09-13):
  `AdjunctionUnitKernelConeData.presentedUnitTriangleObjIso` applies Mathlib's
  triangle-isomorphism completion theorem to the presented dg and independently
  selected Fourier--Mukai unit triangles at each source object.  Their first two
  components are identities because both triangles use the same presented
  adjunction unit.  Inverse rotation yields
  `presentedCotwistTriangleObjIso`; its first component compares the
  transported dg cotwist object with the Fourier--Mukai cotwist object, and a
  final composite reaches the transport of the actual shifted dg cone.  The
  chosen cone comparison is not proved natural in the source object, so no
  functor isomorphism, choice independence, exactness/equivalence transfer,
  kernel presentation of the dg cotwist, or sphericality is inferred.
- Exactness and equivalence after ordinary `H⁰` transport (2026-09-13):
  `DGFunctor.transportedH0` names equivalence conjugation of `H⁰ F`, while
  `transportedH0CommShift`, `transportedH0IsTriangulated`, and the equivalence
  accessors compose Mathlib's canonical inverse-mate, functor-composition, and
  triangulated-equivalence packages.  `UnitConeData.transportedCotwist`
  specializes these interfaces and the canonical exact `[-1]` shift.  Its
  exactness is unconditional in the chosen cone; its autoequivalence requires
  the explicit hypothesis that the unshifted cone is an equivalence on `H⁰`.
  No dg quasi-equivalence, choice independence, natural Fourier--Mukai
  comparison, or sphericality is inferred.
- Conventional cotwist triangles from presented dg adjunctions (2026-09-13):
  `DGAdjunction.H0Presentation.presentedCotwistTriangle` reuses Mathlib's
  `invRotate` on the normalized unit-triangle family.  Its first vertex is the
  pointwise `[-1]` shift `UnitConeData.transportedCotwist`, and
  `transportedCotwistH0Iso` specializes the reusable
  `DGFunctor.transportedShiftedFunctorH0Iso` to compare it with the transported
  `H⁰` of the actual shifted dg unit cone;
  `transportedCotwistH0Iso_commShift` specializes the corresponding canonical
  shift-compatibility theorem.  The adjunction unit is literally the rotated
  second map and every value is distinguished under the existing source-side
  hypotheses.  Exactness and equivalence are separate capability accessors
  with their own hypotheses; this presentation infers no
  natural Fourier--Mukai comparison, distinguished functor-category triangle,
  or sphericality.
- Ordinary presentations of dg-adjunction unit triangles (2026-09-13):
  `DGAdjunction.H0Presentation.unitFirstMapNormalizationData` is the
  source-side mirror of the counit presentation and reuses the same generic
  `Triangle.FirstMapNormalizationData` root.  Its `presentedUnitTriangle` has
  literal first two vertices `𝟭 X` and `F ⋙ G`, literal first map equal to
  the presented adjunction unit, and the transported unshifted dg unit cone
  as third vertex; the other two maps and the raw comparison are named.
  Pointwise distinguishedness requires only that the source equivalence be
  triangulated.  The separate cotwist-presentation root owns inverse rotation;
  this normalization root itself infers no Fourier--Mukai comparison,
  exactness, equivalence, or sphericality.
- Ordinary presentations of dg-adjunction counit triangles (2026-09-13):
  `DGAdjunction.H0Presentation.counitFirstMapNormalizationData` feeds the raw
  counit-cone family transported through the target equivalence into the
  generic `Triangle.FirstMapNormalizationData` root.  The resulting
  `presentedCounitTriangle` has literal first two vertices `G ⋙ F` and
  `𝟭 Y`, literal first map equal to the presented adjunction counit, and the
  transported dg twist as its unchanged third vertex; the second and
  connecting maps have semantic natural-transformation names.  A natural
  triangle isomorphism compares the raw and normalized families, and
  pointwise distinguishedness requires only that the target equivalence be
  triangulated.  No unit-side mirror, comparison with an independently chosen
  Fourier--Mukai cone, exactness, autoequivalence, or sphericality is inferred.
- Fourier--Mukai presentations of strict dg adjunctions (2026-09-13):
  `RightAdjointKernelData.ofH0Presentation` and its left-adjoint mirror spend
  the generic equivalence-transported `DGAdjunction.H0Presentation` on the
  existing Fourier--Mukai adjoint-kernel structures.  The two orientations
  agree definitionally with the existing correspondence-swap adapters, so no
  dg-specific copy of kernel-adjunction data is introduced.  Kernels,
  endpoint comparisons, and any kernel arrow realizing the unit or counit
  remain supplied; no comparison of dg and kernel cones is inferred.
- Ordinary presentations of strict dg adjunctions (2026-09-13):
  `DGAdjunction.H0Presentation` transports `DGAdjunction.h0` through supplied
  source and target category equivalences and identifies the resulting two
  functors with named ordinary functors.  Its ordinary adjunction is assembled
  exclusively from Mathlib's adjunction composition and natural-isomorphism
  transport, and its public unit/counit formulas retain both category
  equivalences and endpoint comparisons.  This is the generic bridge needed
  to present strict dg adjunctions by geometric or Fourier--Mukai functors;
  the comparisons are supplied, and no dg lift, kernel realization, or
  compatibility with a separately chosen ordinary adjunction is inferred.
- Scalar-linear object twist as copower--Hom counit twist (2026-09-13):
  The selected `LinearEvaluationData` cone type and
  `linearCopowerAdjunction.CounitConeData` are definitionally equal, so the
  selected object-twist and adjunction-twist functors and their full `H⁰`
  triangle functors need no transport or second cone construction.  For an
  arbitrary scalar-linear evaluation choice,
  `LinearEvaluationData.TwistConeData.adjunctionTwistIso` reuses the existing
  strict-square cone comparison, preserves the canonical inclusion strictly,
  and composes coherently with changes of evaluation data.  The H⁰ layer now
  exposes the scalar-linear twist triangle, its distinguishedness and
  automatic exactness, coherent choice-independence, and the corresponding
  natural isomorphism to the adjunction counit triangle.  This concerns the
  adjunction from all module complexes; it does not construct or restrict to
  `Perf(k)`, provide the other adjoint, or assert sphericality or
  autoequivalence.
- Automatic dg exactness consumer cutover (2026-09-13):
  Public H⁰ exactness and `K₀.map` theorems for homogeneous-transformation
  cones, additive and scalar-linear object twists, and all four enhanced
  adjunction twists/cotwists now construct cone preservation from the dg
  functor itself.  Their redundant endpoint witness arguments have been
  removed.  The lower structured 3-by-3 constructors deliberately remain:
  they expose how cone preservation is assembled from chosen endpoint
  witnesses, but no specialized H⁰ or `K₀` leaf in this cutover requires
  callers to provide them.  The lower capability-parametric adapters remain
  available.  Sign-correct `CommShift` data for the conventional `[-1]`
  functors is unchanged.  The reusable `shiftedFunctorH0IsTriangulated`
  interface likewise retains only the shift witness selecting that comparison
  and derives cone preservation internally.  No global exactness instance is
  installed.
- Automatic dg-functor cone preservation and H⁰ exactness (2026-09-13):
  `DGFunctor.preservesChosenCones` maps a supplied strong split cone witness
  through an arbitrary dg functor.  The images of `IsConeOf.fst` and `.snd`
  give an explicit inverse to the target splitting map, so fullness,
  pretriangulated existence, copowers, and endpoint hypotheses are unnecessary.
  Together with the existing automatic shift preservation,
  `DGFunctor.h0CommShift` and `h0IsTriangulated` package the canonical
  non-instance conclusion that every dg functor between pretriangulated dg
  categories induces a triangulated functor on `H⁰`.  The capability
  structures and their `id`/`comp`/`ofIso` constructors remain as useful named
  data; no global `CommShift` or `IsTriangulated` instance is installed.
- Finite-support comparison for formal complexes (2026-09-13):
  `Homotopy.FiniteCohomologyPresentation` owns the categorical comparison from
  the full zero-differential homology model to the existing finite-biproduct
  model under an explicit vanishing witness.  The specialized
  `Homotopy.FiniteCohomologyPresentationOfSupport` module owns only the
  division-ring constructor which composes that comparison with the
  noncanonical unbounded formality theorem.  This introduces no second
  presentation type, does not require the selected degree set to be minimal,
  and infers neither finite support from boundedness nor naturality from the
  chosen splittings.
- Homology model and unbounded formality over a division ring (2026-09-13):
  `Homotopy.HomologyModel` owns the generic zero-differential complex of
  homology objects in any abelian category.  It makes no formality claim.
  `Homotopy.ModuleCatFormality` owns the coefficient-side theorem that every
  `ModuleCat k`-valued cochain complex is noncanonically homotopy equivalent
  to its zero-differential homology model when `k` is a division ring.  The
  proof uses Mathlib's homology quotient, categorical projectivity of vector
  spaces, and explicit splittings of cycles and boundaries.  It is unbounded
  and requires neither finite-dimensionality nor finite support.  The choices
  are deliberately not packaged as natural data, and the theorem asserts no
  quasi-isomorphism invariance.  The downstream finite-support comparison is
  recorded separately and reuses the existing `FiniteCohomologyPresentation`.
- Bounded-derived `K₀` comparison and geometric class-map transport
  (2026-09-12): `DerivedCategory.boundedHeartToAmbient` is the direct
  standard-heart map `K₀Ab(A) →+ K₀(Dᵇ(A))`, and bounded cohomological
  dévissage proves that it is inverse to `boundedEulerClassHom`.  The proof
  handles shifted single objects with the parity formula for `K₀`, lifts the
  truncation triangles into the bounded full subcategory, and uses triangle
  additivity; it does not assume the comparison.  Consequently
  `boundedDerivedClassMap` canonically transports any supplied additive class
  map on `K₀Ab(A)` to `K₀(Dᵇ(A))`.  For coherent sheaves,
  `K3MukaiTilt.derivedMukaiClass` applies this construction to the existing
  numerical-realization Mukai class and proves the former ambient restriction
  obligation automatically.  The canonical tilt constructor therefore no
  longer asks for an arbitrary ambient map or compatibility proof.  It still
  exposes exactly the geometric inputs not proved here: Grothendieck slope
  boundedness (the remaining `MuHNInput` field on a Noetherian scheme), the
  Hilbert/numerical normalization, dimension-zero Mukai-class classification,
  Hodge positivity, and the boundary Mukai decomposition.
- Bounded-derived cohomological Euler classes (2026-09-12):
  `K₀Ab.of_exact` expresses the middle term of an exact pair through its two
  image classes, and `K₀Ab.eulerClass_add_of_exact` telescopes those identities
  over a finitely supported integer-indexed long exact sequence. For every
  abelian category `A`, `DerivedCategory.boundedEulerClassHom` then gives the
  canonical map `K₀(Dᵇ(A)) →+ K₀Ab(A)` by alternating bounded cohomology.
  This file constructs only the cohomological direction; the separate
  comparison entry above supplies the inverse by dévissage rather than
  assuming a Grothendieck-group equivalence.
- Degreewise ambient coherent Ext-finiteness on projective varieties
  (2026-09-12):
  `ProjectivePresentation.module_finite_ambientExt` combines unconditional
  restricted-twist presentations, finite Ext from restricted twists, and the
  long exact Ext sequence to prove `Module.Finite k` for every
  `Ext^n_{X.Modules}(F, G)`. The result deliberately asserts no uniform or
  pairwise degree bound: finite support still requires a genuine regularity or
  finite-global-dimension theorem, and internal Ext in `Coh X` still requires
  `Dqc.CoherentExtComparison X`.
- Closed-immersion counit epimorphism and restricted-twist presentations
  (2026-09-12): `Scheme.Modules.pushforward_faithful_of_isInducing` detects
  equality of module-sheaf morphisms on the canonical target open attached to
  each source open. Closed immersions therefore have faithful pushforward, so
  the general adjunction theorem makes every component of
  `pullbackPushforwardAdjunction` counit epic. The projective-presentation lane
  now gives unconditional finite restricted-negative-twist quotients of
  coherent sheaves. This does not assert the stronger counit isomorphism or
  exactness of closed-immersion pullback; neither is needed for the quotient.
- Scheme-module stalk and pullback comparison (2026-09-12):
  `AlgebraicGeometry/Modules/Pullback/Stalk.lean` now owns the local-ring-valued
  module-stalk functors, their finite-limit and joint-reflection theorems, the
  private module-skyscraper construction, and the canonical presheaf and sheaf
  pullback-to-stalk isomorphisms. These declarations previously lived in
  `DerivedCategory/Families/FlatPullback.lean` despite mentioning neither
  derived categories, families, nor flatness. The families file now contains
  only the flat local-ring calculation and its exact-pullback consequence;
  open-immersion and relative-perfect consumers use the canonical neutral API.
  The transitional comparison records are removed rather than retained as a
  compatibility shim.
- Finite-biproduct calculus in triangulated `K₀` (2026-09-12):
  `Triangulated/GrothendieckGroup/Biproduct.lean` owns the reusable identities
  `[X ⊞ Y] = [X] + [Y]` and `[⨁ i, X i] = ∑ i, [X i]`, together with
  the constant-family `nsmul` specialization.  The binary law is exactly
  Mathlib's distinguished split triangle; the finite law uses Mathlib's
  finite-type induction and biproduct comparison maps.  This is generic
  triangulated `K₀` infrastructure, not a copower- or twist-specific
  formula.  It makes no Euler-characteristic, formality, or scalar-evaluation
  assertion; those remain downstream consumers.
- Finite cohomology presentation and scalar-linear copower transport
  (2026-09-12):
  `Homotopy.FiniteCohomologyPresentation` owns the coefficient-side data of an
  explicit homotopy equivalence to a finite biproduct of single homology
  objects.  Its shifted normal form reuses Mathlib's `singleFunctors.shiftIso`,
  with a degree-`i` single identified as a degree-zero single shifted by `-i`.
  `DGEnhancement.FiniteCohomologyCopower` transports this presentation through
  `linearCopowerFunctor`: generic additivity of `DGFunctor.h0` and `Cdg.toH0`
  lets Mathlib supply finite-biproduct preservation, and
  `SingleFunctors.postcomp` supplies the coherent shifted family.
  `DGCategory.LinearCopowerUnit` proves directly from the representing
  property that the scalar unit copower is `X`, using the strict canonical
  `IsLinearCopowerOf.compareIso`.
  `DGEnhancement.LinearCopowerFiniteFree` owns the generic `H⁰` leaf: a
  supplied finite basis expands a degree-zero copower as a finite biproduct of
  copies of `X`, with arbitrary finite index universe handled by Mathlib's
  categorical biproduct reindexing.  `Module.finBasis` gives the finite-free
  `finrank` specialization.  The finite-presentation consumer composes these
  interfaces into its nested finite-biproduct normal form.  No new direct-sum
  or shift interface is introduced.  This root still assumes the actual
  `HomotopyEquiv`; it proves no automatic formality, quasi-isomorphism
  invariance, Hom-cohomology comparison, Euler/K₀ formula, cone preservation,
  or basis independence.  The concrete standard-model copower instance is
  supplied separately by `DGCategory.Model.LinearCopower`.
- Supplied-presentation scalar-copower `K₀` class (2026-09-12):
  `DGEnhancement.FiniteCohomologyCopowerK0` owns the numerical leaf
  `FiniteCohomologyPresentation.linearCopowerK₀Of`.  For an explicitly
  supplied finite cohomology presentation whose displayed homology modules
  are finite free, it combines `linearCopowerFinrankIso`, the generic finite
  biproduct law in triangulated `K₀`, and `K₀.of_shift_int` to identify the
  selected scalar-linear copower class with Mathlib's
  `HomologicalComplex.homologyEulerChar` times `[X]`.  The support reduction
  comes only from the supplied presentation; the theorem assumes a nontrivial
  base ring and infers neither a presentation nor formality from bare
  finiteness.  It introduces no
  parallel Euler-characteristic definition and supplies no comparison between
  scalar-linear `LinearEvaluationData` and additive `EvaluationData`.
- Rank-one `K₀` interface and scalar-linear Euler evaluation (2026-09-12):
  `Triangulated/GrothendieckGroup/RankOne` owns the reusable factorization
  `K₀ C →+ ℤ →+ K₀ D` and the objectwise `K₀.IsRankOne` predicate.
  Natural isomorphisms preserve that predicate without exactness; only the
  separate `map_eq_rankOne` theorem assumes the existing hypotheses needed to
  form `K₀.map`.  Both additive `EvaluationData.IsEulerCopower` and the new
  generic-H⁰ scalar-linear specialization reuse this root.  The H⁰
  Hom-cohomology Euler bridge identifies Mathlib's homological Euler
  characteristic with `chiHom` without a boundedness hypothesis.
  `DGEnhancement.HomComplexFiniteCohomologyPresentation` turns the finite
  support already carried by `HomFiniteBounded` into an explicit presentation
  of each `DGLinear.homComplex`, using the coefficient-side division-ring
  formality theorem and the H⁰ homology/shift linear equivalence.
  `HomotopyCategory/DGEnhancement/LinearEvaluationK0` owns the realization:
  the supplied-presentation theorem remains reusable, while
  `IsEulerCopower.ofHomFiniteBounded` constructs that family automatically
  when all linear copowers exist.  Exactness is supplied independently by the
  generic dg-functor theorem; this result does not compare the additive and
  scalar-linear universal properties.
- Direct scalar-linear object twist on `K₀` (2026-09-12):
  `DGCategory.Pretriangulated.LinearObjectTwist` packages the cone of the
  scalar-linear evaluation transformation as
  `LinearEvaluationData.TwistConeData`, delegating cone construction,
  strict-square comparison, shift preservation, and chosen-cone preservation
  to the existing generic interfaces.  The generic H⁰ `K₀` leaf computes
  identity minus scalar-linear evaluation, and
  `SphericalTwist.LinearObjectTwistK0` combines it with the shared
  `IsEulerCopower` predicate to recover the existing numerical `twistK₀`
  formula.  The homotopy-category DG-enhancement leaf
  `DGEnhancement.LinearObjectTwistK0` discharges that predicate automatically
  from `HomFiniteBounded` and all linear copowers.  This path does not pass
  through additive `EvaluationData`.
  Exactness is automatic for the underlying dg functors, and the H⁰ and `K₀`
  leaves no longer accept a cone-preservation witness.
  No autoequivalence, sphericality, naturality of formality, or comparison of
  the two copower universal properties is claimed.
- Scalar-linear copower DG functor and homotopy invariance (2026-09-12):
  `DGCategory.LinearCopowerFunctor` packages the universal property as a
  degreewise `homComplexIso`, then uses it to define the homogeneous
  `coefficientMap`.  Differential, identity, and composition compatibility
  assemble the selected objects into the `k`-linear dg functor
  `linearCopowerFunctor k X : Cdg (ModuleCat k) ⟶ C`.  The standard complex
  model's `DGLinear` instance is only a bridge to Mathlib's existing
  pointwise module action and its `δ_smul`/cochain-composition laws.
  Chain homotopies give coboundary differences, and homotopy equivalences give
  isomorphic witnessed copowers in `H⁰ C`.  The selected-object wrapper is
  owned by `HomotopyCategory.DGEnhancement.LinearCopower`, where it is
  transported through the existing `Cdg.h0Functor` seam rather than a new
  quotient construction.  This
  proves neither quasi-isomorphism invariance nor a finite cohomology
  decomposition, Euler formula, or cone-preservation theorem.  Concrete
  existence for the standard module-complex model is a separate model-layer
  instance.
- Concrete scalar-linear copowers for module complexes (2026-09-13):
  `DGCategory.Model.LinearCopower` identifies the scalar-linear copower of a
  standard dg module complex `X` by a coefficient complex `K` with Mathlib's
  total tensor product `K ⊗ X`.  The forward map is tensor currying in every
  homogeneous degree; its inverse combines Mathlib's total-complex coproduct
  eliminator with `TensorProduct.lift`.  Currying the identity gives the
  universal family, and Mathlib's `D₁`/`D₂` formulas reduce its chain-map
  law to cancellation of the two vertical Koszul signs.  The resulting
  `IsLinearCopowerOf` witness supplies
  `HasLinearCopowers k (Cdg (ModuleCat k))`.  No parallel monoidal, coproduct,
  Hom-complex, or copower abstraction is introduced.  The instance is
  intentionally same-universe because Mathlib's present monoidal `ModuleCat`
  instance has that restriction; it does not assert concrete additive
  copowers, quasi-isomorphism invariance, or a copower instance for another dg
  model.
- Scalar-linear tensor--Hom dg adjunction (2026-09-13):
  `DGCategory.LinearHomFunctor` packages fixed-source right composition as the
  `k`-linear dg functor `DGLinear.homFunctor k E` from an arbitrary
  `k`-linear dg category to the standard dg category of module complexes.
  Under `HasLinearCopowers`, `DGCategory.LinearCopowerAdjunction` proves that
  `linearCopowerFunctor k E` is its strict dg left adjoint.  The unit is the
  selected universal copower chain map, the counit is exactly
  `LinearEvaluationData.ofHasLinearCopowers.evaluation`, and the two triangle
  identities reuse `univ_comp_coefficientMap` and `univ_comp_evalHom`.
  No second adjunction interface, tensor construction, or evaluation map is
  introduced.  The result concerns all coefficient complexes; it does not
  construct `Perf(k)`, compare linear and additive evaluation, produce an
  adjoint on the other side, or imply quasi-equivalence, sphericality, or
  autoequivalence.
- Scalar-linear evaluation root (2026-09-12):
  `DGCategory.LinearEvaluation` assembles the `IsLinearCopowerOf` family at an
  object `E` into `LinearEvaluationData k E`.  Fixed-source right composition
  is exposed once as `DGLinear.postcompCochain`; the evaluation action is its
  composite with the target universal chain map, followed by the source
  copower's linear representing inverse.  The result is a `k`-linear dg
  functor, a closed evaluation transformation to the identity, and a coherent
  canonical `Z⁰` isomorphism between any two choices which commutes strictly
  with evaluation.  `HasLinearEvaluationData` stores only existence and is
  supplied at low priority by `HasLinearCopowers`.
  This is parallel to, not a refinement of, additive `EvaluationData`: there
  is no adapter between their incompatible universal properties.  The
  coefficient-complex homotopy result is owned by the copower DG-functor root;
  this evaluation root itself asserts no cone, exactness, Euler/K₀,
  or finite-presentation result.  Its standard module-complex inputs now obtain
  concrete existence from the separate model-layer tensor instance.
- Scalar-linear dg Hom and copower root (2026-09-12):
  `DGCategory.Linear` repackages the existing Hom-complex of a `DGLinear k C`
  as `DGLinear.homComplex`, a `ModuleCat k`-valued cochain complex.
  `DGCategory.LinearCopower` defines `IsLinearCopowerOf` by a bundled linear
  equivalence with Mathlib's existing `HomComplex.Cochain`.  Its
  lift, closed canonical comparison, strict comparison laws, and
  `HasLinearCopower(s)` choice-free existence capabilities follow the same
  universal-property pattern as the additive root.  There is deliberately no
  projection to `IsCopowerOf`: that interface represents all additive
  cochains, so forgetting scalar structure would strengthen rather than
  preserve the linear contract.  Scalar-linear evaluation data and the
  coefficient DG-functor/homotopy root now consume this universal property
  separately; no Euler-class or finite-presentation result is asserted here.
- Scalar-linear dg Hom-cohomology comparison (2026-09-12):
  `DGCategory.Pretriangulated.ShiftIso` now packages the degreewise
  bijectivity in `IsShiftBy` as an actual isomorphism of Hom-complexes, and
  `LinearShiftIso` supplies its `ModuleCat k` refinement through the existing
  `DGLinear.postcompCochain` and Mathlib cocycle-to-shift equivalence.
  `DGCategory.LinearH0Homology` owns the intrinsic degree-zero quotient
  comparison, and `Pretriangulated.LinearShiftHomology` combines it with
  Mathlib's shifted-homology isomorphism for an explicit `IsShiftBy` witness.
  `DGEnhancement.H0.HomCohomology` only selects the existing `HasShift` object,
  giving
  `Hⁿ(DGLinear.homComplex k X Y) ≃ₗ[k] Hom_{H⁰ C}(X, Y⟦n⟧)`, both for an
  explicit shift witness and for the selected `HasShift` object.  Public
  representative laws identify the maps with `H0.homMk` and right composition
  by the shift element.  The `+n` target convention follows from the `-n`
  shift of Hom-complexes.  This is a pointwise linear comparison only: no
  naturality package, finite-dimensional transfer, formality, Euler
  characteristic, `K₀`, or sphericality statement is inferred.
- Object-twist `K₀` action and Euler-realization boundary (2026-09-12):
  `DGEnhancement.H0.NaturalTransformationConeK0` owns the reusable theorem
  that a functorial cone acts on `K₀` by target endpoint minus source
  endpoint, both on generators and, via automatic dg-functor exactness, as a
  homomorphism.  The object twist specializes this to identity minus its
  evaluation functor.  `DGEnhancement.H0.ObjectTwistK0` owns the explicit,
  choice-invariant `EvaluationData.IsEulerCopower` capability saying exactly
  when that evaluation class is the Euler multiple of `[E]`.  Together with
  that exactness, the spherical consumer proves that the induced
  object-twist map equals the existing numerical `twistK₀`.
  This capability is supplied realization input, not a consequence of the
  present additive `IsCopowerOf`, which represents ℤ-additive rather than
  `k`-linear cochains.  The separate scalar-linear copower and evaluation
  roots now exist, coefficient-complex homotopy invariance is closed, and
  supplied finite cohomology presentations now transport to shifted finite
  biproducts and finite-free homology expands these into `finrank` copies.
  The scalar-linear Hom-cohomology comparison is now closed, generic
  triangulated `K₀` computes finite biproduct classes, and the supplied
  finite-presentation scalar-copower class is Mathlib's homological Euler
  characteristic times the object class.  The shared `K₀.IsRankOne`
  interface and its direct linear-evaluation consumer are now closed as well.
  Any passage to additive `EvaluationData` remains explicit, and automatic
  formality remains a separate later lane.
- `K₀` actions of enhanced adjunction cones (2026-09-12):
  `SphericalTwist.EnhancedFunctorK0` derives the four generator identities
  directly from the distinguished adjunction triangles and lifts them, via
  automatic dg-functor exactness, to equalities of `K₀`
  homomorphisms.  Each conventional twist or cotwist acts as the identity
  minus its corresponding adjunction composite.  This does not identify an
  object-twist evaluation composite with an Euler multiple of the object;
  that copower computation remains the next seam toward `twistK₀`.
- Exact twist and cotwist equivalences on `H⁰` (2026-09-12):
  `twistH0EquivalenceIsTriangulated` and
  `cotwistH0EquivalenceIsTriangulated` combine the separately proved ordinary
  equivalences and exact forward functors using Mathlib's canonical
  `Equivalence.CommShift` and `Equivalence.IsTriangulated` interfaces.  The
  compatible shift structure and triangulatedness of each inverse are derived,
  not assumed or duplicated in a repository-owned record.  This packaging
  still proves no `K₀` action formula, cone relation, or sphericality.
- Sign-correct exactness of shifted dg functors (2026-09-12):
  `DGFunctor.shiftedFunctorH0CommShift` composes the canonical comparison on
  `H⁰(F)` with the signed integral-shift package and transports it across
  `shiftedFunctorH0Iso`; `shiftedFunctorH0IsTriangulated` transports exactness
  by the same route.  `shiftedFunctorH0Iso_commShift` now proves that this
  transported package agrees with the package constructed directly from the
  shifted dg functor, including the Koszul sign, while
  `transportedShiftedFunctorH0Iso_commShift` carries the comparison through
  endpoint equivalences.  Beyond the endpoint shift and additivity packages
  needed to state compatibility, the only extra functor hypothesis there is
  additivity of the forward target equivalence, used by the reusable
  `Pretriangulated.commShiftIso_commShift`.  These are explicit interfaces,
  not global instances.
  The underlying `H⁰` capability transport now also keeps independent source
  and target object universes, matching the shifted-functor comparison API.
  The conventional `[-1]` dual twist and cotwist now reuse this root, and their
  exactness wrappers require no endpoint witnesses.  This proves no dg
  quasi-equivalence, cone relation, or sphericality.
- Inverse-rotated dg cone projection coherence (2026-09-13):
  `H0.shiftFunctorCompIsoId_hom_app` computes Mathlib's packaged cancellation
  of an integral shift pair using the composite dg shift witness.
  `ConeData.inverseRotateFirstH0` assembles the first maps of the objectwise
  inverse-rotated cone triangles into a natural transformation, while
  `ConeData.shiftedFstH0` descends the source-regraded closed degree-one cone
  projection.  Their equality through `shiftedFunctorH0Iso` proves that the
  cone-triangle and inverse-rotation minus signs cancel and that the remaining
  `[1][-1]` cancellation is exactly the existing `HasShift` comparison.
  `DGFunctor.h0CompIso` and `h0IdIso` now expose their identity components,
  while `HomogeneousNatTrans.h0_comp'`, `h0_whiskerLeft`, and
  `h0_whiskerRight` package descent of strict composition and whiskering.
  `CounitConeData.twistAdjointComparisonH0_eq_inverseRotateFirstH0` consumes
  those generic laws to factor the twist comparison through the
  inverse-rotated first map and the descended left counit.  No adjunction,
  exactness, invertibility, or sphericality is inferred from the cone-generic
  statement, and the specialization adds no such conclusion.
- Sign-correct exactness of integral shift functors (2026-09-12):
  `Triangulated.ShiftFunctor` now owns the explicit Koszul-signed `CommShift`
  on `[n]`, its comparison with `Triangle.shiftFunctor`, and
  triangulatedness for every `n : ℤ`.  The unsigned `CommShift` remains
  available as explicit data for object-only uses, but neither package is a
  global instance.  The stability-action `[±2]` implementation is reduced to
  compatibility wrappers over this root.  This closes the odd-shift sign
  seam; composing it with an already exact functor is a downstream operation,
  not another shift-functor abstraction.
- Exactness of the four stored dg adjunction cones (2026-09-12):
  `EnhancedAdjunctionCones` now exposes shift preservation, chosen-cone
  preservation, the induced `H⁰` `CommShift`, and triangulatedness for the
  twist, dual cotwist, and the unshifted cones underlying the dual twist and
  cotwist.  The retained structured cone-preservation constructors reuse the
  generic adjunction-cone 3-by-3 theorem and accept endpoint witnesses to
  expose that computation; the exactness wrappers require none.
  Exactness for the two conventional `[-1]` shifted functors is obtained in
  the separate shifted-dg-functor root above.  No cone relation, equivalence,
  or sphericality follows.
- Conventional shifted dg twists on `H⁰` (2026-09-12):
  `DGFunctor.shiftedFunctor_h0_eq` and `shiftedFunctorH0Iso` package the
  objectwise and morphism computations as a functor-level comparison
  `H⁰(F[n]) ≅ H⁰(F) ⋙ [n]`.  Equivalence of `H⁰ F` therefore transports to
  every shifted dg functor without asserting a dg quasi-equivalence or
  exactness.  `EnhancedAdjunctionCones` now names the conventional
  `dualTwistFunctor` and `cotwistFunctor`, and `cotwistH0Equivalence` applies
  that bridge to the recorded unshifted cotwist condition.  This introduces
  no second shift structure and proves no relation among the four adjunction
  cones or sphericality.
- Generic twist kernels and left-adjunction Fourier--Mukai dual cotwists
  (2026-09-12): `CounitKernelConeData.twistKernel` now names the ordinary image
  of the selected enhanced cone, with its definitional transform isomorphism
  and the correspondingly narrow `IsKernelFunctor` conclusion.
  `DualCotwistKernelData` and its enhanced form then swap the correspondences
  through `LeftAdjointKernelData.toRightAdjointKernelData` and reuse that
  counit/twist construction for the left-adjunction counit.  The semantic API
  names `dualCotwist`, presents it by `dualCotwistKernel`, and exposes the
  source-natural triangle
  `Φ_P ⋙ Φ_Q ⟶ 𝟭 X ⟶ dualCotwist ⟶ (Φ_P ⋙ Φ_Q)⟦1⟧`, pointwise
  distinguished under the existing exactness hypotheses.  No new cone or
  normalization is introduced, and no exactness, invertibility, canonicity,
  dual-kernel identity, or sphericality is asserted.
- Left-adjunction Fourier--Mukai dual twists (2026-09-12):
  `DualTwistKernelData` and its enhanced cone form read
  `LeftAdjointKernelData.toRightAdjointKernelData` with the correspondences
  swapped, so the left-adjunction unit reuses the generic unit-kernel,
  normalization, inverse-rotation, and shifted-kernel machinery.  The semantic
  API names the resulting functor `dualTwist`, presents it by
  `dualTwistKernel`, and exposes the target-natural triangle
  `dualTwist ⟶ 𝟭 Y ⟶ Φ_Q ⋙ Φ_P ⟶ dualTwist⟦1⟧`, pointwise
  distinguished under the existing exactness hypotheses.  This is not a new
  adjunction, cone choice, or normalization construction, and it asserts no
  exactness, invertibility, dual-kernel identity, or sphericality.
- Presented dg/Fourier--Mukai dual-twist comparison (2026-09-13):
  `DGAdjunctionDualTwistComparison` is a semantic facade over the existing
  right-unit/cotwist comparison after swapping the endpoint categories and
  correspondences.  `PresentedDualTwistComparisonData` is an abbreviation of
  the canonical `PresentedUnitComparisonData`, so objectwise and supplied
  natural triangle comparisons, the conventional and actual-dg shift laws,
  exactness, and conditional `KernelAutoequivalence` packaging introduce no
  second comparison or shift structure.  The equivalence of `H⁰` of the
  unshifted unit cone, the natural comparison data, endpoint exactness, and
  the target `CommShift` remain explicit inputs.  No dg quasi-equivalence,
  inverse-kernel formula, comparison canonicity, or sphericality is asserted.
- Presented dg/Fourier--Mukai dual-cotwist comparison (2026-09-13):
  `DGAdjunctionDualCotwistComparison` swaps the endpoints and correspondences
  and exposes the existing right-counit/twist comparison through
  dual-cotwist names.  `PresentedDualCotwistComparisonData` and its
  `ShiftCompatibility` are aliases of the canonical comparison roots; the
  semantic constructors merely populate those existing records.  The dual
  cotwist is the unshifted counit cone, so no inverse rotation or `[-1]` shift
  is introduced.  Natural comparison data, the `H⁰` equivalence hypothesis,
  endpoint exactness, and the target `CommShift` remain explicit.  No dg
  quasi-equivalence, inverse-kernel formula, canonicity, or sphericality is
  asserted.
- Enhanced twist/cotwist conditions to Fourier--Mukai kernels (2026-09-13):
  `DGAdjunctionTwistCotwistAutoequivalence` is an FM-owned consumer of the
  canonical `SphericalTwist.TwistCotwistEquivalenceConditions`.  Its two
  quasi-equivalence fields supply the existing twist and unshifted cotwist
  `H⁰` equivalence hypotheses through `DGFunctor.isEquivalence_h0`; the
  existing comparison constructors then package the selected kernels as
  independent `KernelAutoequivalence`s.  No paired or spherical record is
  introduced.  Exactness still consumes the existing per-side
  `ShiftCompatibility` and endpoint triangulated equivalence, and the dual
  twist/cotwist, inverse kernels, comparison canonicity, and full sphericality
  remain outside the conclusion.
- Shifted Fourier--Mukai cone kernels (2026-09-12):
  `KernelConeNormalizationData` names the ordinary kernel represented by its
  selected enhanced cone and, for every integer shift, the kernel obtained by
  shifting that cone in the enhancement's homotopy category.  The enhancement
  comparison and the kernel family's existing Mathlib `CommShift` component
  give the reusable isomorphism from its transform to the pointwise-shifted
  cone transform.  `AdjunctionUnitKernelConeData.cotwistKernel` specializes
  this at `-1`, so the conventional cotwist is now explicitly a kernel functor.
  No second shift structure is installed, and the statement does not make the
  selected kernel canonical, exact, invertible, or spherical.
- Fourier--Mukai cotwist inverse rotation (2026-09-12):
  `AdjunctionUnitKernelConeData.cotwist` is the pointwise functor-category
  `[-1]` shift of the selected unshifted cone transform, and
  `cotwistTriangleInSource` reuses Mathlib's `invRotate` to produce the
  source-natural family
  `cotwist ⟶ 𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧`.  Its three projection functors
  are identified strictly, its second map is literally the adjunction unit as
  a natural transformation, and every value is distinguished.  The result is
  choice-dependent and ordinary-categorical.  Its shifted-kernel presentation
  is now constructed downstream; exactness, invertibility, comparison with a
  dg adjunction cone, and sphericality remain separate seams.
- Right-adjunction unit kernels and literal unit triangles (2026-09-12):
  `FourierMukai.AdjunctionUnitKernelData` and its enhanced cone form are
  definitional specializations of the generic kernel-transformation roots,
  providing their second consumer without a parallel record or normalization
  proof.  They package the supplied kernel arrow `O_Δ ⟶ P ⋆ Q`, its exact
  transform equation, and the source-natural triangle
  `𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟭 X)⟦1⟧`, pointwise distinguished under
  the existing exactness hypotheses.  The third functor is the unshifted
  cotwist-cone candidate; its `[-1]` shift and inverse-rotated triangle are now
  constructed downstream, while exactness, autoequivalence, and sphericality
  remain separate seams.
- First-map normalization for triangle-valued functors (2026-09-13):
  `Triangle.FirstMapNormalizationData` is the generic owner for replacing the
  first two projections of `T : J ⥤ Triangle C` by named isomorphic functors
  and making a compatible named first map literal.  It reuses Mathlib's
  triangle-functor constructors, leaves the third projection unchanged, and
  transports pointwise distinguishedness.  It supplies no canonicity,
  exactness, or distinguished triangle in a functor category.
- Generic enhanced kernel-transformation cones (2026-09-12):
  `Enhancement.liftedCocycle` and `Enhancement.conePresentation` own the
  noncanonical lift of an ordinary morphism to a closed representative and dg
  cone.  `FourierMukai.KernelTransformationData` packages a kernel morphism
  whose transform is a named natural transformation in supplied endpoint
  presentations; `KernelTransformationConeData` adds the enhanced choices and
  forgets back one way.  Its `normalizationData` feeds
  `Correspondence.KernelConeNormalizationData`, whose adapter delegates the
  endpoint/first-map transport to `Triangle.FirstMapNormalizationData`.  The
  counit kernel records now delegate to these generic owners without changing
  their public contracts, with inverse adapters and simp round trips proving
  the two presentations equivalent.  Fullness remains only a sufficient
  constructor, choices remain noncanonical, and the normalized result is only
  pointwise distinguished: no exactness, functor-category distinguishedness,
  autoequivalence, or sphericality is inferred.
- Literal Fourier--Mukai counit triangles (2026-09-12):
  `CounitKernelConeData.counitTriangleInSource` transports the raw transform
  triangle of an enhanced counit-kernel cone to a source-natural triangle with
  vertices `Φ_Q ⋙ Φ_P`, `𝟭 Y`, and the kernel-presented twist, and with
  first map literally the supplied adjunction counit.  The construction uses
  the generic `Triangle.FirstMapNormalizationData` wrapper around Mathlib's
  `Triangle.functorMk` and `Triangle.functorIsoMk`; the natural
  comparison exposes all three components, and exact kernel evaluation makes
  every value of the normalized family distinguished.  This is pointwise
  distinguishedness only: it does not assert a distinguished triangle in the
  functor category, exactness or autoequivalence of the twist, or independence
  from the selected enhancement representative and cone.
- Ordinary counit-kernel data and enhanced cone selection (2026-09-12):
  `FourierMukai.CounitKernelData` separates the geometric kernel morphism and
  its exact transform equation from any enhancement or cone choice.
  `CategoryTheory.Z0.toH0_full` records the reusable quotient-surjectivity fact,
  so `CounitKernelData.toConeData` uses Mathlib's `Functor.preimage` to choose a
  closed representative and pretriangulated cone in any enhancement.  The
  forgetful map recovers the ordinary datum, but no selected representative or
  cone is claimed canonical.  `CounitKernelData.ofFull` is only a constructor
  under the explicit strong hypothesis `E.kernelTransform.Full`; the geometric
  counit-trace realization remains open.
- H⁰ cone-triangle comparison across strict isomorphism squares (2026-09-12):
  `Algebra/Homology/DGCategory/FunctorCategoryH0.lean` owns the canonical
  `DGFunctor.h0Iso`, including identity and composition coherence.
  `DGEnhancement/H0/NaturalTransformationCone.lean` upgrades the existing
  strict-square natural transformation to `ConeData.triangleIsoOfStrictSquare`
  when both endpoint maps are isomorphisms. Its third component is the `H⁰`
  image of the canonical dg cone-functor comparison, not a second comparison
  construction. `DGEnhancement/H0/ObjectTwist.lean` specializes this interface
  to `TwistConeData.twistTriangleIsoOfEvaluation` across both evaluation and
  cone choices, with component, identity, and composition laws, while retaining
  the original `twistTriangleIso` definition for same-evaluation callers. This is
  choice-independence of the full triangle functor; it does not assert that the
  twist itself is an autoequivalence or that the object is spherical.
- DG cone comparison and preservation transport (2026-09-12):
  `Algebra/Homology/DGCategory/Pretriangulated/Functor.lean` proves that
  `DGFunctor.PreservesChosenCones` transports across an isomorphism in
  `Z⁰ (DGFunctor C D)`.  This remains useful compatibility data even though
  every dg functor now supplies the capability directly.
  `Pretriangulated/Lift.lean` owns the reusable
  `IsConeOf.isoOfStrictSquare`: endpoint isomorphisms in a strictly commuting
  square lift to an isomorphism between arbitrary chosen cones.
  `Pretriangulated/NaturalTransformationCone.lean` specializes it to cone dg
  functors, and `Pretriangulated/ObjectTwist.lean` gives the resulting
  `TwistConeData.compareIso`, strict compatibility with `id ⟶ T_E`, and strict
  identity/composition coherence.  This identifies the twist dg functor
  independently of both evaluation and cone choices; it does not assert
  autoequivalence or sphericality.
- DG copower and evaluation-data existence packaging (2026-09-12):
  `Algebra/Homology/DGCategory/Copower.lean` owns the Mathlib-style
  `HasCopower` and `HasCopowers` mere-existence capabilities, their
  noncomputable `copowerData` selector returning a `CopowerData` witness, and
  the narrower `HasEvaluationData E` capability consumed by object twists. It
  also proves
  that canonical copower comparisons are closed and compose strictly, then
  assembles these into `EvaluationData.compareIso` in
  `Z⁰ (DGFunctor C C)` with strict compatibility with evaluation. No
  concrete dg category is asserted to have all copowers.  Generic cone
  preservation is derived from the cone's split matrix identities, not from
  this mapping-out universal property.
- Exact functor-family shift coherence (2026-09-12):
  `CategoryTheory/Triangulated/ExactFunctorFamily.lean` now makes
  `Functor.ExactFamily F` extend Mathlib's `F.CommShift ℤ` for the pointwise
  shift on the target functor category, and adds only pointwise
  triangulatedness. The parallel `FamilyCommShift` record and its manually
  stored evaluation naturality are removed. The generic extensionality
  theorem for `CommShift` lives at the mirrored Mathlib definition site in
  `CategoryTheory/Shift/CommShift.lean`; the explicit, non-instance adapters
  from `CommShift₂` and their evaluation-agreement theorems live in
  `CategoryTheory/Shift/FunctorCategory.lean`. Thus `ExactBifunctor` retains
  Mathlib's two-variable Koszul contract while its two family projections use
  the canonical one-variable interface, with complete shift-data agreement
  rather than an isolated comparison at shift one.
- Bounded dévissage for the derived functor of an exact functor
  (2026-09-10, #1069/#1070/#1071):
  `Algebra/Homology/DerivedCategory/CohomologyObjectProperty/Bounded.lean` owns
  `DerivedCategory.bounded_induction` and the truncation stability of
  `cohomologyIn`; `Algebra/Homology/DerivedCategory/ExactFunctor/Bounded.lean`
  owns `Functor.mapDerivedCategory_map_bijective_of_bounded` and
  `Functor.exists_bounded_iso_mapDerivedCategory_obj`. For an exact
  `F : A ⥤ B` between abelian categories that is bijective on every `Ext`
  group, the derived functor is fully faithful on bounded objects and hits
  every bounded object whose cohomology lies in the essential image of `F`;
  that is `Dᵇ(A) ≌ Dᵇ_{F(A)}(B)`, stated in Mathlib's namespace with no
  geometry, and it is an upstream candidate. The one geometric consumer,
  `AlgebraicGeometry/DerivedCategory/Dqc/Identification.lean`, reduces
  `BoundedCoherentDqcIdentification X` on a locally noetherian scheme to the
  single proposition `CoherentExtComparison X`: `Coh.ι X` is bijective on
  `Ext^n(F, G)` for coherent `F`, `G`. The `comparison` field is `Iso.refl _`.
  Three decisions are recorded here so the sub-issues do not reopen them.
  1. *The #1069 formulation fork is settled as: neither form is on the path.*
     The identification as typed lands in `D(X.Modules)`, not in a derived
     category of quasi-coherent sheaves, and `Dqc.lean` pins the functor to
     `mapDerivedCategory (Coh.ι X)`. Once full faithfulness is known,
     essential surjectivity is the formal cone argument above, so the
     dévissage that classically consumes coherent subsheaves (subobject form,
     Stacks 01PG) is not consumed, and the Ind form is not either. The
     scheme-level approximation statement becomes relevant only for a route
     through an abelian category of quasi-coherent sheaves, which the
     repository does not have; it stays unwritten until such a route exists.
  2. *The #1070 route taken is the general root, not the special case.* The
     route not taken, a direct proof for `Coh ⊂ QCoh`, would not have reached
     the stated target anyway: the surjection-lifting hypothesis of Stacks
     0FCL fails for `Coh X ⊆ X.Modules`. On `X = 𝔸¹`, the module sheaf
     `F := ⨁_{U ⊊ X open} j_{U!}𝒪_U` surjects onto `𝒪_X`, but `Γ(X, F) = 0`
     because a nonzero section of `𝒪_U` on a proper open of an integral scheme
     has support `U`, which is not closed; so `Hom(M~, F) = Hom(M, Γ(X, F)) = 0`
     for every quasi-coherent `M~`, and no coherent sheaf maps onto `𝒪_X`
     through `F`. The Ext comparison is therefore genuine geometric content.
  3. *What supplies `CoherentExtComparison X` remains open, and the affine
     case is not a shortcut.* The classical proofs pass through
     `D(QCoh X) ≌ D_qc(X)` (Stacks 08DB, the coherator) or through
     quasi-coherent injectives being injective in `X.Modules` (Hartshorne,
     *Residues and Duality* II.7.18); neither is available at this Mathlib
     pin. Mathlib's own sufficient conditions,
     `Functor.mapExt_bijective_of_preservesProjectiveObjects` and
     `…_of_preservesInjectiveObjects`, do not apply to `Coh X`: it has neither
     enough projectives nor enough injectives. For `X = Spec R` with `R`
     noetherian, scoping on 2026-09-10 found that a finite-free-resolution
     argument needs `Ext^i_{X.Modules}(𝒪_X, N~) = 0` for `i > 0`, and the
     affine vanishing in `Cohomology/Derived/AffineVanishing.lean` is stated
     for `Sheaf.H`, the `Ext` of *abelian* sheaves out of the constant sheaf.
     Bridging the two needs either injective module sheaves to be flasque
     plus flasque abelian sheaves to be `Sheaf.H`-acyclic (the Čech
     comparison in `Sites/SheafCohomology/Cech/Comparison.lean` gives
     acyclicity only from Čech exactness), or `tilde` of an injective module
     to be an injective module sheaf (Hartshorne III.3.4, which needs
     Artin--Rees, absent from Mathlib). `tilde` is also not yet known to be
     exact in the tree. Each of these is its own lane; the first was taken, see 4.
  4. *Affine noetherian schemes satisfy `CoherentExtComparison`* (2026-09-10,
     same lane). `AlgebraicGeometry/DerivedCategory/Dqc/AffineIdentification.lean`
     proves `coherentExtComparison_spec` for `Spec R`, `R` noetherian, by
     `Functor.bijective_mapExtAddHom_of_generators`
     (`Algebra/Homology/DerivedCategory/Ext/AcyclicGenerators.lean`: dimension
     shifting in the first variable along a class of generators acyclic on both
     sides, the mirror of `extComparisonAddEquiv` in `Ext/AcyclicComparison.lean`)
     with generators `𝒪^k` (`Modules/Coherent/Affine/Free.lean`): projective in
     `Coh (Spec R)` through `Coh.affineEquivalence`, and acyclic in `X.Modules`
     because `Ext_{X.Modules}(𝒪_X, G) ≅ H(G)` vanishes by affine vanishing. That
     bridge is `SheafOfModules.extUnitAddEquivH` in
     `Algebra/Category/ModuleCat/Sheaf/Cohomology.lean`, stated for sheaves of
     modules on a site with a terminal object under an acyclicity hypothesis on
     injectives, discharged on a space by flasqueness
     (`Topology/Sheaves/Flasque.lean`, `Topology/Sheaves/ModulesCohomology.lean`)
     and reassembled for the `X.Modules` wrapper in
     `AlgebraicGeometry/Cohomology/Derived/UnitExt.lean`. The general-scheme
     comparison is still open; the affine proof uses that `𝒪^k` present every
     coherent sheaf, which fails off the affine case, so it is not a shortcut.
- Divisorial charge block (2026-09-09; owner corrected by #1313 on 2026-09-13):
  `CategoryTheory/Triangulated/StabilityCondition/CentralCharge/Divisorial/`
  owns the central-charge arithmetic on an uncompressed real divisor space.
  `Coordinates.lean` owns `ChargeCoordinates`; `Charge.lean` owns
  `ChernCharacter`, `StabilityParameters` and the intrinsic charge;
  `Slice.lean` owns `fullChargeFamily` and `OrthogonalSlice`; and
  `Discriminant.lean` owns the Macri--Schmidt quadratic forms. The abstract
  `DivisorSpace` and Hodge certificates now live at the neutral
  `LinearAlgebra/BilinearForm/HodgeIndex.lean` owner. `Walls/Divisorial/`
  retains the fixed-slice wall equation, circle geometry and finiteness.

  The geometric adapters stay under `AlgebraicGeometry/Numerical/Stability/`:
  `SurfaceChargeNumerical.lean`, `DivisorialChargeNumerical.lean`,
  `DivisorialChargeScalarExtension.lean`, `DivisorialWallTransport.lean`, and
  the numerical-realization halves of `DivisorialDiscriminant.lean` and
  `DivisorialWallCircle.lean`. The old paths are removed rather than shimmed.
  `SurfaceChargeNumerical.lean` declares its adapters into
  `Wall.Divisorial.ChargeCoordinates` so dot notation keeps working on the
  coordinates they produce, which the placement rule permits; its module is
  still under `AlgebraicGeometry/`, so its records stay in the
  algebraic-geometry audit lane, while the 177 moved declarations are audited
  in `scripts/StabilityConditionAudit/Divisorial.lean`. Rule 8 of
  `scripts/check_layering.py` pins the six charge structures to the
  `CentralCharge/Divisorial/` subtree, the three Hodge structures to their
  neutral owner, and fails if a geometric module declares them again.

  **The candidate entry for this lane overstated its payoff.** It said the move
  would let `Wall.stChargeFamily` be defined as a reindexing of
  `ChernCharacter.fullChargeFamily`, leaving one formula owner. That is not
  what the move buys. `reZ` and `imZ` in `Walls/Numerical/Basic.lean` remain
  the definition the circle, line, disjointness and nesting theorems are stated
  against, and redefining them would rewrite that whole development. The two
  presentations stay related by the proved bridges
  `ChargeCoordinates.stCharge_toNumClass` and
  `OrthogonalSlice.chargeFamily_reindex_ofST`. What the move buys is the
  placement itself, and that a future threefold or BMT charge family, or the
  spherical wall lane, can now consume the divisorial layer without importing
  geometry.

- Mukai stability-condition specialization (2026-09-08):
  `CategoryTheory/Triangulated/StabilityCondition/Mukai/` is the sibling
  consumer of generic weak stability and tilting. `Charge.lean` owns the
  categorical Mukai class map and its additive charge, `Slope.lean` owns weak
  slope compatibility, `NumericalCases.lean` owns the four numerical
  half-plane adapters, `Ambient.lean` owns restriction from `K₀ C` to a heart,
  and `Tilting.lean` owns the HN-tilt consumers. The generic
  `Weak/Foundation/StabilityFunction` and `Weak/Tilting/TorsionPair` umbrellas
  no longer import this specialization. At the lower layer,
  `LinearAlgebra/Lattice/Mukai/CentralCharge.lean` now exposes
  `Mukai.expChargeHom`, so heart and ambient charges compose additive
  homomorphisms instead of reproving additivity. The canonical
  numerical lemmas are `Mukai.expCharge_zero`, `expCharge_add`, and
  `expCharge_neg`; their historical `CategoryTheory.Triangulated` names remain
  stable as aliases in `Mukai/Charge.lean`. `GeometricInput.lean` now isolates
  the two remaining geometric obligations as independent propositions:
  classification of rank-and-degree-zero torsion classes and a factorwise
  boundary Mukai decomposition. The boundary contract
  `HasBoundaryMukaiDecompositionWith` is parameterized by a predicate on the
  factors; the exact-Hodge-margin contract and the uniform `realForm ≥ -δ`
  contract are its abbreviations, the historical K3 contract is only `δ = 1`,
  and the theorems turning each predicate into `Re Z > 0` live in
  `Tilting.lean` rather than in the contract.
  `Assembly.lean` carries the same hierarchy through
  `tiltStabilityFunctionOfMargin`, `tiltStabilityFunctionOfLowerBound`, and the
  legacy `tiltStabilityFunction`. Todd normalization remains upstream in the
  additive class map, so this categorical construction has no surface-type
  flag. Its extension argument is not Mukai-specific: the reusable constructor
  lives at
  `Weak/Tilting/TorsionPair/HnTiltStabilityFunction.lean` and consumes any
  additive ambient charge positive on nonzero torsion and shifted-free
  generators.
- Left orthogonals are closed under colimits (2026-09-04):
  `CategoryTheory/ObjectProperty/Orthogonal.lean` owns
  `instIsClosedUnderColimitsOfShapeLeftOrthogonal`, beside Mathlib's own
  `Mathlib/CategoryTheory/ObjectProperty/Orthogonal.lean`. It is the one
  hypothesis of `ObjectProperty.coprodClosure_le` that neither Mathlib file
  supplied: `IsClosedUnderIsomorphisms` and `ContainsZero` come from
  `ObjectProperty/Orthogonal.lean` and `IsTriangulatedClosed₂` from
  `Triangulated/Orthogonal.lean`. `CompactlyGenerated/Coaisle.lean` and
  `CompactlyGenerated/IndExtension.lean` each hand-rolled the same induction
  over `coprodClosure` with verbatim identical `of_iso`, `of_coproduct`, and
  `of_extension` branches; both now apply `coprodClosure_le` and prove only
  their own generator case, which is 42 lines deleted for 29 added. The
  instance is stated for an arbitrary colimit shape, not just `Discrete ι`,
  because `IsColimit.hom_ext` is the entire proof; no dual for
  `rightOrthogonal` under limits was added, as no consumer needs one.
- Restricting a functor to the subcategories an `ObjectProperty` cuts out
  (2026-09-04): `CategoryTheory/ObjectProperty/Lift.lean` owns
  `liftOfLE` with its `Additive`, `CommShift ℤ`, and `IsTriangulated`
  instances, `preimageLift` with the same three, `inverseImageLift`,
  `liftToInverseImage`, and `Adjunction.restrictInverseImageLeft` and
  `restrictInverseImageRight`. Mathlib defines `lift`, `ι`, `ιOfLE`,
  `liftCompιIso`, and `fullyFaithfulι` in
  `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`, so the file
  mirrors that directory; it is named `Lift.lean` and not `FullSubcategory.lean`
  because the latter is one of the two paths `check_source_independence.py`
  keeps retired. The block needs Mathlib alone and imports nothing from
  `DerivedAlgGeo`, which is what makes it generic rather than t-structure
  theory. `CategoryTheory/Triangulated/TStructure/Restriction.lean` keeps
  Steps 2--4 of Theorem A.17 and now imports the root; `Polishchuk.lean`,
  `Phase/Transfer/Inducing.lean`, and `Phase/Transfer/BaseChange.lean` import
  it directly rather than through the t-structure file, and no compatibility
  shim was left behind. The twelve `#print axioms` entries moved from
  `StabilityConditionAudit/TStructureCore.lean` to the new
  `StabilityConditionAudit/ObjectPropertyLift.lean`. Rule 7 of
  `scripts/check_layering.py` keeps the block at that path: the root must
  import no `DerivedAlgGeo` module, must declare all six, and no other module
  may redeclare any of them.
- Orthogonal exceptional blocks and residual projections:
  `CategoryTheory/Triangulated/SemiorthogonalDecomposition/Blocks.lean`
  owns positive-length mutually orthogonal exceptional blocks, their
  triangulated spans, decomposition type, and residual right orthogonal;
  `Projection.lean` owns a chosen right adjoint to a full-subcategory
  inclusion and its universal Hom equivalence; `Mutation.lean` constructs the
  objectwise counit triangle and proves the generic projection-chain theorem.
  Ext profiles, their bidirectional transport, and classification-induced
  candidate matching remain generic in `Triangulated/SerreFunctor/`, which
  since 2026-09-13 imports the linear duality root rather than owning it; adjacent Ext shift
  rigidity and bidirectional ordered block-length comparison live in
  `SemiorthogonalDecomposition/AdjacentExt.lean`.  The one-step criterion and
  result interface live in `FourierMukai/ExceptionalExtension.lean`, while
  `ExceptionalInduction.lean` owns dependent finite extension and derives
  ambient generation from right admissibility.
  `AlgebraicGeometry/Surface/Enriques/PaperBlocks.lean` and
  `PaperExtension.lean`, `PaperMatching.lean`, and `PaperTorelli.lean` are
  geometric consumers: they identify the block members with the ten selected
  line bundles, record the numerical `(-2)`-chains, and specialize projection,
  classification matching, shift rigidity, and ambient kernel extension.
  `Divisors/EffectiveLineBundle.lean` and
  `DerivedCategory/DivisorSequence.lean` now construct the line-bundle-twisted
  divisor triangles; `PaperExtension.lean` transports them to the chosen block
  representatives and derives the projection-chain maps. Curve-quotient
  residual orthogonality remains supplied geometric data.
- Functorial dg cones and kernel-variable transforms:
  `Algebra/Homology/DGCategory/Pretriangulated/ConeCategory.lean` owns the
  category of chosen dg cones and homotopy-coherent cone morphisms;
  `DGEnhancement/H0/ConeFunctor.lean` maps it functorially into distinguished
  `H⁰` triangles.  `FourierMukai/Basic.lean` owns the functor from kernels to
  transforms and its objectwise evaluation, while `FourierMukai/KernelCone.lean`
  maps dg cones of an enhanced kernel category to pointwise transform
  triangles and packages an exact kernel evaluation as a functor valued in
  distinguished triangles.  The kernel category enters through an
  `Enhancement`, never as an `H⁰` on the nose; the cone lift has one owner
  (`homogeneousLift`, with `lift` and `HomotopySquare` its degree-zero case);
  and cone morphisms carry the shift-free `fst` square, so the cone category
  needs no pretriangulated instance.  The enhancement of the geometric kernel
  category with an exact comparison, the paper's actual enhanced kernel
  morphism, and the exactness instance for its evaluation remain realization
  tasks; the generic cone itself is no longer a supplied paper-layer seam.
- Generic moduli boundedness: `CategoryTheory/Moduli/Boundedness.lean`.
- Generic replete subprestack machinery:
  `CategoryTheory/Bicategory/Functor/Cat/ObjectProperty/`, reusing Mathlib's
  `Pseudofunctor.ObjectProperty.fullsubcategory`.
- Ordinary ring/module helpers already extracted to `Algebra/Module/`.
- Generic sheaves and ringed-site module sheaves:
  `Algebra/Category/ModuleCat/Sheaf/`.
- Generic abelian and derived-category infrastructure:
  `CategoryTheory/Abelian/` and
  `Algebra/Homology/DerivedCategory/`.
- Canonical scheme-derived specializations:
  `AlgebraicGeometry/DerivedCategory/Basic.lean` names the derived categories
  of module sheaves (the standard localization is a local instance in each
  consumer, never a global one), while
  `AlgebraicGeometry/DerivedCategory/Coherent.lean` owns `D(Coh X)`,
  `Dᵇ(Coh X)`, `Perf(X)`, and the structure-sheaf perfect object without
  importing scheme-family, pullback, determinant, or moduli consumers.
  `Families/BoundedGeometry.lean` now begins with base-change fiber aliases and
  the coherent pullback contract; the perfect lift is in
  `Families/PerfectPullback.lean` and the pullback identity/composition laws in
  `Families/CoherentPullbackCoherence.lean`.
- Derived opposites and exact linear duality:
  `Algebra/Homology/DerivedCategory/Opposite.lean` owns the generic
  `DerivedCategory.OppositeComparison`;
  `Algebra/Category/ModuleCat/LinearDual/Basic.lean` owns the bare
  contravariant ModuleCat linear-dual functor,
  `LinearDual/Exact.lean` beside it proves its exactness, and
  `Algebra/Homology/DerivedCategory/LinearDual.lean` owns the derived lift.
  Canonical and Serre duality consume those roots together with
  `AlgebraicGeometry/DerivedCategory/Coherent.lean`; the former geometric
  `Duality/Serre/LinearDual.lean` path and its ModuleCat-specific comparison
  carrier are retired.
- Bounded-coherent and compact/perfect comparison consumption:
  `AlgebraicGeometry/DerivedCategory/Dqc/Comparison.lean` converts the
  explicit `HasBoundedCoherentDqcIdentification` and
  `PerfectObjectsAreCompactInDqc` propositions into coherent representatives,
  comparison isomorphisms, and membership equivalences without registering
  global instances. The relative-perfect category is the first geometric
  consumer and states bounded coherent cohomology at the use site.
- Perfect-complex notion reconciliation:
  `schemePerfect` remains the absolute thick envelope in `D(Coh X)`,
  `schemeRelativePerfect` remains the base-dependent pseudo-coherent finite-Tor
  locus in `Dqc(X)`, and `TwoTermPerfectDeterminantData` remains explicit
  presentation data. `Moduli/PerfectComplex/Comparison.lean` proves the valid
  two-term-to-absolute-to-Dqc direction without asserting a reverse or
  absolute/relative equivalence. The canonical `Dqc(X)` zero now lives in
  `DerivedCategory/Dqc.lean` for every scheme; the moduli consumer only proves
  its additional relative properties.
- Ordinary semilinear and top exterior-power algebra:
  `LinearAlgebra/ExteriorPower/`.
- Exterior powers of presheaves of modules over an arbitrary ring presheaf:
  `Algebra/Category/ModuleCat/Presheaf/ExteriorPower.lean`; scheme
  sheafification remains a geometric consumer in
  `Modules/ExteriorPower.lean`, and restriction comparison is
  `Modules/ExteriorPower/Restriction.lean`.
- Higher-categorical adjunctions: Mathlib's
  `CategoryTheory.Bicategory.Adjunction`, extended under
  `CategoryTheory/Bicategory/Adjunction/`; ordinary adjoint functors are the
  `Cat` specialization through `Adjunction.bicategoricalEquiv`.
- Pseudofunctor-presentation transport:
  `CategoryTheory/Bicategory/Functor/Cat/Transport.lean` owns conjugation through
  objectwise equivalences together with transported units, compositors,
  pentagon, and triangle equations. Both affine bounded-projective derived
  realizations consume this root; the former
  `CategoryTheory/EquivalenceTransport.lean` path and the private geometric
  duplicate are retired.
- Pseudofunctorial triangulated families:
  `CategoryTheory/Triangulated/Families/TriangulatedFiberFamily` now owns a
  Cat-valued pseudofunctor on `LocallyDiscrete Bᵒᵖ`, exposes its pullback unit
  and compositor, and derives the `K₀` identity and composition laws through
  those isomorphisms. Ordinary `Bᵒᵖ ⥤ Cat` families enter through
  `TriangulatedFiberFamily.ofFunctor`. Pre-stability base change transports
  its iterated preimage witness through the pseudofunctor compositor.
- Generic preservation through composition and reflective transport:
  `CategoryTheory/Limits/Preserves/`. The former repository
  `CategoryTheory/Adjunction/` root is retired.
- Module-localization kernel maps:
  `Algebra/Module/Localization/Kernels.lean`. This owns `LinearMap.kerMap` and
  the `IsLocalizedModule.{kerMap,kernelMap,kernelNatTrans}` chain; the
  coherent-sheaf kernel theorem imports and directly reuses that root.
- Relative-perfect moduli selectors are explicitly fiberwise:
  `AlgebraicGeometry.RelativePerfectModuliSelector` exposes `familyLocus` and
  `geometricLocus`, each closed under isomorphisms but with no claimed
  restriction maps. The genuine affine relative-perfect subprestack is built
  separately by `AffineFamilyRelativePerfectPseudofunctor.lean` through the
  generic `universallyStable` and `fullsubcategory` APIs.
- Weighted-basis decompositions:
  `LinearAlgebra/GradedBasis.lean` owns `gradedPiece`, its spanning and
  independence results, and multiplicativity promoted from basis vectors.
  `AlgebraicGeometry/Numerical/Core/GradedBasis.lean` retains only
  `NumericalRingData.ofGradedBasis` and its smoke test.
- Division by multivariate monomials:
  `Algebra/MvPolynomial/DivMonomial.lean` owns the `Finsupp.degree` bridge,
  homogeneous-degree result, factor-commutation identities, and
  `MvPolynomial.divMonomial_pow_mul`, exact division by a variable power, and
  cross-variable cancellation. Projective Laurent and section comparisons
  import that root directly.
- Graded-module localization and shifts:
  `Algebra/Module/GradedModule/` extends Mathlib's `GradedModule` namespace with
  `DegreeZeroLocalization`, natural and integer shifts, twist
  trivializations, and transport along equal power denominators. Proj sheaves
  and Čech complexes import these roots as geometric consumers.
- Graded-ring homogeneous-localization domain properties:
  `RingTheory/GradedAlgebra/HomogeneousLocalization/Domain.lean` owns the five
  `HomogeneousLocalization` declarations proving nontriviality, domain, and
  reducedness from nonzerodivisor hypotheses. Their complete signatures use no
  projective spectrum or scheme. `AlgebraicGeometry/ProjectiveSpectrum/Integral.lean` imports
  this owner directly and adds the geometric chart and integrality results;
  the former Proj-owned source path is retired without a compatibility shim.
- Laurent monomial bases:
  `Algebra/Finsupp/LaurentExponent.lean` owns the exponent-vector arithmetic,
  while `Algebra/MvPolynomial/{Grading,LaurentBasis}.lean` owns the standard
  polynomial grading, polynomial twists, and the monomial spanning and
  independence API for degree-zero localizations. The former
  `AlgebraicGeometry/Proj/Modules/LaurentBasis.lean` path is retired.
- Laurent localization projections and blocks:
  `Algebra/MvPolynomial/{LaurentProjection,LaurentBlock,LaurentHomotopy,LaurentFinite}.lean`
  owns representative-independent sign projections, negative-support block
  projections, the one-localization contracting map, and full-block
  finite-generation results. The corresponding former Proj module paths are
  retired; the polynomial Čech algebra and its geometric consumers import the
  algebraic leaves directly.
- Polynomial variable Čech algebra:
  `Algebra/MvPolynomial/Cech/{Basic,Homotopy,Primitive,Finite}.lean` owns the
  denominator diagram, graded-localization terms and faces, canonical `p / 1`
  variable-localization element, block homotopy, cocycle primitive, and
  finite-block assembly. The former
  `AlgebraicGeometry/Proj/Modules/Cech{Homotopy,Primitive,Finite}.lean` paths
  are retired. `Proj/Modules/ProjectiveSpace.lean` now begins at comparison
  with projective basic opens and sections; geometric cohomology files import
  the algebraic leaves directly.
- Polynomial projective-space algebraic prefix:
  `Algebra/MvPolynomial/Grading.lean` owns generation by the variables over the
  degree-zero homogeneous submodule; `DivMonomial.lean` owns the exact-division
  and cross-variable cancellation lemmas; and `Cech/Basic.lean` owns the
  canonical localized fraction. `Proj/Modules/ProjectiveSpace.lean` now keeps
  only the generic-point, basic-open, section, and cohomology comparisons that
  introduce geometric vocabulary.
- Negative-twist arithmetic prefix:
  `Algebra/Module/GradedModule/Shift.lean` owns triviality of an integer-shifted
  piece below degree zero, while `Algebra/MvPolynomial/DivMonomial.lean` owns
  the homogeneous variable-power divisibility vanishing theorem and its
  cross-variable corollary. `AlgebraicGeometry/Cohomology/Cech/NegativeTwist.lean`
  now begins with the Čech overlap and projective-cohomology plumbing.
- Relative numerical algebra:
  `Algebra/RelativeNumerical/Basic.lean` owns indexed direct sums, saturated
  family-relation quotients, and their universal properties, while
  `Overlattice.lean` owns additive-map images, factorizations, and
  finite-relative-index predicates. The former
  `AlgebraicGeometry/Numerical/GrothendieckGroup/Relative{,Overlattice}.lean`
  paths are retired; a future geometric adapter must introduce actual scheme
  data and import the algebra root directly. `FamilyRelationSystem` is
  deliberately recorded by the single-instantiation ratchet as statement-layer
  input: downstream applications supply admissible families, so this slice
  does not fabricate a second library-owned inhabitant merely to satisfy a
  count.
- Triangulated Grothendieck-group realizations and Euler forms:
  `CategoryTheory/Triangulated/GrothendieckGroup/Realization.lean` owns the
  canonical `K₀.Realization` alias and exact-functor descent squares, while
  `EulerForm.lean` owns `K₀.EulerForm`, its canonical linear-category form, and
  preservation by exact functors. Numerical Riemann--Roch, Euler-pairing, and
  Mukai-vector transfer remain in `AlgebraicGeometry/Numerical/` as consumers.
  The former geometry-owned one-field carriers `NumericalRealization` and
  `CategoricalEulerForm`, together with their parallel descent and preservation
  APIs, are retired rather than retained as compatibility wrappers.
- Finite free integral lattices: there is no repository lattice class. The
  interface is Mathlib's pair of instances `Module.Finite ℤ` and
  `Module.Free ℤ`, the latter from `Module.free_of_finite_type_torsion_free'`
  in `Mathlib/LinearAlgebra/FreeModule/PID.lean`.
  `NumericalVarietyData.instFiniteNumericalQuotient` remains in
  `AlgebraicGeometry/Numerical/GrothendieckGroup/Lattice.lean` because it
  introduces the Euler radical and numerical quotient. The former
  `AlgebraicGeometry.Numerical.ZLattice` namespace and the former
  `LinearAlgebra/Lattice/Basic.lean` are retired rather than retained as
  compatibility aliases.
- Numerical polynomials and mixed finite differences:
  `Algebra/NumericalPolynomial/Basic.lean` owns integer-lattice numerical
  functions, mixed differences, degree bounds, Newton coefficients, and top
  multilinear coefficients. `AlgebraicGeometry/IntersectionTheory/Snapper.lean`
  imports that root and begins with Picard powers, coherent twists, Euler
  characteristics, and the geometric induction certificate. The former
  `AlgebraicGeometry/IntersectionTheory/NumericalPolynomial.lean` and
  `AlgebraicGeometry/IntersectionTheory/NumericalPolynomial/` paths, together
  with the `AlgebraicGeometry.IntersectionTheory.NumericalPolynomial`
  namespace, are retired rather than retained as compatibility shims.
- Coverwise local equivalences of additive presheaves:
  `CategoryTheory/Sites/Sheaves/CoversTop.lean` owns detection of local
  injectivity, local surjectivity, and `J.W` membership on a family covering
  the terminal object. Scheme tensor, divisor, associated-sheaf, and Proj
  modules import that arbitrary-site root directly; the declarations no
  longer live inside the scheme tensor consumer.
- Over-site restriction infrastructure:
  `CategoryTheory/Sites/Over.lean` owns cocontinuity of `Over.post`,
  `Algebra/Category/ModuleCat/Sheaf/Over.lean` owns the module-sheaf
  restriction API, and `CategoryTheory/Sites/CoversTop.lean` owns
  transport of a terminal-covering family through a cover-preserving
  equivalence. `AlgebraicGeometry/Modules/Restriction/OpenImmersion.lean`
  imports these roots and now begins at the scheme/open-site equivalence; the
  three declaration names are preserved without a compatibility shim.
- Ringed-site presentation restriction:
  `Algebra/Category/ModuleCat/Sheaf/Presentation/Over.lean` owns
  restriction of `Presentation`, `GeneratingSections`, and
  `QuasicoherentData` to over sites, including preservation of a finite
  generating index. `AlgebraicGeometry/Modules/Affine/{BasicOpen,Finiteness}.lean`
  import that root directly and now begin with `Spec R`, distinguished opens,
  and affine finiteness. The seven declaration names are preserved without a
  compatibility shim.
- Ringed-site finite-presentation invariance and locality:
  `CategoryTheory/Sites/Sheaves/Modules/Presentation/{Isomorphism,Locality}.lean`
  own transport across isomorphisms, closure of the finite-presentation object
  property, restriction to over sites, and descent from a `CoversTop` family.
  `AlgebraicGeometry/Modules/Coherent/Basic/Isomorphism.lean` now contains only
  the `coherent X` instance, while `Descent/Locality.lean` contains only
  scheme open-immersion and affine-cover consumers. The seven declaration
  names are preserved without compatibility shims, and unnecessary hypotheses
  are removed from five declarations in the presentation transport/locality chain.
- Ringed-site finite-presentation closure:
  `CategoryTheory/Sites/Sheaves/Modules/Presentation/{Zero,Extensions}.lean`
  own the empty finite presentation of the zero module sheaf and the finite
  horseshoe construction proving closure under short-exact extensions.
  `AlgebraicGeometry/Modules/Coherent/Abelian/Extensions.lean` now contains only
  the resulting `coherent X` extension instance, while `Abelian/Basic.lean`
  retains the geometric zero, finite-product, abelian, and exact-inclusion
  instances. Public declaration names are preserved without compatibility
  shims.
- Generic invertible module sheaves and tensor/sheafification descent:
  `Algebra/Category/ModuleCat/Sheaf/Invertible.lean` owns rank-one local
  generator data, intrinsic `SheafOfModules.IsInvertible`, transport, finite
  presentation, and local trivializations. The adjacent `Tensor.lean` owns
  preservation of local equivalences by tensoring with a rank-one factor on an
  arbitrary site. `Topology/Sheaves/ModuleTensor.lean` owns the stalkwise
  arbitrary-factor strengthening. Scheme tensor objects, tensor closure,
  associativity, and Picard classes remain direct geometric consumers.
- Stalk tensor products of module presheaves:
  `Topology/Sheaves/ModuleTensor/StalkTensor.lean` owns the comparison between
  the stalk of a tensor product and the tensor product of stalks, together with
  its open-neighbourhood, germ, and stalk-map infrastructure. The parent
  `Topology/Sheaves/ModuleTensor.lean` imports that root to prove the
  arbitrary-factor stalkwise local-equivalence theorem. The former
  `Algebra/Category/ModuleCat/StalkTensor.lean` path and its export from the
  algebra umbrella are retired without a compatibility shim.
- Basiswise detection of topological sheaf isomorphisms:
  `Topology/Sheaves/Basis.lean` owns surjectivity of stalk maps detected on a
  basis and the resulting criterion that a sheaf morphism is an isomorphism.
  `AlgebraicGeometry/Modules/Affine/Comparison.lean` imports that root and now
  begins with scheme modules, distinguished opens, and localization. Both
  declaration names are preserved without a compatibility shim.
- Finite products of prime-spectrum basic opens:
  `RingTheory/Spectrum/Prime/BasicOpen.lean` owns
  `PrimeSpectrum.basicOpen_prod_eq_pi`, while
  `AlgebraicGeometry/Cohomology/Cech/Affine.lean` imports it and retains only
  the private localization machinery and public affine Čech exactness
  theorems. The declaration name and full signature are preserved without a
  compatibility shim. The earlier queue classified this under `Algebra/` from
  its ring input alone; the complete signature instead contains
  `Opens (PrimeSpectrum R)` and a categorical finite product supplied by
  `Topology/Category/TopCat/Opens/Limits`, so `RingTheory/Spectrum/Prime/` is the first valid
  owner without a forbidden `Algebra -> Topology` edge.
- Generating sections from free epimorphisms:
  `Algebra/Category/ModuleCat/Sheaf/GeneratingSections.lean` owns
  `SheafOfModules.GeneratingSections.ofFreeEpi`, its finite-index instance,
  and the lemma recovering the original epimorphism. The full signatures use
  only a ring sheaf on an arbitrary site. The affine coherent-chart module
  imports this owner directly and now retains only its scheme/open/coherence
  theorem; the declaration names and signatures are preserved without a
  compatibility shim.
- Alternating finranks along long exact sequences: restated on Mathlib's API
  (2026-09-02). `Algebra/Homology/EulerCharacteristic.lean` owns
  `GradedObject.eulerChar_eq_add_of_exact`, the `ℤ`-indexed balance stated on
  Mathlib's `GradedObject.eulerChar` with the signs of `ComplexShape.up ℤ`;
  `Algebra/Exact/Sequence.lean` owns the bounded zig-zag companion
  `Module.sum_neg_one_pow_finrank_eq_zero_of_longExact` beside Mathlib's
  `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`; and
  `LinearAlgebra/FiniteDimensional/Lemmas.lean` owns their shared rank--nullity
  lemma `Function.Exact.finrank_eq_finrank_range_add_finrank_range`. The former
  `LinearAlgebra/AlternatingFinsum.lean` with its parallel `altDim` vocabulary,
  and `LinearAlgebra/AlternatingSum.lean`, whose single-sequence theorem is
  Mathlib's, are retired.
- Geometric realizations live with the geometric object (2026-09-01): the
  seven former `CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves
  moved to
  `AlgebraicGeometry/DerivedCategory/Stability/{BoundedCoherentBaseChange,DerivedPullback,FourierMukaiAction}.lean`,
  `AlgebraicGeometry/Moduli/Semistability/{SchemeProbes,LocusProbes,FiniteType}.lean`,
  and `AlgebraicGeometry/Moduli/HarderNarasimhan/DedekindProblem.lean`, and the
  `IsCompatibleWithTriangulation` instance for `Dᵇ(Coh X)` merged into
  `DerivedCategory/FourierMukai/DerivedTensorCoherence.lean` beside the class
  it registers. The eight instance umbrellas, the `GeometryInstances` layer,
  the subject rank order, and the reverse-edge allowlist are retired;
  `scripts/check_layering.py` now enforces the six policy edges in
  `layers.md`. Declaration names and namespaces are unchanged.
- Homological algebra at Mathlib's paths (2026-09-01):
  `CategoryTheory/Triangulated/DerivedCategory/` and
  `Triangulated/CohomologyObjectProperty.lean` moved to
  `Algebra/Homology/DerivedCategory/`; `Triangulated/BoundedHomotopyCategory.lean`
  to `Algebra/Homology/HomotopyCategory/Bounded.lean`;
  `Triangulated/DGEnhancement/Instances/HomotopyCategory/` to
  `Algebra/Homology/HomotopyCategory/DGEnhancement/`;
  `CategoryTheory/SpectralSequence/` to `Algebra/Homology/SpectralSequence/`;
  and `CategoryTheory/Enriched/DGCategory/` to `Algebra/Homology/DGCategory/`
  (ADR-0010 amendment). The `CategoryTheory/Enriched` umbrella and the
  `DGEnhancement/Instances` umbrella are retired. Declaration names and
  namespaces are unchanged; the declaration sweep routes the moved subtrees
  to the audit lanes that already hold their records.
- Sheaves of modules at Mathlib's path (2026-09-01):
  `CategoryTheory/Sites/Sheaves/Modules/` moved to
  `Algebra/Category/ModuleCat/Sheaf/`, where Mathlib defines `SheafOfModules`.
  `Algebra/Category`, `Algebra/Category/Grp`, and `Algebra/Category/ModuleCat`
  gained the umbrellas the tree never had. Declaration names and namespaces
  are unchanged; the sweep routes the subtree to the audit lane that holds its
  records.
- Site, bicategory, abelian, simplicial, ring-theoretic, and topological
  extensions at Mathlib's paths (2026-09-01): site-level Čech theory moved to
  `CategoryTheory/Sites/SheafCohomology/Cech/` and its topological half
  (compact-open bases, boundedness, the free abelian Yoneda stalk, global
  sections, injective and flasque acyclicity) to `Topology/Sheaves/Cech/`;
  stacks in groupoids to `CategoryTheory/Sites/Descent/StackInGroupoids/`;
  pseudofunctor loci and transport to `CategoryTheory/Bicategory/Functor/Cat/`;
  weak Serre classes to `CategoryTheory/Abelian/SerreClass/Weak.lean`; the
  extra-codegeneracy contraction to `AlgebraicTopology/`; basic-open products
  to `RingTheory/Spectrum/Prime/BasicOpen.lean`; and the opens category to
  `Topology/Category/TopCat/Opens/`. Umbrellas exist at every new level, the
  public root exports the two new subjects, and the sweep routes each moved
  subtree to the audit lane that holds its records. Declaration names and
  namespaces are unchanged.
- Geometry organized by Mathlib's object names (2026-09-01):
  `AlgebraicGeometry/Proj/` moved to `AlgebraicGeometry/ProjectiveSpectrum/`,
  Mathlib's name for the directory whose `Proj` it extends, and
  `AlgebraicGeometry/CoherentSheaf/` to `AlgebraicGeometry/Modules/Coherent/`
  with its `Quasicoherent/` child beside it as `Modules/Quasicoherent/`, since
  both are subcategories of the `X.Modules` that Mathlib defines in
  `AlgebraicGeometry/Modules/Sheaf.lean`. Declaration names and namespaces
  (`AlgebraicGeometry.Proj`, `Scheme.Modules`, `SheafOfModules`) are
  unchanged.
- Stability nested by name (2026-09-01): `CategoryTheory/Triangulated/WeakStabilityCondition/`
  became `CategoryTheory/Triangulated/StabilityCondition/` with weak stability
  as the child `Weak/`, following Mathlib's `MetricSpace/Pseudo/`: the
  directory is named for the canonical concept and the variant by its
  adjective, while the dependency still runs from Bridgeland to weak. The
  strong umbrella imports its weak child, so the former explicit umbrella
  boundary is gone; the layering gate still rejects any import from `Weak/`
  into the Bridgeland theory and still requires `PreStabilityCondition` to
  extend `WeakPreStabilityCondition`. Declaration namespaces are unchanged.
- The `ZLattice` class is retired (2026-09-02): `LinearAlgebra/Lattice/Basic.lean`
  bundled `Module.Finite ℤ` and `Module.Free ℤ` into a class whose name is
  Mathlib's `ZLattice` namespace. The interface is Mathlib's pair of instances;
  `NumericalVarietyData.numericalZLattice` became the instance
  `instFiniteNumericalQuotient`, and freeness of the torsion-free quotient is
  Mathlib's `Module.free_of_finite_type_torsion_free'`.
- The bundled variety types are retired (2026-09-02): `SchemeOverField`,
  `Variety k`, `SmoothProperVariety k`, `ProjectiveVariety k`, `K3Surface`,
  and `EnriquesSurface` were second carriers for objects Mathlib already has.
  A variety is now `X : Scheme` with `[X.Over (Spec (CommRingCat.of k))]`,
  whose structure morphism is `X ↘ Spec (CommRingCat.of k)`, and the
  `Prop` classes `IsVariety k X` (integral, locally of finite type over `k`),
  `IsSmoothProperVariety k X`, `Variety.IsProjective k X`,
  `SmoothProperVariety.IsK3Surface k X C`, and
  `SmoothProperVariety.IsEnriquesSurface k X C` state the properties, as
  `IsProper` does for a morphism. The base field is an `outParam` so that
  `Variety.isLocallyNoetherian`, whose conclusion mentions no `k`, is found
  by instance search. Data that was reached through the bundle takes the
  field explicitly: `FiniteCohomology k X`, `FiniteDimensionalCohomology k X`,
  `LinearCohomology k X`, `SmoothProperVariety.CanonicalSheafData k X n`,
  `NumericalData k X n A N`, `SurfaceChernCharacter k X`,
  `ProjectivePresentation k X`, `EulerRealization k X V`, and the relative
  differentials `Variety.relativeDifferentials k X` with their derivation and
  descent API. Projective space carries `instOverProjectiveSpace`,
  `isVariety_projectiveSpace`, and `isProjective_projectiveSpace` in place of
  `projectiveSpaceVariety`; the point `Spec k` carries
  `isSmoothProperVariety_point`. The `Variety` and `SmoothProperVariety`
  namespaces remain as the homes of the API; they are no longer types.
  Unbundling exposed hypotheses the bundle had hidden: the base-field scalar
  action on coherent cohomology, the relative differentials with their
  descent API, and the twisting sheaf on projective space need only the
  structure morphism; additivity of derived coherent cohomology holds on any
  scheme; the projective-space scalar files no longer assume a finite
  nonempty index, which only the finiteness theorems use as `[Fintype ι]`;
  and the two Euler-additivity exactness lemmas assume
  `IsLocallyNoetherian X`, which is what they use.
- Adjacent placement defects found by the 2026-09-02 review of the restructure
  (landed 2026-09-02). Generic t-structure retract closure moved from
  `Algebra/Homology/DerivedCategory/TStructure.lean` to
  `CategoryTheory/Triangulated/TStructure/Retracts.lean`; `QuasiAbelian.lean`
  moved from `Triangulated/` to `CategoryTheory/Abelian/`;
  `Triangulated/LinearOpposite.lean` split into `CategoryTheory/Linear/Opposite.lean`
  and `Triangulated/Opposite/Linear.lean`; `DerivedCategory/LinearDual.lean` split,
  with the ordinary `ModuleCat` duality at `Algebra/Category/ModuleCat/LinearDual.lean`;
  `Ext/InjectiveResolutionNaturality.lean` split, with
  `CategoryTheory/Localization/SmallShiftedHom.lean` and
  `Algebra/Homology/HomotopyCategory/HomComplexPostcomp.lean`;
  `Triangulated/CompactlyGenerated.lean` split, with the generic compact-object
  vocabulary at `CategoryTheory/Preadditive/CompactObject.lean`; and
  `CategoryTheory/StabilityCharge.lean` moved to
  `Triangulated/StabilityCondition/Weak/Charge.lean`. Declaration names and
  namespaces are unchanged; the old paths are retired in the layering gate; the
  audit sweep routes all of `Algebra/Category/ModuleCat/` to the StabilityCondition
  lane. The four upper-half-plane facts in `Weak/Charge.lean` remain an upstream
  candidate for `Analysis/Complex/UpperHalfPlane/` under the `Complex` namespace,
  deferred by the name-stability rule.
- The global `HasDerivedCategory.standard` registrations are retired
  (2026-09-02). `AlgebraicGeometry/DerivedCategory/Basic.lean` (module sheaves,
  in both spellings, with a priority hack), `Coherent.lean` (`Coh X`), and
  `Algebra/Homology/DerivedCategory/LinearDual.lean` (`ModuleCat k` and its
  opposite) registered Mathlib's standard localization as global instances,
  against Mathlib's own guidance that a chosen localization be introduced
  locally. Every consumer that spells a derived category now declares
  `attribute [local instance] HasDerivedCategory.standard` after
  its preamble, the idiom fifteen files already used; the instance term in every
  signature is literally `HasDerivedCategory.standard _`, so definitions agree
  across files and across the reducibly equal spellings `X.Modules` and
  `SheafOfModules X.ringCatSheaf` without the priority hack. A consumer that
  wants a different localization takes `[HasDerivedCategory C]` as a hypothesis,
  as `SemiorthogonalDecomposition/DerivedField.lean` already does.
- The alternating-finsum vocabulary is retired (2026-09-02) in favour of
  Mathlib's `Algebra/Homology/EulerCharacteristic.lean`: see the owner entry
  above. The Euler form `chiHom` is now `GradedObject.eulerChar` of the shifted
  Hom family by `rfl`, and its additivity on distinguished triangles applies
  `GradedObject.eulerChar_eq_add_of_exact` directly.

## Confirmed next lanes

Every path lane confirmed by the 2026-09-01 audit has landed, and so have
both lanes recorded after it: the `ObjectProperty` lift block (2026-09-02)
and the left-orthogonal colimit closure (2026-09-03). Both are entries under
"Completed roots" above.

The divisorial charge block recorded here as a candidate on 2026-09-08 landed
on 2026-09-09 and is now an entry under "Completed roots" above; the entry
also records where that candidate's stated payoff was wrong.

When a lane is added here, take it one per pull request. Remove the old path rather than retaining
an import-only shim, update audits and umbrellas in the same pull request, and
add a focused layering guard preventing the declaration from returning to its
consumer.
