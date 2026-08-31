# Contributing to DerivedAlgGeo

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`. Follow the existing subject
hierarchy; do not add new top-level libraries or restore retired repository
roots.

Choose the narrowest natural home:

- geometric objects and theorems: `DerivedAlgGeo/AlgebraicGeometry/`;
- ordinary ring and module theory independent of sites and schemes:
  `DerivedAlgGeo/Algebra/`;
- generic abelian-category results extending Mathlib's abelian hierarchy:
  `DerivedAlgGeo/CategoryTheory/Abelian/`;
- bicategorical adjunctions, adjoint equivalences, mates, and their `Cat`
  specialization: `DerivedAlgGeo/CategoryTheory/Bicategory/`;
- generic preservation and reflective transport for limits and colimits:
  `DerivedAlgGeo/CategoryTheory/Limits/`;
- generic sheaves, including module sheaves on an arbitrary ringed site:
  `DerivedAlgGeo/CategoryTheory/Sites/Sheaves/`;
- neutral moduli predicates: `DerivedAlgGeo/CategoryTheory/Moduli/`;
- Cat-valued pseudofunctor loci and subprestacks:
  `DerivedAlgGeo/CategoryTheory/Pseudofunctor/ObjectProperty/`;
- generic monoidal coherence and tensor--triangulation compatibility:
  `DerivedAlgGeo/CategoryTheory/Monoidal/`;
- raw dg enrichment: `DerivedAlgGeo/CategoryTheory/Enriched/DGCategory/`;
- derived, triangulated, dg-enhancement, and stability-category theory:
  `DerivedAlgGeo/CategoryTheory/`;
- geometric realizations of categorical interfaces: an explicit
  `Instances/AlgebraicGeometry/` leaf below the generic construction;
- reusable lattice or matrix theory: `DerivedAlgGeo/LinearAlgebra/`;
- exploratory API probes: `DerivedAlgGeo/Development/`.

Apply the declaration-signature table in
`docs/architecture/placement.md` before relying on this summary. The weakest
vocabulary sufficient for the full public type determines the owner. A
geometric motivation, a geometric first consumer, or a proof written with
geometric lemmas does not make an otherwise ordinary algebra, linear algebra,
or category-theory statement geometric.

In particular, use `Algebra/` for ordinary module localization and ring
operations, and `LinearAlgebra/` for generic linear maps, bases, lattices,
matrices, multilinear constructions, and exterior powers. When a geometric
file contains a generic helper followed by its scheme application, split the
helper into its general root and import that root from the consumer.
The canonical repository extension for localization commuting with kernels is
`Algebra/Module/Localization/Kernels.lean`; scheme and coherent-sheaf files
consume it directly rather than restating its linear-map or `ModuleCat` forms.
The same rule puts weighted-basis decompositions in
`LinearAlgebra/GradedBasis.lean` and pure multivariate-polynomial monomial
division identities in `Algebra/MvPolynomial/DivMonomial.lean`. Numerical-ring
constructors and projective graded localizations are consumers of those roots,
not alternative owners.

Use Mathlib's established namespace when extending a Mathlib concept. Add a
same-named umbrella for a new non-leaf directory and export stable leaves
through their nearest existing umbrellas.

Mathlib's `CategoryTheory.Bicategory.Adjunction` is the canonical general
adjunction. Ordinary adjoint functors are its specialization in `Cat`; use
`CategoryTheory.Adjunction.bicategoricalEquiv` when that comparison must be
explicit. Place a theorem that assumes an adjunction by the rest of its
signature: limit-preservation results under `CategoryTheory/Limits/`, derived
`Ext` comparisons under the derived `Ext` root, and Fourier--Mukai adjunction
data with its kernel consumer. Add broader `n`- or `(∞,1)`-category roots only
with a concrete formal model and reusable API.

Generic umbrellas must not import `Instances/AlgebraicGeometry` descendants.
Those bridge modules are opt-in leaves: they may import both category theory
and geometry, but neither generic category theory nor algebraic geometry may
depend on them. Construct generic objects once—for example, obtain
`DerivedCategory (Coh X)` from the abelian instance on `Coh X` rather than
creating a second geometric derived-category theory.

Generic boundedness predicates for moduli problems live under
`CategoryTheory/Moduli/`. Cat-valued prestack loci reuse Mathlib's
`Pseudofunctor.ObjectProperty`: require closure under isomorphisms for a
replete locus and closure under mapped objects before calling it a
subprestack, then use `fullsubcategory`. Scheme parameter spaces, finite-type
witnesses, atlases, and geometric presentations remain below
`AlgebraicGeometry/Moduli/` and consume those roots.

Use `RelativePerfectModuliSelector` for geometric boundedness data that only
selects replete loci independently in each fiber. Its `familyLocus` and
`geometricLocus` fields do not imply restriction stability. Do not describe a
selector as a subfunctor; construct a genuine subprestack only from a
`Pseudofunctor.ObjectProperty` carrying `IsClosedUnderMapObj`.

Do not classify all module or sheaf theory as algebraic geometry. Ordinary
modules over rings belong under `Algebra/`. Sheaves on an arbitrary site, and
sheaves of modules over a sheaf of rings on an arbitrary site, belong under
`CategoryTheory/Sites/Sheaves/`. Scheme-dependent specializations follow the
geometric refinement chain `SheafOfModules(X) -> QCoh(X) -> Coh(X)` under
`AlgebraicGeometry/SheafOfModules/`; the quasicoherent and coherent children
must reuse their parent carriers and forgetful structure rather than creating
parallel categories.

Mathlib owns the `CategoryTheory.Abelian` typeclass. Add missing generic
abelian results below `CategoryTheory/Abelian/`, prove the scheme-specific
instance `[Abelian (Coh X)]` with the coherent-sheaf geometry, and let that
instance feed the one generic derived-category construction.

Generic derived-category extensions belong under
`CategoryTheory/Triangulated/DerivedCategory/`. This includes facts about the
canonical t-structure, exact functors, homology comparison, and K-projective
or bounded-above-projective models. Keep only the `Coh(X)`, `Dqc(X)`, module,
and extension-of-scalars specializations below algebraic geometry.

Put generic `Ext` adjunction, dimension-shift, and injective-resolution
naturality below `CategoryTheory/Triangulated/DerivedCategory/Ext/`. Put
filtered-complex and total-complex spectral-sequence machinery below
`CategoryTheory/SpectralSequence/`, and generic site-theoretic Čech complexes,
injective comparisons, compact-basis arguments, and finite-cover boundedness
below `CategoryTheory/Sites/Cech/`. Affine acyclicity, distinguished-open
bases, and projective-space computations remain under
`AlgebraicGeometry/Cohomology/`.

Scheme-specific specializations of that generic construction live under
`AlgebraicGeometry/DerivedCategory/`: this is the owner for module-sheaf
derived categories, `Dqc`, scheme-indexed derived pullback, and geometric
Fourier--Mukai kernels. A registration-only adapter may instead use the generic
construction's `Instances/AlgebraicGeometry/` leaf. The former
`AlgebraicGeometry/StabilityCondition/` subtree is retired: an API that
implements weak or Bridgeland stability belongs in the corresponding
categorical construction's `Instances/AlgebraicGeometry/` leaf, while the
underlying geometric object or theorem remains with its geometric owner.

Declaration namespaces follow those owners. Use
`AlgebraicGeometry.DerivedCategory` for the scheme-derived category API in
`DerivedCategory/Basic.lean`, and
`AlgebraicGeometry.DerivedCategory.Families` for scheme base-change and
pullback declarations below `DerivedCategory/Families/`. Use
`AlgebraicGeometry.DerivedCategory.Dqc` for the quasicoherent-cohomology loci
and affine realizations in `DerivedCategory/Dqc.lean` and `DerivedCategory/Dqc/`.
Use `AlgebraicGeometry.DerivedCategory.FourierMukai` for neutral geometric
kernel declarations below `DerivedCategory/FourierMukai/`. A compatibility
umbrella may preserve imports, but neutral geometric declarations must not
remain qualified through a categorical stability-condition namespace.

Enriched categories depend on a monoidal base; dg categories are the cochain-
complex specialization of that pattern. This does not make every dg category
monoidal, and monoidal and triangulated structures do not imply one another.
Place their intersections explicitly:

- exact tensor compatibility in `CategoryTheory/Monoidal/Triangulated/`;
- optional monoidal dg refinements in
  `CategoryTheory/Enriched/DGCategory/Monoidal/`;
- passage of that structure to triangulated `H⁰` in
  `CategoryTheory/Triangulated/DGEnhancement/Monoidal/`.

Keep tensor products on sheaves, invertible sheaves, and scheme-derived
categories in algebraic geometry. They should implement the generic monoidal
interface instead of relocating their geometric object types.

Weak stability is the parent categorical theory. Put it, the generic
stability-function API, and shared slicing prerequisites under
`CategoryTheory/Triangulated/WeakStabilityCondition/`. Put ordinary Bridgeland
stability under its stronger
`WeakStabilityCondition/StabilityCondition/` child. The weak parent may not
import the child; the strong structure must expose its weak parent directly.
Do not recreate a `WeakCompatibility/` adapter leaf or the old
sibling `CategoryTheory/Triangulated/StabilityCondition/` path. Keep
scheme-specific Mumford slope input geometry-owned, and place a valid
promotion to Bridgeland stability below the strong theory through an explicit
geometric realization.

Place the geometric substance of semistability and relative HN theory under
`AlgebraicGeometry/Moduli/Semistability/` and
`AlgebraicGeometry/Moduli/HarderNarasimhan/`. Place their weak- or
Bridgeland-family adapters under that categorical family's
`Instances/AlgebraicGeometry/` leaf. Likewise, neutral kernels and convolution
stay under `AlgebraicGeometry/DerivedCategory/FourierMukai/`; the generic
kernel-autoequivalence interface stays under
`CategoryTheory/Triangulated/FourierMukai/`; and an action on Bridgeland
stability is implemented under
`WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/`, with
its geometric realization in that source's `Instances/AlgebraicGeometry/`
leaf. Algebraic-geometry modules must never import those instance leaves.

Geometric declarations keep the namespace of their geometric owner even when
their implementation bridge is physically attached to a categorical source.
Registration declarations may extend the categorical source namespace. Never
use the retired `AlgebraicGeometry.StabilityCondition` namespace or the
retired flattened categorical stability-family namespace.

Generic stack-in-groupoids construction, discrete stacks from sheaves, stack
morphisms, and site-object representability belong under
`CategoryTheory/Sites/StackInGroupoids/`. Big-Zariski representables and
geometric properties of their representing scheme morphisms belong under
`AlgebraicGeometry/Stacks/`.

Neutral categorical family declarations use the matching
`CategoryTheory.Triangulated.Families` namespace. In particular,
`TriangulatedFiberFamily` must not be declared inside a weak- or
Bridgeland-stability namespace merely because those theories consume it.
Shared moduli boundedness uses the independent `CategoryTheory.Moduli`
namespace. Treat a namespace migration as an API cutover: update all stable
consumers, audits, declaration baselines, documentation, and regression gates
together.

Weak-family declarations likewise use
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`. Put the shared
Definition 20.5 probes and structures bound to `WeakStabilityFunction` in that
namespace, and let ordinary Bridgeland family packages import them from the
stronger child.

Generic numerical support predicates and the weak-stability packages built
from them use `CategoryTheory.Triangulated.WeakStabilityCondition.Support`.
The former `CategoryTheory.Triangulated.StabilityCondition.Support` namespace
is retired; consumers must not use it as a compatibility alias.

Place the finite-length simple-charge lattice model with the weak
stability-function foundation in
`WeakStabilityCondition/Foundation/StabilityFunction/`, using namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength`. The former
plural `WeakStabilityCondition/Foundations/` path is retired.

Declarations owned by that stronger child use
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
This namespace owns ordinary family packages and categorical pre-stability
base change, not their scheme-specific realizations.

Wall theory in the same strong child uses
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`.
Do not put new wall declarations back under the former sibling
`CategoryTheory.Triangulated.StabilityCondition.Wall` namespace.

Generic kernel autoequivalences and the Bridgeland-action extensions implemented
in the strong child's `Symmetry/` subtree use their canonical
`CategoryTheory.Triangulated.FourierMukai` namespace. Do not qualify them
through either stability `Symmetry` namespace; the former sibling
`CategoryTheory.Triangulated.StabilityCondition.Symmetry` namespace remains
retired.

Group actions on slicings, pre-stability conditions, and Bridgeland stability
conditions use
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
The former sibling `CategoryTheory.Triangulated.StabilityCondition.GroupAction`
namespace is retired, including its public compatibility aliases. Historical
names embedded in immutable review payloads live only in the executable support
module `exe/RestateHistoricalNames.lean`; do not import that module from
library code, add aliases to it, or use those names in new reviews.

Import-only migration shims at `Divisors/{Tensor,Picard,Monoidal}.lean`,
`Stacks/Basic.lean`, and `Compatibility/StabilityConditionFamilies.lean` have
been retired. Import `AlgebraicGeometry.Modules.Tensor`,
`CategoryTheory.Sites`, or the appropriate stability/derived-category owner
directly. Do not restore a combined compatibility surface or the
`DerivedAlgGeo.Compatibility` umbrella.

Deformation-specific Bridgeland helpers use
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation`.
The flattened `CategoryTheory.Triangulated.Deformation` namespace is retired.
Keep extensions of canonical structures such as `Slicing`,
`PreStabilityCondition.WithClassMap`, and `StabilityCondition.WithClassMap` in
their established namespaces even when the implementing module is physically
grouped below `Foundation/Deformation/`.

Keep generic `Algebra`, `Topology`, and `LinearAlgebra` modules independent of
specialized geometry and stability applications. A new top-level subject is
appropriate only for a coherent body of reusable mathematics, not for one
milestone or provenance boundary.

Generic stacks in groupoids and descent-equivalence data belong under
`CategoryTheory/Sites/` and use the `CategoryTheory` namespace. Keep
scheme-specific representability, atlases, and algebraicity under
`AlgebraicGeometry/Stacks/`; a compatibility import must not retain a second
canonical qualified name.

## Choose the common root before the leaf

Read [the canonical-root policy](docs/architecture/abstraction-tree.md) before
adding a public structure, class, quotient carrier, category, or parallel
presentation of an existing object.  The pull request must name the canonical
root and explain how the specialization projects or compares to it.

Do not create a paper-specific or geometry-specific sibling of an existing
generic object.  In particular, use Mathlib's `Preadditive`/`Linear` hierarchy,
the repository's `GrothendieckPresentation` specializations, and the generic
site/descent stack roots.  When two presentations are independently useful,
prove their comparison and agreement instead of selecting one silently.  When
an apparent unification is mathematically false, record the obstruction and
keep the leaves separate.

## Proof and trust policy

Committed library code must not use `sorry`, `admit`, or hidden axioms. Explicit
mathematical hypotheses and structure fields are acceptable; proof holes are
not. Keep conditional geometry honest by recording the exact hypothesis that a
later realization must supply.

Public declarations belong in the appropriate hand-maintained axiom audit:

- `scripts/AlgebraicGeometryAudit.lean`
- `scripts/StabilityConditionAudit.lean`
- `scripts/DGCategoryAudit.lean`

The completeness ratchet rejects growth in unaudited public declarations. When
the ratchet improves, lower its ceiling; never raise one to make a change pass.

## Where verification runs

**Full verification runs on the self-hosted Windows runners, not on your
machine.** `.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]` and triggers on `agent/**`, so pushing an agent
branch already runs the whole gate there. For a verdict without pushing:

```bash
gh workflow run ci.yml --ref <branch>
```

This is enforced rather than advised. A `PreToolUse` hook in the tracked
`.claude/settings.json` runs `scripts/check_local_build.py`, which refuses
`scripts/gates.sh` in any mode and refuses `lake build` with no target.
`DAG_ALLOW_LOCAL_BUILD=1` overrides it for one command; say so in the pull
request when you use it.

This section previously read "Build the stable root while developing:
`lake build`", and told you to run the fast gate before review and the full gate
before merge. All three instructions are withdrawn. `CLAUDE.md` was corrected
first, in `c91374a`, and this file was left behind — so for a while the two
disagreed about the most basic question a contributor asks. `CLAUDE.md`
§"Required verification" is the fuller statement; this is the short form.

## Local workflow

Build only what you changed, and probe freely:

```bash
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
lake env lean scratch.lean
```

`lake env lean` on a scratch file is deliberately unrestricted: it is the
seconds-long probe interactive proof work depends on, and a push per attempt
would make writing a lemma impractical.

`scripts/gates.sh` remains the definition of what CI runs — read it to know what
will be checked — but let the runners run it.

The full gate includes:

- Mathlib-style and environment linting for `DerivedAlgGeo`;
- all three axiom audits and the audit-completeness ratchet;
- source-independence, pin, paper-coverage, and no-lint checks;
- roadmap/tracker agreement, when `gh` is available;
- repository-wide emission and `sorryAx` coverage checks.

**A green `scripts/gates.sh` is not a green CI.** The containment runs one way:
every gate in the script also runs in CI, but CI runs more than the script does.
CI's `Contract gates` step additionally runs the `mfc` contract tooling —
`validate`, `env`, `bundle`, `lint`, and `check-ilean-coverage` against the
pinned registry — from a virtualenv it builds per run, and the script does not
reproduce any of it. Expect to learn about those failures from CI.

This file previously called the script "the complete CI-equivalent gate". It was
not, and the difference is not academic: a roadmap entry left at `planned` after
its issue closed reddened CI on `main` and on every open pull request while
`scripts/gates.sh` stayed green on all of them. The `roadmap` gate above closes
that particular hole; the `mfc` steps remain CI-only.

For a focused audit run:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake env lean scripts/StabilityConditionAudit.lean \
  > /tmp/stability-condition-audit.txt 2>&1
python3 scripts/check_audit.py /tmp/stability-condition-audit.txt
```

## Documentation

Module docstrings should explain the mathematical statement, assumptions,
conventions, and relationship to surrounding APIs. Avoid provenance language
such as “the old CohLean version”; Git already records that history.

Build generated API documentation through the nested package:

```bash
cd docbuild
lake build DerivedAlgGeo:docs
```

## Changes that move declarations

Structural changes must update imports, umbrellas, audit names, registry
bindings, source-independence checks, documentation, and CI paths in the same
change. A move is complete only when CI passes on the pushed branch from a clean
checkout — not when a local `scripts/gates.sh` goes green, which is neither
permitted here nor sufficient.

Mark completed and newly confirmed ownership defects in
`docs/architecture/cutover-ledger.md`. Do not use the ledger as an exception:
new declarations must go directly to their canonical owner.
