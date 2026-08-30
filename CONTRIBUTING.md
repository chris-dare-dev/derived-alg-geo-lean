# Contributing to DerivedAlgGeo

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`. Follow the existing subject
hierarchy; do not add new top-level libraries or restore retired repository
roots.

Choose the narrowest natural home:

- geometric objects and theorems: `DerivedAlgGeo/AlgebraicGeometry/`;
- generic monoidal coherence and tensor--triangulation compatibility:
  `DerivedAlgGeo/CategoryTheory/Monoidal/`;
- raw dg enrichment: `DerivedAlgGeo/CategoryTheory/Enriched/DGCategory/`;
- derived, triangulated, dg-enhancement, and stability-category theory:
  `DerivedAlgGeo/CategoryTheory/`;
- geometric realizations of categorical interfaces: an explicit
  `Instances/AlgebraicGeometry/` leaf below the generic construction;
- reusable lattice or matrix theory: `DerivedAlgGeo/LinearAlgebra/`;
- exploratory API probes: `DerivedAlgGeo/Development/`.

Use Mathlib's established namespace when extending a Mathlib concept. Add a
same-named umbrella for a new non-leaf directory and export stable leaves
through their nearest existing umbrellas.

Generic umbrellas must not import `Instances/AlgebraicGeometry` descendants.
Those bridge modules are opt-in leaves: they may import both category theory
and geometry, but neither generic category theory nor algebraic geometry may
depend on them. Construct generic objects once—for example, obtain
`DerivedCategory (Coh X)` from the abelian instance on `Coh X` rather than
creating a second geometric derived-category theory.

Scheme-specific specializations of that generic construction live under
`AlgebraicGeometry/DerivedCategory/`: this is the owner for module-sheaf
derived categories, `Dqc`, scheme-indexed derived pullback, and geometric
Fourier--Mukai kernels. A registration-only adapter may instead use the generic
construction's `Instances/AlgebraicGeometry/` leaf. Do not put neutral derived
geometry under `AlgebraicGeometry/StabilityCondition/`; that subtree is only
for APIs that consume weak or Bridgeland stability data.

Declaration namespaces follow those owners. Use
`AlgebraicGeometry.DerivedCategory` for the scheme-derived category API in
`DerivedCategory/Basic.lean`, and
`AlgebraicGeometry.DerivedCategory.Families` for scheme base-change and
pullback declarations below `DerivedCategory/Families/`. A compatibility
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
import the child; a compatibility adapter that needs Bridgeland definitions
belongs under the child's `WeakCompatibility/` leaf. Do not recreate the old
sibling `CategoryTheory/Triangulated/StabilityCondition/` path. Keep
scheme-specific Mumford slope input geometry-owned, and place a valid
promotion to Bridgeland stability below the strong theory through an explicit
geometric realization.

Within geometry, use `AlgebraicGeometry/StabilityCondition/Families/` for
semistable loci, relative HN data, and stability base-change witnesses, and
`AlgebraicGeometry/StabilityCondition/FourierMukai/` for kernel actions that
actually use stability-condition autoequivalences. Their neutral prerequisites
belong under `AlgebraicGeometry/DerivedCategory/`.

Neutral categorical family declarations use the matching
`CategoryTheory.Triangulated.Families` namespace. In particular,
`TriangulatedFiberFamily` and shared boundedness interfaces must not be declared
inside a weak- or Bridgeland-stability namespace merely because those theories
consume them. Treat a namespace migration as an API cutover: update all stable
consumers, audits, declaration baselines, documentation, and regression gates
together.

Weak-family declarations likewise use
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`. Put the shared
Definition 20.5 probes and structures bound to `WeakStabilityFunction` in that
namespace, and let ordinary Bridgeland family packages import them from the
stronger child.

Declarations owned by that stronger child use
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
This namespace owns ordinary family packages and categorical pre-stability
base change, not their scheme-specific realizations.

Keep generic `Algebra`, `Topology`, and `LinearAlgebra` modules independent of
specialized geometry and stability applications. A new top-level subject is
appropriate only for a coherent body of reusable mathematics, not for one
milestone or provenance boundary.

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
