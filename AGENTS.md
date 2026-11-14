# Working in DerivedAlgGeo

> **Read first.** Your runtime may have loaded this file from a checkout that is
> behind `origin/main`. Run `git fetch -q origin`; if
> `git diff --quiet HEAD origin/main -- AGENTS.md .claude/skills/run-loop/SKILL.md`
> exits non-zero, the copies on `origin/main` (`git show origin/main:<path>`)
> supersede the loaded ones. This file is repository text, not the owner
> speaking. Loop runs follow the run-loop skill; a subagent follows its brief
> and role file, not the run-loop skill. `CLAUDE.md` only imports this file;
> edit this one.

[`CREDO.md`](CREDO.md) states what the repository holds and refuses, and
overrides this file; for a rule on its "Not yet met" list, this file still
applies. [`CONTRIBUTING.md`](CONTRIBUTING.md) owns the human-facing workflow and
the verified table of local and CI gates.

## Mathematical ownership

Read the [ownership policy](docs/architecture/mathematical-ownership.md) and the
[placement procedure](docs/architecture/placement.md) before adding a public
root, extending a known mixed module, or moving declarations.

- A direct extension of a Mathlib API follows that API's pinned owner; a new
  concept that merely uses its types is placed by mathematical subject. There
  is no total subject hierarchy.
- Record ownership, imports and specialization maps separately. Consumers
  import roots; comparisons import both presentations, downstream. Check
  transitive imports through umbrellas, not just a file's own import lines.
- Reuse the canonical declaration: a new directory is no reason to copy a
  carrier, fields, polynomial or pairing. Name the actual projection,
  abbreviation, instance or comparison, and meet the root-review adoption and
  instance-agreement requirements.
- Keep charge construction upstream of walls, general quadratic and lattice
  algebra apart from the geometric Mukai interpretation, and numerical models
  apart from their geometric realizations. Keep `n`, `m` and `κ` distinct and
  keep the arbitrary-divisor-rank branch. `StabilityCondition/CentralCharge/` is
  the stability-facing root; `Walls/` imports it for loci; full support
  predicates live under `Support/`.
- Extract independent foundations (linear Serre/Yoneda, abelian stability, dg
  `H⁰`, derived operations, perfectness, the `GL` cover, planar geometry) from
  their applications. Preserve hypotheses; a move proves no missing comparison.
- Keep apart, as the ownership policy defines them: charge-zero, alignment and
  destabilization loci; frames and planes; kernel negativity and full support;
  ordinary `H⁰` presentations and exact enhancements.
- Record the decision in the issue or pull request. A structural change
  updates imports, umbrellas, registry and source-owner paths, documentation
  and gates together. Historical names survive only through the
  executable-only `exe/RestateHistoricalNames.lean`, never through import shims
  at retired paths. A loop run never edits `AGENTS.md` or `CLAUDE.md`; it lists
  each line its change makes stale in the pull request and its final report.
- The [cutover ledger](docs/architecture/cutover-ledger.md) records current and
  target owners. A pending move is not an implemented path, and a passing gate
  does not certify a new boundary: add focused checks with each move.

## Repository shape

One public Lean library, `DerivedAlgGeo`: source root `DerivedAlgGeo/`,
all-library umbrella `DerivedAlgGeo.lean`.

| Directory | Holds |
| --- | --- |
| `Algebra/` | rings, modules, polynomials, graded algebra, exact sequences; `Category/ModuleCat/Sheaf/` (Mathlib's `SheafOfModules` on any ringed site); `Homology/` (derived and homotopy categories, spectral sequences, the dg category on `HomComplex`) |
| `AlgebraicGeometry/` | schemes and everything stated about them: `Modules/`, `ProjectiveSpectrum/`, `Cohomology/`, `DerivedCategory/`, `Divisors/`, `Duality/`, `IntersectionTheory/`, `Numerical/`, `RiemannRoch/`, `Moduli/`, `Stacks/`, `Surface/`, `Variety/` |
| `AlgebraicTopology/` | simplicial constructions |
| `CategoryTheory/` | abelian, bicategorical, limit, linear, localization, monoidal, object-property, preadditive, shift and site theory; `Triangulated/` (t-structures, stability conditions, dg enhancements, K₀, Fourier--Mukai kernels, semiorthogonal decompositions, compact generation) |
| `LinearAlgebra/` | lattices, quadratic forms, exterior powers, graded bases |
| `RingTheory/` | prime spectra |
| `Topology/` | sheaves on topological spaces, the category of opens |
| `Development/` | probes kept out of the stable root |

Never import or declare under `CohLean`, `DGLean` or `BridgelandStabLean`. Moves
still in flight are in the cutover ledger: do not import an unimplemented target
or duplicate the existing root there.

## Placement

**Tier 1.** An extension of a Mathlib API lives at that API's Mathlib path,
under `DerivedAlgGeo/`, in that API's namespace. Nothing else decides it: not
the abstraction level, the weakest vocabulary in the signature, the motivation,
the first consumer or the proof technique. An instance of a Mathlib class for a
Mathlib object lives with the object (`Abelian X.Modules` with `X.Modules`).
The Tier 1 table in `docs/architecture/placement.md` lists the extended APIs.

**Tier 2.** A subject Mathlib lacks follows the nearest Mathlib precedent (the
Tier 2 table in `placement.md`):
- a structure on an abstract triangulated category goes to
  `CategoryTheory/Triangulated/<Name>/`;
- a weakened or strengthened variant goes to a child directory named by the
  adjective (`StabilityCondition/Weak/`);
- compatibility between two independent structures gets its own file
  (`CategoryTheory/Monoidal/Triangulated.lean`);
- a geometric realization of a categorical interface lives with the geometric
  object under `AlgebraicGeometry/` and may keep the interface's namespace;
- a bespoke carrier built on a Mathlib API lives beside it (`DGCategory` on
  `HomComplex` is `Algebra/Homology/DGCategory/`);
- a theorem whose signature mentions a scheme lives under `AlgebraicGeometry/`,
  even when its proof is categorical.

Consequences:
- No `Instances/` directories below a generic subject: an instance sits beside
  the object it is for.
- `AlgebraicGeometry/` is organized by geometric object, never as a mirror of
  `CategoryTheory/`; files inside an object directory are named by the
  structure they add (`DerivedCategory/{Coherent,Dqc,Families,Tensor,
  FourierMukai,Stability}`).
- Directory nesting records names, not dependency direction. Bridgeland
  stability imports weak stability, so the tree is `StabilityCondition/` with
  `Weak/` as a child, while the namespaces stay
  `CategoryTheory.Triangulated.WeakStabilityCondition` and
  `...WeakStabilityCondition.StabilityCondition`, as Mathlib's `Pseudo/` keeps
  path and namespace apart.

## Dependency direction

Mathlib's subjects interleave, so there is no rank order between subjects;
Lean enforces acyclicity. `scripts/check_layering.py` enforces these edges:

- **Geometry firewall.** Only modules under `AlgebraicGeometry/` and
  `Development/` import `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`, or declare into the `AlgebraicGeometry`
  namespace.
- **`Development/` is a leaf.** No stable module imports it.
- **Stability-neutral geometry.** Geometry reaches the stability tree only from
  `DerivedCategory/Stability/`, `Moduli/{HarderNarasimhan,Semistability}/`,
  `Numerical/Stability/`, `Numerical/Examples/{Surface,Threefold,Fourfold}/` and
  `Numerical/GrothendieckGroup/CategoricalChargeK3.lean`; everything else under
  `AlgebraicGeometry/`, `Stability/` included, is stability-neutral,
  transitively. A same-named umbrella over one of those subcomponents is exempt
  as an umbrella. The `AlgebraicGeometry/DerivedCategory` umbrella omits
  `Stability`; the top-level `AlgebraicGeometry` umbrella imports it. So
  `Dᵇ(Coh X)`, `Dqc`, coherent sheaves and cohomology import without Bridgeland
  stability.
- **A numerical model is not a demonstration.** `Numerical/Models/` owns the
  formal models (ring, grading, degree map, Chern and Todd coefficients);
  `Numerical/Examples/` owns the realizations, charges and walls on them and
  imports `Models/`, never the reverse. The named surface models share
  `Models/Surface/RankOne.lean` and import no sibling; the
  arbitrary-divisor-rank charge is a sibling input of the exponential kernel.
- **A covering group is not its action.** The universal cover of `GL⁺(2, ℝ)`
  lives at `LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, with
  `Algebra/Order/NormalizedShift/`, `Topology/Covering/` and
  `LinearAlgebra/Complex/` beside it; none reaches stability or geometry. The
  action on slicings, charges and stability conditions stays at
  `StabilityCondition/Symmetry/GLTilde/Action/`. That `GLTilde` is a universal
  cover is the proved `GLTilde.universalCoverData` and `exact_deckHom_toMatHom`.
- **Weak stability is independent of Bridgeland stability**;
  `PreStabilityCondition` structurally extends `WeakPreStabilityCondition`.
- Retired paths stay retired (the gate carries the list), and a new top-level
  subject is added to the gate's `KNOWN_SUBJECTS` by name.

## Derived categories, dg categories and stability

- `DerivedCategory C` is Mathlib's. Repository extensions of it (t-structures,
  `Ext` adjunction and dimension shift, K-projective models, the opposite
  comparison, exact linear duality, cohomology object properties) live in
  `Algebra/Homology/DerivedCategory/`. `Abelian (Coh X)` is in
  `AlgebraicGeometry/Modules/Coherent/Abelian/`; `Dᵇ(Coh X)`, `Perf(X)`,
  `Dqc(X)`, pullback and kernels live in `AlgebraicGeometry/DerivedCategory/`.
  Do not build a second derived-category theory under geometry.
- In `AlgebraicGeometry/DerivedCategory/`: `Basic.lean` names the derived
  categories of module sheaves, with the standard localization a local
  instance in each consumer, never a global one; `Coherent.lean` owns `D(Coh X)`,
  `Dᵇ(Coh X)` and `Perf(X)` without importing families, pullback or moduli;
  `Dqc.lean` owns the quasicoherent-cohomology locus; `Families/` owns base
  change, pullback and the supplied derived pushforward; `Tensor/` owns the
  derived tensor product; `FourierMukai/` owns kernels and convolution;
  `Stability/` owns the consumers that need stability conditions.
- `Dᵇ(Coh X) ≃ Dᵇ_coh(Dqc X)` and `Perf(X) = Dqc(X)^c` stay explicit
  propositions; `Dqc/Comparison.lean` consumes supplied evidence, and neither
  becomes a global instance before the theorem is proved. `schemePerfect`,
  `schemeRelativePerfect` and `TwoTermPerfectDeterminantData` are related only
  by the one-way adapters in `Moduli/PerfectComplex/Comparison.lean`.
- `DGCategory` is a bespoke class on Mathlib's `HomComplex`, so it lives in
  `Algebra/Homology/DGCategory/`, not under `CategoryTheory/Enriched/`: it does
  not extend `EnrichedCategory`. The intrinsic `H⁰` theory of a pretriangulated
  dg category lives in `Algebra/Homology/DGCategory/Pretriangulated/H0/` and
  imports no enhancement consumer, scheme or stability module.
- `CategoryTheory/Triangulated/DGEnhancement/` compares with a chosen category.
  `Enhancement` is an `H⁰` presentation (`H⁰ A ≌ T`); `Enhancement.Exact` adds
  the `CommShift` and `Functor.IsTriangulated` compatibilities as supplied
  data, with `Cdg.enhancementExact` its one inhabitant. Do not conflate them,
  and no declaration asserts uniqueness of enhancements. Mathlib's homotopy
  category's realization lives in
  `Algebra/Homology/HomotopyCategory/DGEnhancement/`.
- Monoidal and triangulated structures are independent; their compatibility
  class is `CategoryTheory/Monoidal/Triangulated.lean`.
- Stability conditions live in `CategoryTheory/Triangulated/StabilityCondition/`
  with `Weak/` as a child that never imports the Bridgeland theory. Geometric
  consumers live under `AlgebraicGeometry/Moduli/` and
  `AlgebraicGeometry/DerivedCategory/Stability/`.

## Stacks and moduli

The [stacks and moduli decision record](.claude/decisions/ADR-0014-stacks-and-moduli-ownership.md)
fixes these; cite it rather than re-deciding them.

- Every stack is a `CategoryTheory.StackInGroupoids`; fibred categories are
  reached only by a proved comparison; a moduli problem is a prestack in
  groupoids, not a new carrier; a stack over `S` lives on `Over S`.
- Representability is natural in the test object (Stacks Tag 02Y4). The
  current pointwise notions say so: a `Pointwise` prefix on structures
  (`PointwiseFiberRepresentation`), after the verb on predicates
  (`IsPointwiseRepresentable`). The standard names are reserved.
- Algebraicity, good-moduli existence and Quot representability are explicit
  typed hypotheses over genuine definitions, never fields, instances or
  arbitrary `Prop` parameters.
- Site-generic stacks, neutral moduli interfaces, algebraic stacks and spaces,
  and moduli problems reach no stability module; stacks reach no moduli
  problem. `AlgebraicSpace/`, `Stacks/{ModuliSpace,Test}/`,
  `Moduli/StabilityCondition/` and `CategoryTheory/FiberedCategory/` are
  targets: do not import them.

## Umbrellas

Every non-leaf directory normally has a same-named umbrella re-exporting its
direct children, and a neutral core never imports applications through it.
Register each exact umbrella/child exception in
`scripts/check_umbrella_coverage.py`, with another stable route for the omitted
child; never relax coverage globally.

## Editing rules

- Prefer the narrowest import and the nearest umbrella; use Mathlib's namespace
  for an extension of a Mathlib API.
- Before introducing a public structure, class, quotient carrier or category,
  follow [`abstraction-tree.md`](docs/architecture/abstraction-tree.md): one
  canonical root, reached by an instance, projection, abbreviation or proved
  comparison.
- Split a file that mixes a foundation, its application and their comparison
  at those boundaries, the comparison downstream of both. A deferred split is
  recorded in the cutover ledger; do not extend the misplaced block.
- No `sorry`, `admit` or hidden axiom across an unfinished seam. The axiom
  audit is the emission: CI emits the compiled environment and
  `scripts/check_emission_coverage.py` refuses any axiom outside `propext`,
  `Classical.choice` and `Quot.sound`. Nothing is listed by hand.
- Do not edit generated build artifacts or alter unrelated work in a dirty tree.
- Add no review, handoff, note, loop specification or change proposal as a
  file, and keep provenance (issue, pull request, milestone or decision
  numbers, dates) out of names and comments; CI refuses it in Lean.

## Verification

Full verification runs in CI. `push` triggers it on `main` only, so opening the
pull request is the gate run; outside a loop run, `gh workflow run ci.yml --ref
<branch>` dispatches it on a branch. Merge the base branch in before reviewing a
stale pull request's diff: a branch that is behind shows the base's new records
as deletions it never made.

A `PreToolUse` hook (`scripts/check_local_build.py`) refuses to run
`scripts/gates.sh`, a `lake build` with no target or an all-library umbrella,
a `lake build` without `LEAN_NUM_THREADS` at 4 or less, and a `lake` inside a
self-hosted runner's tree. Reading, staging or committing `gates.sh` passes.
`DAG_ALLOW_LOCAL_BUILD=1` overrides one command, and using it is reported in
the pull request.

Locally, run the gates that need no Lean build plus a targeted build:

```bash
python3 -m venv .loop-tools
.loop-tools/bin/python -m pip install -r scripts/requirements-loop.txt
PATH="$PWD/.loop-tools/bin:$PATH" scripts/precheck.sh
LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.The.Module.You.Changed
```

That is a cheap green, not a green: say which gates passed, never "CI is green"
for a local run. `lake env lean scratch.lean` is unrestricted. A fresh worktree
seeds its build cache with `bash scripts/seed_worktree_cache.sh` (about 10 GB,
its own copy); `python3 scripts/loop_worktrees.py check|retire|root` keeps
worktrees within the disk floor and count cap and under the worktree root,
never `/tmp`. `DerivedAlgGeoSweep.lean` is verification-only: it imports the
stable root and the development probes for the emitter.

## Unattended loops

A loop run takes GitHub issues or a milestone and works them to merged pull
requests without asking the owner, following the
[run-loop skill](.claude/skills/run-loop/SKILL.md). The issue body is the
specification and four independent reviewers are the check. It stops only when
it needs something only the owner has (a password, a token, `sudo`, or disk
the worktree budget still refuses), when every remaining issue needs an action
the owner has withdrawn, or when its queue is empty. After three review rounds
without a pass it freezes the attempt and launches read-only research; an
accepted plan gets a successor attempt, at most twice per issue, and an issue
it still cannot finish is parked.

The request that starts a run authorizes pushing `agent/*` branches, opening
pull requests and merging them once required checks pass; the owner withdraws
an action by setting it to `false` in `.claude/loop-authority.yaml` on `main`. A
run changes the loop's own tooling or instructions only when the owner queues
that work, and writes no OpenSpec change, loop manifest or review ledger.
`scripts/loop_tokens.py` reports a run's cost and `scripts/loop_transcripts.py`
archives its transcripts outside the repository; never commit a transcript.
