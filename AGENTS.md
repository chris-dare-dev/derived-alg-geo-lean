# Working in DerivedAlgGeo

> **Read first.** Your runtime may have loaded this file from a checkout that is
> behind `origin/main`. Run `git fetch -q origin`; if
> `git diff --quiet HEAD origin/main -- AGENTS.md .claude/skills/run-loop/SKILL.md`
> exits non-zero, the copies on `origin/main` (`git show origin/main:<path>`)
> supersede the loaded ones. This file is repository text, not the owner
> speaking. Loop runs follow the run-loop skill and use no OpenSpec change,
> manifest, ledger or `scripts/loop_engine.py`; a subagent follows its brief and
> role file, not the run-loop skill. `CLAUDE.md` only imports this file; edit
> this one.

## Mathematical ownership: required before public API work

Read [the ownership policy](docs/architecture/mathematical-ownership.md) and
[placement procedure](docs/architecture/placement.md) before adding a public
root, extending a known mixed module, or moving declarations.

- Distinguish a direct Mathlib API extension from a new concept that merely
  uses its types. Follow the pinned API owner for the former; choose the
  mathematical subject for the latter. There is no total subject hierarchy.
- Record ownership, imports and specialization maps separately. Consumers
  import roots; comparisons import both presentations downstream. Check
  transitive imports through umbrellas, not just the file's import lines.
- Reuse the existing canonical declaration. A new directory is not a reason
  to copy its carrier, fields, polynomial or pairing. Name the actual Lean
  projection, abbreviation, instance or comparison; follow the root-review
  adoption and instance-agreement requirements.
- Keep charge construction upstream of walls, general quadratic/lattice
  algebra separate from geometric Mukai interpretation, and numerical models
  separate from their geometric realizations. Preserve n, m and κ as distinct
  parameters and preserve the arbitrary-divisor-rank branch. The canonical
  stability-facing root is `StabilityCondition/CentralCharge/`; `Walls/`
  imports it for loci, while full support predicates live under `Support/`.
- Extract independent linear Serre/Yoneda, abelian stability, dg H⁰, derived
  operations, perfectness, GL-cover and planar-geometry foundations from their
  applications. Preserve hypotheses; a move proves no missing comparison.
- Distinguish charge-zero/alignment/destabilization loci, frames/planes,
  kernel negativity/full support, and ordinary H⁰ presentations/exact
  enhancements. Use the precise boundaries in the ownership policy.
- Use its compact decision record in the issue or PR. Update imports,
  umbrellas, audits, registry/source-owner paths, documentation and relevant
  gates in the source cutover; preserve historical names through the existing
  executable-only mechanism, without retired-path import shims. A loop run
  never edits AGENTS.md or CLAUDE.md: it lists each line its cutover makes
  stale under the PR's follow-ups and in its final report.
- Consult the cutover ledger for current and target owners. Pending MO1 moves
  are not implemented paths, and a passing current gate does not certify the
  new component boundaries. Add focused checks with each implementing move.

## Repository shape

This repository contains one public Lean library, `DerivedAlgGeo`. Its source
root is `DerivedAlgGeo/` and its all-library umbrella is `DerivedAlgGeo.lean`.
The layout follows Mathlib's broad subjects and the pinned definition sites
of APIs it directly extends. New subjects follow mathematical ownership;
using a Mathlib type alone does not determine their directory.

| Directory | Mathlib counterpart | What lives here |
| --- | --- | --- |
| `Algebra/` | `Mathlib/Algebra/` | ring, module, polynomial, graded algebra, and exact sequences; `Algebra/Category/ModuleCat/Sheaf/` extends Mathlib's `SheafOfModules` on an arbitrary ringed site; `Algebra/Homology/` extends Mathlib's homological algebra: derived categories, homotopy categories, spectral sequences, and the bespoke dg category built on `HomComplex` |
| `AlgebraicGeometry/` | `Mathlib/AlgebraicGeometry/` | schemes and everything stated about them: `Modules/` (with its `Coherent/` and `Quasicoherent/` children), `ProjectiveSpectrum/`, `Cohomology/`, `DerivedCategory/`, `Divisors/`, `Duality/`, `IntersectionTheory/`, `Numerical/`, `RiemannRoch/`, `Moduli/`, `Stacks/`, `Surface/`, `Variety/` |
| `AlgebraicTopology/` | `Mathlib/AlgebraicTopology/` | simplicial constructions |
| `CategoryTheory/` | `Mathlib/CategoryTheory/` | abelian, bicategorical, limit, linear, localization, monoidal, object-property, preadditive, shift, and site theory; `Triangulated/` with its t-structures, stability conditions, dg enhancements, Grothendieck groups, Fourier--Mukai kernels, semiorthogonal decompositions, and compact generation |
| `LinearAlgebra/` | `Mathlib/LinearAlgebra/` | lattices, quadratic forms, exterior powers, graded bases |
| `RingTheory/` | `Mathlib/RingTheory/` | prime spectra |
| `Topology/` | `Mathlib/Topology/` | sheaves on topological spaces and the category of opens |
| `Development/` | none | probes intentionally excluded from the stable root |

Never add imports or namespaces rooted at `CohLean`, `DGLean`, or
`BridgelandStabLean`; those migration artifacts are retired. Lanes still in
flight toward this layout are listed under "Confirmed next lanes" in
`docs/architecture/cutover-ledger.md`. Distinguish a current module from a
confirmed target or a proposal awaiting a declaration-level split. Do not
import an unimplemented target or duplicate the existing root there.

## The placement rule

Direct Mathlib extensions follow their API's definition site. New concepts
are placed by mathematical subject and the nearest applicable precedent.
The mere appearance of a carrier in a public type does not decide which
case applies. Two tiers.

**Tier 1. An extension of a Mathlib API lives at that API's Mathlib path,
under `DerivedAlgGeo/`, in that API's namespace.** Nothing else decides it:
not the abstraction level of the statement, not the weakest vocabulary in its
signature, not its motivation, its first consumer, or its proof technique.
The Tier 1 table in `docs/architecture/placement.md` lists each extended
Mathlib API with its repository path; an ownership cutover updates it there. An
instance of a Mathlib class for a Mathlib object lives with the object, never
below the interface: `Abelian (ModuleCat R)` with `ModuleCat`, `Abelian
X.Modules` with `X.Modules`.

**Tier 2. A subject Mathlib lacks is placed by the nearest Mathlib
precedent**, listed in the Tier 2 table of `docs/architecture/placement.md`.
For example:
- a structure on an abstract triangulated category goes to
  `CategoryTheory/Triangulated/<Name>/` (stability conditions, dg enhancements,
  K₀, Fourier--Mukai kernels, semiorthogonal decompositions, spherical twists,
  compact generation, families);
- a weakened or strengthened variant of a named concept goes to a child
  directory named by the adjective: `Triangulated/StabilityCondition/Weak/`;
- compatibility between two independent structures gets its own file:
  `CategoryTheory/Monoidal/Triangulated.lean`;
- a geometric realization of a categorical interface lives with the geometric
  object under `AlgebraicGeometry/`, and may keep the interface's namespace for
  dot notation;
- a bespoke carrier built on a Mathlib API lives beside that API: `DGCategory`
  on `HomComplex` is `Algebra/Homology/DGCategory/`;
- a theorem whose signature mentions a scheme lives under `AlgebraicGeometry/`,
  even when the proof is entirely categorical.

Three consequences follow, and each retires a former convention.

- **There are no `Instances/` directories below a generic subject.** Mathlib
  has none. The instance of `IsCompatibleWithTriangulation` for `Dᵇ(Coh X)`
  sits in `AlgebraicGeometry/DerivedCategory/Tensor/Coherent.lean`
  beside the class it registers; the scheme realizations of the stability
  family interfaces sit under `AlgebraicGeometry/Moduli/` and
  `AlgebraicGeometry/DerivedCategory/Stability/`. The former
  `CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves and the
  `GeometryInstances` virtual layer are retired.
- **`AlgebraicGeometry/` is organized by geometric object, never as a mirror
  of `CategoryTheory/`.** One object satisfies many interfaces: `Dᵇ(Coh X)` is
  triangulated, has a t-structure, is conditionally monoidal, is a fiber of a
  family, and carries stability conditions. Inside an object directory, files
  are named by the structure they add, as Mathlib's `ModuleCat/` has
  `Abelian.lean`, `Monoidal/`, and `Limits.lean`. So
  `AlgebraicGeometry/DerivedCategory/{Coherent,Dqc,Families,Tensor,FourierMukai,Stability}`,
  never `AlgebraicGeometry/Triangulated/DerivedCategory/`.
- **Directory nesting records names, not dependency direction.** Mathlib's
  `MetricSpace/Defs.lean` imports its own child `MetricSpace/Pseudo/Defs.lean`.
  Bridgeland stability is the canonical concept and imports weak stability,
  so the tree is `Triangulated/StabilityCondition/` with `Weak/` as a child.
  Declaration namespaces stay `CategoryTheory.Triangulated.WeakStabilityCondition`
  and `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition`;
  Mathlib's `Pseudo/` precedent has namespace and path differ too, and a
  namespace cutover would invalidate the immutable review payloads the
  `exe/RestateHistoricalNames.lean` bridge exists to protect.

Within Tier 2, use sufficient hypotheses to separate independent mathematics
from its application. Do not rank subjects by their weakest vocabulary or
move a direct Mathlib extension away from its API owner. The examples and
boundaries are in `docs/architecture/mathematical-ownership.md`.

## Dependency direction

Mathlib's subjects interleave: `Algebra/Homology` imports `CategoryTheory`,
and `CategoryTheory/Linear` imports `Algebra`. There is therefore no rank
order between subjects, and `scripts/check_layering.py` does not enforce one.
Lean enforces module acyclicity. The currently enforced broad policy edges
are below; finer ownership boundaries remain explicit review obligations
until their implementing cutovers add the corresponding checks.

- **Geometry firewall.** Only modules below `AlgebraicGeometry/` and
  `Development/` import `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`, and only they declare into the
  `AlgebraicGeometry` namespace. Everything else is usable without schemes.
- **`Development/` is a leaf.** No stable module imports it.
- **Stability-neutral geometry.** Geometry reaches the stability tree only from
  the subcomponents that exist to consume it: `DerivedCategory/Stability/`,
  `Moduli/{HarderNarasimhan,Semistability}/`, `Numerical/Stability/`,
  `Numerical/Examples/{Surface,Threefold,Fourfold}/`,
  and `Numerical/GrothendieckGroup/CategoricalChargeK3.lean`.
  Everything else below `AlgebraicGeometry/` is stability-neutral, transitively
  included -- `Stability/` among it since MO1.08 (#1319), which moved the
  abstract slope theory it instantiates to `CategoryTheory/Abelian/Stability/`
  and removed the exemption rather than renaming it. A same-named umbrella over one of those subcomponents is exempt as
  an umbrella, and its other children are not. The
  `AlgebraicGeometry/DerivedCategory` umbrella is the one that omits a child
  outright -- it drops `Stability`, and the top-level `AlgebraicGeometry`
  umbrella imports it. This is what keeps `Dᵇ(Coh X)`, `Dqc`, coherent sheaves,
  and cohomology importable without Bridgeland stability. The list was narrowed
  from the four blanket subtrees on 2026-09-13 (MO1.01, #1312); see
  `docs/architecture/cutover-ledger.md`.
- **A numerical model is not a demonstration.** `Numerical/Models/` owns the
  formal rank-degree-coordinate models -- ring, grading, degree map, Chern and
  Todd coefficients. `Numerical/Examples/` owns the realization maps, charges
  and walls demonstrated on them and imports `Models/`, never the reverse. The
  named surface models share `Models/Surface/RankOne.lean` and import no
  sibling; the arbitrary-divisor-rank charge is a sibling input of the
  exponential kernel, not a child of the scalar `H`-degree compression
  (MO1.06, #1317).
- **A covering group is not its action.** The universal cover of
  `GL⁺(2, ℝ)` -- the compatible-pair group, its `ℤ` deck group, the global
  chart, simple connectedness, the covering map and the topological-group laws
  -- is at `LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, with the
  `+1`-equivariant order automorphisms of `ℝ` at
  `Algebra/Order/NormalizedShift/`, the general product-of-coverings lemma at
  `Topology/Covering/`, and the cover-independent complex-coordinate adapter at
  `LinearAlgebra/Complex/`. None of them reaches the stability tree or
  geometry. The phase conventions and the action on slicings, charges and
  stability conditions stay at `StabilityCondition/Symmetry/GLTilde/Action/`,
  which still imports the cover. `GLTilde` being a universal cover is
  `GLTilde.universalCoverData` and `exact_deckHom_toMatHom`, two proved
  theorems, not an inference from the identifier (MO1.12, #1323).
- **Weak stability is independent of Bridgeland stability**, and
  `PreStabilityCondition` structurally extends `WeakPreStabilityCondition`.
- **Retired paths stay retired.** The gate carries the list.
- **A new top-level subject is deliberate**, added to the gate's
  `KNOWN_SUBJECTS` by name.

## Derived categories and `Dᵇ(Coh X)`

Derived-category theory is generic and is built once. Three declarations,
three owners:

- the construction `DerivedCategory C` for an abelian `C` is Mathlib's, in
  `Mathlib/Algebra/Homology/DerivedCategory/`;
- repository extensions of it (t-structure results, `Ext` adjunction and
  dimension shift, K-projective and bounded-above-projective models, the
  opposite comparison, exact linear duality, cohomology object properties)
  live in `Algebra/Homology/DerivedCategory/`;
- `Abelian (Coh X)` is a geometric instance in
  `AlgebraicGeometry/Modules/Coherent/Abelian/`, and the abbreviation
  `Dᵇ(Coh X) := DerivedCategory.Bounded (Coh X)` together with everything
  scheme-specific about it, `Perf(X)`, `Dqc(X)`, pullback, and kernels, lives
  in `AlgebraicGeometry/DerivedCategory/`.

Do not build a second derived-category theory under geometry. `Basic.lean`
names the derived categories of module sheaves, with the standard
  localization as a local instance in each consumer and never a global one; `Coherent.lean` owns
`D(Coh X)`, `Dᵇ(Coh X)`, and `Perf(X)` without importing families, pullback,
or moduli; `Dqc.lean` owns the quasicoherent-cohomology locus and its
canonical zero for every scheme; `Families/` owns scheme base change and
pullback and the supplied derived pushforward; `Tensor/` owns the derived
tensor product in its unbounded, bounded-coherent and relative tiers;
`FourierMukai/` owns neutral kernels and convolution and consumes all of those;
`Stability/` owns the three consumers that need stability conditions.

The identifications `Dᵇ(Coh X) ≃ Dᵇ_coh(Dqc X)` and `Perf(X) = Dqc(X)^c`
remain explicit propositions. `Dqc/Comparison.lean` consumes supplied
evidence to produce representatives and membership comparisons; do not turn
either into a global instance before the geometric theorem is proved. The
three uses of "perfect" (`schemePerfect`, `schemeRelativePerfect`,
`TwoTermPerfectDeterminantData`) are related only by the one-way adapters in
`Moduli/PerfectComplex/Comparison.lean`; see the ledger in
`docs/architecture/placement.md`.

## dg categories, enhancements, and stability

- `DGCategory` is a bespoke class built on Mathlib's `HomComplex` (ADR-0010,
  ADR-0011), so by definition site it lives in `Algebra/Homology/DGCategory/`
  beside the `HomotopyCategory/` it enhances. It does not extend
  `EnrichedCategory`; a path under `CategoryTheory/Enriched/` would assert an
  `extends` that is not there. If the enriched encoding (ADR-0010 Option A′)
  ever lands, the subtree moves under `CategoryTheory/Enriched/` in the same
  change.
- The intrinsic `H⁰` theory of a pretriangulated dg category -- the zero
  object, the shift, the distinguished triangles built from dg cones, the
  functorial cone diagrams and the exactness of what `DGFunctor.h0` produces --
  mentions no other category, so it lives with the dg encoding, in
  `Algebra/Homology/DGCategory/Pretriangulated/H0/`. It imports no enhancement
  consumer, scheme realization or stability module, and layering rule 13 keeps
  that true (#1320).
- Comparison with a *chosen* category lives in
  `CategoryTheory/Triangulated/DGEnhancement/`. Two strengths are distinguished
  and must not be conflated: `Enhancement` is the underlying **H⁰
  presentation** -- a plain equivalence `H⁰ A ≌ T` with `T` an arbitrary
  category -- and `Enhancement.Exact` is the refinement carrying the `CommShift`
  and `Functor.IsTriangulated` compatibilities as data. The refinement is
  supplied, not proved; `Cdg.enhancementExact` is its one inhabitant. No
  declaration asserts uniqueness of enhancements in either strength.
- The realization for Mathlib's homotopy category, and the proved agreement of
  the two triangulated structures for the complexes model, live with that
  object, in `Algebra/Homology/HomotopyCategory/DGEnhancement/`.
- Monoidal and triangulated structures are independent; their compatibility
  class is `CategoryTheory/Monoidal/Triangulated.lean`, and geometric exact
  tensors instantiate it from geometry.
- Stability conditions live in `CategoryTheory/Triangulated/StabilityCondition/`
  with weak stability as the child `Weak/`. Weak stability never imports the
  Bridgeland theory. Geometric consumers live under `AlgebraicGeometry/Moduli/`
  (semistable loci, relative HN filtrations, finite-type openness, scheme
  probes) and `AlgebraicGeometry/DerivedCategory/Stability/` (base change of
  pre-stability data, the geometric Fourier--Mukai action).

## Umbrellas

Every non-leaf directory normally has a same-named umbrella re-exporting its
direct children. A neutral core must not import applications through that
umbrella. Document each exact umbrella/child exception and register it in
`scripts/check_umbrella_coverage.py` in the source cutover, preserving another
stable export/build route for the omitted child. A module that defines the
object studied by its same-named directory is not necessarily an umbrella.
Update imports, audits, declaration routing, documentation and affected
gates/CI paths together; do not silently omit a child or relax coverage globally.

## Editing rules

- Prefer the narrowest import and the nearest umbrella.
- Before editing public API, apply the two-tier rule above and the decision
  table in `docs/architecture/placement.md`.
- Use Mathlib's namespace for extensions of an existing Mathlib API.
- Before introducing a public structure, class, quotient carrier, or
  category, follow `docs/architecture/abstraction-tree.md`: reuse one
  canonical root and make specializations reach it by an instance,
  projection, abbreviation, or proved comparison.
- If a file mixes a foundation, its application and their comparison, split
  at those declaration boundaries. Put the comparison downstream of both
  presentations. If the split is deferred, record it in the cutover ledger
  and do not extend the misplaced block in place or create a competing root.
- Preserve explicit trust boundaries; do not use `sorry`, `admit`, or a
  hidden axiom to cross an unfinished mathematical seam.
- Add every new public declaration to the relevant audit.
- Do not edit generated build artifacts by hand.
- Do not alter unrelated work in a dirty tree.

Read `CONTRIBUTING.md` before creating a new directory or publishing a
change; it owns the human-facing placement and contribution rules.

## Reading the diff of a stale pull request

**Merge the base branch in before reviewing a diff.** A branch that is behind
renders every record the base has added since the fork as a DELETION the pull
request never made. This is an artifact of the two-dot diff GitHub shows, not a
change anyone wrote.

It matters most for the audit record slices, where a real deletion is a defect.
`check_audit.py` and `check_audit_complete.py` judge the merged tree in `ci`, so
a phantom deletion cannot reach `main`; the incidents are in
`docs/architecture/verification-history.md`.

## Required verification

**Full verification runs in CI, not on your machine.** Since 2026-09-19
`.github/workflows/ci.yml` triggers `push` on `main` alone, so **pushing an
agent branch is no longer a gate run — opening the pull request is.** The
`pull_request` lane runs the identical job set on `ubuntu-latest`; it is the
faster lane and the one branch protection reads.

To run the self-hosted Ubuntu lane on a branch, dispatch it by hand:

```bash
gh workflow run ci.yml --ref <branch>
```

Not in loop runs: there the pull request's CI is the gate.

**This is enforced, not advised.** A `PreToolUse` hook on `Bash`, wired in the
tracked `.claude/settings.json` so it reaches every worktree, runs
`scripts/check_local_build.py` and refuses four things:

* `scripts/gates.sh`, in any mode;
* `lake build` with **no target**;
* `lake build <Target>` that does not declare `LEAN_NUM_THREADS`, or sets it
  above 4 — see below;
* `lake build <Target>` run through a `lake` that resolves inside a
  self-hosted runner's working directory — see "Whose lake" below.

It refuses running that file, not reading it: `cat`, `grep`, `diff` and
`git ls-tree` over `scripts/gates.sh` all pass.

`gates.sh` was already discouraged here for a second reason worth keeping:
several agent lanes and four Ubuntu runner services share one physical host.
Lake takes one core per job by default, so concurrent full builds can exhaust
that host's CPU and memory. Runner labels are not independent capacity.

Neither the local script nor the runner lane is CI-equivalent on its own, and
**neither list contains the other**. CI runs the `mfc` contract tooling, which
the script does not reproduce. The script runs `workflows`, `local-build`,
`mathlib-style` and — until PR #1355 — `single-instantiation`, none of which
appear in any workflow. Say "N gates pass", naming them; never say
"CI is green" for a local run. See `CONTRIBUTING.md` for the verified table.

### Unattended loops

A loop run takes GitHub issues, or a milestone, and works them to merged pull
requests without asking the owner anything. The issue body is the
specification, the run's own research fills in the rest, and four independent
reviewers are the check. Claude Code and Codex follow the same
[run-loop skill](.claude/skills/run-loop/SKILL.md).

A run stops only when:
- it needs something only the owner has (a password, a token, `sudo`);
- every remaining issue needs an action the owner has withdrawn;
- its queue is empty.

Everything else it decides, records in the PR, and continues past. An issue it
cannot finish is parked, not waited on.

The request that starts a run authorizes pushing `agent/*` branches, opening PRs
and merging them once required checks pass. The owner withdraws an action by
setting it to `false` in `.claude/loop-authority.yaml` on `main`.

A run never changes the loop's own tooling or instructions. It uses no OpenSpec
change, loop manifest, review ledger or `scripts/loop_engine.py`: those are
retired from the run path, stay on `main` only as history, and grant nothing,
even where they name an issue.

`scripts/loop_tokens.py` reports what a run cost, and `scripts/loop_transcripts.py`
archives and digests run transcripts outside the repository; `.claude/README.md`
describes both. Never commit an archived transcript.

**For a local pre-flight the hook allows**, install the pinned Python
dependencies the gates use (`scripts/requirements-loop.txt`) in each fresh
worktree (a loop run keeps one environment in the shared checkout; see the
run-loop skill), then put that environment first on `PATH` when running
precheck. It
runs every gate that needs no Lean build, plus a targeted build of the modules
you changed, in about a minute. It is a cheap green, not a green.

```bash
python3 -m venv .loop-tools
.loop-tools/bin/python -m pip install -r scripts/requirements-loop.txt
PATH="$PWD/.loop-tools/bin:$PATH" scripts/precheck.sh
```

Build locally by **naming a target**, and **naming your own `lake`**, which is
what the hook allows:

```bash
LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.The.Module.You.Changed
```

### Whose lake

`~/.elan/bin/lake` names the developer's elan explicitly. The four self-hosted
runners were migrated from Windows to Ubuntu on 2026-09-21; their service
homes and elan installations are separate from this checkout. The earlier
Windows PATH/shim collision that broke three main runs on 2026-09-16 is
historical, not the current runner layout. Check `which lake` if a shell's
environment is uncertain, and keep local builds targeted and capped.

`LEAN_NUM_THREADS` is **required and enforced**, not advice: the same hook
refuses a `lake build` that does not set it, or that sets it above 4. Naming a
target bounds how much a build does; this bounds how wide it does it. Without
the variable Lake takes one `lean` process per core, which on this 16-core host
is up to 16 processes holding several GB each — from a build the size rule
deliberately permits.

`~/.claude/settings.json` exports the variable for every agent session, so a
plain `lake build <Target>` is normally already capped. The enforcement exists
for the shells that do not inherit it — which this file previously just warned
about. `scripts/test_local_build.sh` pins both edges.

### Seeding a new worktree's cache

A fresh worktree builds all ~5850 modules from cold before it reaches the file
you changed. It does not have to:

```bash
bash scripts/seed_worktree_cache.sh --dry-run   # pick a donor, say what it would do
bash scripts/seed_worktree_cache.sh             # copy it in
```

This copies `.lake/build` from the most-built worktree of this clone and links
`.lake/packages` to the shared dependency set. Lake verifies every trace against
the source it finds, so anything your branch changes is still rebuilt and
nothing stale is trusted. It **copies rather than hardlinks**, because Lean
writes an `.olean` at its final path and a hardlink would let a rebuild in one
worktree write through into another's cache.

The script only ever writes to the worktree you run it in, and refuses a target
that already has a build cache unless you pass `--force`.

`lake env lean scratch.lean` is **not** restricted and is not meant to be. It is
the seconds-long probe interactive proof work depends on; routing each attempt at
a lemma through CI would be a ~12 minute round trip and would stop anyone writing
a proof at all.

### Cache loss, and why the rule still stands

The Ubuntu runners and this host use the same platform, but their writable
build directories are separate. A runner build does not populate this
checkout's `.olean` files. A targeted local build may still compile its
dependencies after cache loss; naming a target bounds the work without making
that cost vanish. For a full verification verdict, use the CI workflow:

```bash
gh workflow run ci.yml --ref <branch>
```

Not in loop runs: there the pull request's CI is the gate.

When a local build genuinely cannot be avoided, `DAG_ALLOW_LOCAL_BUILD=1`
overrides the hook for one command. **Using it is a reportable event**: say so in
the pull request or the session report, because a whole-library local build is
precisely what this rule exists to keep off the developer's machine.

Useful focused commands are:

```bash
PATH="$PWD/.loop-tools/bin:$PATH" scripts/precheck.sh  # gates plus targeted build
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake exe runLinter DerivedAlgGeo
lake exe lint-style
python3 scripts/check_source_independence.py
python3 scripts/check_layering.py
python3 scripts/check_umbrella_coverage.py
python3 scripts/check_coverage_map.py
```

New public declarations must be added to the relevant audit. The declaration
sweep in `scripts/EnumDecls.lean` and
`scripts/check_audit_complete.py` guards the opposite direction, so renames
must update both the source declaration and its audit record.

`DerivedAlgGeoSweep.lean` is verification-only. It imports the stable root and
development probes for full emitter coverage; do not treat it as a public
package boundary.
