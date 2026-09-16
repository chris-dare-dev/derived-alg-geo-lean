# Working in DerivedAlgGeo

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
  parameters and preserve the arbitrary-divisor-rank branch.
- Extract independent linear Serre/Yoneda, abelian stability, dg H⁰, derived
  operations, perfectness, GL-cover and planar-geometry foundations from their
  applications. Preserve hypotheses; a move proves no missing comparison.
- Distinguish charge-zero/alignment/destabilization loci, frames/planes,
  kernel negativity/full support, and ordinary H⁰ presentations/exact
  enhancements. Use the precise boundaries in the ownership policy.
- Use its compact decision record in the issue or PR. Update imports,
  umbrellas, audits, registry/source-owner paths, documentation and relevant
  gates in the source cutover; preserve historical names through the existing
  executable-only mechanism, without retired-path import shims.
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

| Concept | Mathlib defines it in | So it lives in |
| --- | --- | --- |
| `DerivedCategory C`, `Ext`, K-projectives, its t-structure, `Bounded` | `Algebra/Homology/DerivedCategory/` | `Algebra/Homology/DerivedCategory/` |
| `HomotopyCategory`, `HomComplex`, bounded and plus variants | `Algebra/Homology/HomotopyCategory/` | `Algebra/Homology/HomotopyCategory/` |
| `SheafOfModules`, `GeneratingSections`, `IsQuasicoherent`, presentations, invertibility | `Algebra/Category/ModuleCat/Sheaf/` | `Algebra/Category/ModuleCat/Sheaf/` |
| `ObjectProperty`, `FullSubcategory`, `lift`, `inverseImage` | `CategoryTheory/ObjectProperty/` | `CategoryTheory/ObjectProperty/` |
| Čech cohomology on a site | `CategoryTheory/Sites/SheafCohomology/` | `CategoryTheory/Sites/SheafCohomology/Cech/` |
| Spectral sequences and total complexes | `Algebra/Homology/SpectralSequence/`, `SpectralObject/` | `Algebra/Homology/SpectralSequence/` |
| `Pseudofunctor.ObjectProperty`, Cat-valued pseudofunctor transport | `CategoryTheory/Bicategory/Functor/Cat/` | `CategoryTheory/Bicategory/Functor/Cat/` |
| `IsStack`, descent data | `CategoryTheory/Sites/Descent/` | `CategoryTheory/Sites/Descent/` |
| `PrimeSpectrum.basicOpen` | `RingTheory/Spectrum/Prime/` | `RingTheory/Spectrum/Prime/` |
| `Abelian (ModuleCat R)`, `Abelian X.Modules` | with `ModuleCat`, with `X.Modules` | with the object, never below the interface |

**Tier 2. A subject Mathlib lacks is placed by the nearest Mathlib
precedent.**

| Situation | Mathlib precedent | So it lives in |
| --- | --- | --- |
| A structure on an abstract triangulated category | `Triangulated/TStructure/`, `Subcategory`, `Orthogonal`, `Generators` | `CategoryTheory/Triangulated/<Name>/`: stability conditions, dg enhancements, K₀, Fourier--Mukai kernels, semiorthogonal decompositions, spherical twists, compact generation, families |
| A weakened or strengthened variant of a named concept | `Topology/MetricSpace/Pseudo/`, `Monoidal/Braided/`, `Monoidal/Closed/` | a child directory named by the adjective: `Triangulated/StabilityCondition/Weak/` |
| Compatibility between two independent structures | `Monoidal/Preadditive.lean`, `Monoidal/Linear.lean` | `CategoryTheory/Monoidal/Triangulated.lean` |
| A geometric realization of a categorical interface | `Algebra/Category/ModuleCat/Abelian.lean`, `AlgebraicGeometry/Modules/Sheaf.lean` | with the geometric object under `AlgebraicGeometry/`; the declaration may keep the interface's namespace for dot notation |
| A bespoke carrier built on a Mathlib API | definition site | beside that API: `DGCategory` on `HomComplex` is `Algebra/Homology/DGCategory/` |
| A theorem whose signature mentions a scheme | `AlgebraicGeometry/` | `AlgebraicGeometry/`, even when the proof is entirely categorical |

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
- A dg enhancement is a structure on an abstract triangulated category and
  lives in `CategoryTheory/Triangulated/DGEnhancement/`. Its realization for
  Mathlib's homotopy category lives with that object, in
  `Algebra/Homology/HomotopyCategory/DGEnhancement/`.
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

Observed twice on 2026-09-12. #1268 and #1272 each appeared to delete ~84 lines
across five `scripts/*Audit*/*.lean` files; after merging their base, each was a
single file with insertions only and no deletions anywhere. One of the
"deleted" files, `scripts/StabilityConditionAudit/ExpDivisorial.lean`, existed
on neither the branch nor its merge base -- the base created it after the fork.

This matters most for the audit record slices, because deleting a record is a
real defect and the artifact is indistinguishable from it by eye. Those slices
are NOT trust surface -- `trust-guard.yml` excludes
`scripts/AlgebraicGeometryAudit/` and `scripts/StabilityConditionAudit/`
deliberately, since guarding append-only record lists would fire the gate on
almost every pull request. They are protected instead by `check_audit.py` and
`check_audit_complete.py`, which run in `ci` and judge the merged tree, where
the artifact does not exist. So a phantom deletion cannot reach `main`; the cost
is a reviewer's time and a wrongly rejected pull request.

## The `trust-reviewed` label

`trust-guard.yml` fails any pull request touching `.github/`, `scripts/`
(minus the two audit-record directories above), `exe/`, `registry/`,
`DerivedAlgGeoSweep.lean`, `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `pins.json` or `LICENSE.md`, until a human adds the
`trust-reviewed` label.

The label asserts that a person read that diff. Never apply it to your own
change, and never apply it for someone else unless they have said they read it.
Adding it re-runs the check; `gh run rerun` does NOT, because the job reads the
label set from the event payload and a rerun replays the original, empty one --
and its `concurrency` group cancels the real `labeled` run. To re-fire the
check, remove the label and add it again.

After resolving a merge on a branch that already carries the label, check
whether the label still covers the diff -- over the guarded paths only, or the
phantom deletions above will make an unchanged diff look rewritten:

```bash
diff <(git diff <base> <old-head> -- <guarded paths>) \
     <(git diff <base> <new-head> -- <guarded paths>)
```

Identical or smaller means the reviewer approved a superset and the label
holds. Anything added means it no longer covers the diff: remove it and ask for
a fresh review.

## Required verification

**Full verification runs on the self-hosted Windows runners, not on your machine.**
`.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]`, and it triggers on `main` and `agent/**`. So
pushing already runs the whole gate there; to get a verdict without pushing, use

```bash
gh workflow run ci.yml --ref <branch>
```

**This is enforced, not advised.** A `PreToolUse` hook on `Bash`, wired in the
tracked `.claude/settings.json` so it reaches every worktree, runs
`scripts/check_local_build.py` and refuses two commands:

* `scripts/gates.sh`, in any mode;
* `lake build` with **no target**.

Advice was what this section used to give, and advice is what failed: on
2026-08-27 an agent read "the normal build stays local", ran a whole-library
`lake build` on a cold tree, and spent three hours of the developer's machine on
work the runners were idle and waiting to absorb.

`gates.sh` was already discouraged here for a second reason worth keeping: several
agent lanes share one Mac, Lake takes one core per job by default, and four
concurrent full gates oversubscribe a 14-core machine five times over — that is
how a ten-minute gate becomes an hour.

Neither the local script nor the runner lane is CI-equivalent on its own, and the
difference has bitten: every gate in `gates.sh` runs in CI, but CI also runs the
`mfc` contract tooling, which the script does not reproduce. Say "N gates pass",
not "CI is green". See `CONTRIBUTING.md`.

Build locally by **naming a target**, which the hook allows:

```bash
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
```

`LEAN_NUM_THREADS` is **required and enforced**, not advice: the same hook
refuses a `lake build` that does not set it, or that sets it above 4. Naming a
target bounds how much a build does; this bounds how wide it does it. Without
the variable Lake takes one `lean` process per core, which on this 16-core host
is up to 16 processes holding several GB each — from a build the size rule
deliberately permits.

It used to be advice, and on 2026-09-15 that failed exactly as the size rule had
in #837. The host reached ~60 concurrent `lean` processes across worktrees and
the four self-hosted runners; the commit limit collapsed to 2.9 GB free; CI
`build` jobs on five branches died with **no log and no step records** ("the
self-hosted runner lost communication"), `lean` died mid-build with
`std::bad_alloc` (exit code 3221226505), and `elan` failed to relink `lake.exe`
behind a crashed job's leftovers. None of those failures names memory in its
message, which is what made it expensive to diagnose.

`~/.claude/settings.json` exports the variable for every agent session, so a
plain `lake build <Target>` is normally already capped. The enforcement exists
for the shells that do not inherit it — which this file previously just warned
about. `scripts/test_local_build.sh` pins both edges.

### Seeding a new worktree's cache

A fresh worktree builds all ~5850 modules from cold before it reaches the file
you changed. It does not have to:

```bash
scripts/seed_worktree_cache.sh --dry-run   # pick a donor, say what it would do
scripts/seed_worktree_cache.sh             # copy it in
```

This copies `.lake/build` from the most-built worktree of this clone and links
`.lake/packages` to the shared dependency set, which a fresh worktree otherwise
lacks and nothing documents. Lake verifies every trace against the source it
finds, so anything your branch changes is still rebuilt and nothing stale is
trusted. Measured on 2026-09-15: 1556 modules seeded, after which a targeted
build completed 2069 jobs in 43 seconds.

It **copies rather than hardlinks**, and the script's header says why -- Lean
writes an `.olean` at its final path, so a hardlink would let a rebuild in one
worktree write through into another's cache. It therefore spends disk to save
commit, which is the right trade on this host and not a universal one.

The script only ever writes to the worktree you run it in, and refuses a target
that already has a build cache unless you pass `--force`.

`lake env lean scratch.lean` is **not** restricted and is not meant to be. It is
the seconds-long probe interactive proof work depends on; routing each attempt at
a lemma through CI would be a ~12 minute round trip and would stop anyone writing
a proof at all.

### The olean asymmetry, and why the rule still stands

Lean's `.olean` files are platform-specific, so the Windows runners can never warm
this checkout: a local build is the only way to get local oleans, and a targeted
build still compiles its dependencies. **After a cache loss, naming a target does
not make the cost go away.** That is the honest limit of this rule, and the answer
is not to quietly run the whole-library build anyway — it is to take the verdict
from the runners, which need no local oleans at all:

```bash
gh workflow run ci.yml --ref <branch>
```

When a local build genuinely cannot be avoided, `DAG_ALLOW_LOCAL_BUILD=1`
overrides the hook for one command. **Using it is a reportable event**: say so in
the pull request or the session report, because a whole-library local build is
precisely what this rule exists to keep off the developer's machine.

Useful focused commands are:

```bash
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
