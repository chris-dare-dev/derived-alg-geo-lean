# Working in DerivedAlgGeo

## Repository shape

This repository contains one public Lean library, `DerivedAlgGeo`. Its source
root is `DerivedAlgGeo/` and its all-library umbrella is `DerivedAlgGeo.lean`.
The layout mirrors Mathlib's subject hierarchy, directory for directory, so
that a file extending a Mathlib API sits where that API sits in Mathlib and an
upstream pull request is a copy, not a relocation.

| Directory | Mathlib counterpart | What lives here |
| --- | --- | --- |
| `Algebra/` | `Mathlib/Algebra/` | ring, module, polynomial, graded algebra, and exact sequences; `Algebra/Category/ModuleCat/Sheaf/` extends Mathlib's `SheafOfModules` on an arbitrary ringed site; `Algebra/Homology/` extends Mathlib's homological algebra: derived categories, homotopy categories, spectral sequences, and the bespoke dg category built on `HomComplex` |
| `AlgebraicGeometry/` | `Mathlib/AlgebraicGeometry/` | schemes and everything stated about them: `Modules/` (with its `Coherent/` and `Quasicoherent/` children), `ProjectiveSpectrum/`, `Cohomology/`, `DerivedCategory/`, `Divisors/`, `Duality/`, `IntersectionTheory/`, `Numerical/`, `RiemannRoch/`, `Moduli/`, `Stacks/`, `Surface/`, `Variety/` |
| `AlgebraicTopology/` | `Mathlib/AlgebraicTopology/` | simplicial constructions |
| `CategoryTheory/` | `Mathlib/CategoryTheory/` | abelian, bicategorical, limit, linear, localization, monoidal, preadditive, shift, and site theory; `Triangulated/` with its t-structures, stability conditions, dg enhancements, Grothendieck groups, Fourier--Mukai kernels, semiorthogonal decompositions, and compact generation |
| `LinearAlgebra/` | `Mathlib/LinearAlgebra/` | lattices, quadratic forms, exterior powers, graded bases |
| `RingTheory/` | `Mathlib/RingTheory/` | prime spectra |
| `Topology/` | `Mathlib/Topology/` | sheaves on topological spaces and the category of opens |
| `Development/` | none | probes intentionally excluded from the stable root |

Never add imports or namespaces rooted at `CohLean`, `DGLean`, or
`BridgelandStabLean`; those migration artifacts are retired. Lanes still in
flight toward this layout are listed under "Confirmed next lanes" in
`docs/architecture/cutover-ledger.md`; a path named there is the target even
before the move lands.

## The placement rule

Mathlib does not organize by abstraction level. It organizes by *definition
site*: a file lives where the carrier it is about is defined, and extensions
follow the definition. Two tiers.

**Tier 1. An extension of a Mathlib API lives at that API's Mathlib path,
under `DerivedAlgGeo/`, in that API's namespace.** Nothing else decides it:
not the abstraction level of the statement, not the weakest vocabulary in its
signature, not its motivation, its first consumer, or its proof technique.

| Concept | Mathlib defines it in | So it lives in |
| --- | --- | --- |
| `DerivedCategory C`, `Ext`, K-projectives, its t-structure, `Bounded` | `Algebra/Homology/DerivedCategory/` | `Algebra/Homology/DerivedCategory/` |
| `HomotopyCategory`, `HomComplex`, bounded and plus variants | `Algebra/Homology/HomotopyCategory/` | `Algebra/Homology/HomotopyCategory/` |
| `SheafOfModules`, `GeneratingSections`, `IsQuasicoherent`, presentations, invertibility | `Algebra/Category/ModuleCat/Sheaf/` | `Algebra/Category/ModuleCat/Sheaf/` |
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
  sits in `AlgebraicGeometry/DerivedCategory/FourierMukai/DerivedTensorCoherence.lean`
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
  `AlgebraicGeometry/DerivedCategory/{Coherent,Dqc,Families,FourierMukai,Stability}`,
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

The weakest-vocabulary signature test in `docs/architecture/placement.md` is
the tie-breaker within Tier 2, not the primary rule; it must not move an
extension of a Mathlib API away from that API's path.

## Dependency direction

Mathlib's subjects interleave: `Algebra/Homology` imports `CategoryTheory`,
and `CategoryTheory/Linear` imports `Algebra`. There is therefore no rank
order between subjects, and `scripts/check_layering.py` does not enforce one.
Lean enforces module acyclicity. The policy edges are exactly these.

- **Geometry firewall.** Only modules below `AlgebraicGeometry/` and
  `Development/` import `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`, and only they declare into the
  `AlgebraicGeometry` namespace. Everything else is usable without schemes.
- **`Development/` is a leaf.** No stable module imports it.
- **Stability-neutral geometry.** Modules below `AlgebraicGeometry/` outside
  `Moduli/`, `Numerical/`, and `DerivedCategory/Stability/` never reach the
  stability tree, even transitively. The `AlgebraicGeometry/DerivedCategory`
  umbrella therefore omits its `Stability` child; the top-level
  `AlgebraicGeometry` umbrella imports it. This is what keeps `Dᵇ(Coh X)`,
  `Dqc`, coherent sheaves, and cohomology importable without Bridgeland
  stability.
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
pullback; `FourierMukai/` owns neutral kernels and convolution; `Stability/`
owns the three consumers that need stability conditions.

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

Every non-leaf directory has a same-named umbrella that re-exports its direct
children. Two umbrellas deliberately omit a child, and
`scripts/check_umbrella_coverage.py` knows both: the weak stability umbrella
omits the Bridgeland child, and `AlgebraicGeometry/DerivedCategory.lean` omits
`Stability`. A module that shares a name with a directory of its consequences
is not an umbrella and is left alone. A structural move updates imports,
umbrellas, audits, declaration-sweep routing, documentation, the layering
gate, and CI paths together.

## Editing rules

- Prefer the narrowest import and the nearest umbrella.
- Before editing public API, apply the two-tier rule above and the decision
  table in `docs/architecture/placement.md`.
- Use Mathlib's namespace for extensions of an existing Mathlib API.
- Before introducing a public structure, class, quotient carrier, or
  category, follow `docs/architecture/abstraction-tree.md`: reuse one
  canonical root and make specializations reach it by an instance,
  projection, abbreviation, or proved comparison.
- If a file contains a generic block followed by its geometric use, split at
  the first declaration whose signature no longer needs the geometry. If the
  block is not moved in the current slice, record it in
  `docs/architecture/cutover-ledger.md` and do not extend it in place.
- Preserve explicit trust boundaries; do not use `sorry`, `admit`, or a
  hidden axiom to cross an unfinished mathematical seam.
- Add every new public declaration to the relevant audit.
- Do not edit generated build artifacts by hand.
- Do not alter unrelated work in a dirty tree.

Read `CONTRIBUTING.md` before creating a new directory or publishing a
change; it owns the human-facing placement and contribution rules.

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

`LEAN_NUM_THREADS=2` limits Lake to two concurrent `lean` processes; without it
Lake takes one per core. It is set for every agent session in
`~/.claude/settings.json`, so a plain `lake build <Target>` is already capped —
set it explicitly if you are building from a shell that does not inherit that.

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
