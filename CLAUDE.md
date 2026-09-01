# Working in DerivedAlgGeo

## Repository shape

This repository contains one public Lean library: `DerivedAlgGeo`. Its source
root is `DerivedAlgGeo/` and its all-library umbrella is `DerivedAlgGeo.lean`.
The layout follows Mathlib's subject hierarchy.

The principal areas are:

- `DerivedAlgGeo/AlgebraicGeometry/` for coherent sheaves, cohomology,
  divisors, duality, intersection theory, numerical geometry, and
  Riemann--Roch;
- `DerivedAlgGeo/Algebra/` for ordinary ring and module theory independent of
  sites and schemes, including localization and its kernel behavior under
  `Algebra/Module/Localization/`;
- `DerivedAlgGeo/CategoryTheory/Abelian/` for repository-owned results about
  arbitrary abelian categories, extending Mathlib's abelian hierarchy;
- `DerivedAlgGeo/CategoryTheory/Bicategory/` for higher-categorical
  adjunctions, adjoint equivalences, mates, and their specialization to `Cat`;
- `DerivedAlgGeo/CategoryTheory/Limits/` for generic limit and colimit
  infrastructure, including preservation and reflective transport;
- `DerivedAlgGeo/CategoryTheory/Sites/Sheaves/` for generic sheaf theory,
  including module sheaves on an arbitrary ringed site;
- `DerivedAlgGeo/CategoryTheory/Moduli/` for neutral moduli predicates such as
  boundedness;
- `DerivedAlgGeo/CategoryTheory/Pseudofunctor/ObjectProperty/` for generic
  replete loci and subprestack machinery;
- `DerivedAlgGeo/CategoryTheory/Monoidal/` for generic monoidal coherence and
  compatibility interfaces;
- `DerivedAlgGeo/CategoryTheory/Enriched/DGCategory/` for raw dg categories
  and their internal pretriangulated structure;
- `DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/` for the
  triangulated `H⁰` of a pretriangulated dg category and dg enhancements;
- `DerivedAlgGeo/CategoryTheory/Triangulated/TStructure/` for t-structures;
- `DerivedAlgGeo/CategoryTheory/Triangulated/Families/` for generic
  contravariant families of triangulated categories and pullback functors;
- `DerivedAlgGeo/CategoryTheory/Triangulated/WeakStabilityCondition/` for weak
  stability, generic stability functions, and shared slicing prerequisites;
- `DerivedAlgGeo/CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/` for
  the stronger Bridgeland refinement and its categorical applications;
- `DerivedAlgGeo/LinearAlgebra/` for lattice and matrix prerequisites;
- `DerivedAlgGeo/Development/` for code intentionally excluded from the stable
  root.

Never add imports or namespaces rooted at `CohLean`, `DGLean`, or
`BridgelandStabLean`; those migration artifacts are retired.

## Structural ownership principles

Organize code by its most general mathematical construction, then attach
concrete applications through explicit instance leaves.

- Ordinary ring and module theory that mentions no site or scheme belongs
  under `Algebra/`.
- Arbitrary categorical, functorial, abelian, triangulated, enriched,
  site-theoretic, or sheaf-theoretic statements belong under
  `CategoryTheory/`. Reuse Mathlib's `CategoryTheory.Abelian` class and put
  only missing generic results below `CategoryTheory/Abelian/`.
- Higher-categorical work begins with Mathlib's `CategoryTheory.Bicategory`.
  Its `Bicategory.Adjunction` is the source-of-truth; ordinary adjoint functors
  are the `Cat` specialization through `Adjunction.toCat` and `ofCat`, bundled
  here by `Adjunction.bicategoricalEquiv`.
- Determine categorical dimension before subject ownership. Associators,
  unitors, pentagons, triangles, mates, pseudofunctors, strong
  transformations, and modifications are higher-categorical source data;
  their ordinary functor and natural-isomorphism formulas are `Cat`
  projections. Objectwise-equivalence transport of such a presentation is
  owned by `CategoryTheory/Pseudofunctor/Transport.lean`, never by a geometric
  consumer.
- Generic sheaves belong under `CategoryTheory/Sites/Sheaves/`; sheaves of
  modules over a sheaf of rings on an arbitrary site belong in its `Modules/`
  child.
- Definitions and lemmas that intrinsically mention schemes, varieties,
  scheme-indexed sheaf categories, or geometric morphism properties belong
  under `AlgebraicGeometry/`.
- Generic stacks in groupoids and their descent-equivalence interface belong
  under `CategoryTheory/Sites/` and use the `CategoryTheory` namespace;
  scheme-specific representability and presentations remain geometric.
- A geometric realization of a generic categorical interface belongs under
  `CategoryTheory/<construction>/Instances/AlgebraicGeometry/`. Such a bridge
  leaf may import geometry, but generic siblings and generic umbrellas must
  never import it.
- Stronger theories import weaker theories and expose the relationship in
  Lean through a projection or constructor. Directory nesting is not a
  replacement for the actual type-level refinement.

In particular, derived-category theory is generic. Prove `[Abelian (Coh X)]`
under the correct geometric hypotheses and then use
`DerivedCategory (Coh X)`; do not build a second derived-category theory under
algebraic geometry. Generic t-structure, exact-functor, homology-comparison,
and K-projective results live under
`CategoryTheory/Triangulated/DerivedCategory/`. `Dqc(X)` may be represented by
the quasicoherent-cohomology locus until the abelian `QCoh X` construction and
its derived comparison are available, but this is a geometric specialization
of the generic theory and lives under `AlgebraicGeometry/DerivedCategory/`,
not below stability. Use an
`Instances/AlgebraicGeometry/` leaf for registration-only adapters whose
generic categorical interface is the primary owner.

The opposite comparison `(DerivedCategory C)ᵒᵖ ≃ DerivedCategory Cᵒᵖ` is
generic derived-category data and belongs in
`CategoryTheory/Triangulated/DerivedCategory/Opposite.lean`. Exact algebraic
linear duality and its derived lift belong in the adjacent `LinearDual.lean`
specialization. Geometric Serre or Grothendieck duality imports those roots and
`AlgebraicGeometry/DerivedCategory/Coherent.lean`; it does not own replacement
localizations for coherent sheaves or modules.

The geometric specialization chain is `SheafOfModules(X) -> QCoh(X) ->
Coh(X)`. Its scheme-owned source tree is
`AlgebraicGeometry/SheafOfModules/QuasicoherentSheaf/CoherentSheaf/` as the
staged cutover reaches those APIs. The fact that `Coh(X)` is abelian is a
geometric instance; the derived-category construction it unlocks remains the
single generic construction under category theory.

The same ownership rule applies to cohomological infrastructure. Generic
`Ext` adjunction, dimension shift, and injective-resolution naturality live
under `CategoryTheory/Triangulated/DerivedCategory/Ext/`; filtered-complex and
total-complex spectral sequences live under `CategoryTheory/SpectralSequence/`;
and site-theoretic Čech constructions, injective comparisons, compact-basis
arguments, and finite-cover boundedness live under
`CategoryTheory/Sites/Cech/`. Geometric cohomology modules consume these roots
and add affine, scheme, and projective-space input.

An adjunction hypothesis does not by itself make a theorem part of the
adjunction foundation. Results whose conclusion is preservation of limits or
colimits live under `CategoryTheory/Limits/`; generic `Ext` adjunctions remain
with derived `Ext`, and Fourier--Mukai adjunction packages remain with their
kernel consumers. The repository currently formalizes the higher-categorical
spine through bicategories. Introduce general `n`-category or
`(∞,1)`-category roots only when an actual reusable formal model is added, not
as placeholder directories.

Monoidal structure precedes enrichment in the dependency graph: a
`V`-enriched category is defined relative to a monoidal category `V`, and a dg
category specializes this pattern to cochain complexes. Monoidal and
triangulated structures are otherwise independent, so neither is a superclass
of the other. Put their compatibility under
`CategoryTheory/Monoidal/Triangulated/`; put an optional monoidal refinement of
a dg category under `CategoryTheory/Enriched/DGCategory/Monoidal/`, and put
the induced monoidal structure on triangulated `H⁰` under
`CategoryTheory/Triangulated/DGEnhancement/Monoidal/`.

A bare tensor bifunctor is weaker than a coherent monoidal structure. Add
associators, unitors, and coherence only at the stronger layer and provide a
one-way forgetful adapter. Tensor products on sheaves and `Dᵇ(Coh X)` remain
geometric inputs; they should instantiate the generic categorical interface.

Raw dg categories are enriched categories, not automatically triangulated
categories. A pretriangulated dg category has the zero objects, shifts, and
cones needed for its `H⁰` to be triangulated. Consequently:

- raw dg and pretriangulated-dg internals live under
  `CategoryTheory/Enriched/DGCategory/`;
- the `H⁰` triangulation, dg-enhancement interface, and enhancement models
  live under `CategoryTheory/Triangulated/DGEnhancement/`;
- a dg category of complexes enhances the homotopy category, not the derived
  category, until the relevant dg localization or resolution model is proved.

Pure weak and Bridgeland stability theory remains categorical. Weak stability
is the independently importable dependency parent at
`CategoryTheory/Triangulated/WeakStabilityCondition/`; ordinary Bridgeland
stability is its child at `WeakStabilityCondition/StabilityCondition/`. Never
restore a sibling `CategoryTheory/Triangulated/StabilityCondition/` tree, and
make ordinary prestability structurally expose its weak parent. Do not add a
`WeakCompatibility/` leaf for data already provided by that projection.
Abstract pullback, pseudofunctor, and Fourier--Mukai interfaces remain
categorical. Scheme-derived categories, `Dqc`, geometric pullback, and kernel
convolution live under `AlgebraicGeometry/DerivedCategory/`; only
registration-only adapters belong in explicit `Instances/AlgebraicGeometry/`
leaves. General Mumford slope data is
weak-stability input, while a promotion to Bridgeland stability belongs below
the strong child only under hypotheses where that promotion is valid.
Scheme-specific data remains geometry-owned and realizes the categorical
interface through an explicit bridge.

Likewise, generic stack-in-groupoids construction, discrete stacks from
sheaves, stack morphisms, and site-object representability live under
`CategoryTheory/Sites/StackInGroupoids/`. Big-Zariski representable stacks and
geometric properties of their representing morphisms remain under
`AlgebraicGeometry/Stacks/`.

Match declaration namespaces to those geometric owners. Scheme-derived
category declarations in
`AlgebraicGeometry/DerivedCategory/{Basic,Coherent}.lean` use
`AlgebraicGeometry.DerivedCategory`: `Basic.lean` owns the module-sheaf
specialization, while `Coherent.lean` owns `D(Coh X)`, `Dᵇ(Coh X)`, and
`Perf(X)` independently of families and pullback. Scheme base-change and
pullback declarations in `AlgebraicGeometry/DerivedCategory/Families/` use
`AlgebraicGeometry.DerivedCategory.Families`; quasicoherent-cohomology loci
and affine realizations in `AlgebraicGeometry/DerivedCategory/Dqc.lean` and
its `Dqc/` subtree use `AlgebraicGeometry.DerivedCategory.Dqc`; neutral
geometric kernel declarations in `AlgebraicGeometry/DerivedCategory/FourierMukai/`
use `AlgebraicGeometry.DerivedCategory.FourierMukai`. Do not retain neutral
geometric declarations in a categorical stability-condition namespace merely
for source compatibility.

The former `AlgebraicGeometry/StabilityCondition/` subtree and
`AlgebraicGeometry.StabilityCondition` namespace are retired. Keep actual
semistable loci and relative HN filtrations under
`AlgebraicGeometry/Moduli/{Semistability,HarderNarasimhan}/`; keep neutral
Fourier--Mukai kernels under `AlgebraicGeometry/DerivedCategory/FourierMukai/`.
Attach the declarations that implement a weak- or Bridgeland-stability
interface to that categorical source through its explicit
`Instances/AlgebraicGeometry/` leaf. Geometric source modules must not import
those leaves, so the direction remains categorical source plus geometry into
the instance bridge.

The generic kernel-autoequivalence source lives under
`CategoryTheory/Triangulated/FourierMukai/`. Its action on Bridgeland stability
belongs under the strong stability child's `Symmetry/Autoequivalence/`
subtree, and its scheme-specific action adapter belongs in that source's
`Instances/AlgebraicGeometry/` leaf. A bridge may extend either its categorical
source namespace or the namespace of the geometric object it realizes; its
physical path records which interface it implements.

The generic family root also owns its declaration namespace:
`TriangulatedFiberFamily` belongs to
`CategoryTheory.Triangulated.Families`. Its source is a Cat-valued
pseudofunctor on `LocallyDiscrete Bᵒᵖ`; an ordinary strict functor enters only
through `TriangulatedFiberFamily.ofFunctor`. Neutral moduli boundedness is
more general still: `BoundednessProblem` and `UniversalBoundedness` belong to
`CategoryTheory.Moduli`, not to triangulated or stability families. Namespace
migrations are separate from path moves and must update consumers, audits,
baselines, documentation, and enforcement together.

Mathlib's `Pseudofunctor.ObjectProperty` is the canonical fiberwise locus for
a Cat-valued pseudofunctor. Closure under isomorphisms makes the locus replete;
closure under mapped objects makes it restriction-stable; `fullsubcategory`
constructs the corresponding subprestack. Repository extensions live under
`CategoryTheory/Pseudofunctor/ObjectProperty/`. Do not add a competing
`Subprestack` carrier below algebraic geometry.

The geometric `RelativePerfectModuliSelector` is only a pair of indexed
replete loci, named `familyLocus` and `geometricLocus`. It is valid input to a
finite-type boundedness witness but is not a subfunctor or subprestack. The
affine relative-perfect pseudofunctor applies the generic `universallyStable`
construction and then Mathlib's `fullsubcategory`; use that pattern whenever
restriction stability has actually been established.

The weak family root follows the same rule. Shared family probes and APIs bound
to `WeakStabilityFunction` use
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`; the stronger
Bridgeland child consumes them instead of owning them.

Generic numerical support predicates and their weak-stability bindings use
`CategoryTheory.Triangulated.WeakStabilityCondition.Support`. Do not qualify
them through the former strong-sibling
`CategoryTheory.Triangulated.StabilityCondition.Support` namespace.

The finite-length simple-charge lattice model belongs to the weak
stability-function foundation under
`WeakStabilityCondition/Foundation/StabilityFunction/` and uses
`CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength`. Do not
recreate the duplicate plural `WeakStabilityCondition/Foundations/` tree.

Ordinary Bridgeland family packages use the matching child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
Geometric realizations consume that API but keep geometry-owned declarations
separate.

Bridgeland wall declarations likewise use the matching strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`,
not the former sibling `CategoryTheory.Triangulated.StabilityCondition.Wall`.

Generic kernel autoequivalences and their Bridgeland-action extensions use the
canonical `CategoryTheory.Triangulated.FourierMukai` namespace even though the
strong-dependent implementation lives in the stability child's `Symmetry/`
subtree. Do not route these declarations through either stability `Symmetry`
namespace; the former sibling
`CategoryTheory.Triangulated.StabilityCondition.Symmetry` remains retired.

Group actions on slicings, pre-stability conditions, and Bridgeland stability
conditions use the matching strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`,
not the former sibling
`CategoryTheory.Triangulated.StabilityCondition.GroupAction`. Public aliases in
that retired namespace are forbidden. The executable-only
`exe/RestateHistoricalNames.lean` bridge carries the historical names
needed to elaborate immutable human-review payloads; library modules must not
import it or redeclare those names.

The staged import-only shims at `Divisors/{Tensor,Picard,Monoidal}.lean`,
`Stacks/Basic.lean`, and `Compatibility/StabilityConditionFamilies.lean` are
retired. Import the categorical or geometric owner directly; do not recreate a
compatibility path that mixes owners or restore the `DerivedAlgGeo.Compatibility`
umbrella.

Helpers intrinsically about deforming a Bridgeland stability condition use
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation`,
not the retired flattened `CategoryTheory.Triangulated.Deformation` namespace.
Declarations that extend canonical structures such as `Slicing`,
`PreStabilityCondition.WithClassMap`, or `StabilityCondition.WithClassMap`
remain in those structures' established namespaces even when their source
files live in the deformation subtree.

Every non-leaf directory needs a same-named umbrella. Generic umbrellas export
generic theory only; `Instances/` umbrellas remain opt-in leaves. A structural
move must update imports, umbrellas, audits, declaration-sweep routing,
documentation, architecture checks, and CI paths together.

## Editing rules

- Prefer the narrowest import and the nearest umbrella.
- Before editing public API, apply the declaration-signature decision table in
  `docs/architecture/placement.md`. Motivation, filename, namespace, and proof
  technique are not ownership evidence.
- Ring/module/localization declarations with no site belong to `Algebra/`;
  linear-map, basis, lattice, matrix, multilinear, and exterior-power
  declarations with no site belong to `LinearAlgebra/`.
- Weighted-basis submodules and their internal direct-sum proofs use
  `LinearAlgebra/GradedBasis.lean`; numerical intersection-ring assembly
  consumes them from algebraic geometry.
- Pure `Finsupp` and `MvPolynomial.divMonomial` identities use
  `Algebra/MvPolynomial/DivMonomial.lean`, even when their first application is
  a projective Čech calculation. Polynomial generation over the degree-zero
  grading uses `Algebra/MvPolynomial/Grading.lean`, and a canonical `p / 1`
  variable-localization element uses `Algebra/MvPolynomial/Cech/Basic.lean`.
- Generic internally graded-module localization and shift APIs use
  `Algebra/Module/GradedModule/` and the `GradedModule` namespace. Laurent
  exponent arithmetic uses `Algebra/Finsupp/`; polynomial Laurent-basis,
  projection, block, one-localization homotopy, and full-block finiteness APIs
  use `Algebra/MvPolynomial/`. The polynomial-variable Čech diagram and its
  homotopy, primitive, and finite-block algebra use
  `Algebra/MvPolynomial/Cech/`; only comparison with projective basic opens,
  sections, and cohomology remains geometric. Do not restore the former Proj
  foundation paths or make algebra import a geometric consumer.
- Inspect the surrounding consumer file for adjacent generic declarations. If
  an identified block is not moved in the current slice, record it in
  `docs/architecture/cutover-ledger.md` and do not extend it in place.
- Before introducing a public structure, class, quotient carrier, or category,
  follow `docs/architecture/abstraction-tree.md`: reuse one canonical root and
  make specializations reach it by an instance, projection, abbreviation, or
  proved comparison.
- Use Mathlib's namespace for extensions of an existing Mathlib API.
- Keep generic layers independent of specialized geometric applications.
- Preserve explicit trust boundaries; do not use `sorry`, `admit`, or a hidden
  axiom to cross an unfinished mathematical seam.
- Do not edit generated build artifacts by hand.
- Do not alter unrelated work in a dirty tree.

Read `CONTRIBUTING.md` before creating a new directory or publishing a
change; it owns the human-facing placement and contribution rules.

## Required verification

**Full verification runs on the self-hosted Windows runners, not on your machine.**
`.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]`, and it triggers on `agent/**`. So pushing an agent
branch already runs the whole gate there; to get a verdict without pushing, use

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
python3 scripts/check_coverage_map.py
```

New public declarations must be added to the relevant audit. The declaration
sweep in `scripts/EnumDecls.lean` and
`scripts/check_audit_complete.py` guards the opposite direction, so renames
must update both the source declaration and its audit record.

`DerivedAlgGeoSweep.lean` is verification-only. It imports the stable root and
development probes for full emitter coverage; do not treat it as a public
package boundary.
