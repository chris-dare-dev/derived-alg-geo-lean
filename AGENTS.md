# Working in DerivedAlgGeo

## Structural ownership

Organize stable code by its most general mathematical construction, not by the
first application that motivated it.

- Put statements about arbitrary categories, functors, abelian categories,
  triangulated categories, or enriched categories under `CategoryTheory/`.
- Put definitions and geometric lemmas that intrinsically mention schemes,
  varieties, sheaves, or geometric morphism properties under
  `AlgebraicGeometry/`.
- Put a concrete realization of a generic categorical interface in an explicit
  `Instances/AlgebraicGeometry/` leaf below the generic construction. These
  bridge leaves may import both subjects; generic siblings and their umbrellas
  must not import bridge leaves.
- Generic stacks in groupoids and descent-equivalence data belong under
  `CategoryTheory/Sites/` and use the `CategoryTheory` namespace. Scheme-level
  representability, atlases, and algebraicity remain under
  `AlgebraicGeometry/Stacks/`.
- A category or locus intrinsically defined from a scheme remains a geometric
  object. Put scheme-derived categories, `Dqc`, and their geometric pullback
  machinery under `AlgebraicGeometry/DerivedCategory/`; reserve an
  `Instances/AlgebraicGeometry/` leaf for registration or comparison adapters
  whose parent generic interface is the primary object being realized.
- Express refinement in the import tree from weak to strong. A stronger theory
  imports its weaker parent and supplies a projection or constructor in Lean;
  directory nesting alone is not a substitute for the type-level relationship.

The intended pattern is:

```text
CategoryTheory/<generic construction>/
  Basic.lean
  ...
  Instances/AlgebraicGeometry/<concrete realization>.lean
```

Do not create a second implementation of a categorical construction below
`AlgebraicGeometry/`. For example, prove that `Coh X` is abelian, then use the
single generic `DerivedCategory (Coh X)` construction. A geometric module may
provide notation, instances, or comparison theorems, but it must not present a
new derived-category theory.

## Monoidal, derived, dg, and triangulated categories

- Generic monoidal structures, monoidal functors, and tensor coherence belong
  under `CategoryTheory/Monoidal/`.
- Enrichment is relative to a monoidal base category. Thus the conceptual
  dependency is `Monoidal V -> V-enriched categories`; dg categories are the
  specialization in which `V` is a category of cochain complexes.
- Monoidal and triangulated structures are independent. Do not make either a
  superclass of the other. Their exact-tensor compatibility belongs under
  `CategoryTheory/Monoidal/Triangulated/`.
- A monoidal dg category is an optional refinement of a raw dg category and
  belongs under `CategoryTheory/Enriched/DGCategory/Monoidal/`. Compatibility
  of its induced monoidal structure on triangulated `H⁰` belongs under
  `CategoryTheory/Triangulated/DGEnhancement/Monoidal/`.
- A tensor bifunctor alone is weaker than a monoidal category. Require
  associators, unitors, and coherence only when a consumer actually needs
  them, and expose a one-way forgetful map to the weaker tensor interface.

- The derived category is a generic construction on an abelian category and
  belongs under `CategoryTheory/Triangulated/DerivedCategory/`, together with
  its canonical t-structure, exact-functor, homology-comparison, and
  K-projective APIs.
- `Coh X`, `QCoh X`, and module-sheaf categories are geometric inputs. Their
  scheme-specific categories and loci belong under
  `AlgebraicGeometry/DerivedCategory/`; registration-only adapters for generic
  categorical interfaces may live in explicit `Instances/AlgebraicGeometry/`
  leaves.
- Raw dg categories are categories enriched over cochain complexes. They live
  under `CategoryTheory/Enriched/DGCategory/` and are not assumed to be
  triangulated.
- A pretriangulated dg category is a dg category with zero objects, shifts, and
  cones. Its internal dg machinery remains under
  `CategoryTheory/Enriched/DGCategory/Pretriangulated/`.
- A dg enhancement is additional structure on a triangulated category: a
  pretriangulated dg category together with an equivalence from its `H⁰`.
  The passage to the triangulated `H⁰`, enhancement interfaces, and their
  models live under `CategoryTheory/Triangulated/DGEnhancement/`.
- The dg category of complexes enhances the homotopy category. Do not call it
  an enhancement of a derived category until a dg localization or a suitable
  projective/injective model and the required equivalence have been proved.
- A monoidal construction on invertible sheaves, coherent sheaves, or
  `Dᵇ(Coh X)` remains geometric when its statement intrinsically mentions
  `X`; it should realize the generic monoidal or tensor--triangulated interface
  rather than moving the geometric objects themselves into category theory.

## Stability conditions and geometric applications

- Pure weak-stability theory belongs under
  `CategoryTheory/Triangulated/WeakStabilityCondition/`. Ordinary Bridgeland
  stability is its stronger child under
  `WeakStabilityCondition/StabilityCondition/`; do not restore a sibling
  `CategoryTheory/Triangulated/StabilityCondition/` tree.
- The weak parent must not import its Bridgeland child. Strong conditions must
  extend or canonically contain their weak data. Do not add a parallel
  `WeakCompatibility/` adapter leaf for a relationship already expressed by
  the structure projection.
- Abstract pullback, pseudofunctor, Fourier--Mukai correspondence, and kernel
  convolution interfaces stay categorical. Scheme pullback, geometric
  derived categories, `Dqc`, pullback constructions, and geometric kernels live
  under `AlgebraicGeometry/DerivedCategory/`. Registration-only realizations may
  go in a corresponding `Instances/AlgebraicGeometry/` leaf. In particular,
  the base category, fiber categories, and abstract pullback functors of a
  triangulated family belong under `CategoryTheory/Triangulated/Families/`
  before any stability or geometry is imposed.
- Generic stacks, discrete-stack construction from a sheaf, stack morphisms,
  and site-object representability belong under
  `CategoryTheory/Sites/StackInGroupoids/`. Big-Zariski representables,
  scheme-morphism properties, atlases, and algebraicity remain under
  `AlgebraicGeometry/Stacks/`.
- Declarations owned by that generic family root use the
  `CategoryTheory.Triangulated.Families` namespace. Do not place
  `TriangulatedFiberFamily`, shared boundedness interfaces, or future neutral
  family APIs below a stability-condition namespace.
- Scheme-derived category declarations owned by
  `AlgebraicGeometry/DerivedCategory/Basic.lean` use the
  `AlgebraicGeometry.DerivedCategory` namespace. Scheme base-change and
  pullback declarations owned by `AlgebraicGeometry/DerivedCategory/Families/`
  use `AlgebraicGeometry.DerivedCategory.Families`. Do not place these neutral
  geometric APIs below a categorical stability-condition namespace.
- Quasicoherent-cohomology loci and affine `Dqc` realizations owned by
  `AlgebraicGeometry/DerivedCategory/Dqc.lean` and its `Dqc/` subtree use
  `AlgebraicGeometry.DerivedCategory.Dqc`. Consumers should open or qualify
  that namespace explicitly; do not route `Dqc` declarations through a
  stability-family namespace.
- Neutral geometric Fourier--Mukai declarations owned by
  `AlgebraicGeometry/DerivedCategory/FourierMukai/` use
  `AlgebraicGeometry.DerivedCategory.FourierMukai`. Generic kernel
  autoequivalences belong under `CategoryTheory/Triangulated/FourierMukai/`;
  their Bridgeland action belongs under the strong stability child's
  `Symmetry/Autoequivalence/` subtree, with scheme-specific action adapters in
  its `Instances/AlgebraicGeometry/` leaf.
- Declarations owned by weak-stability families use
  `CategoryTheory.Triangulated.WeakStabilityCondition.Families`. Shared
  Definition 20.5 probes and APIs bound to `WeakStabilityFunction` belong to
  that weak parent, not to the Bridgeland family's declaration namespace.
- Generic numerical support predicates and the weak-stability structures that
  consume them use
  `CategoryTheory.Triangulated.WeakStabilityCondition.Support`. Do not restore
  the former strong-sibling
  `CategoryTheory.Triangulated.StabilityCondition.Support` namespace.
- The finite-length simple-charge lattice model extends the weak
  stability-function foundation. Keep it under
  `WeakStabilityCondition/Foundation/StabilityFunction/` with namespace
  `CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength`; do not
  restore the duplicate plural `Foundations/` tree or its former strong
  namespace.
- Declarations owned by ordinary Bridgeland families use
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
  Strong family packages and pre-stability base-change data belong to that
  child; geometry-owned realizations remain separate consumers.
- Bridgeland wall theory under the strong child's `Walls/` subtree uses
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`;
  do not restore the former sibling `CategoryTheory.Triangulated.StabilityCondition.Wall`
  namespace.
- Generic kernel autoequivalences and the Bridgeland-action extensions under
  the strong child's `Symmetry/` subtree use the canonical
  `CategoryTheory.Triangulated.FourierMukai` namespace. Do not qualify them
  through either stability `Symmetry` namespace; the former sibling
  `CategoryTheory.Triangulated.StabilityCondition.Symmetry` namespace remains
  retired.
- Group actions on slicings, pre-stability conditions, and Bridgeland stability
  conditions use
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
  Do not restore the former sibling
  `CategoryTheory.Triangulated.StabilityCondition.GroupAction` namespace. The
  public compatibility aliases have been retired. Historical names embedded in
  immutable review payloads are confined to the executable-only
  `exe/RestateHistoricalNames.lean` bridge; no library module may import it
  or redeclare those names.
- Do not recreate the retired import-only shims under
  `Divisors/{Tensor,Picard,Monoidal}.lean`, `Stacks/Basic.lean`, or
  `Compatibility/StabilityConditionFamilies.lean`, and do not restore the
  `DerivedAlgGeo.Compatibility` umbrella. Consumers import the categorical or
  geometric owner directly.
- Helpers intrinsically about deforming a Bridgeland stability condition use
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation`.
  Do not restore the flattened `CategoryTheory.Triangulated.Deformation`
  namespace. A declaration extending a canonical structure such as `Slicing`,
  `PreStabilityCondition.WithClassMap`, or `StabilityCondition.WithClassMap`
  remains in that structure's established namespace; physical placement in the
  deformation subtree does not override API ownership.
- Generic moduli boundedness interfaces shared by weak stability and geometric
  moduli also belong under `CategoryTheory/Triangulated/Families/`; neither
  consumer owns the common root.
- Do not restore the retired `AlgebraicGeometry/StabilityCondition/` subtree or
  `AlgebraicGeometry.StabilityCondition` namespace. Put actual semistable loci
  and relative HN filtrations under
  `AlgebraicGeometry/Moduli/{Semistability,HarderNarasimhan}/`; attach their
  weak- or Bridgeland-family realizations to the relevant categorical source in
  `Instances/AlgebraicGeometry/`.
- Geometric source modules must not import `Instances/AlgebraicGeometry`
  leaves. Instance bridges may import both category theory and geometry, and
  their declarations may use the geometric namespace when they extend a
  geometric object. Their physical path records the categorical interface
  implemented; generic umbrellas must remain independent of every bridge.
- General Mumford slope data belongs with weak geometric stability. A module
  constructing a Bridgeland stability condition from it belongs below the
  Bridgeland child only under the hypotheses where that construction is valid,
  such as the appropriate curve case; intrinsically scheme-specific input
  remains an algebraic-geometric instance or realization.

## Umbrellas and dependency direction

- Prefer the narrowest useful import and provide a same-named umbrella for
  every non-leaf directory.
- Generic umbrellas must export only generic theory. `Instances/` umbrellas
  are separate opt-in leaves; the public repository root may import both.
- Keep the Lean module graph acyclic at file level. Do not enforce a coarse
  top-level subject rule that misclassifies an explicit `Instances/` bridge as
  generic category theory.
- Preserve established declaration namespaces during a path-only migration
  unless a namespace change is separately justified.
- A separately justified namespace cutover must update every stable consumer,
  audit record, declaration baseline, compatibility note, and regression gate
  in the same change; do not leave parallel canonical names behind.

Structural changes must update imports, umbrellas, audits, declaration-sweep
routing, documentation, architecture checks, and CI paths in the same change.
Build changed modules with explicit targets locally. Full verification belongs
on the self-hosted Windows runners: pushing an `agent/**` branch triggers it.
Do not run targetless `lake build` or `scripts/gates.sh` locally; see
`CLAUDE.md` and `CONTRIBUTING.md` for the enforced runner-first workflow.

## General editing rules

- Stable library code lives below `DerivedAlgGeo/`; exploratory code belongs
  in `DerivedAlgGeo/Development/`.
- Use Mathlib's namespace when extending a Mathlib concept.
- Do not use `sorry`, `admit`, or hidden axioms.
- Preserve unrelated user changes in a dirty worktree.
- Never restore the retired `CohLean`, `DGLean`, or `BridgelandStabLean`
  module roots.

Read `CONTRIBUTING.md` and `docs/architecture/layers.md` for the human-facing
workflow and the current dependency graph.
