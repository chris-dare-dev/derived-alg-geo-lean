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
  belongs under `CategoryTheory/Abelian/DerivedCategory/`.
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
  canonically expose their weak data; adapters that require strong definitions
  belong in the child's `WeakCompatibility/` leaf.
- Abstract pullback, pseudofunctor, Fourier--Mukai correspondence, and kernel
  convolution interfaces stay categorical. Scheme pullback, geometric
  derived categories, `Dqc`, pullback constructions, and geometric kernels live
  under `AlgebraicGeometry/DerivedCategory/`. Registration-only realizations may
  go in a corresponding `Instances/AlgebraicGeometry/` leaf. In particular,
  the base category, fiber categories, and abstract pullback functors of a
  triangulated family belong under `CategoryTheory/Triangulated/Families/`
  before any stability or geometry is imposed.
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
  `AlgebraicGeometry.DerivedCategory.FourierMukai`. Keep only kernel actions
  that consume stability-condition data under
  `AlgebraicGeometry/StabilityCondition/FourierMukai/`.
- Declarations owned by weak-stability families use
  `CategoryTheory.Triangulated.WeakStabilityCondition.Families`. Shared
  Definition 20.5 probes and APIs bound to `WeakStabilityFunction` belong to
  that weak parent, not to the Bridgeland family's declaration namespace.
- Declarations owned by ordinary Bridgeland families use
  `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
  Strong family packages and pre-stability base-change data belong to that
  child; geometry-owned realizations remain separate consumers.
- Generic moduli boundedness interfaces shared by weak stability and geometric
  moduli also belong under `CategoryTheory/Triangulated/Families/`; neither
  consumer owns the common root.
- `AlgebraicGeometry/StabilityCondition/` may contain only constructions that
  actually depend on weak or Bridgeland stability data. Scheme semistable loci,
  relative HN data, and stability-specific Fourier--Mukai actions belong there;
  neutral derived pullback, `Dqc`, and kernel convolution do not.
- Declarations below `AlgebraicGeometry/StabilityCondition/Families/` use
  `AlgebraicGeometry.StabilityCondition.Families`; declarations below its
  `FourierMukai/` sibling use
  `AlgebraicGeometry.StabilityCondition.FourierMukai`. Geometry-owned moduli
  and registration instances must likewise use their geometric namespace,
  never the retired flattened categorical stability-family namespace.
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
