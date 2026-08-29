# Canonical roots and specialization trees

This document is the repository contract for reusable abstractions.  The
subject dependency DAG in `layers.md` decides which top-level subject may
import which other subject.  This document decides the finer question: when
two constructions share mathematical structure, where does that structure
live and how do the specializations relate to it?

## The rule

Every reusable concept has one canonical root in the lowest natural owner.
Specialized geometry supplies instances, refinements, subobjects, quotients,
or equivalences at the leaves.  A leaf must not copy the carrier or fields of
its root.

In Lean, "inheritance" means the narrowest of the following that expresses the
mathematics:

1. reuse an existing typeclass or structure directly;
2. add a small capability typeclass whose parent is already an instance;
3. use `extends` when there is a canonical forgetful projection;
4. use an `abbrev` for a genuine specialization;
5. use a proved equivalence or agreement theorem for two independently useful
   presentations.

It does **not** mean putting a theorem, algebraicity claim, preservation result,
or other unfinished conclusion into a structure field.  It also does not mean
forcing unlike formulas into one record merely because their carriers look
similar.

## Canonical spine

This is the ownership target. Existing reverse edges are tracked defects to
burn down, not exceptions that authorize more leaf-to-root imports.

```text
Category
├─ Preadditive
│  └─ Linear k C                         Mathlib root
├─ FiniteExactTower
│  └─ FiniteFiltration                    zero-to-object endpoint refinement
│     └─ almost-disconnected witness       scheme-geometric leaf
├─ DGCategory C
│  ├─ DGLinear k C                       scalar refinement
│  ├─ DGFunctor C D
│  ├─ H0 C
│  └─ IsPretriangulated C
│     └─ Enhancement T                   comparison data, not a class
├─ GrothendieckPresentation
│  ├─ K₀Ab                               short-exact relations
│  ├─ K₀                                 triangle relations
│  └─ K₀dg := K₀ (H0 C)                 reuse, not a third presentation
└─ Sites / descent / stacks in groupoids
   └─ scheme-site realizations

Algebra
└─ saturation of an additive subgroup
   └─ saturated quotient and torsion-free universal property

AlgebraicGeometry
├─ scheme module sheaves
│  ├─ intrinsic IsInvertible
│  │  └─ pullback preservation          theorem inherited by every consumer
│  └─ LineBundleData                     invertible sheaf plus chosen tensor inverse
│     ├─ determinant and Picard interpretations
│     ├─ monoidal pullback and projection formula
│     └─ almost-disconnected graded pieces   scheme-geometric leaf
├─ scheme-derived category
│  ├─ Dqc
│  ├─ bounded coherent locus
│  └─ perfect / relative-perfect loci
├─ numerical K-theory
│  └─ Euler quotient
│     └─ relative numerical quotient              uses Algebra root
│        └─ family-relation system                 statement-layer adapter
├─ moduli
│  ├─ replete subprestack
│  ├─ boundedness witness
│  ├─ stack presentation
│  └─ perfect-complex specialization
└─ stability in families                 final geometric adapter
```

The arrows implied by this tree point downwards from consumers to roots.  In
particular:

- do not add `KLinearCategory`; use Mathlib's `Preadditive` and `Linear` and
  bridge `DGLinear` to them;
- do not add a coherent, derived, dg, projective-space, or relative sibling of
  the Grothendieck group presentation; specialize the canonical presentation
  and prove comparison maps;
- keep quotient mechanics such as additive-subgroup saturation in `Algebra`;
  the relative numerical leaf supplies only its fibre groups and geometric
  relation generators through the family-relation system; scheme connectivity
  and relative perfection are proved by geometric inhabitants, not stored as
  inert fields in the numerical root;
- generic stacks, replete subprestacks, boundedness, and presentation data do
  not import stability-condition modules;
- a paper-specific module may instantiate these roots but never becomes a root
  imported by them.

## Root review before a new structure

Every issue or pull request that introduces a public `structure`, `class`,
quotient carrier, or category must answer these questions before implementation.

1. **Canonical owner.** What existing root is closest?  Give its declaration
   and module.  If none exists, name the proposed neutral module.
2. **Adoption.** Name two independent consumers, or say explicitly that this is
   statement-layer data whose purpose is to compare multiple inhabitants.
3. **Projection.** How does a specialization forget to, refine, or compare with
   the root?  The answer must be an existing instance, a projection, an
   `abbrev`, or a theorem—not prose.
4. **Diamond.** If both the root and leaf synthesize inherited instances, add a
   compile-time or equality test showing that the paths agree.
5. **Dependency direction.** Confirm that the root imports no leaf or
   paper-specific module.
6. **Negative result.** If the apparent generalization is false, record the
   counterexample and keep the leaves separate.  A falsified unification is a
   successful architecture result.

Moving declarations is not complete until imports, umbrellas, audit records,
registry bindings, and compatibility reexports are updated together, as
required by `CONTRIBUTING.md`.

## Agreement is part of the feature

If the target already carries the structure being constructed, agreement is
an acceptance criterion, not follow-up cleanup.  The dg enhancement of the
homotopy category is the model: its transported shift and distinguished
triangles are compared with Mathlib's existing instances.  The same rule
applies to exact versus triangulated K-groups, ordinary versus dg linearity,
and classical versus derived moduli truncations.

## Enforcement

The policy is partly mechanical and partly a review obligation:

- `scripts/check_layering.py` enforces the top-level dependency DAG;
- `scripts/check_umbrella_coverage.py` keeps every specialization in the public
  tree;
- `scripts/check_single_instantiation.py` rejects new thin abstractions in the
  generic subjects;
- `scripts/check_roadmap.py` keeps materialized lanes synchronized with their
  tracker issues;
- the pull-request template records the non-mechanical root, projection, and
  agreement decisions.

The projective-families roadmap carries the first finer-grained burn-down:
generic stack roots move out of scheme geometry, moduli-to-stability reverse
imports are removed, and the relative numerical K-group is built as a quotient
of the existing K-theory spine.
