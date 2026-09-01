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
Bicategory                              Mathlib higher-categorical root
├─ Adjunction of 1-morphisms
│  ├─ adjoint equivalences and mates
│  └─ Cat specialization ≃ ordinary functor adjunction
└─ Pseudofunctor
   ├─ equivalence transport of Cat presentations
   └─ fiberwise object properties / full subpseudofunctors

Category
├─ Limits and colimits
│  ├─ preservation through composition
│  └─ reflective transport using an ordinary adjunction
├─ Preadditive
│  └─ Linear k C                         Mathlib root
├─ Abelian                               Mathlib typeclass
│  ├─ weak-Serre exactness               repository generic extension
│  └─ DerivedCategory C                  generic construction
│     └─ OppositeComparison C            explicit derived/opposite bridge
│        └─ exact ModuleCat linear dual  categorical specialization
├─ FiniteExactTower
│  └─ FiniteFiltration                    zero-to-object endpoint refinement
│     └─ almost-disconnected witness       scheme-geometric leaf
├─ DGCategory C
│  ├─ DGLinear k C                       scalar refinement
│  ├─ DGFunctor C D
│  ├─ H0 C
│  └─ IsPretriangulated C
│     └─ Enhancement T                   comparison data, not a class
├─ Derived-category extensions
│  └─ Ext adjunction / dimension shift / resolution naturality
├─ filtered-complex spectral sequences
├─ Moduli
│  └─ BoundednessProblem                 neutral boundedness predicate
├─ GrothendieckPresentation
│  ├─ K₀Ab                               short-exact relations
│  ├─ K₀                                 triangle relations
│  │  ├─ Realization := K₀ C →+ A        additive target
│  │  │  └─ Descends                    commuting realization square
│  │  └─ EulerForm := K₀ C →+ K₀ C →+ ℤ
│  │     ├─ ofLinear                    canonical linear-category pairing
│  │     └─ Preserves                   exact-functor compatibility
│  └─ K₀dg := K₀ (H0 C)                 reuse, not a third presentation
└─ Sites / descent / stacks in groupoids
   ├─ over-site functoriality
   │  └─ cocontinuity of `Over.post`
   ├─ `CoversTop` equivalence transport
   ├─ Sheaves
   │  ├─ coverwise detection of local equivalences
   │  ├─ constant pullback and cohomology pushforward
   │  └─ module sheaves on a ringed site
   │     ├─ restriction to an over site
   │     ├─ exact forgetful functor
   │     ├─ finite-presentation transport
   │     └─ intrinsic IsInvertible
   │        ├─ rank-one local trivializations
   │        ├─ arbitrary-site tensor descent
   │        └─ topological specialization
   │           ├─ stalk/tensor comparison
   │           └─ stalkwise arbitrary-factor strengthening
   ├─ site-theoretic Čech complexes and derived comparison
   │  └─ compact-basis and finite-cover boundedness
   └─ scheme-site realizations

LinearAlgebra
├─ finite free integral lattices
│  ├─ ZLattice                              finite + free over ℤ
│  └─ ZLattice.ofFiniteTorsionFree          generic construction
│     └─ NumericalVarietyData.numericalZLattice
│                                            geometric quotient consumer
└─ weighted-basis graded pieces
   ├─ internal direct-sum decomposition
   └─ NumericalRingData.ofGradedBasis        geometric numerical consumer

Algebra
├─ ordinary ring and module theory
│  └─ module localization
│     └─ kernel maps                       consumed by coherent-sheaf geometry
├─ numerical polynomials on integer lattices
│  ├─ mixed finite differences and degree
│  └─ top multilinear coefficients
│     └─ Snapper polynomiality             geometric Picard/coherent consumer
├─ multivariate polynomials
│  └─ division by monomials                consumed by projective localization
├─ saturation of an additive subgroup
│  └─ saturated quotient and torsion-free universal property
└─ relative numerical algebra
   ├─ indexed sums and saturated family-relation quotients
   └─ additive-map images and finite-index-overlattice predicates

AlgebraicGeometry
├─ SheafOfModules(X)
│  ├─ QuasicoherentSheaf(X)
│  │  └─ CoherentSheaf(X)
│  │     ├─ Abelian instance under geometric hypotheses
│  │     └─ DerivedCategory (Coh X)     consumes the generic construction
│  ├─ scheme tensor and Picard classes   consume intrinsic IsInvertible
│  └─ LineBundleData                     invertible sheaf plus chosen tensor inverse
│     ├─ determinant and Picard interpretations
│     ├─ monoidal pullback and projection formula
│     └─ almost-disconnected graded pieces   scheme-geometric leaf
├─ scheme-derived category                     `DerivedCategory/`
│  ├─ Dqc                                      neutral geometric locus
│  │  ├─ canonical zero                        owned by Dqc, all schemes
│  │  └─ explicit comparison evidence          representatives, not instances
│  ├─ bounded coherent locus
│  ├─ scheme pullback and geometric kernels
│  └─ absolute perfect locus                   thick envelope in `D(Coh X)`
│     └─ essential image in Dqc
│        └─ compact objects                    only with explicit evidence
├─ relative-perfect locus over `p : X ⟶ S`     `Moduli/PerfectComplex/Relative`
│  └─ pseudo-coherent + finite Tor amplitude   not absolute perfection by definition
├─ two-term determinant presentation           explicit finite-locally-free resolution
│  └─ absolute perfect degree-zero object       proved comparison adapter
├─ numerical K-theory
│  ├─ Euler quotient
│  │  └─ future scheme-specific relation generators consume Algebra root
│  └─ Riemann--Roch and Mukai transfer
│     └─ consume categorical K₀ realizations and Euler forms
├─ moduli
│  ├─ fiberwise replete locus selector     not a subprestack
│  ├─ finite-type boundedness witness      consumes selector + generic predicate
│  ├─ affine stable subprestack            consumes pseudofunctor object property
│  ├─ stack presentation
│  └─ perfect-complex specialization
└─ stability in families                       stability-dependent adapter only
```

The arrows implied by this tree point downwards from consumers to roots.  In
particular:

- do not introduce a second adjunction hierarchy: reuse Mathlib's
  `Bicategory.Adjunction`, and recover ordinary adjoint functors through the
  bicategory `Cat`; place results that merely assume an adjunction with their
  actual conclusion, such as limit preservation or derived `Ext`;
- do not add `KLinearCategory`; use Mathlib's `Preadditive` and `Linear` and
  bridge `DGLinear` to them;
- do not add a coherent, derived, dg, projective-space, or relative sibling of
  the Grothendieck group presentation; specialize the canonical presentation
  and prove comparison maps;
- represent additive K₀ targets and categorical Euler pairings by the canonical
  `K₀.Realization` and `K₀.EulerForm` aliases. Their descent and preservation
  laws stay with the triangulated Grothendieck-group root; geometric
  `IsRiemannRoch`, Euler-transfer, and Mukai-pairing theorems consume them;
- keep indexed additive-group sums, additive-subgroup saturation,
  family-relation systems, additive-map images, and finite-index-overlattice
  predicates in `Algebra/RelativeNumerical`; a geometric consumer must
  introduce actual schemes, connectivity, relative perfection, or other
  geometric data and import this root directly;
- keep integer-lattice numerical functions, mixed forward differences,
  finite-difference degree, Newton coefficients, and top multilinear
  coefficients in `Algebra/NumericalPolynomial`; Snapper's theorem imports
  that root and adds the Picard, coherent-sheaf, and Euler-characteristic data;
- keep the finite-free abelian-group interface `ZLattice` and its construction
  from finite torsion-free groups in `LinearAlgebra/Lattice/Basic.lean`;
  `NumericalVarietyData.numericalZLattice` remains the geometric theorem that
  supplies those hypotheses for an Euler-radical quotient;
- keep ordinary module theory under `Algebra`, generic sheaves and module
  sheaves on ringed sites under `CategoryTheory/Sites/Sheaves`, and only the
  scheme-indexed `SheafOfModules(X) -> QCoh(X) -> Coh(X)` refinements under
  algebraic geometry; in particular, coherent-sheaf kernels directly reuse
  the module-localization kernel maps rather than owning them;
- keep detection of additive-presheaf local equivalences on a `CoversTop`
  family under the generic site/sheaf root; scheme charts and sheafified
  tensor constructions only consume that theorem chain;
- keep cocontinuity of `Over.post`, module-sheaf restriction to over sites,
  and equivalence transport of `CoversTop` families under the generic site and
  sheaf roots; open-immersion geometry consumes them only after introducing
  schemes and their open-set sites;
- keep restriction of presentations, generating sections, and quasicoherent
  presentation data under the generic ringed-site presentation root; affine
  geometry consumes that API only when it introduces `Spec R` and basic opens;
- keep stalk/tensor comparisons for module presheaves under
  `Topology/Sheaves/ModuleTensor/`: their use of open neighbourhoods, germs,
  and stalk functors makes them topological specializations of arbitrary-site
  sheaf theory, not ordinary module algebra;
- extend Mathlib's abelian-category hierarchy under `CategoryTheory/Abelian`
  and make the geometric proof that `Coh(X)` is abelian an input to the generic
  derived-category construction;
- generic stacks, replete subprestacks, and boundedness predicates do not
  import stability-condition or geometric modules; scheme presentations and
  finite-type witnesses remain geometric consumers;
- a paper-specific module may instantiate these roots but never becomes a root
  imported by them.

Bicategories are the first implemented higher-categorical stage. A future
general `n`-category or `(∞,1)`-category layer must name its formal model and
its comparison with this spine; an empty directory does not establish an
abstraction relationship.

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
imports are removed, and geometric relative numerical K-theory consumes the
indexed quotient machinery rooted in ordinary algebra.
