# Declaration placement

This is the operational placement test for new declarations and structural
moves. Apply it with the subject/application boundaries in
[mathematical-ownership.md](mathematical-ownership.md). Tier 1 follows an
identified Mathlib API owner; deciding whether a declaration extends that API
or introduces a new subject still requires mathematical review.

## Tier 1: an extension of a Mathlib API lives at that API's Mathlib path

A direct extension of a Mathlib API follows that API's definition site at the
repository's pinned revision, under `DerivedAlgGeo/`, in that API's namespace.
Using a Mathlib type does not by itself make a new concept an extension of its
elementary API. Follow Tier 2 for a new subject. This alignment aids navigation
and future upstream work; matching directories is not required to import Mathlib.

| Concept the declaration extends | Mathlib path | Repository path |
| --- | --- | --- |
| `DerivedCategory C`, `Ext`, K-projectives, its t-structure, `Bounded` | `Algebra/Homology/DerivedCategory/` | `Algebra/Homology/DerivedCategory/` |
| `HomotopyCategory`, `HomComplex`, bounded and plus variants | `Algebra/Homology/HomotopyCategory/` | `Algebra/Homology/HomotopyCategory/` |
| Spectral sequences and total complexes | `Algebra/Homology/SpectralSequence/` | `Algebra/Homology/SpectralSequence/` |
| `SheafOfModules` and `PresheafOfModules` | `Algebra/Category/ModuleCat/{Sheaf,Presheaf}/` | `Algebra/Category/ModuleCat/{Sheaf,Presheaf}/` |
| `ModuleCat`, `Grp` | `Algebra/Category/{ModuleCat,Grp}/` | `Algebra/Category/{ModuleCat,Grp}/` |
| `ObjectProperty`, the full subcategory it cuts out, and functor lifts into it | `CategoryTheory/ObjectProperty/` | `CategoryTheory/ObjectProperty/` |
| Sites, sheaves, sheaf cohomology, descent, stacks | `CategoryTheory/Sites/` | `CategoryTheory/Sites/`, with Čech theory under `SheafCohomology/Cech/` and stacks under `Descent/` |
| Bicategories, pseudofunctors, `Pseudofunctor.ObjectProperty` | `CategoryTheory/Bicategory/` | `CategoryTheory/Bicategory/`, with Cat-valued pseudofunctor loci and transport under `Functor/Cat/` |
| Abelian categories, Serre classes | `CategoryTheory/Abelian/` | `CategoryTheory/Abelian/` |
| Quasi-abelian categories and strict morphisms | `CategoryTheory/Abelian/` (precedent `Abelian/NonPreadditive.lean`) | `CategoryTheory/Abelian/QuasiAbelian.lean` |
| Linear categories and opposite linearity | `CategoryTheory/Linear/` | `CategoryTheory/Linear/` |
| Compact objects and coproduct-preserving functors on a preadditive category | `CategoryTheory/Preadditive/` | `CategoryTheory/Preadditive/CompactObject.lean` |
| `SmallShiftedHom` in a localization | `CategoryTheory/Localization/` | `CategoryTheory/Localization/` |
| The opposite of a (pre)triangulated category and its shift | `CategoryTheory/Triangulated/Opposite/` | `CategoryTheory/Triangulated/Opposite/` |
| `HomComplex` and its cohomology classes | `Algebra/Homology/HomotopyCategory/` | `Algebra/Homology/HomotopyCategory/` |
| Pretriangulated and triangulated categories, t-structures | `CategoryTheory/Triangulated/` | `CategoryTheory/Triangulated/` |
| Monoidal categories and their compatibility with other structure | `CategoryTheory/Monoidal/` | `CategoryTheory/Monoidal/` |
| Simplicial objects and face-map complexes | `AlgebraicTopology/` | `AlgebraicTopology/` |
| Sheaves on a topological space, stalks, the category of opens | `Topology/Sheaves/`, `Topology/Category/TopCat/` | `Topology/Sheaves/`, `Topology/Category/TopCat/` |
| `PrimeSpectrum` and its topology | `RingTheory/Spectrum/Prime/` | `RingTheory/Spectrum/Prime/` |
| `HomogeneousLocalization` and graded algebras | `RingTheory/GradedAlgebra/` | `RingTheory/GradedAlgebra/` |
| Modules, localization, graded modules, polynomials | `Algebra/Module/`, `Algebra/MvPolynomial/` | the same |
| Lattices, bilinear forms, exterior powers, finite-dimensional lemmas | `LinearAlgebra/` | `LinearAlgebra/` |
| Euler characteristics of graded objects | `Algebra/Homology/EulerCharacteristic.lean` | `Algebra/Homology/EulerCharacteristic.lean` |
| Alternating sums along finite exact sequences | `Algebra/Exact/Sequence.lean` | `Algebra/Exact/Sequence.lean` |
| Schemes, `X.Modules`, `Proj`, morphism properties | `AlgebraicGeometry/` | `AlgebraicGeometry/`, with `ProjectiveSpectrum/` under Mathlib's name |

If two rows seem to apply, identify the API actually being extended, rather
than choosing the weakest type appearing in the statement.
`PrimeSpectrum.basicOpen_prod_eq_pi` is stated
in the lattice of opens of a prime spectrum, but `basicOpen` is defined in
`RingTheory/Spectrum/Prime/Topology.lean`, so it lives there and not in
`Topology/` or `Algebra/`. Stalks of module presheaves are stated with
`TopCat`, germs, and stalk functors, which Mathlib defines in
`Topology/Sheaves/`, so they live there.

## Tier 1 is about extension, not use

Tier 1 decides where an *extension of an existing Mathlib API* lives. It does
not follow that everything built with a Mathlib API belongs at that API's path.
A new mathematical object that merely uses `Module.Dual`, a bilinear form, or
`HomComplex` is placed by its own subject and at an appropriately general root,
by Tier 2. Reading Tier 1 as a universal carrier rule is how a new subject ends
up filed under whichever upstream definition its implementation happened to
reach for, and how the *same* policy simultaneously recognized conceptual
ownership for weak charges while filing the analogous numerical constructions
under a consumer directory.

Two consequences, both load-bearing:

- **A directory is an index; it is not the import graph and not the
  specialization graph.** The three must agree where they overlap and cannot be
  identical. A comparison theorem between two constructions does not license
  the generic one to import the special one, and a shared directory does not
  make two constructions instances of each other.
- **A narrowly imported module is not a full subject umbrella.** Keep them
  distinct in prose and in the layering gate: an umbrella re-exports its
  children by construction, so a rule that holds for a leaf may fail for the
  umbrella above it for reasons that have nothing to do with the leaf's
  subject.

Proposed destinations in an architecture review are local recommendations, not
promises that Mathlib will accept a module of that name.

## The agreed owner map

`docs/architecture/cutover-ledger.md` carries the declaration-level owner map
agreed in MO1.01 (#1312) for the 2026-09-13 ownership review: for each
confirmed finding, the definition owner, the neutral core, the application
adapter and the comparison owner, together with the independent-consumer
justification for every proposed new carrier. Two of its standing decisions
apply to every structural change in the repository, not only to MO1:

1. paths move and fully qualified declaration names do not, so a relocation
   never invalidates a historical review payload; and
2. a proposed new carrier needs a consumer outside the module it was extracted
   from, or it is replaced by a theorem or an `abbrev` -- an extraction is not
   its own second consumer.

Read that map before proposing a destination for code it already covers.

## Tier 2: a subject Mathlib lacks is placed by the nearest precedent

| Situation | Mathlib precedent | Repository placement |
| --- | --- | --- |
| A structure on an abstract triangulated category | `Triangulated/TStructure/`, `Subcategory`, `Orthogonal`, `LocalizingSubcategory`, `Generators` | `CategoryTheory/Triangulated/<Name>/` |
| A weakened or strengthened variant of a named concept | `Topology/MetricSpace/Pseudo/`, `Monoidal/Braided/`, `Monoidal/Closed/` | a child directory named by the adjective, below the canonical concept |
| Compatibility between two independent structures | `Monoidal/Preadditive.lean`, `Monoidal/Linear.lean` | `CategoryTheory/Monoidal/<Other>.lean` |
| A structure on an abstract abelian category | `Abelian/SerreClass/`, `Abelian/GrothendieckCategory/` | `CategoryTheory/Abelian/<Name>/` |
| A geometric realization of a categorical interface | `Algebra/Category/ModuleCat/Abelian.lean`, `AlgebraicGeometry/Modules/Sheaf.lean` | with the geometric object under `AlgebraicGeometry/`; the declaration may keep the interface's namespace for dot notation |
| A bespoke carrier built on a Mathlib API | definition site | beside that API |
| A neutral predicate on pseudofunctors used by both geometry and stability | `CategoryTheory/Bicategory/Functor/Cat/` | `CategoryTheory/Moduli/` until Mathlib has a home for it |
| A theorem whose public type mentions a scheme, variety, `Coh X`, `Dqc X`, or a geometric morphism property | `AlgebraicGeometry/` | `AlgebraicGeometry/`, organized by geometric object |

Within Tier 2, identify the mathematical object and its independently useful
theory. Use the weakest sufficient hypotheses to separate a reusable block
from its application, not to rank all subjects or file every construction
under its most elementary carrier. A stability function has a stability
owner even though its charge is an additive map. A general bilinear identity
has a linear-algebra owner even when first used by stability. This subject
decision never relocates a direct Mathlib extension away from its API owner.

## What does not decide placement

- The abstraction level of the statement. A derived category is a
  triangulated category, and Mathlib still files it under `Algebra/Homology`.
- The weakest vocabulary in the signature, when the carrier has a definition
  site.
- The motivating theorem, the current filename, the first consumer, or the
  proof technique.
- The namespace. Declarations inside `LinearMap`, `Module`, `SheafOfModules`,
  or `ChargeProbe` still live at their carrier's path.
- Which interface a geometric object happens to satisfy. `AlgebraicGeometry/`
  is organized by object; inside an object directory the files are named by
  the structure they add.

## Root and consumer test

Before adding or moving a public declaration:

1. Search Mathlib and this repository for the carrier or concept.
2. Name the canonical root module and the concrete consumer module.
3. State the Lean relationship between them: direct reuse, `extends`, an
   instance, an `abbrev`, or a proved comparison.
4. Verify that the root imports no specialization, consumer, paper-specific
   file, or geometric realization, including through umbrellas. Put comparison
   modules downstream of both presentations.
5. Import the root directly from the consumer. Do not add a compatibility shim
   merely to preserve the old motivational path.
6. Update the nearest umbrella, axiom audit, declaration baseline, layering
   gate, and this documentation in the same change.

If a file mixes a generic block, its application and their comparison, split
at those declaration boundaries. Record hypotheses separately from subject
ownership. Use the [decision record](mathematical-ownership.md#record-the-decision-in-the-issue-or-pr)
to make the owner, imports and Lean specialization map reviewable.

The charge ownership cutover is complete (#1313). General paired functionals,
quadratic continuity and coercivity, and abstract Hodge-signature input live
under `LinearAlgebra/`. Additive charge families and exponential, numerical and
divisorial constructors live under
`CategoryTheory/Triangulated/StabilityCondition/CentralCharge/`. Wall equations
import those constructors from `StabilityCondition/Walls/`; full support
predicates live under `StabilityCondition/Support/`; geometric Chern/Todd
realizations remain under `AlgebraicGeometry/Numerical/`. Rule 8 of
`scripts/check_layering.py` pins the owners and checks their transitive import
boundaries. Preserve the existing roots and comparisons instead of creating
another charge carrier or retired-path shim.

Orthogonal exceptional blocks and a chosen right adjoint to a residual
full-subcategory inclusion are structures on abstract (pre)triangulated
categories, so their canonical owner is
`CategoryTheory/Triangulated/SemiorthogonalDecomposition/`.  Constructors
for objectwise mutation triangles and the same-projection theorem also live
there; neither requires scheme vocabulary.  The `k`-linear Serre duality data,
its Hom-finiteness hypothesis, the Serre pairing and trace, and uniqueness of
the Serre functor mention no shift and no triangulation, so their owner is
`CategoryTheory/Linear/SerreFunctor/`, with the three representability helpers
that need no Serre datum at all in `CategoryTheory/Linear/Yoneda.lean`.  Ext
profiles, transport of spherical and pseudoprojective objects, and
classification-induced matching are shift-dependent and stay in
`CategoryTheory/Triangulated/SerreFunctor/`, which imports the linear root.
Adjacent Ext shift rigidity and ordered
block-length comparison belong with the semiorthogonal root.  One-step and
dependent finite kernel extension, including generation from right
admissibility, live beside the generic Fourier--Mukai API.  Only the comparison
with an Enriques surface's ten line bundles, its already-defined residual
property, the numerical `(-2)`-curve chains, and the paper-specific
degree-three and ambient-equivalence conclusions belong under
`AlgebraicGeometry/Surface/Enriques/`; the dependency runs from that consumer
to the categorical roots.

An adjunction in its most general implemented form is
`CategoryTheory.Bicategory.Adjunction`. Mathlib identifies ordinary functor
adjunctions with its `Cat` specialization. A theorem that merely assumes an
ordinary adjunction is placed by the other vocabulary in its signature:
preservation results belong with limits, `Ext` comparisons with derived `Ext`,
and kernel packages with Fourier--Mukai theory.

Comparison data of type `(DerivedCategory C)ᵒᵖ ≃ DerivedCategory Cᵒᵖ` extends
Mathlib's derived category, so its owner is
`Algebra/Homology/DerivedCategory/Opposite.lean`. The bare algebraic-dual
functor on `ModuleCat` currently lives at `CategoryTheory/ModuleCat/LinearDual.lean`;
its target owner is `Algebra/Category/ModuleCat/LinearDual.lean`, with its
exactness API (pending #1325). The exactness and derived lift currently live in
`Algebra/Category/ModuleCat/LinearDual.lean` and
`Algebra/Homology/DerivedCategory/LinearDual.lean`. A Serre-duality statement that mentions a scheme
imports those roots and the canonical coherent-derived specialization; its
geometric motivation does not move the generic functors into duality.

The comparison `Dᵇ(Coh X) ≃ Dᵇ_coh(Dqc X)` intrinsically mentions a scheme,
so its statement and conditional consumer API belong under
`AlgebraicGeometry/DerivedCategory/Dqc/`. The existence proposition is not an
instance: `Dqc/Comparison.lean` accepts it explicitly and produces a coherent
representative and comparison isomorphism. The same rule applies to the
conditional equality of the perfect and compact-object properties. A moduli
consumer adds its relative-perfect and bounded-cohomology hypotheses without
becoming the owner of either comparison.

## Perfect-complex notion ledger

The word "perfect" currently appears in three non-interchangeable APIs. The
paths below describe the present implementation. Moving foundational relative
perfectness out of the moduli consumer is tracked in #1322; it does not change
these mathematical comparisons. In particular, the current cohomological
`schemePseudoCoherent` criterion is not automatically standard pseudo-coherence
on arbitrary non-Noetherian bases; preserve the scope warning in #554.
The ambient categories and formal relationships are:

| Notion | Ambient object | Meaning and owner | Valid comparison |
| --- | --- | --- | --- |
| `schemePerfect X` | `D(Coh X)` | Thick envelope of degree-zero finite locally free coherent sheaves; `AlgebraicGeometry/DerivedCategory/Coherent.lean` | `perfectDerivedToDqc_obj_mem_schemePerfectInDqc` maps it into the defining perfect essential image in `Dqc(X)` |
| `schemeRelativePerfect p` | `Dqc(X)` for `p : X ⟶ S` | Pseudo-coherence plus local finite Tor amplitude over the chosen base; `DerivedCategory/Perfect/Relative.lean` | It implies `schemePseudoCoherent`; it is not identified with absolute perfection without an additional geometric theorem |
| `Coh.TwoTermPerfectDeterminantData F` | a coherent sheaf `F` plus presentation data | An explicit two-term finite locally free resolution used by determinant and Chern-class consumers; `Divisors/Determinant.lean` | `Moduli/PerfectComplex/Comparison.lean` forgets it to an absolute perfect degree-zero object and then to `schemePerfectInDqc` |

`schemePerfectInDqc X` is the bridge, not a fourth competing definition: it
is the essential image of `SchemePerfectDerivedCategory X` under the concrete
coherent-derived functor. The general equality with compact objects remains
explicit evidence. Neither relative perfection nor two-term amplitude is
promoted to an equivalence with the full absolute perfect locus.

The canonical zero of `SchemeQuasicoherentDerivedCategory X` belongs to
`Dqc.lean` and is available for every scheme. Perfect-moduli files may prove
that this root object satisfies their additional predicates, but may not
reconstruct or rename the ambient zero.

## Moduli and subprestacks

`CategoryTheory.Moduli.BoundednessProblem` is the neutral boundedness root. A
stability-family package may require it and a geometric moduli package may
realize it with finite-type parameter data, but neither consumer owns the
predicate.

Mathlib's `Pseudofunctor.ObjectProperty` is the canonical fiberwise locus for a
Cat-valued pseudofunctor:

- `IsClosedUnderIsomorphisms` makes the locus replete;
- `IsClosedUnderMapObj` makes it stable under restriction;
- `fullsubcategory` and `ι` construct the sub-pseudofunctor and its inclusion.

Repository extensions to that mechanism live under
`CategoryTheory/Bicategory/Functor/Cat/ObjectProperty/`, where Mathlib defines
it. Do not introduce a parallel `Subprestack` carrier in algebraic geometry. An
indexed collection of isomorphism-closed fiber predicates is not yet a
subprestack until restriction stability is supplied.

Concrete finite-type witnesses, atlases, scheme presentations, semistable loci,
and Harder--Narasimhan filtrations remain under `AlgebraicGeometry/Moduli/`
because their signatures intrinsically mention geometry. The relative-perfect
*predicates* do not: pseudo-coherence, local finite Tor amplitude and relative
perfection are properties of one complex over one morphism, needed by base
change and derived operations before a moduli functor exists, so their owner is
`AlgebraicGeometry/DerivedCategory/Perfect/` and the moduli problem consumes
them. Stalkwise flatness of a module sheaf over a morphism is a further step
down, at `AlgebraicGeometry/Modules/Flat.lean`.

`AlgebraicGeometry.RelativePerfectModuliSelector` is the canonical name for
the weaker geometric input used by finite-type boundedness: it stores the
independent replete `familyLocus` and `geometricLocus` over each actual scheme
base change. It is not a pseudofunctor object property and provides no
restriction functors. The affine construction first places its locus on an
actual Cat-valued pseudofunctor, applies `universallyStable`, and only then
calls `fullsubcategory`; that is the root-to-consumer relationship required
for a genuine subprestack.

## Review evidence

Every structural pull request must include:

- for each moved or new public root, the Tier 1 row or the Tier 2 precedent
  that places it;
- the root-to-consumer import direction;
- the specialization map or a statement that the consumer directly reuses the
  root;
- any adjacent misplaced declarations discovered while editing, recorded in
  `docs/architecture/cutover-ledger.md` if they are not part of the same slice.
