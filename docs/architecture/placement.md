# Declaration placement

This is the operational placement test for new declarations and structural
moves. It has two tiers, and the first one is mechanical.

## Tier 1: an extension of a Mathlib API lives at that API's Mathlib path

Mathlib organizes by definition site, not by abstraction level. A file that
extends a Mathlib API goes at the path Mathlib uses for that API, under
`DerivedAlgGeo/`, in that API's namespace. That is also where an upstream pull
request would put it, so the move to Mathlib is a copy.

| Concept the declaration extends | Mathlib path | Repository path |
| --- | --- | --- |
| `DerivedCategory C`, `Ext`, K-projectives, its t-structure, `Bounded` | `Algebra/Homology/DerivedCategory/` | `Algebra/Homology/DerivedCategory/` |
| `HomotopyCategory`, `HomComplex`, bounded and plus variants | `Algebra/Homology/HomotopyCategory/` | `Algebra/Homology/HomotopyCategory/` |
| Spectral sequences and total complexes | `Algebra/Homology/SpectralSequence/` | `Algebra/Homology/SpectralSequence/` |
| `SheafOfModules` and `PresheafOfModules` | `Algebra/Category/ModuleCat/{Sheaf,Presheaf}/` | `Algebra/Category/ModuleCat/{Sheaf,Presheaf}/` |
| `ModuleCat`, `Grp` | `Algebra/Category/{ModuleCat,Grp}/` | `Algebra/Category/{ModuleCat,Grp}/` |
| Sites, sheaves, sheaf cohomology, descent, stacks | `CategoryTheory/Sites/` | `CategoryTheory/Sites/`, with Čech theory under `SheafCohomology/Cech/` and stacks under `Descent/` |
| Bicategories, pseudofunctors, `Pseudofunctor.ObjectProperty` | `CategoryTheory/Bicategory/` | `CategoryTheory/Bicategory/`, with Cat-valued pseudofunctor loci and transport under `Functor/Cat/` |
| Abelian categories, Serre classes | `CategoryTheory/Abelian/` | `CategoryTheory/Abelian/` |
| Pretriangulated and triangulated categories, t-structures | `CategoryTheory/Triangulated/` | `CategoryTheory/Triangulated/` |
| Monoidal categories and their compatibility with other structure | `CategoryTheory/Monoidal/` | `CategoryTheory/Monoidal/` |
| Simplicial objects and face-map complexes | `AlgebraicTopology/` | `AlgebraicTopology/` |
| Sheaves on a topological space, stalks, the category of opens | `Topology/Sheaves/`, `Topology/Category/TopCat/` | `Topology/Sheaves/`, `Topology/Category/TopCat/` |
| `PrimeSpectrum` and its topology | `RingTheory/Spectrum/Prime/` | `RingTheory/Spectrum/Prime/` |
| `HomogeneousLocalization` and graded algebras | `RingTheory/GradedAlgebra/` | `RingTheory/GradedAlgebra/` |
| Modules, localization, graded modules, polynomials | `Algebra/Module/`, `Algebra/MvPolynomial/` | the same |
| Lattices, bilinear forms, exterior powers | `LinearAlgebra/` | `LinearAlgebra/` |
| Schemes, `X.Modules`, `Proj`, morphism properties | `AlgebraicGeometry/` | `AlgebraicGeometry/`, with `ProjectiveSpectrum/` under Mathlib's name |

If two rows seem to apply, the definition site of the *carrier* in the
declaration's public type wins. `PrimeSpectrum.basicOpen_prod_eq_pi` is stated
in the lattice of opens of a prime spectrum, but `basicOpen` is defined in
`RingTheory/Spectrum/Prime/Topology.lean`, so it lives there and not in
`Topology/` or `Algebra/`. Stalks of module presheaves are stated with
`TopCat`, germs, and stalk functors, which Mathlib defines in
`Topology/Sheaves/`, so they live there.

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

Within Tier 2, when the precedent does not decide, use the weakest vocabulary
sufficient for the full public type as the tie-breaker: rings before linear
algebra before categories before sites before topological spaces before
schemes. That tie-breaker never overrides Tier 1.

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
4. Verify that the root imports no consumer, paper-specific file, or
   geometric realization.
5. Import the root directly from the consumer. Do not add a compatibility shim
   merely to preserve the old motivational path.
6. Update the nearest umbrella, axiom audit, declaration baseline, layering
   gate, and this documentation in the same change.

If a file contains both a generic block and its geometric use, split the block
at the first declaration whose signature no longer needs the consumer's
vocabulary.

An adjunction in its most general implemented form is
`CategoryTheory.Bicategory.Adjunction`. Mathlib identifies ordinary functor
adjunctions with its `Cat` specialization. A theorem that merely assumes an
ordinary adjunction is placed by the other vocabulary in its signature:
preservation results belong with limits, `Ext` comparisons with derived `Ext`,
and kernel packages with Fourier--Mukai theory.

Comparison data of type `(DerivedCategory C)ᵒᵖ ≃ DerivedCategory Cᵒᵖ` extends
Mathlib's derived category, so its owner is
`Algebra/Homology/DerivedCategory/Opposite.lean`. Exact algebraic linear
duality on `ModuleCat` and its derived lift are the specialization in the
adjacent `LinearDual.lean`. A Serre-duality statement that mentions a scheme
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

The word "perfect" currently appears in three non-interchangeable APIs. Their
ambient categories and formal relationships are:

| Notion | Ambient object | Meaning and owner | Valid comparison |
| --- | --- | --- | --- |
| `schemePerfect X` | `D(Coh X)` | Thick envelope of degree-zero finite locally free coherent sheaves; `AlgebraicGeometry/DerivedCategory/Coherent.lean` | `perfectDerivedToDqc_obj_mem_schemePerfectInDqc` maps it into the defining perfect essential image in `Dqc(X)` |
| `schemeRelativePerfect p` | `Dqc(X)` for `p : X ⟶ S` | Pseudo-coherence plus local finite Tor amplitude over the chosen base; `Moduli/PerfectComplex/Relative.lean` | It implies `schemePseudoCoherent`; it is not identified with absolute perfection without an additional geometric theorem |
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

Concrete finite-type witnesses, atlases, scheme presentations, relative-perfect
objects, semistable loci, and Harder--Narasimhan filtrations remain under
`AlgebraicGeometry/Moduli/` because their signatures intrinsically mention
geometry.

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
