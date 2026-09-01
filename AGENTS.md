# Working in DerivedAlgGeo

## Structural ownership

Organize stable code by its most general mathematical construction, not by the
first application that motivated it.

- Put ordinary ring and module theory that mentions no site or scheme under
  `Algebra/`.
- Put statements about arbitrary categories, functors, abelian categories,
  triangulated categories, enriched categories, sites, or sheaves on an
  arbitrary site under `CategoryTheory/`.
- Reuse Mathlib's `CategoryTheory.Bicategory` hierarchy for 2-categorical
  mathematics. Adjunctions between 1-morphisms, adjoint equivalences, and
  mates belong under `CategoryTheory/Bicategory/`; ordinary adjoint functors
  are the specialization in the bicategory `Cat`.
- Reuse Mathlib's `CategoryTheory.Abelian` class. Repository-owned results for
  arbitrary abelian categories belong under `CategoryTheory/Abelian/`; do not
  define a competing abelian-category hierarchy.
- Put generic sheaf theory under `CategoryTheory/Sites/Sheaves/`. This includes
  sheaves of modules over a sheaf of rings on an arbitrary site; those belong
  under `CategoryTheory/Sites/Sheaves/Modules/`, not under affine or scheme
  geometry.
- Put sheaf results whose signatures intrinsically use the opens, bases,
  germs, or stalks of a topological space under `Topology/Sheaves/`.
  Basiswise detection of a sheaf isomorphism belongs in
  `Topology/Sheaves/Basis.lean`; affine comparison imports it as a consumer.
- Put results combining a prime spectrum with its lattice of opens under
  `Topology/PrimeSpectrum/`. Even when the input is only a commutative ring,
  categorical products of basic opens require the topological opens-limit
  owner and therefore do not belong in the lower `Algebra/` layer.
- Over-category cocontinuity for arbitrary sites belongs in
  `CategoryTheory/Sites/Over.lean`; restriction API for module sheaves on an
  arbitrary ringed site belongs in
  `CategoryTheory/Sites/Sheaves/Modules/Over.lean`. Transport of a `CoversTop`
  family through a cover-preserving equivalence belongs in the purely
  site-theoretic `CategoryTheory/Sites/CoversTop.lean`. An open-immersion file
  is a consumer only once its public signatures introduce schemes or
  topological opens.
- Intrinsic rank-one and invertibility data for module sheaves belong in
  `CategoryTheory/Sites/Sheaves/Modules/Invertible.lean`. Tensoring a local
  equivalence by a rank-one module sheaf on an arbitrary site belongs in the
  adjacent `Tensor.lean`. The comparison between stalks and tensor products on
  a topological space belongs in
  `Topology/Sheaves/ModuleTensor/StalkTensor.lean`; the resulting stalkwise
  strengthening for an arbitrary tensor factor belongs in the parent
  `Topology/Sheaves/ModuleTensor.lean`. Neither belongs under `Algebra/`.
- Detection of local injectivity, local surjectivity, and sheafification weak
  equivalences on a family covering the terminal object belongs in
  `CategoryTheory/Sites/Sheaves/CoversTop.lean`. Scheme charts, divisors, and
  tensor constructions import that root as consumers.
- Put definitions and geometric lemmas that intrinsically mention schemes,
  varieties, scheme-indexed sheaf categories, or geometric morphism
  properties under `AlgebraicGeometry/`.
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
- The geometric specialization chain is `SheafOfModules(X) -> QCoh(X) ->
  Coh(X)`: place scheme module sheaves under
  `AlgebraicGeometry/SheafOfModules/`, quasicoherent refinements below
  `QuasicoherentSheaf/`, and coherent refinements below `CoherentSheaf/` as
  the staged cutover reaches them. Prove the relevant abelian instance for
  `Coh(X)` in geometry, then consume the single generic derived construction.
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

### Mandatory placement check

Before creating or moving a public declaration, classify its complete Lean
signature using `docs/architecture/placement.md`. Ownership is determined by
the weakest vocabulary needed to state the declaration, not by its motivating
application, current file, namespace, or proof technique.

- Ring, ideal, ordinary-module, and localization statements go to `Algebra/`.
- Linear-map, basis, lattice, matrix, multilinear, and exterior-power
  statements go to `LinearAlgebra/` when they require no site or scheme.
- The finite-free abelian-group interface is the global `ZLattice` class in
  `LinearAlgebra/Lattice/Basic.lean`. Its finite-torsion-free constructor is
  generic; a numerical Euler-radical quotient imports that root and proves
  `NumericalVarietyData.numericalZLattice` geometrically. Do not restore the
  retired `AlgebraicGeometry.Numerical.ZLattice` namespace.
- A declaration that needs categories or pseudofunctors but no geometry goes
  to `CategoryTheory/`; prestack loci use
  `CategoryTheory/Pseudofunctor/ObjectProperty/`.
- Additive `K₀` targets, their exact-functor descent squares, and categorical
  Euler pairings belong under
  `CategoryTheory/Triangulated/GrothendieckGroup/`. Reuse `K₀.Realization` and
  `K₀.EulerForm`; keep only numerical Riemann--Roch and Mukai consumers under
  algebraic geometry. Do not restore the retired geometry-owned
  `NumericalRealization`, `Descends`, `CategoricalEulerForm`, or
  `PreservesCategoricalEuler` APIs.
- A geometric consumer imports the general root directly. Do not preserve the
  old consumer path with an import-only shim.
- A theorem about additive presheaves on an arbitrary Grothendieck site remains
  site theory even when all current covers are scheme charts. In particular,
  do not redeclare the `Presheaf.{isLocallyInjective,isLocallySurjective,W}_of_coversTop`
  chain below algebraic geometry.
- A theorem about `J.over X`, `Over.post F`, `SheafOfModules.over`, restriction
  of a `Presentation`, `GeneratingSections`, or `QuasicoherentData`, or
  transport of `J.CoversTop` through an equivalence remains site theory when
  its full signature mentions no scheme. Put the presentation-restriction API
  in `CategoryTheory/Sites/Sheaves/Modules/Presentation/Over.lean`; scheme
  consumers import these roots directly rather than owning the generic prefix.
- Converting an epimorphism `SheafOfModules.free I ⟶ M` into
  `M.GeneratingSections`, including its finite-index and recovery lemmas,
  belongs in
  `CategoryTheory/Sites/Sheaves/Modules/GeneratingSections.lean`. An affine
  chart is a consumer only after `Spec R`, a scheme open, or coherence enters
  the signature.
- Isomorphism invariance, restriction, and `CoversTop` descent of finite
  presentation for module sheaves on an arbitrary ringed site belong in
  `CategoryTheory/Sites/Sheaves/Modules/Presentation/{Isomorphism,Locality}.lean`.
  The zero-object and short-exact extension closure belong in the adjacent
  `Presentation/{Zero,Extensions}.lean` roots. `AlgebraicGeometry/CoherentSheaf/`
  owns only the resulting `coherent X` instances, affine-open criteria, and
  the abelian structure on `Coh X`.
- A rank-one predicate, intrinsic invertibility class, local trivialization, or
  sheafification-whiskering theorem stated on an arbitrary ringed site belongs
  with generic module sheaves. A scheme Picard class consumes that root; it
  does not own another invertibility definition.
- A declaration whose signature uses a topological space together with open
  neighbourhoods, germs, or stalk functors belongs under `Topology/`, even
  when its remaining types are ordinary modules. In particular, do not
  restore `Algebra/Category/ModuleCat/StalkTensor.lean`; consumers import the
  topological stalk-tensor owner directly.
- A criterion detecting that a sheaf morphism is an isomorphism from its
  components on a basis belongs in `Topology/Sheaves/Basis.lean`, not at the
  front of an affine-scheme consumer.
- A theorem whose result is an equality of opens in `PrimeSpectrum R` belongs
  under `Topology/PrimeSpectrum/` when its signature uses the lattice or
  categorical products of opens. Do not force it into `Algebra/` by duplicating
  or hiding the `Topology/Opens/Limits` dependency.
- Kernel maps for ordinary localized modules, including their `ModuleCat`
  formulation, belong under `Algebra/Module/Localization/`. Coherent-sheaf
  arguments import that algebraic owner and add only the scheme-dependent
  comparison and finiteness steps.
- Indexed additive-group sums, saturated relation quotients,
  family-relation systems, additive-map ranges, and finite-index-overlattice
  predicates belong under `Algebra/RelativeNumerical/`. A geometric consumer
  must mention actual geometric data and import this root directly; do not
  restore the retired `AlgebraicGeometry/Numerical/GrothendieckGroup/Relative*`
  paths.
- Integer-lattice numerical functions, mixed forward differences, finite-
  difference degree, Newton coefficients, and their multilinear top
  coefficients belong under `Algebra/NumericalPolynomial/`. Snapper
  polynomiality begins only when Picard classes, coherent sheaves, and Euler
  characteristics enter the signature, and remains in
  `AlgebraicGeometry/IntersectionTheory/Snapper.lean`. Do not restore the
  former geometric `NumericalPolynomial` path or namespace.
- Weight-indexed spans and direct-sum arguments for a basis belong in
  `LinearAlgebra/GradedBasis.lean`; `NumericalRingData.ofGradedBasis` is the
  geometric consumer that adds numerical-intersection-ring data.
- Facts stated only with `Finsupp`, `MvPolynomial`, homogeneity, and
  `divMonomial` belong in `Algebra/MvPolynomial/DivMonomial.lean`. Standard
  polynomial grading and generation over degree zero belong in `Grading.lean`;
  the canonical `p / 1` element of a variable localization belongs in
  `Cech/Basic.lean`. Projective files import those roots and begin only when
  projective opens, sheaves, or cohomology enter the signature.
- Degree-zero localization of an internally graded module, graded shifts,
  twist trivializations, and denominator-equality transport belong in
  `Algebra/Module/GradedModule/` under Mathlib's `GradedModule` namespace.
  Laurent exponent vectors belong in `Algebra/Finsupp/`. Their polynomial
  localization basis, representative-independent sign and block projections,
  one-localization homotopies, and full-block finiteness belong in
  `Algebra/MvPolynomial/`. Polynomial-variable Čech denominators, terms, faces,
  block homotopies, primitives, and finite-block results belong specifically in
  `Algebra/MvPolynomial/Cech/`; projective basic-open, section, and cohomology
  comparisons are downstream consumers.

When editing a consumer file, inspect adjacent declarations for a generic
prefix or suffix. Move an in-scope generic block with the consumer change, or
record it in `docs/architecture/cutover-ledger.md`; do not add more generic
material beside a known misplaced block. Every structural pull request must
identify its signature-test row, canonical root, consumer, and Lean-level
specialization relationship in the pull-request checklist.

Generic moduli predicates belong under `CategoryTheory/Moduli/`. A replete
subprestack is represented by Mathlib's `Pseudofunctor.ObjectProperty` together
with closure under isomorphisms and mapped objects; its canonical construction
is `fullsubcategory`. Do not introduce a parallel geometric `Subprestack`
carrier, and do not call an indexed isomorphism-closed predicate a subprestack
until restriction stability is present. Finite-type parameter schemes,
geometric boundedness witnesses, atlases, and scheme presentations remain
geometric consumers.

`AlgebraicGeometry.RelativePerfectModuliSelector` is intentionally weaker than
a subprestack: its `familyLocus` and `geometricLocus` fields are independently
indexed replete object properties and supply no restriction maps. Finite-type
boundedness witnesses may consume that selector. Only after an ambient
pseudofunctor and `IsClosedUnderMapObj` are available may a geometric module
construct a subprestack, through the categorical `fullsubcategory` API.

## Higher categories, adjunctions, and limits

- Classify categorical dimension before choosing a subject owner. Definitions
  whose essential data are 2-morphisms, associators, unitors, pentagons,
  triangles, mates, pseudofunctors, strong transformations, or modifications
  belong at the bicategory or pseudofunctor root. An ordinary-functor or
  natural-isomorphism formula is a `Cat` projection of that source, not a more
  general owner.
- The canonical root for adjunction is Mathlib's
  `CategoryTheory.Bicategory.Adjunction`. Do not define a repository-owned
  competitor or treat ordinary functor adjunction as the more general notion.
- The equivalence `CategoryTheory.Adjunction.bicategoricalEquiv` identifies an
  ordinary `F ⊣ G` with the corresponding adjunction of 1-morphisms in `Cat`.
  Use the ordinary presentation in a theorem whose remaining signature is
  about functors, but keep the higher-categorical source explicit in the
  architecture.
- When duality in a monoidal category is genuinely being used as an
  adjunction, use Mathlib's one-object bicategory bridge
  (`MonoidalSingleObj`). This is a higher-categorical specialization, not a
  claim that monoidal structure is a superclass of every dg or triangulated
  category.
- Classify results *using* an adjunction by their conclusion. Preservation of
  limits or colimits belongs under `CategoryTheory/Limits/`; `Ext` adjunction
  belongs under `Triangulated/DerivedCategory/Ext/`; kernel-adjunction data
  belongs with the generic or geometric Fourier--Mukai consumer.
- Bicategories are the current implemented higher-category layer. Add general
  `n`-category or `(∞,1)`-category roots only together with an actual formal
  model and reusable interfaces; do not create empty nominal hierarchies.
- Objectwise-equivalence transport of Cat-valued pseudofunctor presentations
  belongs in `CategoryTheory/Pseudofunctor/Transport.lean`. Geometric and
  derived consumers must import that root and must not reproduce local
  functor/unit/compositor/pentagon/triangle transport helpers.

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
- The comparison `(DerivedCategory C)ᵒᵖ ≃ DerivedCategory Cᵒᵖ` is generic
  derived-category data and belongs in `DerivedCategory/Opposite.lean`.
  Exact algebraic linear duality and its derived lift belong in the adjacent
  `LinearDual.lean` specialization. A geometric duality theorem imports those
  roots and the canonical `AlgebraicGeometry/DerivedCategory/Coherent.lean`
  owner; it must not choose private replacement localizations for `Coh(X)` or
  `ModuleCat`.
- Generic `Ext` adjunction, dimension shift, and injective-resolution
  naturality belong under the derived-category root's `Ext/` child. Generic
  filtered-complex and total-complex spectral-sequence machinery belongs under
  `CategoryTheory/SpectralSequence/`.
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
- The underlying source of `TriangulatedFiberFamily` is a pseudofunctor
  `LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat`, and its identity and composition comparisons
  come from that source. Admit an ordinary strict `Bᵒᵖ ⥤ Cat` only through
  `TriangulatedFiberFamily.ofFunctor`; do not weaken the canonical root back
  to a strict functor for the convenience of one consumer.
- Generic stacks, discrete-stack construction from a sheaf, stack morphisms,
  and site-object representability belong under
  `CategoryTheory/Sites/StackInGroupoids/`. Big-Zariski representables,
  scheme-morphism properties, atlases, and algebraicity remain under
  `AlgebraicGeometry/Stacks/`.
- Čech constructions for arbitrary presheaves or sheaves on a site belong
  under `CategoryTheory/Sites/Cech/`. This includes cosimplicial exactness,
  injective-resolution bicomplexes, Čech-to-derived comparison, compact-open
  basis arguments, and finite-cover boundedness. Affine-scheme acyclicity,
  distinguished-open bases, and projective-space computations remain
  geometric consumers.
- Declarations owned by that generic family root use the
  `CategoryTheory.Triangulated.Families` namespace. Do not place
  `TriangulatedFiberFamily` or future neutral family APIs below a
  stability-condition namespace. Moduli boundedness uses the independent
  `CategoryTheory.Moduli` namespace.
- Scheme-derived category declarations owned by
  `AlgebraicGeometry/DerivedCategory/{Basic,Coherent}.lean` use the
  `AlgebraicGeometry.DerivedCategory` namespace. `Basic.lean` owns the
  module-sheaf specialization; `Coherent.lean` owns `D(Coh X)`, `Dᵇ(Coh X)`,
  and `Perf(X)` without importing family or pullback consumers. Scheme
  base-change and pullback declarations owned by
  `AlgebraicGeometry/DerivedCategory/Families/` use
  `AlgebraicGeometry.DerivedCategory.Families` and consume those canonical
  categories. Do not place these neutral geometric APIs below a categorical
  stability-condition namespace.
- Quasicoherent-cohomology loci and affine `Dqc` realizations owned by
  `AlgebraicGeometry/DerivedCategory/Dqc.lean` and its `Dqc/` subtree use
  `AlgebraicGeometry.DerivedCategory.Dqc`. Consumers should open or qualify
  that namespace explicitly; do not route `Dqc` declarations through a
  stability-family namespace.
- The general bounded-coherent and compact/perfect comparisons in `Dqc.lean`
  are explicit propositions, not global instances. Consume them through
  `Dqc/Comparison.lean` by passing evidence as an ordinary argument. Do not
  install an unconditional equivalence, essential-surjectivity instance, or
  compact/perfect instance for an unsupported scheme.
- `SchemeQuasicoherentDerivedCategory.zero` is canonical `Dqc` infrastructure
  and belongs in `AlgebraicGeometry/DerivedCategory/Dqc.lean`, with no local
  Noetherian hypothesis. A moduli consumer may prove that this object is
  pseudo-coherent, relative perfect, or universally gluable; it must not
  reconstruct an ambient, coherent, or bounded-coherent zero to define it.
- Keep the three perfect-complex notions distinct. `schemePerfect` is the
  absolute thick envelope in `D(Coh X)`; `schemeRelativePerfect p` is the
  base-dependent pseudo-coherent finite-Tor locus in `Dqc(X)`; and
  `TwoTermPerfectDeterminantData` is explicit two-term presentation data for a
  coherent sheaf. Cross-notion theorems live in
  `Moduli/PerfectComplex/Comparison.lean`. Add only proved one-way adapters;
  never infer an absolute/relative equivalence from the shared word “perfect”.
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
  moduli belong under `CategoryTheory/Moduli/`; neither
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
They must also update `docs/architecture/cutover-ledger.md` when a known lane is
completed or a new reverse-ownership block is confirmed.
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
