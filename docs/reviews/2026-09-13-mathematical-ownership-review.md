# Mathematical ownership and directory structure in DerivedAlgGeo

Review date: 13 September 2026. Source snapshot: [9edfb9d6a6b01556ac203a755666b91f46984a99](https://github.com/chris-dare-dev/derived-alg-geo-lean/tree/9edfb9d6a6b01556ac203a755666b91f46984a99), the GitHub HEAD resolved at the start of the review. Mathlib pin: `520045ab14e26149ee970e2e617ca04b09bde5d6` (`v4.32.1`).

**The repository has a sensible broad subject structure, but several intermediate directories assign ownership to the first application of a construction. Other directories do the opposite: they give application-specific terminology to ordinary mathematics. Those two tendencies explain much of the unease.**

The repair should be surgical. Preserve the general constructions and proved comparison maps already present; change their owners and separate comparisons from foundations. A grand renaming of every directory would obscure the mathematical work and would not by itself improve abstraction.

## Scope and strength of the review

I inventoried all 1,153 `.lean` files below `DerivedAlgGeo/`, totaling 225,634 lines, including aggregation and development files. I examined the whole directory inventory, module descriptions and declaration listings across subjects, and read the definitions and import boundaries underlying the findings in detail. The source snapshot linked above fixes the complete module inventory. This is a repository-wide architectural review with targeted declaration inspection, not a line-by-line verification of all proofs.

The existing `scripts/check_layering.py` passes on this snapshot. It reports 1,155 modules when including the two root files, and 258 of 381 geometry modules as stability-neutral. These numbers describe the existing policy, not mathematical correctness. I did not run a Lean build or change the repository. The downloaded snapshot was inspected separately from the user's working checkout, which was behind GitHub.

## The mathematical distinction that should govern the design

There are three different relationships:

1. **Subject ownership:** where a mathematician would look for the definition and its elementary theory.
2. **Logical dependency:** what must be imported to state and prove a result.
3. **Specialization or realization:** the projection, instance, class map, or comparison identifying one construction as an instance of another.

A directory tree cannot encode all three. A K3 surface is a surface; its derived category is triangulated and has a Serre functor; its algebraic Mukai lattice is a quadratic lattice; its central charge is an additive homomorphism constructed from characteristic classes. These relationships form a graph, not a single inheritance chain.

The basic placement test should be: **what mathematical object is this declaration about, and does that object have a natural independent theory?** Follow Mathlib's existing owner for a direct API extension. For a new subject, choose its mathematical owner. Then verify separately that generic modules do not import their realizations or comparisons with special cases.

This differs from filing every result under the weakest primitive in its signature. A stability condition does not belong under additive groups because its charge is a group homomorphism. Conversely, a Gram-determinant identity does not belong under Mukai theory just because the first use was a wall calculation.

## Central charges: the common parent must be more general than Chern characters

The proposed reuse across K3, Enriques, and threefold examples is right, but the ultimate parent should not require a Chern character or Todd class. Abstractly, a charge is a homomorphism `Z : Λ →+ ℂ`, often pulled back along a class map `K₀(C) →+ Λ`. Positivity relative to a heart, Harder–Narasimhan existence, a slicing, local finiteness, and a support condition are further structures or properties. This agrees with the separation in [Bridgeland's definition](https://arxiv.org/html/math/0212237#S1).

A geometric construction can then factor as

```text
K₀(C) ──class/realization──▶ numerical classes
      ──Chern character───▶ graded numerical ring
      ──multiply by κ─────▶ corrected classes
      ──linear functional─▶ ℂ.
```

For a suitable graded realization, an exponential family has the schematic form

\[
Z_{B,\omega,\kappa}(E)
=-\int_X e^{-(B+i\omega)}\operatorname{ch}(E)\,\kappa.
\]

Here `κ = 1` and `κ = √td(X)` are distinct choices, with explicit sign and normalization conventions. A common constructor should expose the correction, not silently substitute one for the other. A formula alone does not prove that it defines a stability condition on a chosen heart.

The repository already has much of this factorization: `ChargeFamily`, `Exp.ofMoments`, `corrComp`, `hDegreesHom`, and their comparison theorems. The recommendation is to make those roots independently importable. In particular, preserve the distinction between the variety dimension `n` and truncation degree `m`; the code explicitly supports a threefold tilt construction with `(n,m) = (3,2)`. Do not assert that every threefold or higher-dimensional stability charge is merely the full exponential formula at a different dimension; additional coefficients, corrections, hearts, and support inequalities can matter.

K3 and Enriques should be siblings under a surface/numerical-surface construction, not ancestors of each other. Calabi–Yau conditions, dimension, polarization, divisor rank, and integrality are largely independent refinements. Surface Mukai integrality and symmetric Euler-pairing identifications must remain hypotheses or theorems of the appropriate specialization; they cannot be inherited universally from the existence of a Todd class. The distinction between ordinary and Todd-corrected charges already appears explicitly in the repository's divisorial Mukai code.

## Walls and period domains: a correction to the proposed intuition

There are at least four useful notions here:

- **An orthogonality or charge-zero locus:** `Z(δ) = 0`.
- **A numerical alignment locus:** `Re Z(v) Im Z(w) − Im Z(v) Re Z(w) = 0`.
- **A signed ray locus:** for example `Z(δ) ∈ ℝ≤0` in an exponential chart.
- **An actual destabilization wall:** an appropriate numerical locus together with categorical existence and stability data.

The first is generically real codimension two, while the second is generically real codimension one. The determinant equation also includes opposite rays and zero charges; equal phases require additional nonvanishing and sign conditions. Degenerate equations need not define hypersurfaces at all. Thus a common `RealCodimensionOneSubmanifold` parent would be mathematically incorrect for the current collection. General regular-level-set results can be imported when one proves smoothness and transversality for a particular locus.

There is a second distinction: `PeriodDomain.periodDomain` stores **unoriented positive two-planes**, whereas the ordered real and imaginary parts of a complex vector constitute a **positive frame**. Forgetting the frame loses a basis, and forgetting orientation loses further information. Bridgeland's K3 charge domain is a locus of complex vectors whose real and imaginary parts span positive planes; it is not literally the set of submodules in the current definition. His paper explicitly describes the change-of-basis action on this locus. The identification needs the appropriate frame/quotient maps. [Bridgeland, K3 stability](https://arxiv.org/html/math/0307164).

This does not make positive-plane theory specific to algebraic geometry. It makes `PositivePlane`, `PositiveFrame`, `OrthogonalityLocus`, and a geometric period-domain realization better-separated names. Keep general signature and positivity results in quadratic-form theory. A future Hodge-theoretic period-domain API or manifold structure can be added when those structures are actually present.

## Findings

The priorities below rank architectural consequence, not proof soundness. “High” means that the current ownership obscures an independent root, a required mathematical distinction, or a real dependency inversion. “Medium” means a clearer owner or terminology would improve reuse and navigation. Proposed new paths are local recommendations; they are not claims that Mathlib already contains modules with those names.


### 01. Separate complex linear functionals from central-charge applications

**High priority — Quadratic forms.**

PeriodDomain.centralCharge is the complex-valued functional obtained from two polar pairings. Additivity, real linearity, and the description of its kernel are ordinary bilinear algebra. The same file then presents the negative-kernel theorem as ‘the support property’ and interprets orthogonality loci as walls. WallFiniteness likewise puts continuity of arbitrary quadratic forms, coercivity of positive-definite forms, and boundedness of level sets in a file named after spherical walls.

**Recommended ownership.** Keep the neutral functional and kernel statements under LinearAlgebra/BilinearForm/ComplexPairing.lean or QuadraticForm/ComplexPairing.lean, and extract continuity/coercivity into QuadraticForm/Continuous.lean and QuadraticForm/Bounds.lean. Put the central-charge interpretation and support-property adapter under StabilityCondition/CentralCharge/Quadratic.lean and StabilityCondition/Support/. A mathematical term in a filename should identify what the API actually owns.

**Limits and distinctions.** This is a split, not a wholesale move into algebraic geometry. The existing definition has no category, heart, Chern character, or scheme. Negative definiteness on ker Z is only one part of the quadratic support criterion; nonnegativity on the relevant semistable classes is an additional requirement. The repository’s Weak/Support/Predicate/Quadratic.lean:57 explicitly records both. This is a documentation and abstraction-boundary finding, not a claim that the kernel theorem is false.

Source: [DerivedAlgGeo/LinearAlgebra/QuadraticForm/CentralCharge.lean:61](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/QuadraticForm/CentralCharge.lean#L61); [DerivedAlgGeo/LinearAlgebra/QuadraticForm/WallFiniteness.lean:60](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/QuadraticForm/WallFiniteness.lean#L60)


### 02. Distinguish positive planes, positive frames, and stability walls

**High priority — Quadratic forms.**

periodDomain is a set of two-dimensional submodules; Orientation instead uses ordered pairs. Neither carrier is interchangeable with the other. PeriodDomain.wall imposes orthogonality to a class, whereas ChargeFamily.wall imposes real linear dependence of two charges. The spherical chart also has a signed half-wall, and Chambers defines components after removing charge-zero loci. The existing comparison file correctly distinguishes some of these constructions, but the directory and umbrella names still compress them into ‘walls’ and ‘period domains’.

**Recommended ownership.** Use QuadraticForm/PositiveSubspace/ and PositiveFrame/ for the neutral theory, and a clearly named OrthogonalityLocus or HyperplaneArrangement module for the deleted loci. Retain arrangement finiteness as reusable quadratic/lattice mathematics when formulated independently of stability. Under stability distinguish Walls/Numerical, Walls/Actual, and ChargeZeroLocus or RegularLocus; do not create an Actual directory until there is actual destabilization content. Put the K3 identification with the appropriate framed domain in its geometric realization.

**Limits and distinctions.** A real codimension-one submanifold is not a sufficient parent for these notions. Z(δ)=0 is generically two real equations; phase alignment is generically one and still requires nonvanishing, a sign, and destabilizing objects to describe an actual stability wall. The current plane API does not supply a manifold theorem. Moving it into Geometry/Manifold would claim more structure than it has.

Source: [DerivedAlgGeo/LinearAlgebra/QuadraticForm/PeriodDomain.lean:91](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/QuadraticForm/PeriodDomain.lean#L91); [DerivedAlgGeo/LinearAlgebra/QuadraticForm/Orientation.lean:65](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/QuadraticForm/Orientation.lean#L65); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/ChargeFamily.lean:118](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/ChargeFamily.lean#L118); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Spherical/WallComparison.lean:8](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Spherical/WallComparison.lean#L8); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Chambers/Basic.lean:9](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Chambers/Basic.lean#L9)


### 03. Unpack the Mukai subtree into a hyperbolic extension and its applications

**High priority — Lattices.**

MukaiLattice N is ℤ × N × ℤ with pairing b(c,c′) − rs′ − r′s. That is an abstract hyperbolic extension, rather than the Mukai lattice of an actual surface. Yet Basic also exports IsSpherical and expectedDim = square + 2. Reflection and rank-two Gram identities are restricted to this particular extension even though their arguments are standard bilinear-lattice arguments. RealForm then mixes the quadratic extension with its exponential chart.

**Recommended ownership.** Create a neutral HyperbolicExtension owner beside the relevant bilinear-form API. Extract norm-minus-two reflections and Gram-determinant identities to general bilinear/lattice modules, parameterized by an arbitrary ambient lattice. Keep the exponential chart with numerical central-charge constructions. Keep the Mukai vector, integral structure, Euler comparison, and actual surface realization in AlgebraicGeometry/Numerical/Mukai and the appropriate surface modules. Replace generic IsSpherical terminology by a root or square condition; reserve spherical-object terminology and expected moduli dimension for the application.

**Limits and distinctions.** Mukai is already a child of LinearAlgebra/Lattice, not a top-level repository subject. The geometric name is defensible for a conventional abstract construction; the stronger problem is mixing independent mathematics with its interpretation and specializing the reusable reflection API too early. An arbitrary additive group with a form need not be finite free or nondegenerate, so ‘lattice’ must not silently imply these extra hypotheses.

Source: [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean:51](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean#L51); [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean:188](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean#L188); [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean:216](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Basic.lean#L216); [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Reflection.lean:73](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/Reflection.lean#L73); [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/RankTwo.lean:43](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/RankTwo.lean#L43); [DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/RealForm.lean:139](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/RealForm.lean#L139)


### 04. Central-charge construction is upstream of wall equations

**High priority — Stability.**

Walls owns exponential charge construction, Chern-character coordinates, divisor spaces, square-root Todd data, Hodge-index certificates, and support discriminants. These objects are needed to construct charges and prove positivity before a wall question is asked. The subtree is named for a major consumer rather than for its foundation.

**Recommended ownership.** Give CentralCharge/ its own lightweight owner within the stability subject, with Family, Exponential, Quadratic, and appropriately named numerical constructors. Let Walls/ import it. Put Hodge-signature linear algebra in a neutral form module, geometric Chern/Todd realizations in Numerical/, and semistable support statements in Support/. The precise home of the abstract divisorial numerical model is a policy choice; retaining it under a stability numerical-construction folder is reasonable, but burying it under Walls is not helpful.

**Limits and distinctions.** The existing ChargeFamily and Exp.ofMoments are valuable roots. Preserve them and their proved specialization maps. Do not introduce another common central-charge record merely to improve names. The current layering gate explicitly requires six divisorial structures to live under Walls, so this recommendation requires a deliberate policy update rather than just moving files.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Exp/Kernel.lean:84](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Exp/Kernel.lean#L84); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Charge.lean:9](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Charge.lean#L9); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Mukai.lean:77](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Mukai.lean#L77); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Discriminant.lean:86](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Discriminant.lean#L86)


### 05. Serre functors do not require triangulated categories

**High priority — Categorical foundations.**

The public SerreFunctorData and HomFinite definitions require a k-linear category, and the module explicitly says no shift or triangulation is needed. Their home under Triangulated is therefore an unnecessarily specialized parent. Uniqueness additionally exports isoOfLinearYonedaIso and hom_ext_of_linearYoneda, which do not even require a Serre functor.

**Recommended ownership.** Move the general Serre definitions and uniqueness theorem to CategoryTheory/Linear/SerreFunctor/. Move the standalone Yoneda helpers to CategoryTheory/Linear/Yoneda.lean. Keep Ext profiles, shift relations, Enriques-category refinements, and triangulated compatibility in a triangulated specialization importing the linear root.

**Limits and distinctions.** Do not move every file in SerreFunctor/ together: Objects, Classification, and Enriques involve additional structures. Split by declarations. This is one of the clearest misplacements because the source itself gives the weaker natural owner.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/SerreFunctor/Basic.lean:58](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/SerreFunctor/Basic.lean#L58); [DerivedAlgGeo/CategoryTheory/Triangulated/SerreFunctor/Uniqueness.lean:58](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/SerreFunctor/Uniqueness.lean#L58)


### 06. Abelian stability and μ-stability are placed under later theories

**High priority — Stability.**

StabilityFunctionOn uses a class datum and an additive charge; its abelian specialization uses only an abelian category. Its slope and HN API is nevertheless deep below Triangulated/StabilityCondition/Weak/Foundation. On the geometric side, μ-stability and the μ-HN existence theorem sit under Gieseker, although slope and Gieseker stability are distinct theories with comparison results.

**Recommended ownership.** Place abelian stability functions and their HN theory under CategoryTheory/Abelian/StabilityFunction/, with weak variants as children and separate quasi-abelian extensions where needed. Keep restriction to hearts and reconstruction of triangulated stability in Triangulated/StabilityCondition/. Under AlgebraicGeometry/Stability use sibling Slope/ and Gieseker/ developments, with HilbertPolynomial data shared and Comparison.lean joining them.

**Limits and distinctions.** Weak/ below StabilityCondition is not itself a defect: directory nesting can name a variant even when the stronger theory imports the weaker. The problem here is the independent abelian subject and μ-HN results being owned by later consumers. Do not label the current μ-HN theorem as a proof of Gieseker HN existence merely because of its directory.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Weak/Foundation/StabilityFunction/Basic.lean:35](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Weak/Foundation/StabilityFunction/Basic.lean#L35); [DerivedAlgGeo/AlgebraicGeometry/Stability/Gieseker/MuStability.lean:102](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Stability/Gieseker/MuStability.lean#L102); [DerivedAlgGeo/AlgebraicGeometry/Stability/Gieseker/HarderNarasimhan/Existence.lean:146](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Stability/Gieseker/HarderNarasimhan/Existence.lean#L146)


### 07. Several purported parents still import their specializations

**High priority — Numerical geometry.**

The general sqrtComp and sqrtToddComp file imports Numerical/RiemannRoch/K3 and ends with K3 specializations. PolarisedWallTransport advertises all dimensions and corrections but imports both the surface and threefold transports to prove comparison theorems. The abelian-surface model imports K3, and Enriques imports the abelian model, partly to supply comparative examples. These are concrete dependency inversions or sibling couplings, not merely unconventional folder names.

**Recommended ownership.** Separate square-root algebra, Todd construction, and K3 simplification. Make the generic polarised transport import only its numerical data, correction, and charge kernel; put old/new agreement theorems in a downstream Comparison module. Extract a shared surface model constructor and move K3/abelian/Enriques comparison witnesses into a downstream Models/Surface/Comparison.lean.

**Limits and distinctions.** The present comparisons are good mathematics and should remain. A comparison theorem does not, by itself, make the import graph follow the claimed abstraction. The codimension-four bound on sqrtComp is explicit and must survive any relocation; it is not currently an arbitrary-degree square-root construction.

Source: [DerivedAlgGeo/AlgebraicGeometry/Numerical/Mukai/SqrtTodd.lean:5](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Mukai/SqrtTodd.lean#L5); [DerivedAlgGeo/AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean:5](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean#L5); [DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Abelian.lean:5](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Abelian.lean#L5); [DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Enriques.lean:5](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Enriques.lean#L5)


### 08. The universal cover of GL⁺(2,ℝ) should be usable independently of its stability action

**Medium priority — Independent mathematics.**

GLTilde includes a group construction, deck transformations, a covering map, simple connectedness, and topological-group laws. NormalizedShift is an order automorphism of ℝ commuting with unit translation. These are recognizable independent mathematical objects, whereas Action/ genuinely concerns stability conditions.

**Recommended ownership.** Extract the neutral group and covering development beside the general-linear-group API, for example LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/, with general covering lemmas near Topology/Covering. Keep phase conventions and the action on slicings, charges, and stability conditions in Symmetry/GLTilde/Action/. Put a general complex-coordinate linear-map adapter near LinearAlgebra/Complex when its public type is independent of GLTilde.

**Limits and distinctions.** The exact new path is a proposed local extension, not an existing Mathlib module. The present compatible-pair construction can be retained. Its π-normalization is a convention to expose through adapters, not a reason to make covering-space theory part of triangulated categories.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Basic.lean:164](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Basic.lean#L164); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/ComplexRepresentation.lean:29](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/ComplexRepresentation.lean#L29); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Phase/NormalizedShift.lean:36](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Phase/NormalizedShift.lean#L36)


### 09. Mass and planar convex geometry should not be owned by metric proofs

**Medium priority — Stability.**

HN mass is an invariant of an object and a stability condition, used by metrics but also by mass–Hom estimates and dynamical constructions. Metric/Mass/Subadditivity/PolygonPerimeter goes further: it defines real continuous linear functionals on ℂ and proves Euclidean polygon inequalities inside a triangulated namespace.

**Recommended ownership.** Make StabilityCondition/Mass/ a sibling of Metric/. Keep the metric construction downstream. Extract the category-independent polygonal-path carrier and perimeter comparison into an Analysis/Convex/ or Geometry/Euclidean/ module after checking the available Mathlib API; keep HN-polygon and mass adapters in stability.

**Limits and distinctions.** A longer path is acceptable when it names genuine mathematical subdivisions. Here the objection is independent content trapped inside the proof of one application. Introducing Analysis or Geometry would require registering the subject in the local layering policy.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Metric/Mass/Basic.lean:56](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Metric/Mass/Basic.lean#L56); [DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Metric/Mass/Subadditivity/PolygonPerimeter.lean:17](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/Metric/Mass/Subadditivity/PolygonPerimeter.lean#L17)


### 10. Fourier–Mukai currently owns general derived operations

**High priority — Derived geometry.**

HasDerivedPushforward and HasDerivedTensor are declared inside KernelCorrespondence; HasCoherentDerivedTensor is in the Fourier–Mukai subtree. A derived tensor product, its monoidal coherence, and a derived pushforward are foundations of scheme-derived geometry with many consumers besides integral transforms. At the categorical end, Correspondence itself requires only three ordinary categories, a pull functor, a bifunctor, and a push functor.

**Recommended ownership.** Move geometric tensor capabilities and coherence to DerivedCategory/Tensor/ or Monoidal/, and pushforward to the existing derived-functor/family owner. Let FourierMukai own correspondences, kernels, convolution, units, adjoints, and theorems about their transforms. Consider a CategoryTheory/KernelTransform/ root for the purely functorial correspondence, with Triangulated/KernelTransform/Exactness and the geometric FourierMukai realization downstream.

**Limits and distinctions.** Preserve every hypothesis and witness boundary: Dᵇ(Coh X) is not automatically closed under arbitrary derived tensor on a singular scheme. These records are supplied capabilities, not constructed operations in full generality. The categorical rename is less urgent than extracting geometric tensor/pushforward: ‘abstract Fourier–Mukai formalism’ is a defensible subject name.

Source: [DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/KernelCorrespondence.lean:108](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/KernelCorrespondence.lean#L108); [DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/KernelCorrespondence.lean:169](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/KernelCorrespondence.lean#L169); [DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/DerivedTensorCoherence.lean:57](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/DerivedTensorCoherence.lean#L57); [DerivedAlgGeo/CategoryTheory/Triangulated/FourierMukai/Basic.lean:68](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/FourierMukai/Basic.lean#L68)


### 11. Moduli should consume relative perfection rather than define it

**High priority — Derived geometry.**

The moduli subtree defines flatness of a module sheaf over a morphism, pseudo-coherence, and local finite Tor amplitude. These notions concern individual sheaves or complexes and are needed for base change and derived operations before a moduli functor is introduced.

**Recommended ownership.** Move Modules.IsFlatOver to Modules/Flat.lean or a corresponding relative-module owner. Move the derived-object predicates and local models to DerivedCategory/Perfect/Relative.lean and a precise pseudo-coherence owner. Keep presheaves, restriction stability, boundedness, openness, atlases, and algebraicity under Moduli/PerfectComplex/.

**Limits and distinctions.** The source explicitly warns that its bounded-above finitely-presented-cohomology predicate is the Noetherian criterion and is not standard pseudo-coherence on arbitrary schemes. Preserve this distinction in naming or hypotheses. A move must not promote it to an unrestricted canonical definition, or identify the repository’s different perfectness notions without their comparison theorems.

Source: [DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean:56](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean#L56); [DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean:75](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean#L75); [DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean:119](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean#L119)


### 12. Separate reusable numerical models, specializations, and geometric realizations

**Medium priority — Numerical geometry.**

Examples contains shared constructors, extensive charge calculations, comparison maps, and wall results used by the library. K3 material is scattered through Numerical/Examples, Numerical/RiemannRoch, Numerical/GrothendieckGroup, Surface, and DerivedCategory/Stability. Some of this separation reflects real mathematical layers; ‘Examples’ and broad filenames such as GrothendieckGroup/CentralCharge conceal which layer and which specialization are present. The latter file is explicitly in namespace Numerical.K3.

**Recommended ownership.** Use Numerical/Models/ for explicit algebraic models, place reusable constructors outside the example leaves, and give Surface/K3, Surface/Enriques, and dimension specializations explicit homes within the numerical subject. Keep actual scheme realizations with Surface/K3/ and Surface/Enriques/, or consistently use object-specific children of DerivedCategory/Stability; choose one convention and document it. Put K3-only charge adapters in a visibly K3-specific module.

**Limits and distinctions.** Do not collapse all K3 files into one folder or identify a numerical model with a scheme. The Enriques example explicitly models a polarization slice of a rank-ten numerical divisor lattice; its title ‘Picard rank one’ is misleading. In higher dimensions Picard rank one alone does not imply that the entire numerical intersection ring is ℚ[H]/(H^(n+1)); the RankOne file’s stronger generated-by-H assumption is the one that matters.

Source: [DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/RankOne.lean:79](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/RankOne.lean#L79); [DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Enriques.lean:29](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/Enriques.lean#L29); [DerivedAlgGeo/AlgebraicGeometry/Numerical/GrothendieckGroup/CentralCharge.lean:45](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Numerical/GrothendieckGroup/CentralCharge.lean#L45); [DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Stability/K3MukaiTiltScheme.lean:1](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Stability/K3MukaiTiltScheme.lean#L1)


### 13. There are small, direct violations of the stated definition-site rule

**Medium priority — Mathlib alignment.**

The linear-dual functor on ModuleCat sits under CategoryTheory/ModuleCat while its exactness sits at Algebra/Category/ModuleCat. The file Sheaf/ExteriorPower actually constructs exterior powers of PresheafOfModules. Closure of quasicoherent sheaves under extensions is filed under Cohomology because of its proof. Restriction of exterior powers is under Divisors even though its public subject is module sheaves.

**Recommended ownership.** Consolidate module-category linear duality at Algebra/Category/ModuleCat/LinearDual/, move presheaf exterior powers to ModuleCat/Presheaf/ExteriorPower.lean, quasicoherent extension closure to AlgebraicGeometry/Modules/Quasicoherent/Extensions.lean, and exterior-power restriction to Modules/ExteriorPower/Restriction.lean. Keep divisor-specific determinant and Cartier applications under Divisors.

**Limits and distinctions.** Check the import graph while splitting the quasicoherent file: affine/cohomological helper declarations may need separate owners to avoid a cycle. A cohomological proof does not make the theorem’s subject cohomology, but it can explain why an earlier implementation put it there.

Source: [DerivedAlgGeo/CategoryTheory/ModuleCat/LinearDual.lean:33](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/ModuleCat/LinearDual.lean#L33); [DerivedAlgGeo/Algebra/Category/ModuleCat/Sheaf/ExteriorPower.lean:33](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/Algebra/Category/ModuleCat/Sheaf/ExteriorPower.lean#L33); [DerivedAlgGeo/AlgebraicGeometry/Cohomology/Quasicoherent/Extensions.lean:9](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Cohomology/Quasicoherent/Extensions.lean#L9); [DerivedAlgGeo/AlgebraicGeometry/Divisors/ExteriorPower.lean:9](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/AlgebraicGeometry/Divisors/ExteriorPower.lean#L9)


### 14. The placement policy confuses API ownership, prerequisites, and application names

**Medium priority — Policy and navigation.**

The policy correctly keeps genuine Mathlib API extensions at their upstream paths. It then overstates this as a universal carrier rule, while also recognizing conceptual ownership for weak charges and placing analogous numerical constructions under Walls. The gate verifies the geometry firewall and particular owners, but treats the entire Numerical subtree as allowed to consume stability. It therefore cannot reject the parent/child numerical inversions found here. The checker passed on this snapshot.

**Recommended ownership.** Distinguish a direct extension of an existing API from a new mathematical object built using that API. For the latter, choose its established subject and an appropriately general root. Track named component dependencies, including numerical core → no stability constructions, charge construction → no wall classification, and geometric derived operations → no Fourier–Mukai or moduli consumers. Add focused forbidden-import fixtures for these components rather than a total order on top-level subjects.

**Limits and distinctions.** A directory is an index, the Lean import graph is a dependency DAG, and specialization maps form another graph. They should be consistent, but they cannot be identical. Proposed names here are local architecture recommendations, not guarantees of future Mathlib acceptance. Keep narrowly imported modules distinct from full subject umbrellas.

Source: [docs/architecture/placement.md:1](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/docs/architecture/placement.md#L1); [scripts/check_layering.py:97](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/scripts/check_layering.py#L97); [AGENTS.md:36](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/AGENTS.md#L36)


### 15. Construct H⁰ and its triangulation with the dg category; distinguish an enhancement from an underlying presentation

**High priority — DG categories.**

The dg category has its root under Algebra/Homology/DGCategory, but its H⁰ shift, cone triangles, functor exactness, and related constructions are owned by Triangulated/DGEnhancement/H0. These constructions concern H⁰ of a dg category before choosing an enhancement of some external category. Basic additionally defines Enhancement for an ordinary category using a plain equivalence, explicitly weaker than an exact equivalence to an already triangulated category.

**Recommended ownership.** Keep the current dg encoding root provisionally at Algebra/Homology/DGCategory; place generic H⁰ constructions and pretriangulated H⁰ results below that owner. Reserve Triangulated/DGEnhancement for exact comparisons with a specified triangulated category and their transport. Name the weaker package as an underlying H⁰ presentation, and make an exact enhancement a refinement carrying the compatibility data. Leave Mathlib homotopy-category realizations at Algebra/Homology/HomotopyCategory/DGEnhancement.

**Limits and distinctions.** This is not a request to re-encode the library as enriched categories. Using HomComplex is an implementation choice, not an inheritance relation, but a mature homological-algebra home is defensible. Preserve the existing proved agreement for the complexes model. Exactness is necessary to match the standard enhancement notion; it does not imply a general uniqueness-of-enhancements theorem.

Source: [DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/Basic.lean:71](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/Basic.lean#L71); [DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/Basic.lean:105](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/Basic.lean#L105); [DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/H0/Shift.lean:78](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/H0/Shift.lean#L78); [DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/H0/Triangle.lean:115](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/9edfb9d6a6b01556ac203a755666b91f46984a99/DerivedAlgGeo/CategoryTheory/Triangulated/DGEnhancement/H0/Triangle.lean#L115)

## A proposed ownership map

This is a conceptual destination map, not a command to create every directory now. All paths are relative to `DerivedAlgGeo/`. Existing Mathlib owners remain authoritative for actual Mathlib extensions.

```text
Algebra/
  Category/ModuleCat/{LinearDual, Presheaf, Sheaf}/
  Homology/
    DGCategory/
      H0/                       ordinary H⁰ construction
      Pretriangulated/H0/       shifts, triangles, exact dg functors
      Model/                    explicit dg models
    DerivedCategory/            Mathlib-derived-category extensions
    HomotopyCategory/           extensions and the concrete dg realization

LinearAlgebra/
  BilinearForm/
    ComplexPairing              two real functionals packaged into ℂ
    HyperbolicExtension/        generic construction behind the Mukai model
    ...                        generic reflections and Gram determinants
  QuadraticForm/
    SignatureAdditive
    Continuous, Bounds
    PositiveSubspace/, PositiveFrame/
    OrthogonalityLocus/         neutral incidence and arrangement theory
  Matrix/GeneralLinearGroup/UniversalCover/

CategoryTheory/
  Linear/SerreFunctor/          no shift or triangulation required
  Linear/Yoneda
  Abelian/StabilityFunction/    charges, slopes, semistability, HN
  KernelTransform/             optional neutral functorial root
  Triangulated/
    GrothendieckGroup/, TStructure/, SemiorthogonalDecomposition/
    DGEnhancement/             exact comparison with an external category
    SphericalTwist/
    StabilityCondition/
      CentralCharge/           numerical families and categorical adapters
      Slicing/, Deformation/, Support/
      Mass/, Metric/
      Walls/                   alignment and destabilization results
      RegularLocus/            charge-zero complements, separately named
      Symmetry/                applications of the independent groups
      Families/
      Weak/                    weak triangulated stability and comparisons

AlgebraicGeometry/
  Modules/{Flat, ExteriorPower, Quasicoherent, Coherent, Tensor}/
  DerivedCategory/
    Dqc/, Perfect/, Tensor/, Families/
    FourierMukai/              kernels, convolution, geometric transforms
    Stability/                 common geometric derived-stability adapters
  IntersectionTheory/, RiemannRoch/
  Numerical/
    Core/, CharacteristicClass/, Mukai/
    CentralCharge/             geometric/numerical Chern–Todd realization
    Surface/, Threefold/, Fourfold/
    Models/                    explicit arithmetic models, honestly labeled
  Stability/{HilbertPolynomial, Slope, Gieseker}/
  Surface/
    K3/{Numerical, Stability, FourierMukai}/
    Enriques/{Numerical, Stability, FourierMukai}/
  Moduli/{PerfectComplex, Semistability, HarderNarasimhan, Quot}/
```

`CentralCharge` at the categorical level and at the geometric level must have different jobs. The former consumes additive class maps and defines numerical families or categorical compatibility. The latter realizes them using geometric characteristic data. The primitive charge remains Mathlib's existing additive-hom type. The abelian root and its common charge/class-datum definitions must remain importable without triangulated stability.

The `Surface/K3/...` and `Surface/Enriques/...` rows mean actual surface realizations; the numerical subject retains arithmetic models that are not themselves surfaces. If the project prefers `DerivedCategory/Stability/K3/` for the actual derived-category application, that alternative is also coherent. Pick one owner per declaration and use documentation and narrow imports for discoverability instead of duplicating APIs. Neither Enriques geometry nor threefold geometry should inherit from K3 geometry.

Extract arbitrary truncated-polynomial or graded square-root identities into the corresponding ring/graded-algebra subject when they have an independently useful API. Keep the characteristic-class meaning in algebraic geometry. There is no benefit in stripping a construction of all mathematical names just to obtain the weakest possible signature.

## What I would preserve

- **The single library and Mathlib-like top-level subjects.** Nothing in this review justifies splitting the project into separate repositories. Lake already provides Mathlib interoperability; matching local directory names improves navigation and future upstream work but is not required to import Mathlib.
- **Derived categories under `Algebra/Homology/DerivedCategory`.** This follows the actual Mathlib construction. Moving them to `CategoryTheory/Triangulated/DerivedCategory` would create a less recognizable local fork of the upstream layout.
- **The sheaf/site/scheme distinction.** Arbitrary ringed-site module sheaves, topological-space sheaves, and scheme module sheaves have different owners. `Algebra/Category/ModuleCat/Sheaf`, `CategoryTheory/Sites`, `Topology/Sheaves`, and `AlgebraicGeometry/Modules` are useful boundaries, despite the repetition of words like tensor, cohomology, and restriction.
- **The geometric derived-category/Fourier–Mukai split.** An abstract kernel-transform API and a scheme realization are different layers, not prima facie duplication. The defect is the general operations buried inside the geometric consumer.
- **The generic Grothendieck-presentation spine.** Short-exact and triangle relations lead to distinct realizations; the repository already expresses substantial reuse here. Do not conflate abelian K₀, triangulated K₀, and a numerical quotient just because their names overlap.
- **Explicit mathematical hypotheses and comparison theorems.** Numerical realizations, exact enhancements, positivity input, relative perfectness, and actual surface geometry must remain separate until a theorem joins them. A descriptive directory name must never stand in for such a theorem.
- **The geometry firewall and development leaf.** Strengthen these with a few component-level rules; do not replace them with a rigid ranking of all subjects.

The scan found no comparable architectural reason to reorganize the small `RingTheory`, `AlgebraicTopology`, or general `Topology` subtrees. The ordinary algebra, site theory, Proj, cohomology, divisor, and duality developments are broadly sensibly placed; the concrete counterexamples above merit attention without condemning those whole subjects.

## A migration order that would produce mathematical benefit

1. **Correct the conceptual labels first.** Document the four wall notions, frames versus planes, the two clauses of quadratic support, numerical models versus geometric realizations, and underlying H⁰ presentations versus exact enhancements. These distinctions tell later contributors which theorem they still have to prove.
2. **Remove the explicit dependency inversions.** Split the square-root/K3 file, the generic/specialized polarised transports, and cross-surface comparison examples. Keep the agreement theorems downstream.
3. **Extract small, unambiguous Mathlib extensions.** Module-category duality, presheaf exterior powers, Yoneda helpers, quadratic coercivity, and the quasicoherent extension theorem are relatively contained changes. Reuse existing public declaration names where possible.
4. **Repair the main mathematical owners.** Serre duality, abelian stability, generic H⁰ constructions, derived tensor/pushforward, and relative perfectness. Each should be a separate reviewable change with a stated root-to-consumer relationship.
5. **Reorganize central charges, Mukai applications, and numerical models.** Preserve existing formulas and proved specializations; extract the hyperbolic extension, general reflections, and Gram theory. Make charges upstream of walls and geometric realizations downstream of numerical construction.
6. **Improve remaining navigation.** Extract the GL cover and planar convex geometry; make mass a sibling of metric; simplify `Foundation` and proof-shaped paths only where a clearer mathematical subject replaces them. Paper-number filenames such as `MassHomTheorem75` and `PaperTorelli` should gain descriptive theorem names or a consistent application folder, with the paper citation retained in documentation.

For each structural change, update imports, umbrellas, source-owner assertions, audit routing, declaration baselines, documentation, and CI paths together. Add a focused import-boundary check to prevent the same regression. Preserve historical-name compatibility through the repository's existing executable-only mechanism where required; do not add a forest of import-only compatibility shims against the project's retirement policy.

A generic core need not import its subject's complete umbrella. In particular, new neutral numerical umbrellas should omit model and stability consumers, just as the current scheme-derived umbrella deliberately omits stability. The blanket re-export-every-child convention should permit additional documented exceptions when a subject contains both a foundation and expensive applications.

Validate moves with the lightweight architecture checks and targeted Lean builds where available, then the project's prescribed full CI. The layering check performed for this review is evidence only about the current snapshot; it does not validate this proposed refactor.

## The policy I would adopt

> Extend existing Mathlib APIs at their established owners. Place new concepts in the subject that studies them, separating independently useful foundations from their applications. Require an explicit specialization or realization map for every claimed abstraction relationship, and verify that the root does not import its consumers. Use directories for mathematical navigation and import checks for dependency discipline; neither replaces the other.

The central ambition should be that a mathematician can read an import and know both **which theory is being invoked** and **what has actually been constructed**. That is a more durable organizing principle than either “everything goes where its carrier is implemented” or “everything with a geometric motivation goes under algebraic geometry.”
