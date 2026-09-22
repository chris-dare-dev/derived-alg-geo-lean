# Spec Delta

## Purpose

This capability gives abstract pretriangulated categories a numerical invariant for the least extension depth of a single-object generator, and makes that invariant comparable with the repository's owner closure and transportable across triangulated functors.

## ADDED Requirements

### Requirement: Rouquier dimension uses the single-object generation time

For a pretriangulated category with the integral shift and additive structure required by the generation-time API, the library SHALL define Rouquier dimension as the infimum over objects G of the generation time from the singleton property `ObjectProperty.singleton G` to all objects, with values in `ℕ∞`. The API SHALL state that `(ObjectProperty.singleton G).triangEnvelopeIter n` is Rouquier's `⟨G⟩_{n+1}`, so this definition matches Rouquier's dimension with zero offset. It SHALL expose the finite-bound, finite-dimension, classical-generator, and zero-dimension characterisations.

#### Scenario: Finite bound is witnessed at the same index

- **WHEN** `rouquierDim C ≤ (n : ℕ∞)`
- **THEN** some object G has `(ObjectProperty.singleton G).triangEnvelopeIter n = ⊤`

#### Scenario: Finite dimension gives a classical generator

- **WHEN** `rouquierDim C ≠ ⊤`
- **THEN** some singleton is a strong triangulated generator and hence a classical triangulated generator

#### Scenario: Zero dimension requires no extension step

- **WHEN** `rouquierDim C = 0`
- **THEN** some object G satisfies `((ObjectProperty.singleton G).shiftClosure ℤ).binaryProductsClosure.retractClosure = ⊤`

#### Scenario: The invariant does not select a chosen generator

- **WHEN** a client asks for the Rouquier dimension of a category
- **THEN** the result is a value over single objects and does not package a particular minimizing object; the definition does not quantify over arbitrary object properties

### Requirement: The owner extension closure has only proved comparisons

The library SHALL compare the repository's `ExtensionClosure P` with Mathlib's iterated extension products and triangulated envelope without adding shift-closed, thick, or triangulated-subcategory structure to `ExtensionClosure`. It SHALL provide a typeclass-vocabulary corollary of the existing induction principle for properties closed under isomorphisms, containing zero, and closed under distinguished extensions, and document that these assumptions repackage the raw induction hypotheses. Every finite Mathlib extension-product iterate SHALL lie in `ExtensionClosure P`. The reverse inclusion into `P.triangEnvelope` SHALL require both `P.Nonempty` and a triangulated category. Under `[IsTriangulated C]`, the library SHALL prove `ExtensionClosure P = ⨆ n, (P ⊔ IsZero).extensionProductIter n` without requiring `P.Nonempty`.

#### Scenario: Iterated extension products enter the owner closure

- **WHEN** an object belongs to `P.extensionProductIter n`
- **THEN** it belongs to `ExtensionClosure P`

#### Scenario: Nonempty generators give an envelope comparison

- **WHEN** P is nonempty and the category is triangulated
- **THEN** every object of `ExtensionClosure P` belongs to `P.triangEnvelope`

#### Scenario: Typeclass closure data restates the induction principle

- **WHEN** Q is closed under isomorphisms, contains zero, is closed under distinguished extensions, and P is contained in Q
- **THEN** the comparison API provides the corresponding induction corollary and documents any difference from the raw hypotheses

#### Scenario: Empty generators do not justify the reverse inclusion

- **WHEN** `P = ⊥`
- **THEN** `ExtensionClosure P` still contains every zero object while `P.triangEnvelope = ⊥`, so no unconditional reverse-inclusion claim is made

#### Scenario: The owner closure is the supremum of finite zero-augmented iterates

- **WHEN** P is any object property and the category is triangulated
- **THEN** `ExtensionClosure P = ⨆ n, (P ⊔ IsZero).extensionProductIter n`, including when `P` is empty

#### Scenario: A Postnikov step has a generation-time bound

- **WHEN** an object lies in `P.extensionProductIter n`
- **THEN** its singleton generation time from P is at most n

### Requirement: Triangulated functors do not increase generation time

For a functor between pretriangulated categories that commutes with integral shifts and is triangulated, the library SHALL transport membership in each iterated envelope from an object to its image, and SHALL prove that generation time between mapped object properties does not increase. For an essentially surjective such functor, the target Rouquier dimension SHALL be at most the source Rouquier dimension. For a triangulated equivalence, Rouquier dimension and generation time SHALL be invariant, and strong generation SHALL transfer across the equivalence. The API SHALL document the direction of transport and SHALL NOT claim a reverse inclusion for arbitrary functors.

#### Scenario: Envelope membership transports pointwise

- **WHEN** X lies in the n-th iterated envelope of P and F is a triangulated functor commuting with integral shifts
- **THEN** F(X) lies in the n-th iterated envelope of the image of P

#### Scenario: Essential surjectivity bounds target dimension

- **WHEN** F is essentially surjective and triangulated
- **THEN** the Rouquier dimension of its target is at most the Rouquier dimension of its source

#### Scenario: Equivalences preserve the numerical invariants

- **WHEN** F is a triangulated equivalence
- **THEN** Rouquier dimension and generation time agree across the equivalence

#### Scenario: Strong generation transfers across an equivalence

- **WHEN** one side of a triangulated equivalence has a strong generator
- **THEN** the other side has a strong generator

#### Scenario: No reverse image claim for a general functor

- **WHEN** F is not assumed to be essentially surjective or an equivalence
- **THEN** no reverse envelope inclusion or equality of Rouquier dimensions is asserted
