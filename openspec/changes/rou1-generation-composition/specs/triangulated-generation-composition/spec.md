# Spec Delta

## Purpose

Specify how finite iterated-envelope bounds compose, how those bounds control generation time and Rouquier dimension, and which strong-generation consequences follow from a uniform bound.

## ADDED Requirements

### Requirement: Iterated envelope bounds compose

For an object property `P` in a pretriangulated category, the library MUST expose that stage zero of any iterated envelope is contained in that stage, that composing stages `m` and `n` is bounded by stage `m * n + m + n`, and that the bound transfers through an intermediate object property. These statements MUST preserve the empty-property case and MUST NOT introduce another envelope carrier.

#### Scenario: Finite generation passes through an intermediate property
- **WHEN** `Q ≤ P.triangEnvelopeIter m` and `R ≤ Q.triangEnvelopeIter n`
- **THEN** `R ≤ P.triangEnvelopeIter (m * n + m + n)`

#### Scenario: Empty source property
- **WHEN** `P` is empty
- **THEN** its iterated envelopes remain empty and the stage-zero containment remains valid

### Requirement: Generation time plus one is submultiplicative

The library MUST state generation-time composition in the `ℕ∞` form `generationTime P R + 1 ≤ (generationTime P Q + 1) * (generationTime Q R + 1)`. It MUST document that generation time itself is not additive and MUST NOT expose a false additive theorem.

#### Scenario: Finite stages compose
- **WHEN** `Q` is generated from `P` in `m` steps and `R` from `Q` in `n` steps
- **THEN** `R` is generated from `P` in at most `m * n + m + n` steps and the plus-one generation-time inequality holds

#### Scenario: Additivity counterexample
- **WHEN** generation times are `2` from `P` to `Q`, `1` from `Q` to `R`, and `5` from `P` to `R`
- **THEN** the additive inequality fails, while the stage composition is `iter 2` composed with `iter 1` contained in `iter 5`, corresponding to `⟨P⟩₃ ⋆ ⟨P⟩₃ ⊆ ⟨P⟩₆`

### Requirement: Strong-generator transfer requires a uniform stage

The library MUST prove strong-generation transfer when a strongly generating property is contained in one finite stage of another property, and MUST derive the single-object classical-generator corollary and the finite-Rouquier-dimension consequence. It MUST distinguish this uniform-bound result from a pointwise object-property claim that has no common finite stage.

#### Scenario: A bounded strong property is contained in a classical generator
- **WHEN** `Q` is a strong generator and `Q ≤ P.triangEnvelopeIter k` for one finite `k`
- **THEN** `P` is a strong generator, including when `Q` is a strongly generating singleton and `P` is classical

#### Scenario: No uniform bound is supplied
- **WHEN** each object of an arbitrary strongly generating property lies in some finite stage of a classical generator but the stage depends on the object
- **THEN** the library does not claim that the classical generator is strong from this pointwise information alone
