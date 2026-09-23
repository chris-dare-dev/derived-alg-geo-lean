# Spec Delta

## Purpose

Provides a reproducible way to create an independent topic repository and a falsifiable second-topic gate that cannot pass on an empty or ungrounded adopter.

## ADDED Requirements

### Requirement: A generated topic pins the template source

A generated topic repository MUST record the full 40-character Copier source commit in `.copier-answers.yml` and MUST pin its MathFormalContract dependency to that same commit. `copier update` MUST be able to apply a later template revision using the recorded answer state.

#### Scenario: A topic is copied from a pinned template revision
- **WHEN** a user creates a topic repository from a template commit
- **THEN** the generated answers and dependency manifest identify that exact full commit

#### Scenario: A later template revision is applied
- **WHEN** the user runs `copier update` with a newer template commit
- **THEN** Copier uses the saved answers and reports or applies the template update without losing the recorded source pin

### Requirement: An upstream anchor is optional

The template MUST accept an exact pinned upstream anchor when one is supplied. When no anchor is supplied, it MUST require and generate a direct exact Mathlib pin, and the generated guidance MUST describe the topmost mathematical package pin without requiring an anchor.

#### Scenario: An adopter has no upstream anchor
- **WHEN** the user creates a topic with no anchor
- **THEN** generation requires a 40-character Mathlib revision and emits a direct Mathlib dependency

#### Scenario: An adopter supplies an anchor
- **WHEN** the user supplies an anchor with a package name, HTTPS repository, and exact revision
- **THEN** generation emits that pin and does not add a second independent direct Mathlib pin

### Requirement: Generated claims remain honest

The template MUST initialize unfillable formalization fields as `none` or `pending`. The topic trust record MUST keep `generalization_validated` false until the second-topic gate has passed with recorded evidence.

#### Scenario: A new topic has no source or gate evidence
- **WHEN** the template is rendered before topic research or gate completion
- **THEN** unknown metadata remains `none` or `pending` and the trust record says `generalization_validated: false`

#### Scenario: The adopter is empty or its evidence is incomplete
- **WHEN** the copy renders and basic CI succeeds but the corpus, registry, external binding, or required contract checks are missing
- **THEN** the gate does not pass and the trust record remains false

### Requirement: A second-topic gate requires external and corpus evidence

The gate MUST use an anchor-free analytic-number-theory adopter with one version-pinned arXiv paper fetched and ingested into its arXMCP notebook. Its validated registry MUST contain five sourced entries, including an Iwaniec–Kowalski textbook entry in `digest_only` mode, and at least one direct external binding to a theorem in the pinned Mathlib environment with `relation_claimed: exact`. The external declaration MUST be emitted with its environment digest and MUST NOT count as a topic-local declaration.

#### Scenario: The analytic adopter satisfies the evidence gate
- **WHEN** the notebook corpus, five-entry registry, environment-bound Mathlib declaration, emitted relation, Lean build, and contract checks all agree
- **THEN** the gate records those results as dated evidence and may set `generalization_validated` true

#### Scenario: The paper or registry is not grounded in the notebook corpus
- **WHEN** a registry entry has no matching corpus evidence, a digest-only source lacks the required provenance, or an external binding names a different environment
- **THEN** the gate fails or remains incomplete and `generalization_validated` stays false
