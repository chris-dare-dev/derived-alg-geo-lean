# Spec Delta

## Purpose

This capability formalizes the source-faithful base-change categories and local
t-structure constructions needed by the SF11 issues, while keeping every
geometric theorem boundary visible and independently reviewable.

## ADDED Requirements

### Requirement: Base-change categories are constructed from honest operations

The implementation SHALL construct `D_T` and `(Dqc)_T` from the repository's
derived pullback and tensor operations, rather than postulating the categories
or replacing them with an unrelated carrier. The induced pullback and
pushforward functors SHALL expose their underlying ambient functors and SHALL
prove their component-preservation, fullness, faithfulness, adjunction, and
essential-surjectivity statements under the exact hypotheses used by the
corresponding source theorem.

#### Scenario: Construction retains the source formula

- **WHEN** a source component, a morphism `T ⟶ S`, and the required geometric
  witnesses are supplied
- **THEN** the resulting categories are the closure/intersection construction
  from the external products in §3 and the restricted functors forget to the
  supplied ambient derived functors by a named comparison isomorphism

#### Scenario: Missing geometry is not hidden

- **WHEN** compactness, coherence, generation, projection, or detection data
  required by Proposition 3.15, Theorem 3.17, or Lemma 3.18 is absent
- **THEN** no theorem or instance is produced by an interface field, `sorry`,
  `admit`, or an unrelated replacement construction

### Requirement: The §3 witnesses discharge the supported SF11.1 statements

For the noetherian finite-Krull-dimension and quasi-compact affine-diagonal
scope of issue #1060, the implementation SHALL discharge the source-faithful
semiorthogonal, compact-generation, projection, finite-amplitude,
bounded-coherent, linearity, projection-formula, and detection obligations
needed to state the supported forms of Proposition 3.15, Theorem 3.17, and
Lemma 3.18. Any theorem whose hypotheses are genuinely external SHALL retain
those hypotheses explicitly and SHALL identify the exact paper clause they
represent.

#### Scenario: Supported §3 chain

- **WHEN** the stated scheme hypotheses and all declared source-component
  hypotheses hold
- **THEN** the §3 statements compile with actual witnesses and no placeholder
  existence or preservation conclusion

#### Scenario: Out-of-scope morphism

- **WHEN** a morphism falls outside the theorem's quasi-compact,
  affine-diagonal, or boundedness hypotheses
- **THEN** the API does not infer a §3 conclusion and the missing hypothesis is
  visible at the call site

### Requirement: S-local t-structures and slicings are inhabited

The implementation SHALL define S-local t-structures by quantifying over every
quasi-compact open of the base, SHALL provide the uniqueness statement from
Remark 4.6(1), and SHALL provide at least two non-vacuous affine-base
inhabitants. It SHALL also formalize the noetherian-locality and
filtration-lifting statements of Lemmas 4.15 and 4.16(3), together with the
corresponding S-local slicing analogue, without treating a t-structure or
slicing as an unproved field.

#### Scenario: Restriction over every quasi-compact open

- **WHEN** a t-structure is declared S-local
- **THEN** every quasi-compact open has a restricted t-structure whose
  restriction functor is t-exact, and equality of the restricted aisles implies
  equality of the restricted t-structures

#### Scenario: Affine inhabitants

- **WHEN** the base is affine and one of the supported concrete SF11 examples
  is instantiated
- **THEN** the construction produces two distinct inhabited S-local examples
  and their locality witnesses can be used by downstream §5 statements

#### Scenario: Non-quasi-compact open

- **WHEN** an open is not covered by the required quasi-compact hypothesis
- **THEN** it is not silently quantified as an eligible locality witness

### Requirement: Theorem 5.3 reuses the existing Ind extension

The implementation SHALL reconcile the repository's existing
`TStructure.IndExtensionData` with the Ind/filtered-colimit presentation of
Lemma 5.1 and SHALL prove the supported clauses of Theorem 5.3: the affine
closure construction, filtered-colimit truncation, flat-descent formula,
fpqc-descent formula, tensor right t-exactness, and the four stated
t-exactness comparisons. It MUST NOT create a second incompatible
Ind-extension carrier.

#### Scenario: Existing Ind extension is consumed

- **WHEN** a t-structure with the required Ind-extension data and a faithful
  base change are supplied
- **THEN** the base-changed t-structure and its comparison formulas are
  obtained through the existing extension API and the theorem's formulas
  elaborate with named comparison maps

#### Scenario: Incompatible presentation

- **WHEN** a proposed implementation introduces a duplicate Ind-extension
  carrier or states descent as an unproved structure field
- **THEN** the change is rejected by the abstraction/repository review and the
  affected theorem remains unclosed

### Requirement: The bounded loop records scope and repository friction

The enabled SF11 run SHALL name exactly issues #1060, #1061, and #1062,
freeze file scopes and acceptance statements per chunk, require all four
independent review lenses, and stop a chunk after its third unsuccessful
review/improve round. Explicit authorization for the issues' `epic` labels
MUST be represented in the manifest; the controller MUST continue to reject
unapproved `epic`, blocked, research, and spike issues. Repository comments,
roadmap staleness, and time-wasting practices discovered during the run SHALL
be recorded in the checked-in loop-engineering notes.

#### Scenario: Explicit epic authorization

- **WHEN** the manifest explicitly opts the selected SF11 issues into epic
  processing and all other preflight checks pass
- **THEN** preflight admits only those named issues and reports the exception
  in its validation output

#### Scenario: Fourth review attempt

- **WHEN** a third review round still adjudicates as needing changes
- **THEN** the ledger marks the chunk blocked and refuses any fourth round,
  push, approval, merge, or issue closure for that chunk
