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
- **THEN** the formal §3 statements compile with theorem-backed closure and
  comparison results, while every genuinely external geometric witness remains
  named at its geometry-owner call site rather than being treated as a proof by
  mere structure inhabitation

#### Scenario: Out-of-scope morphism

- **WHEN** a morphism falls outside the theorem's quasi-compact,
  affine-diagonal, or boundedness hypotheses
- **THEN** the API does not infer a §3 conclusion and the missing hypothesis is
  visible at the call site

### Requirement: S-local t-structures and slicings expose formal locality boundaries

The implementation SHALL define S-local t-structures by quantifying over every
quasi-compact open of the base, SHALL provide the uniqueness statement from
Remark 4.6(1), and SHALL provide an affine-base witness adapter that consumes
actual family and t-exactness data. It SHALL also formalize the
noetherian-locality and filtration-lifting statements of Lemmas 4.15 and
4.16(3), together with the corresponding S-local slicing analogue. The
remaining geometric locality, generation, and lifting hypotheses SHALL remain
named at their owner call sites and SHALL NOT be presented as proved merely
because a structure containing them is inhabited.

#### Scenario: Restriction over every quasi-compact open

- **WHEN** a t-structure is declared S-local
- **THEN** every quasi-compact open has a restricted t-structure whose
  restriction functor is t-exact, and equality of the restricted aisles implies
  equality of the restricted t-structures

#### Scenario: Affine inhabitants

- **WHEN** the base is affine and two supported slicing-locality witnesses,
  their t-exactness data, and distinctness data are supplied
- **THEN** the construction produces two distinct inhabited S-local examples,
  records the affine hypothesis, and exposes their locality witnesses to
  downstream §5 statements

#### Scenario: Non-quasi-compact open

- **WHEN** an open is not covered by the required quasi-compact hypothesis
- **THEN** it is not silently quantified as an eligible locality witness

### Requirement: Theorem 5.3 reuses the existing Ind extension

The implementation SHALL reconcile the repository's existing
`TStructure.IndExtensionData` with the Ind/filtered-colimit presentation of
Lemma 5.1 without creating a second carrier. It SHALL prove the formal
consequences available from that carrier (the affine aisle comparison and
inclusion t-exactness), expose filtered-colimit preservation through mathlib's
`PreservesColimit`, and provide source-shaped owner boundaries for the
flat-descent formula, fpqc-descent formula, tensor right t-exactness, and the
four stated t-exactness comparisons. Those geometric owner inputs SHALL remain
explicit and SHALL NOT be presented as proved merely because a boundary
structure is inhabited.

#### Scenario: Existing Ind extension is consumed

- **WHEN** a t-structure with the required Ind-extension data and the named
  filtered-colimit/descent/exactness owner inputs is supplied
- **THEN** the existing extension API proves inclusion t-exactness and the
  aisle comparison, while the owner inputs elaborate as named comparison
  formulas without introducing a duplicate Ind carrier

#### Scenario: Incompatible presentation

- **WHEN** a proposed implementation introduces a duplicate Ind-extension
  carrier or states descent as an unproved structure field
- **THEN** the change is rejected by the abstraction/repository review and the
  affected theorem remains unclosed

### Requirement: The bounded loop records scope and repository friction

The original enabled SF11 run SHALL name exactly issues #1060, #1061, and
#1062. Any approved follow-up, including issue #1445, SHALL use an independent
manifest, freeze file scopes and acceptance statements per chunk, require all
four independent review lenses, and stop a chunk after its fifth unsuccessful
review/improve round. Explicit authorization for an issue's `epic` label MUST
be represented in its manifest; the controller MUST continue to reject
unapproved `epic`, blocked, research, and spike issues. Repository comments,
roadmap staleness, and time-wasting practices discovered during either run
SHALL be recorded in the checked-in loop-engineering notes.

#### Scenario: Explicit epic authorization

- **WHEN** the manifest explicitly opts the selected SF11 issues into epic
  processing and all other preflight checks pass
- **THEN** preflight admits only those named issues and reports the exception
  in its validation output

#### Scenario: Sixth review attempt

- **WHEN** a fifth review round still adjudicates as needing changes
- **THEN** the ledger marks the chunk blocked and refuses any sixth round,
  push, approval, merge, or issue closure for that chunk

### Requirement: Theorem 5.3 owner boundaries are source-shaped and do not duplicate canonical t-structure carriers

The follow-up repair SHALL reuse canonical `IndExtensionData` and Mathlib
exactness interfaces, or prove substantive comparison theorems, rather than
introducing projection-only wrappers. One-sided clauses SHALL expose only the
right- or left-t-exact hypotheses used by their proofs, while genuinely
t-exact clauses MAY require both halves. Tensor, descent, and local-comparison
inputs SHALL name their actual operation-facing data and SHALL NOT claim
scheme-level geometry from mere structure inhabitation.

#### Scenario: One-sided exactness is not strengthened

- **WHEN** a Theorem 5.3 clause uses only right or left t-exactness
- **THEN** the formal boundary accepts that one-sided input without requiring
  the unused opposite direction

#### Scenario: No empty carrier survives the repair

- **WHEN** a proposed carrier has no theorem with substantive content in the
  repaired chunk
- **THEN** the carrier is removed or replaced by a direct owner hypothesis

### Requirement: The AlgebraicGeometry audit records actual declarations without changing the missing-declaration baseline

The follow-up SHALL add every declaration reported by the CI sweep to the
proper AlgebraicGeometry audit slice, with the corresponding `#print axioms`
evidence. It SHALL NOT edit `scripts/audit_missing_baseline.txt`, raise an
audit ceiling, or suppress the sweep.

#### Scenario: Audit completeness is restored

- **WHEN** the declaration sweep runs on the repaired final commit
- **THEN** every new AlgebraicGeometry declaration is covered by an owning
  audit record and the no-sorry/axiom audit proceeds to the downstream gates

#### Scenario: Baseline relaxation is rejected

- **WHEN** a repair attempts to add a missing declaration to the baseline or
  increase a ceiling instead of auditing it
- **THEN** repository review rejects the change as a trust-surface bypass
