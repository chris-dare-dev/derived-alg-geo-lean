# Projective Serre quotient

## ADDED Requirements

### Requirement: Projective space has finite negative-twist coproduct presentations

The repository SHALL expose a proved presentation for every coherent sheaf on
`Proj (polynomialGrading ι k)` as a finite coproduct of copies of one negative
twist, with a coherent kernel and an exponent at least one.

#### Scenario: A coherent sheaf on projective space is presented

- **WHEN** `k` is a field, `ι` is finite and nonempty, and `F` is coherent on
  `Proj (polynomialGrading ι k)`
- **THEN** `exists_shortExact_coproduct_twist` supplies a short exact complex
  whose third object is isomorphic to `F`, whose second object is a finite
  coproduct of `projectiveSpaceTwist ι k (-(N : ℤ))`, and whose `N` satisfies
  `1 ≤ N`

### Requirement: The general Proj theorem is an untwisted finite coproduct epimorphism

The repository SHALL expose the general Proj theorem
`exists_epi_coproduct_twistingSheaf_ge` (and its unconstrained companion) for
an arbitrary coherent module sheaf over a finitely degree-one-generated graded
ring, without assuming global generation, a resolution, or an instance that
supplies the epimorphism.

#### Scenario: The general theorem supplies its own finite presentation

- **WHEN** a graded ring has a finite degree-one generating family and `F` is a
  coherent module sheaf on its Proj
- **THEN** the theorem supplies a finite index type, a threshold-respecting
  exponent, and an epimorphism from the coproduct of copies of `O(-N)` to `F`
  by composing the proved global-generation theorem with the tensor inverse of
  `O(N)`

### Requirement: Repository guidance distinguishes the three Serre-lane statements

The closeout documentation SHALL distinguish the section-extension lemma
(#585 / Hartshorne II.5.14(a)), the global-generation theorem (#586 /
Hartshorne II.5.17), and the untwisted coproduct presentation (#570), and SHALL
not describe the old `Γ_*` correspondence as a prerequisite of the completed
proof.

#### Scenario: A future agent follows the nearby module docstrings

- **WHEN** an agent reads `TwistSection.lean` or `Glue.lean` while extending the
  projective-module lane
- **THEN** the docstrings point to the direct chart-generation, uniform-twist,
  and tensor-inverse route, and preserve the explicit non-goals around a
  general graded Serre correspondence and general line-bundle inverses
