# Design

## Context

The milestone contains four open issues. #929 is the construction prerequisite
for #928, while #930 and #931 consume the resulting interfaces. The current
repository has already extracted tensor ownership to
`DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Tensor/` and has merged the
bounded monoidal restriction that was tracked as #892. This run therefore
targets #929 followed by #928 and deliberately does not widen into the two
downstream issues.

## Goals / Non-Goals

### Goals

- Give #929 an actual localization-based left-derived tensor bifunctor,
  tensor-acyclic resolution contract, universal-property comparison, and an
  exact-case inhabitant.
- Give #928 named transfer lemmas and a constructor for
  `HasCoherentDerivedTensor` whose hypotheses make every exactness and
  triangulation dependency visible.
- Keep the canonical owner and import boundary explicit, with projections and
  comparison maps that downstream twist and pullback code can consume.
- Run no more than three review/correction rounds for either frozen chunk.

### Non-Goals

- Do not implement the invertible twist (#930) or monoidal derived pullback
  reduction (#931) in this run.
- Do not prove finite Tor-dimension or closure of bounded coherent objects
  where the repository already treats that as a supplied `IsMonoidal`
  hypothesis.
- Do not add declarations to `Modules/**`, `CoherentSheaf/**`, Fourier--Mukai
  ownership, or the retired `Families/` tensor roots.
- Do not run a repository-wide Lean build.

## Decisions

1. **Canonical ownership.** New declarations live in
   `AlgebraicGeometry.DerivedCategory` (with the existing Fourier--Mukai
   compatibility namespace only where the public class already requires it)
   under `DerivedCategory/Tensor/`. The umbrella
   `DerivedCategory/Tensor.lean` is the only import projection that is
   extended.
2. **Construction boundary.** #929 may reuse the generic K-flat/localization
   machinery, but its public interface must expose a genuine counit and
   `Functor.IsLeftDerivedFunctor` obligations for fixed arguments. A marker
   class or an existence field without a comparison map is not an inhabitation.
3. **Exact case.** The identity-resolution case is admitted only from an
   explicit inversion/exactness hypothesis, with the invertible-left-factor
   specialization made available for later #930 consumption. No unproved
   exactness instance is introduced.
4. **Bounded transfer.** #928 uses the existing bounded inclusion and
   `ObjectProperty.IsMonoidal` infrastructure. Transfer lemmas are named per
   kernel/structure (additive, commutative shift, and triangulated) so they
   cannot be hidden in an opaque constructor.
5. **Review behavior.** Each chunk is frozen before implementation. The four
   required reviewers run independently on the same commit. A valid finding
   starts a new correction round; after round three, unresolved findings block
   the chunk rather than opening a fourth loop.

## Projections and Diamonds

- The derived tensor bifunctor projects to the existing degreewise module-sheaf
  tensor through its localization counit; the exact-case comparison must be
  the canonical identity-resolution comparison, not a second tensor root.
- The coherent bounded constructor projects through the existing
  `boundedTensorι` and `hasDerivedTensorOfCoherent`; it must not create a
  competing `HasDerivedTensor` instance or a second bounded monoidal category.
- Any associativity, unit, or comparison diagram added here must reuse the
  existing `Tensor/Coherent.lean` declarations and remain definitionally or
  propositionally connected to those projections.

## Verification and Trust Surface

Every correction round uses focused `lake env lean`/named-target checks,
umbrella coverage, coherent-family, layering, and trust-surface audits. The
controller records the exact reviewed commit and OpenSpec digest. The final PR
must use closing references only after both complete chunks pass and required
provider checks are green.
