# Design

## Context

See [proposal.md](proposal.md) for motivation and [the spec](specs/triangulated-generation-composition/spec.md) for the required mathematical statements. The implementation extends Mathlib's existing `ObjectProperty.triangEnvelopeIter` and the repository's existing generation-time and Rouquier-dimension APIs.

## Goals / Non-Goals

**Goals:**

- Keep Mathlib API extensions with the pinned generator API and the numerical consequences with the generation-dimension feature.
- Derive the envelope composition and generator-transfer results from the existing closure operations.
- Keep the generic modules independent of geometry and stability theory.

**Non-Goals:**

- Add a closure operation, carrier, or generator predicate.
- Claim additivity of generation time or a strong-generator conclusion from non-uniform pointwise stage bounds.
- Prove functor transport (#921), geometric applications, or semiorthogonal bounds.

## Decisions

### Ownership and canonical roots

The results about `ObjectProperty.triangEnvelopeIter`, its stage composition, and bounded strong-generator transfer directly extend Mathlib's triangulated-generator API. They belong at `CategoryTheory/Triangulated/Generators/Composition.lean`, in the existing `CategoryTheory.ObjectProperty` namespace. The `ℕ∞` generation-time inequality and Rouquier-dimension consequences depend on those results and belong downstream in `CategoryTheory/Triangulated/Dimension/Composition.lean`. This follows the pinned definition site for direct Mathlib API extensions and introduces no competing root.

### Proof structure and hypotheses

The stage-zero fixed-point proof separates empty and nonempty properties. In the nonempty case the zero object supplies the terminal object needed by the binary-product closure criterion. Retracts of products are products of retracts; products of distinguished triangles supply closure of extension products under binary products. Shift closure is inherited from the pinned instances. These facts establish the closure of each iterated stage without a new closure construction.

The composition theorem inducts on the outer stage using the existing successor formula and the stage-zero containment. Its explicit finite bound is `m * n + m + n`; the transfer theorem composes this inclusion with monotonicity of the existing tower. The public statements preserve the category hypotheses of the reused APIs and do not add a nonemptiness hypothesis to composition or transfer.

The generation-time result translates finite `ℕ∞` bounds through the existing order characterization and the identity `(m + 1) * (n + 1) = m * n + m + n + 1`. The plus-one form keeps the statement meaningful at infinite values and avoids relying on an unshifted product with `0 * ⊤`.

For Stacks 0FXA, the proof carries one explicit common finite stage `k` from the strong property into the classical generator's envelope. A pointwise choice of stage for each object is not a uniform bound, so the API will not state the arbitrary-property version from that weaker premise. The singleton corollary uses the existing canonical singleton and generator predicates; no parallel notion is introduced.

### Imports, comparisons, and instances

`Generators/Composition.lean` imports Mathlib's generator API and owns only its generic envelope extensions. `Dimension/Composition.lean` imports the existing generation-time and Rouquier modules and the generic composition API. The `Generators.lean` and `Dimension.lean` umbrellas re-export their new children. There are no new global instances or comparison structures, and no import reaches algebraic geometry, stability conditions, or `CompactlyGenerated/`.

### Documentation and audit

The generation-time docstring will state the false additive claim with its counterexample and stage-index comparison. The arbitrary-property Stacks limitation will be explicit. Public declarations will be appended to the existing dimension audit and the applicable generalization backlog entry retained. The new modules remain covered by the existing triangulated umbrellas.

## Risks / Trade-offs

- **Stage-index error in the composition bound** → Derive the successor step from Mathlib's tower equation and state the `m * n + m + n` bound alongside the `⟨G⟩_(n+1)` convention.
- **Unintended closure abstraction** → Prove closure facts about Mathlib's existing operators locally and expose only the resulting envelope theorems.
- **Overstated Stacks corollary** → Keep a single finite `k` in the public premise and document why pointwise bounds do not suffice.
- **Import leakage from applications** → Build and inspect the generic modules and umbrellas under the repository's focused checks.
