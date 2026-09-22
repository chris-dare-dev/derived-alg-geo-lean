# Proposal

## Why

Mathlib already supplies the iterated triangulated envelope, and issue #917 adds the reusable `ℕ∞`-valued generation-time API. The remaining milestone work makes that count usable as Rouquier dimension, connects the repository's existing extension closure to Mathlib's envelope, and transports the invariant across triangulated functors.

This change covers the selected ROU1 issues #919, #918, and #921. The three issues share the existing `Dimension.lean` umbrella and audit slice, so the implementation plan serializes their edits.

## What Changes

- Define Rouquier dimension as the infimum of generation times over single-object generators, with the `⟨G⟩_{n+1}` convention and its zero-offset relationship to Mathlib's `triangEnvelopeIter` made explicit.
- Prove the requested finite-bound, finite-dimension, classical-generator, and zero-dimension characterisations.
- Compare `ExtensionClosure` with `extensionProductIter` and `triangEnvelope`, retaining the precise nonempty and triangulated hypotheses and recording the empty-generator counterexample.
- Transport envelope membership and generation time along triangulated functors; prove the Rouquier-dimension bound for essentially surjective functors and invariance for triangulated equivalences.
- Extend the existing dimension umbrella and audit slice. Do not add a competing carrier or closure operation.

The separate composition-law and Stacks 0FXA work in #920 is excluded from this batch. Geometric bounds, semiorthogonal-decomposition bounds, and edits under `CompactlyGenerated/` are also out of scope.

## Capabilities

### New Capabilities

- `triangulated-generation-dimension`: Rouquier dimension, its characterisations, comparison with the owner extension closure, and functorial transport.

### Modified Capabilities

None. The repository has no existing OpenSpec capability spec for this generic triangulated vocabulary.

## Impact

- GitHub issues: [#918](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/918), [#919](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/919), and [#921](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues/921).
- Lean API: `DerivedAlgGeo/CategoryTheory/Triangulated/Dimension/`, its existing umbrella, and declarations in the `CategoryTheory.ObjectProperty` and `CategoryTheory.Triangulated` namespaces.
- Audit: `scripts/StabilityConditionAudit/Dimension.lean`.
- Dependencies: the merged generation-time API from #917 and Mathlib's existing envelope and triangulated-functor APIs. No geometry or stability imports are needed.
