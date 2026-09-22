# Proposal

## Why

PR #1420 closed #929, but its constructed tensor is on `D(X.Modules)`, while
#928 concerns the bounded coherent tier inside `D(Coh X)`.  The former DT1
stack can therefore neither initialize its closed predecessor nor honestly
present the latter construction as a restriction of #1420.

The current coherent-tensor root also requires full two-variable exactness,
including shift naturality and the Koszul law.  A continuation must make that
generic restriction step explicit rather than treating three fixed-kernel facts
as sufficient coherence.

## What Changes

- Add a generic full-subcategory restriction bridge for two-variable shift
  coherence and exact bifunctors.
- Add a conditional #928 constructor that packages separately supplied ambient
  `D(Coh X)` monoidal and exact-bifunctor data on the bounded coherent tier.
- Run #928 as a fresh, independent, three-round-bounded loop from `origin/main`;
  retain `dt1-m41` as historical planning evidence for #929.
- Record verified tracker, cache, controller, and source-contract drift in the
  continuation's observation register.

## Capabilities

### New Capabilities

- `dt1-coherent-tensor`: restrict a supplied coherent ambient exact tensor to
  the bounded coherent tier without asserting an unproved ambient comparison or
  boundedness theorem.

### Modified Capabilities

- None.

## Impact

The generic bridge belongs with `ObjectProperty` and the existing exact-bifunctor
API.  The scheme specialization belongs under
`DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Tensor/` and reuses the named
bounded monoidal restriction.  It updates the Tensor umbrella, the appropriate
derived-operations audit, and a new bounded-loop manifest; it does not edit
module-sheaf tensor code, create a global coherence instance, or claim a
comparison from `D(X.Modules)` to `D(Coh X)`.
