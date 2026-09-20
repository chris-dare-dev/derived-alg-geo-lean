# Proposal

## Why

The SF8/SF9 roadmap contains a natural three-issue dependency chain, but the
work is too large to leave as an unstructured unattended batch. An OpenSpec
plan can make the mathematical trust boundary, construction obligations, and
handoff between issues explicit before the loop is enabled.

## What Changes

- Plan the supported arbitrary derived-pullback construction in SF8.5 (#554).
- Plan the algebraicity proof for the supported relative-perfect moduli stack
  in SF9.2 (#522).
- Plan semistable reduction and the quasi-properness adapter in SF9.3 (#525)
  only after the preceding dependency is actually complete and the required
  gates are green.
- Keep implementation chunks small and independently adversarially reviewed.
- Permit the first #554 witness to land as an explicitly marked progress PR;
  the issue remains open until its full construction and preservation contract
  is satisfied.
- Add a second explicitly marked #554 progress chunk that computes a nonzero
  derived effect for the same non-flat affine map from a two-term free
  resolution; this strengthens the example without claiming the missing
  general resolution or preservation theorems.

## Capabilities

### New Capabilities

- `sf8-sf9-supported-moduli`: construction and algebraicity obligations for the
  selected SF8/SF9 pilot.

### Modified Capabilities

- None.

## Impact

This is a planning change only. It names the issue order, mathematical
acceptance obligations, and proof/audit gates; it does not claim that the
underlying Lean constructions already exist.
