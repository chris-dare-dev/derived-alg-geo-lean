# Proposal

## Why

The SF8/SF9 roadmap contains a natural three-issue dependency chain, but the
work is too large to leave as an unstructured unattended batch. An OpenSpec
plan can make the mathematical trust boundary, construction obligations, and
handoff between issues explicit before the loop is enabled.

## What Changes

- Plan the arbitrary derived-pullback construction in SF8.5 (#554) on the full
  existing interface domain: every scheme morphism and every unbounded complex
  of modules on its source scheme, without a boundedness, quasicoherence,
  Noetherian, flatness, or exactness restriction.
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
- Add a third explicitly marked #554 progress chunk only if it proves an actual
  comparison of that concrete degree-minus-one effect with Mathlib's pinned
  `CategoryTheory.Tor` API. The Tor statement is about the displayed affine
  example only; it does not supply arbitrary derived pullback, K-flat
  resolutions, or relative-perfect preservation.
- Add a fourth explicitly marked #554 progress chunk that compares the actual
  underived scheme-module pullback of the sheafified two-term free resolution
  with the sheafification of its scalar extension and carries the example's
  nonzero `H⁻¹` to scheme-module sheaves. This is a degreewise representative
  calculation, not a `LeftDerivedPullback` or a K-flat-resolution result.
- Add a fifth explicitly marked #554 progress chunk that promotes the affine
  tilde/pullback comparison through derived localization on the full
  K-projective derived locus. This applies to arbitrary affine ring maps but
  does not construct a replacement on all scheme-module complexes or assert a
  general scheme-morphism theorem.
- Add the flat-generator prerequisite for the all-complex construction as a
  separate issue-sized slice: prove the canonical open free-Yoneda stalk
  formula and stalkwise flatness, and add the natural element-indexed
  epimorphism at the generic small-ringed-site owner. This does not claim
  projectivity, a K-flat replacement, or arbitrary pullback acyclicity, and
  does not close #554.
- Execute each outstanding #554 progress chunk through its own one-issue
  independent manifest, with a distinct branch name and a bounded adversarial
  review cap. The merged witness/effect chunks are historical and must not be
  replayed. Keep #522 and #525 out of those runs: they remain a later
  post-closure stack, not a false consequence of a progress PR. The affine
  scheme-module pullback comparisons remain progress slices of SF8.5 and do
  not complete task 1.2 or close #554.

## Capabilities

### New Capabilities

- `sf8-sf9-supported-moduli`: construction and algebraicity obligations for the
  selected SF8/SF9 pilot.

### Modified Capabilities

- None.

## Impact

This plan names the issue order, mathematical acceptance obligations, and
proof/audit gates. Its first executable slice is deliberately narrower than
the full three-issue roadmap; it does not claim that the underlying Lean
constructions, algebraicity, or quasi-properness already exist.
