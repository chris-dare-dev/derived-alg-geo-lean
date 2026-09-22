# Design

## Context

The pilot follows the repository's existing trust boundary: interfaces may
organize derived objects and universal properties, but they must not postulate
existence, preservation, descent, or algebraicity conclusions. #554 is the
construction prerequisite for #522, and #525 remains downstream.

## Goals / Non-Goals

### Goals

- Establish explicit construction and comparison obligations for #554.
- Require actual atlas, diagonal, and local-finiteness morphism statements for
  #522 instead of a representability shortcut.
- Use the loop controller's three adversarial lenses on every frozen chunk.
- Run the outstanding #554 progress slice independently with at most two review
  rounds. A first-round change request permits one revision and re-review; a
  second-round change request stops the chunk. The controller's repository-wide
  upper bound remains five.

### Non-Goals

- Treating a typeclass/interface as proof of an object or property.
- Running #525 before the #522 acceptance contract is met.
- Claiming readiness while roadmap or repository ownership audits fail.

## Decisions

1. Split execution at the progress boundary. The already-merged first witness
   is historical and is not replayed. The outstanding non-flat derived-effect
   chunk runs as an independent, one-issue #554 progress manifest. A separate
   #522/#525 stack may be enabled only after #554 closes; a progress ledger
   never unlocks a downstream issue.
2. Keep the supported nontrivial example and all coherence/equivalence laws in
   the #554 acceptance surface rather than deferring them to an abstraction.
3. Keep the #522 atlas/diagonal/local-finiteness proof statements in the
   requirement surface; implementation may use existing mathlib structures but
   cannot replace these statements with a representability field.
4. Treat the first non-flat affine witness for #554 as a progress chunk: it may
   merge with a non-closing issue reference, but it cannot close #554 or unlock
   #522 until the remaining preservation and coherence obligations are complete.
5. Treat #525 as a separate frozen chunk for supported semistable reduction and
   quasi-properness with a dependency edge, not as a speculative parallel
   improvement.
6. Record the canonical owner and at least two independent consumers (or a
   statement-layer exception) in each abstraction review. The controller ties
   the chunk to exact OpenSpec requirement headings, while the adversary checks
   ownership and adoption against the repository's architecture documents.
7. Treat the explicit nonzero derived effect for `ℤ → ZMod 2` as a second
   progress chunk. It may use the existing affine bounded-projective lane and
   its K-projective representative API, but it must not be presented as a
   construction of a general scheme-level `LeftDerivedPullback` or as proof of
   full relative-perfect preservation.
8. Freeze the derived-effect leaf, its existing witness, the public
   `DerivedCategory` umbrella, the scheme-derived axiom audit, the task
   checklist, and the generalization backlog before ledger initialization.
   The public example needs all of those paths; adding them after review would
   be impermissible scope widening.
9. State the executable endpoint as nonzero degree-minus-one homology of the
   supported affine bounded-projective representative. The familiar Tor
   interpretation may appear in documentation only unless a proved comparison
   to an actual Tor API is supplied.

## Risks / Trade-offs

- **#554 is larger than one chunk** → split by construction layer and freeze
  each file list before review.
- **A progress PR looks like a completed prerequisite** → use an independent
  one-issue run and leave the later stack disabled until the provider reports
  #554 closed.
- **The issue tracker is stale** → preflight queries live issue/PR state and
  stops on stale roadmap or open blockers.
- **A generalization creates duplicate roots** → the abstraction adversary must
  require an owner, two consumers or a statement-layer exception, and a
  comparison/projection argument.
