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
- Use the loop controller's four independent reviewers and both pre-freeze
  advisors on every frozen chunk.
- Run each #554 progress slice independently, with at most three review rounds
  for a frozen chunk. The third unsuccessful round is terminal; it does not
  authorize re-chunking.

### Non-Goals

- Treating a typeclass/interface as proof of an object or property.
- Running #525 before the #522 acceptance contract is met.
- Claiming readiness while roadmap or repository ownership audits fail.

## Decisions

1. Split execution at the progress boundary. The affine witness and the
   degree-minus-one effect are already merged historical chunks and are not
   replayed. The concrete Tor comparison runs as a separate independent,
   one-issue #554 progress manifest. A separate #522/#525 stack may be enabled
   only after #554 closes; a progress ledger never unlocks a downstream issue.
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
7. Treat the explicit nonzero derived effect for `ℤ → ZMod 2` as a completed
   historical progress chunk. It uses the existing affine bounded-projective
   lane and its K-projective representative API; it is not a construction of a
   general scheme-level `LeftDerivedPullback` or proof of full
   relative-perfect preservation.
8. For each new concrete progress chunk, freeze its source leaf, relevant
   public audit, generalization-backlog path, and any outcome log before ledger
   initialization. Append only generalization findings that cannot be acted on
   within that chunk; an existing API consumed directly is not an unverified
   lift, and an empty disposition does not warrant a placeholder row. The
   current loop-controller digest normalizes task-checkbox state, so the active
   task may be checked in its implementation PR. Task wording and the other
   required OpenSpec artifacts remain frozen after ledger initialization.
9. State the first derived-effect endpoint as nonzero degree-minus-one homology
   of the supported affine bounded-projective representative. A Tor
   interpretation is not part of that result unless a proved comparison to an
   actual Tor API is supplied.
10. Treat the concrete `ZMod 2` comparison to Mathlib's
    `CategoryTheory.Tor` as a separate progress chunk. It must use the exact
    fixed-left/derived-second-argument convention, an explicit
    `ProjectiveResolution` comparison, the chain-degree `1` to cochain-degree
    `-1` bridge, and restriction of scalars. No generic Tor wrapper or scheme-
    level derived-pullback claim is included.
11. Keep a tracked loop-engineering friction log for stale worktree context,
    incomplete API discovery, and false starts caught by adversarial review;
    record both the cause and the prevention step so future runs can improve.
12. Publish a new OpenSpec plan and enabled manifest through a one-time,
    owner-authorized planning-only bootstrap PR before controller preflight.
    That PR contains no Lean implementation and does not close #554. After it
    merges, start from a fresh clean checkout at the exact `origin/main`, run
    preflight and initialize the digest-bound ledger, then route every
    implementation-phase provider action through the controller.
13. Do not change task wording or any other required OpenSpec artifact after
    ledger initialization. The controller's v2 digest normalizes task-checkbox
    state, so check the active task in the implementation PR when its work is
    complete; this does not invalidate the ledger evidence.
14. Treat the actual affine scheme-module pullback of the displayed resolution
    as a fourth #554 progress slice. Its comparison is the underived,
    degreewise `Scheme.Modules.pullback` on one finite free representative,
    identified with the sheafification of the already computed scalar-extension
    complex. It may prove a target scheme-module `H⁻¹` effect, but it does not
    inhabit `LeftDerivedPullback`, construct a general K-flat resolution, or
    complete task 1.2. Keep the generic affine pullback/tilde comparison at the
    `AlgebraicGeometry/Modules/Pullback` owner and its concrete derived effect
    beside the existing affine witness; do not infer an arbitrary-scheme
    derived comparison from it.
15. Treat the affine K-projective-locus comparison as a separate progress
    slice: for each commutative-ring map `R → S`, compare degreewise actual
    `Scheme.Modules.pullback (Spec.map f)` on the sheafification of
    K-projective representatives, after localization, with extension of
    scalars followed by the derived functor induced by the exact
    `AlgebraicGeometry.tilde.functor S : ModuleCat S ⥤ (Spec S).Modules`.
    The target is the derived category of all scheme-module sheaves, not the
    separate affine quasi-coherent derived category. The source is only
    `KProjectiveDerivedCategory (ModuleCat R)`. This does not construct a
    replacement on all scheme-module complexes, inhabit
    `SchemeBaseChange.LeftDerivedPullback` for nonflat maps, prove
    preservation for the full relative-perfect locus, or generalize from
    affine spectra to arbitrary scheme morphisms. Keep the comparison beside
    the affine K-projective application in `Dqc/AffineKProjectivePullback.lean`;
    reuse the existing `Modules/Pullback/AffineSpec` comparison and do not add
    another carrier or derived-pullback interface.
16. Resolve the word “supported” in task 1.2 by choosing the full domain of
    the existing geometric interfaces as this chunk's scope; #554 itself does
    not define that word. The choice follows the existing interfaces: for
    every scheme `S`, every
    `T U : SchemeBaseChange S`, every `f : T ⟶ U`, and the unbounded derived
    category `U.DerivedFiber` of all `O_U`-module-sheaf complexes. Construct a
    functorial `SchemeKFlatResolution X` for each scheme `X` (functorial in
    complexes, not asserted natural in `X`), prove its pullback acyclicity for
    every such `f`, and use the existing constructor to inhabit
    `LeftDerivedPullback f`. Impose no boundedness, quasicoherence,
    Noetherian, flatness, or exactness restriction. This task does not prove
    the preservation claims in task 1.3 or the coherence laws in task 1.4.
    Keep the resolution beside the scheme K-flat tensor interface and the
    pullback transport beside `Families/KFlatPullback.lean`; add no competing
    resolution or derived-pullback carrier. The broader ringed-topoi analogue
    is recorded as an unverified altitude lift, not claimed by this scheme
    implementation.

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
