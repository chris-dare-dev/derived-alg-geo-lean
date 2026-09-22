# Design

## Context

See `proposal.md` for the tracker and ambient-category mismatch that requires a
fresh continuation. The current bounded coherent tensor root packages a
`MonoidalCategory` and a full two-variable exactness witness. Its pre-existing
bounded monoidal restriction supplies the monoidal parent from an explicit
boundedness-closure hypothesis, but it does not transfer the full exactness
witness.

## Goals / Non-Goals

**Goals:**

- Prove a generic restriction of two-variable shift coherence and exactness to
  a closed triangulated full subcategory.
- Package a supplied coherent exact tensor on `D(Coh X)` as the existing
  coherent tensor capability on `Dᵇ(Coh X)`.
- Keep every ambient, closure, and coherence hypothesis visible and retain the
  existing one-way raw-tensor projection.
- Limit each frozen code chunk to three review/improve rounds.

**Non-Goals:**

- Construct a comparison from `D(X.Modules)` to `D(Coh X)`, or claim that the
  #929 tensor supplies the latter category's ambient tensor.
- Prove finite Tor dimension, bounded coherent tensor closure, or a monoidal
  structure on `D(Coh X)`.
- Edit module-sheaf tensor code, add a global monoidal/coherent-tensor instance,
  or reach Fourier--Mukai or stability consumers from the Tensor subtree.

## Decisions

1. **Fresh independent run.** Create `dt1-928-coherent-tensor` and a one-issue
   independent manifest for #928. The old `dt1-m41` stack remains historical
   evidence: #929 is closed, has no matching ledger, and cannot legally be
   replayed as an open predecessor.
2. **Generic restriction first.** Put the two-variable shift restriction beside
   `ObjectProperty.lift₂` in `CategoryTheory/ObjectProperty/Bifunctor.lean`.
   Put the wrapper that transfers the repository's `ExactBifunctor` beside that
   structure in `CategoryTheory/Triangulated/ExactFunctorFamily.lean`. This is
   a root-to-consumer dependency: neither generic module imports geometry.
3. **Conditional geometry assembly second.** Add
   `Tensor/CoherentAssembly.lean`, importing the generic bridge and the named
   `boundedMonoidalCategory`/inclusion. It takes separately supplied ambient
   `D(Coh X)` monoidality, ambient exact-bifunctor data, and bounded-property
   monoidality. It installs the bounded monoidal structure locally and defines
   the coherent capability; it does not create an instance.
4. **Projection agreement.** The assembly must compare the restricted generic
   bifunctor with the curried tensor chosen by the named bounded monoidal
   restriction. The resulting coherent capability reuses the existing
   coherent-to-raw projection; it must not construct a competing raw root.
5. **Bounded review loop.** Two pre-freeze advisors record altitude and
   hypothesis findings. Four independent required reviewers inspect the same
   commit. A third unresolved `needs_changes` result marks that chunk blocked;
   no fourth round is opened.
6. **Same-issue handoff.** The controller records dependencies only between
   issue numbers, not between chunks of one issue, and checks a PR against the
   full `origin/main...HEAD` diff. The generic chunk is therefore a reviewed
   `progress` ledger with no PR action. Before initializing the assembly
   ledger, the operator explicitly verifies its passed state and records that
   check in the observation register. The assembly ledger deliberately repeats
   the generic paths so its one final, complete ledger can bind the single PR
   that closes #928.

## Risks / Trade-offs

- **Two-variable transport is absent at the Mathlib pin** → prove the missing
  generic bridge with the full-subcategory inclusion and expose every
  coherence equation; do not replace it with fixed-kernel fields.
- **Ambient categories can be conflated** → make the `D(Coh X)` inputs explicit
  and test the negative module-sheaf-only case in the API boundary.
- **Cold caches make exploratory builds expensive** → seed the worktree only
  after a dry run and use one named target per source change.
- **Tracker and controller drift can recur** → retain the original artifacts,
  record verified observations before ledger initialization, and validate the
  new manifest against live issue state.

## Migration Plan

1. Validate the new OpenSpec change and independent loop manifest on a dedicated
   `agent/dt1-coherent-tensor` branch from `origin/main`.
2. Freeze and implement the generic bridge, verify it, and complete its bounded
   adversarial `progress` ledger without opening a PR.
3. Record and manually recheck that passing ledger, then freeze and implement
   the Tensor assembly, update the Tensor umbrella and derived operations audit,
   and run its separate bounded adversarial ledger.
4. Use only controller actions for the final reviewed PR, CI, approval, merge,
   and issue closure.
