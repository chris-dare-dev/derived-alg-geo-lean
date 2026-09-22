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

1. **Fresh sequential, attested controller runs.** This initial planning
   bootstrap contains only the one-issue
   `dt1-928-exact-bifunctor-restriction` progress manifest. The disabling
   bootstrap and predecessor-attestation controller support are now on
   `origin/main`; this separately reviewed enablement update starts the source
   run, which emits a durable controller predecessor attestation before its
   non-closing PR can merge. Only after that merge will a separate reviewed
   planning bootstrap author
   `dt1-928-coherent-tensor-assembly`, pinning the actual source PR's reviewed
   head, merge commit, and attestation fields. The old `dt1-m41` stack is
   disabled historical evidence: #929 is closed and it cannot legally be
   replayed as an open predecessor or static #928 assembly path.
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
4. **Full-coherence projection agreement.** For an explicit
   `Z : SchemeBaseChange S`, the assembly may reuse the restricted generic
   exactness only after proving that its bifunctor is exactly the
   `curriedTensor` selected by `boundedMonoidalCategory Z.left`. The preferred
   route is a focused definitional equality based on the precise
   `ObjectProperty.prop_tensor` closure witness. If definitional equality is
   unavailable, the replacement must be a named transport of the *complete*
   `CommShift₂Int` package, including both naturality equations and the Koszul
   law after the full-subcategory inclusion. A plain bifunctor isomorphism is
   not an exactness transport. The resulting coherent capability reuses the
   existing coherent-to-raw projection; it must not construct a competing raw
   root.
5. **Bounded review loop.** Two pre-freeze advisors record altitude and
   hypothesis findings. Four independent required reviewers inspect the same
   commit. A third unresolved `needs_changes` result marks that chunk blocked;
   no fourth round is opened. The cap is enforced independently on each of the
   two controller runs.
6. **Enforced sequential handoff.** The first manifest freezes only the
   generic files, creates a `Refs #928` progress PR, and merges it into
   `origin/main` after its passing three-round ledger and exact controller
   attestation. The later assembly manifest uses a distinct issue slug and
   branch, freezes only the assembly files, and pins the source PR's identity,
   closure, reviewed head, merge commit, attestation, source digests, and cap.
   The controller validates that evidence at preflight, ledger initialization,
   PR creation, approval, and merge, including current ancestry. The assembly
   manifest cannot be authored honestly until those source facts exist. This
   avoids pretending that the controller has a same-issue chunk-dependency
   feature it does not implement, or that a new assembly run can reset the
   generic file budget.

## Risks / Trade-offs

- **Two-variable transport is absent at the Mathlib pin** → prove the missing
  generic bridge with the full-subcategory inclusion and expose every
  coherence equation; do not replace it with fixed-kernel fields.
- **Ambient categories can be conflated** → make the `D(Coh X)` inputs explicit
  and test the negative module-sheaf-only case in the API boundary.
- **Cold caches make exploratory builds expensive** → seed the worktree only
  after a dry run and use one named target per source change.
- **Tracker and controller drift can recur** → retain the original artifacts,
  record verified observations before ledger initialization, and validate each
  manifest against live issue state and current branch protection. PR #1449
  deliberately retired the unsatisfiable `trust-surface` gate, so the manifest
  now binds only the live required `ci` context; ordinary owner review remains
  a repository-boundary obligation.

## Migration Plan

1. The disabling planning bootstrap and predecessor-attestation controller
   support are on `origin/main`. Land this reviewed enablement update, then
   validate the generic manifest on a clean
   `agent/dt1-exact-bifunctor-restriction` branch from `origin/main`.
2. Freeze and implement the generic bridge, verify it, complete its bounded
   adversarial ledger, and merge its non-closing progress PR through the
   controller.
3. After the generic merge, use its exact controller attestation and merge
   facts to author and review a planning-only successor bootstrap containing
   the distinct assembly manifest. Start from the resulting `origin/main`,
   validate that manifest on `agent/dt1-coherent-tensor-assembly`, then freeze
   and implement the Tensor assembly, update the Tensor umbrella and derived
   operations audit, and run its separate bounded adversarial ledger.
4. Use only controller actions for the final reviewed PR, CI, approval, merge,
   and #928 closure.
