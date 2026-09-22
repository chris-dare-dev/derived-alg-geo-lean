# Agent observations

This register is append-only.  Entries record only facts checked against a
live tracker response, a committed source file, a controller source path, or a
reproducible command.  They are implementation constraints, not replacement
proofs.

## 2026-09-21 — continuation baseline

- **Stale tracker lineage (verified).** `gh issue view 928 --repo
  chris-dare-dev/derived-alg-geo-lean --json number,state,title,body,url,labels`
  reports #928 as open, but its body still says it is blocked by #892, names
  retired `Families/` paths, and describes a three-field-per-kernel class
  contract. `gh pr view 1420 --repo chris-dare-dev/derived-alg-geo-lean --json
  state,mergedAt,closingIssuesReferences,files` reports that #1420 merged on
  2026-09-20 and closed #929, with the fixed-left tensor in
  `Tensor/LeftDerivedTensor.lean`. The continuation therefore treats #928 as
  an independent live issue and preserves `dt1-m41` as historical evidence;
  it does not replay the closed predecessor or use its retired paths.

- **Ambient-category mismatch (verified).**
  `Tensor/LeftDerivedTensor.lean` constructs on `SchemeDerivedCategory X`
  (the derived category of all module sheaves), whereas
  `Tensor/Coherent.lean` defines the bounded coherent interface inside
  `SchemeCoherentDerivedCategory X`. No committed comparison between those
  ambient categories was found during the source audit. The assembly may take
  a separate ambient `D(Coh X)` tensor as input, but must not assert that
  #1420 supplies it.

- **Exactness contract drift (verified).**
  `HasCoherentDerivedTensor` requires a repository `Functor.ExactBifunctor`,
  not only three independently supplied fixed-kernel fields. In
  `CategoryTheory/Triangulated/ExactFunctorFamily.lean`, that contract retains
  two-variable shift coherence, including naturality and the Koszul law, as
  well as exactness in both variables. This is why the first chunk transfers
  full bifunctor coherence before exposing named fixed-kernel consequences.

- **Pinned Mathlib transport gap (verified).** The pinned
  `Mathlib/CategoryTheory/Shift/CommShiftTwo.lean` source available from the
  runner cache exposes the two precomposition helpers but records the missing
  postcomposition direction as a TODO. The clean continuation worktree itself
  has no local `.lake/packages/mathlib` tree, so cache absence is never used as
  evidence that a Mathlib declaration does not exist; the implementation must
  confirm imports and names with a focused probe after cache seeding.

- **Same-issue controller limitation (verified).**
  `scripts/loop_engine.py`'s `require_selected_dependencies_passed` checks
  only dependencies between issue numbers; `ledger_init` has no ordering edge
  between chunks of the same issue. Its final PR file check compares
  `base_ref...HEAD`. The manifest consequently marks the generic chunk
  `progress`, requires an explicit passing-ledger check before the assembly
  ledger is initialized, and repeats the generic paths in the final chunk so a
  single closing #928 PR can be bound to the whole branch diff. No progress PR
  is created after the generic chunk.

- **Round-cap documentation drift (verified).** The general run-loop skill
  describes a five-round maximum, while the controller accepts smaller caps
  and the checked-in one-issue precedent
  `.claude/loop-specs/aut1-570-doc-hygiene.yaml` uses three. The explicit user
  authorization for this continuation chooses three; the manifest is the
  operative bound and a third unresolved `needs_changes` verdict is terminal.

- **Ownership overlap resolved, but source prose needs care (verified).**
  `gh issue view 796 --repo chris-dare-dev/derived-alg-geo-lean --json
  number,state,body,url` shows the September DT1 boundary ceding the monoidal
  `HasCoherentDerivedTensor` constructor to #928, so no tracker mutation is a
  prerequisite. The current `Tensor/BoundedMonoidal.lean` prose still calls
  the coherent root's obligations three separate exactness fields, whereas
  `Tensor/Coherent.lean` now packages one full `ExactBifunctor`. The geometry
  chunk permits a narrow documentation correction if it is needed, but must
  keep the full contract as the source of truth.

## Future entries

Append evidence for cache seeding, API-name probes, stale references, failed
or blocked controller operations, and each proof boundary encountered during
the two chunks. Do not replace an earlier entry after a later discovery; add a
dated correction that names the earlier evidence instead.

## 2026-09-22 — preflight bootstrap blocker

- **Fresh-manifest preflight is currently unreachable (verified).** Running
  `python3 scripts/loop_engine.py preflight --spec
  .claude/loop-specs/dt1-928-coherent-tensor.yaml` reports all provider checks
  it reaches as passing, then fails because this continuation's manifest and
  OpenSpec artifacts are untracked, `HEAD` is not exactly `origin/main`, and
  the checkout is detached. The relevant controller code requires all three:
  `preflight` loads the on-disk manifest, rejects any dirty worktree, and
  requires `HEAD == base_ref`. Committing the new artifacts to the proposed
  agent branch would make the tree clean but would still violate
  `HEAD == origin/main`; ignoring the artifacts would merely conceal the
  required inputs and is not an acceptable workaround.

- **The protected base moved while provisioning (verified).** The continuation
  worktree started at `4e56e5ca`, but `origin/main` now resolves to
  `503817d7` (`docs(roadmap): threefold gap analysis`, PR #1428). `git diff
  --name-status 4e56e5ca..origin/main --` over the DT1 source, manifest,
  OpenSpec, architecture, and gate paths is empty, so this is not a code
  conflict; it is nevertheless an exact-base failure by design.

- **Safe stop condition.** Do not initialize a ledger, dispatch pre-freeze
  advisors, manually push, or create an unbound bootstrap PR until either the
  planning artifacts are landed on the protected base through an authorized
  bootstrap route, or the loop controller gains an explicitly reviewed
  bootstrap mode that preserves its clean-base and frozen-file guarantees.

- **Authorized bootstrap exception.** On 2026-09-22 the user explicitly
  authorized a one-time, planning-only bootstrap PR on the distinct branch
  `codex/dt1-928-plan-bootstrap`. It contains only this continuation's
  OpenSpec artifacts and loop manifest, uses no closing keyword for #928, and
  exists solely to make the controller's required inputs available on the
  protected base. All code-loop provider actions resume through
  `scripts/loop_engine.py` after that PR is merged.
