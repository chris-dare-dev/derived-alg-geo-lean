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

## 2026-09-21 — preflight bootstrap blocker

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

- **Authorized bootstrap exception.** On 2026-09-21 the user explicitly
  authorized a one-time, planning-only bootstrap PR on the distinct branch
  `codex/dt1-928-plan-bootstrap`. It contains only this continuation's
  OpenSpec artifacts and loop manifest, uses no closing keyword for #928, and
  exists solely to make the controller's required inputs available on the
  protected base. All code-loop provider actions resume through
  `scripts/loop_engine.py` after that PR is merged.

## 2026-09-21 — adversarial pre-freeze corrections

- **Same-issue chunk sequencing is not controller-enforced (verified).** The
  loop adversary confirmed that `ledger_init` checks selected dependencies only
  by issue number. With two #928 chunks in one manifest, it could initialize
  the assembly ledger after a missing or terminally blocked generic ledger;
  repeating generic paths in the assembly file list would then give those paths
  a fresh three-round budget. The original one-manifest plan is therefore
  withdrawn before any ledger exists. Two distinct manifests now enforce the
  handoff through Git history: the generic progress PR is merged first, and
  the final manifest forbids generic source paths.

- **Progress-PR wording was not executable policy (verified).** A progress
  chunk with `allow_progress_pr: true` plus enabled create/merge actions can
  legally create and merge a non-closing PR. The first manifest embraces that
  behavior and disables issue closure; the former prose saying no progress PR
  would be created has been removed rather than relying on a manual promise.

- **Exactness transport needs a stronger boundary (verified).**
  `boundedMonoidalCategory` gives monoidality and an inclusion, but not a
  proof that its curried tensor is `ObjectProperty.lift₂`, and an ordinary
  bifunctor isomorphism cannot carry `ExactBifunctor`'s full
  `CommShift₂Int` coherence. The assembly acceptance criterion now requires a
  focused definitional identification through `ObjectProperty.prop_tensor`, or
  a named transport containing both naturality equations and the Koszul law.

- **Audit prose will become stale on successful assembly (verified).**
  `scripts/AlgebraicGeometryAudit/DerivedOperations.lean` currently describes
  its tensor slice as constructing nothing. The frozen assembly scope includes
  a narrow correction: the new constructor is conditional on supplied ambient
  data, not an unconditional scheme inhabitant.

- **Trust-review integration is stricter than older label guidance (verified).**
  The live `trust-guard-v2` job guards `.claude/loop-specs/` and `openspec/`
  files and requires an OWNER/MEMBER/COLLABORATOR approval containing an
  exact-head, exact-diff `trust-review: v1 ...` marker. It does not accept a
  generic approval or the older label-only guidance. The controller does not
  calculate this marker, so human trust review remains an explicit handoff.

- **Cache-seeding invocation drift (verified).**
  `scripts/seed_worktree_cache.sh` is tracked mode `100644`, despite guidance
  showing direct execution. Use `bash scripts/seed_worktree_cache.sh --dry-run`
  in the future clean worktree; do not infer that a missing executable bit
  means cache seeding is unavailable.

## 2026-09-21 — controller handoff correction and tooling friction

- **Two static same-issue manifests were still insufficient (verified).** A
  second adversarial pass found that merely splitting #928 into a generic and
  assembly manifest did not prove the generic source was merged before the
  assembly could initialize. `ledger_init` had no persisted cross-manifest
  source proof, and a geometry-file duplicate could obtain a fresh budget. The
  controller support change on branch `codex/loop-predecessor-support` (PR
  #1450, pending merge when this entry was recorded) adds
  `predecessor_attestation.emit` for the source and `predecessor_prs` for its
  successor. It verifies source manifest/chunk, issue/branch/closure, both
  digests, cap, reviewed head, merge commit, exact actor-authored marker, PR
  target/body, and ancestry at preflight, ledger initialization, creation,
  approval, and merge. Two independent adversarial reviews passed its second
  and final permitted review round.

- **Assembly-manifest timing is a real data dependency (verified).** The
  successor requires the generic PR number, reviewed head, and merge commit,
  none of which exist during the initial bootstrap. The early static assembly
  manifest is therefore withdrawn rather than populated with placeholders. A
  fresh, reviewed planning-only bootstrap after generic merge will add the
  executable assembly manifest with exact evidence.

- **Precheck invocation ambiguity (verified).** `python3 scripts/precheck.sh`
  fails immediately because `precheck.sh` is POSIX shell, reporting a Python
  syntax error near the shell `case` expression. `bash scripts/precheck.sh`
  succeeds and reports 20 named local gates. Invoke it through `bash` when the
  executable bit or shell association is not guaranteed; this was a no-write
  verification error, not a gate failure.

- **Controller documentation drift (verified).** The controller's historical
  OpenSpec delta still says a run names two or three issues, but the checked-in
  controller and current run-loop skill accept one-to-three issues; every
  tracked one-issue manifest validated successfully. The DT1 manifests use the
  executable one-issue contract and this discrepancy is recorded for future
  controller-documentation cleanup.

- **Pre-support manifest enablement was an escape hatch (verified).** The
  current protected-base controller silently accepts unknown top-level YAML
  keys, so it would ignore `predecessor_attestation.emit` while still allowing
  actions from an enabled generic manifest. The generic manifest is therefore
  shipped disabled until the attestation-aware controller support is merged
  into `origin/main`, after which a separately reviewed enablement update is
  required. The historical `dt1-m41` manifest also remained enabled with a
  five-round static #928 assembly path despite #929 being closed; it is now
  disabled as historical evidence. This correction was raised by the loop
  adversary through a direct validation against the current controller source.

## 2026-09-21 — live protection and controller cutover

- **The exact-head trust guard was retired (verified).** Commit `225d487e`
  (PR #1449) deletes `trust-guard.yml`, removes `trust-surface` from every
  older manifest, and documents why a one-collaborator repository could never
  satisfy an independent approving-review requirement. The live branch
  protection API now reports exactly `contexts: ["ci"]`. Earlier entries about
  `trust-guard-v2` are retained as time-bounded observations, not current
  policy. The generic manifest must therefore require only `ci`; retaining the
  deleted context would make controller preflight fail.

- **The attestation controller is live (verified).** `origin/main` resolves to
  `d224ac70` (`feat(loop): bind successors to attested predecessors`, PR
  #1450), following the merged disabling planning bootstrap `6d3679b2` (PR
  #1448). This reviewed enablement branch is based on that exact main commit;
  it turns on only the generic source manifest, preserves its three-round cap
  and durable attestation policy, and does not create the future assembly
  manifest.

- **Precheck count changed with policy (verified).** The earlier successful
  `bash scripts/precheck.sh` result named 20 local gates before #1449. Its
  removal of the local trust-guard gate reduces the expected current count to
  19; this is a policy change, not a regression or a reason to restore a stale
  required check.

- **Correction — #1449 did not update every historical manifest (verified).**
  The preceding entry overstated #1449's scope. Enabled
  `.claude/loop-specs/sf8-5-nonflat-derived-effect.yaml` still requires
  `trust-surface`; `git merge-base --is-ancestor 17e0b382 225d487e` confirms
  that it predates #1449, and the #1449 diff leaves it untouched. It therefore
  cannot preflight against `main`'s `ci`-only protection. This DT1 enablement
  change fixes its own manifest only; the SF8 repair needs a separately scoped,
  reviewed change. This correction came from independent loop and integration
  adversarial reviews, and records a genuine tooling-integration blind spot.

## 2026-09-21 — phase-order and advisor-schema friction

- **Advisor persistence contradicts executable preflight (verified).**
  `.claude/agents/altitude-scout.md` and
  `.claude/agents/hypothesis-elimination-scout.md` require tracked backlog
  rows before the first `ledger init`, while `scripts/loop_engine.py preflight`
  rejects both a dirty tree and any `HEAD` that differs from `origin/main`.
  An advisor row cannot therefore be persisted before the required immediate
  pre-init preflight: an uncommitted row is dirty and a committed row advances
  `HEAD`. For this run the advisors returned verbatim proposed rows read-only,
  clean preflight passed, the ledger was initialized, and only then was the
  altitude finding appended. A material finding that would change frozen scope
  must instead stop the run before initialization; do not silently use this
  ordering to change the manifest after a ledger exists.

- **Hypothesis-scout state vocabulary is stale (verified).**
  `.claude/agents/hypothesis-elimination-scout.md` directs an advisor to mark
  a compiled weakening `L (proof-witness verified)`, but
  `docs/architecture/generalization-backlog.md` permits only `UNVERIFIED`,
  `CONFIRMED <PR>`, and `FALSIFIED <counterexample>`. The DT1 advisor found no
  proof yet and wrote no row, so no false state was introduced. Future tool
  refinement should reconcile the guide with the tracked schema before a
  verified weakening forces an ambiguous record.

## 2026-09-22 — binary output-transport proof friction

- **The upstream API gap is explicit, not inferred (verified).**
  `Mathlib/CategoryTheory/Shift/CommShiftTwo.lean:155` has a TODO for output
  postcomposition of a `Functor.CommShift₂`; its only supplied restriction
  instances are `precomp₁` and `precomp₂` at lines 120 and 138. The generic
  DT1 proof therefore cannot cite a missing ambient transport. This is a
  source-backed boundary, reproduced by `rg -n "TODO|precomp"`
  `.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/CommShiftTwo.lean`.

- **Canonical full-subcategory shifts are opaque in the proof-relevant places
  that matter here (verified).** A direct `simp`/`rw` calculation stalls on
  definitional-but-not-instance-transparent membership witnesses for
  `P.ι ⋙ F.obj X` and on the selected `P.ι.commShiftIso`. In the reproducible
  probe `lake env lean /tmp/dt1_iota_shiftcomm.lean`, a theorem-local
  `unseal ObjectProperty.hasShift ObjectProperty.commShiftι`, explicit local
  instances, explicit membership witnesses, and `erw` (rather than `rw`) are
  required to prove that the inclusion maps
  `shiftFunctorComm P.FullSubcategory` to the ambient `shiftFunctorComm`.
  The issue is elaborator transparency, not a counterexample to coherence;
  future tool guidance should distinguish the two and document this standard
  full-subcategory normalization route.

- **A tempting existing helper has the wrong dependency altitude (verified).**
  `DerivedAlgGeo/CategoryTheory/Triangulated/ShiftFunctor.lean:143` proves
  `Pretriangulated.commShiftIso_commShift`, but its stated hypotheses are only
  preadditivity and additive integral shifts. Importing that Triangulated leaf
  into `CategoryTheory/ObjectProperty/Bifunctor.lean` would make the generic
  foundation depend on a misplaced application-level path. It is being used
  only as a local proof template; a future ownership cutover may extract it to
  the direct `CategoryTheory/Shift` owner with its own review.

## 2026-09-22 — audit-completeness baseline drift

- **The repository-wide audit-completeness gate is presently red outside this
  chunk (verified).** `lake env lean scripts/EnumDecls.lean >
  /tmp/dt1-enum-decls.txt` followed by `python3
  scripts/check_audit_complete.py /tmp/dt1-enum-decls.txt` reports 14 new,
  unaudited `AlgebraicGeometry.DerivedCategory.Dqc.ZModTwoNonflatDerived.*`
  declarations and an AlgebraicGeometry shortfall of 762 against its 748
  ceiling. The changed paths for this generic branch contain neither
  `DerivedAlgGeo/AlgebraicGeometry/` nor the AlgebraicGeometry audit baseline;
  the StabilityCondition bucket remains exactly 287 missing (its ceiling) and
  DGCategory remains 0. This is an unrelated integration/baseline repair, not
  authority to edit its audit or relax the ratchet here. The DT1 declarations
  are nevertheless registered in `StabilityConditionAudit/TStructureCore.lean`
  and its named audit build passes.
