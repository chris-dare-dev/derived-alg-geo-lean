# SF11 loop-engineering notes

This file is the repository-facing memory for the bounded run covering issues
#1060, #1061, and #1062. It records friction and stale statements; it is not a
replacement for a Lean theorem or an issue acceptance criterion.

## Initial observations (2026-09-19)

- `scripts/loop_engine.py` originally rejected every issue labelled `epic`,
  while all three selected SF11 issues are roadmap epics. The manifest now has a
  narrow `eligibility.allow_epic_issues` allow-list. The controller must retain
  rejection for every unlisted epic, blocked, research, and spike issue.
- The loop branch/tooling PR was merged as PR #1399, but a local checkout may
  still have a stale `origin/main`. Fetch before choosing a protected-base ref;
  do not infer merge state from an old local ref.
- `openspec list --all` is not a valid discovery command in the installed CLI;
  `openspec list` (or `openspec list --specs`) is the supported form. The
  generated skill text and CLI affordance should be kept aligned if this recurs.
- The existing SF11 modules are honest about their boundary but easy to
  misread: `BaseChangeCategory.lean`, `BaseChangeData.lean`, and `SLocal.lean`
  construct carriers and closure operators while still leaving geometric
  compactness, coherence, generation, and restriction witnesses supplied.
  Words such as “actual”, “constructed”, and “nothing is inhabited” must be
  read together, not treated as interchangeable evidence of issue completion.
- `SLocal.lean` uses `CompactSpace U.toScheme` to represent the paper's
  quasi-compact opens. This matches the current Mathlib API but is a likely
  source of confusion for agents reading “compact” as a derived-category
  compactness claim.
- `TStructure/Local.lean` now owns the categorical uniqueness half of Remark
  4.6(1), but its docstring still points to `Phase/Transfer/Inducing.lean` as if
  all S-locality were outside the categorical layer. Retire that sentence only
  after the geometric quantifier and at least one inhabitant are genuinely
  proved.
- `stability-families.yaml` revisions 56–67 are useful status history, not
  completion evidence. In particular revision 65 closes only the categorical
  restriction/equivalence shape, revision 67 explicitly says #1061 has no
  inhabitants, and the #1060 summary lists geometric witness obligations still
  open.
- PRs #1336, #1339, #1340, #1344, and #1346 are historical partial advances;
  their bodies explicitly leave geometric inhabitants or coherence open. A
  future agent should read those bodies before assuming a similarly named
  declaration closes an epic.
- `check_roadmap --require-api` exposes an inherited RM-07 defect: issue #854
  is CLOSED even though its merged PR #1392 explicitly says its shift/triangle
  and Ext obligations remain, while `dg-enhancements-e9` remains
  `in_progress`. This SF11 run must not repair that unrelated tracker state by
  changing the mathematics. The controller now scopes the roadmap gate to the
  manifest base ref, so the defect is reported as inherited and any SF11-authored
  roadmap drift still fails closed.
- The controller's original preflight rejected the exact planned issue branch
  that the manifest requires, even when `HEAD` was the clean `base_ref`. Commit
  `9e9f354a` removes that contradictory branch-name rejection; the exact-head,
  clean-worktree, and duplicate-PR checks remain the real safety conditions.
- The local and CI gate scripts originally validated only
  `.claude/loop-specs/sf8-sf9-pilot.yaml`. `scripts/validate_loop_specs.sh` now
  validates every YAML manifest, and the trust surface/CODEOWNERS explicitly
  cover loop specs, reviewer prompts, the run-loop skill, and `openspec/`.
- OpenSpec task 2.3 named a nonexistent `scripts/precheck.py`; the repository's
  actual local contract is `scripts/precheck.sh --no-build` plus a named
  targeted `lake build` invocation. Keep this distinction visible in future
  plans.
- New public declarations in a Families module also require an entry in the
  exact `scripts/AlgebraicGeometryAudit/StabilityConditionFamilies.lean`
  record. The SF11 manifest now includes that audit slice; omitting it lets a
  compiling change fail later in audit-completeness rather than at the frozen
  chunk boundary.
- `BaseChangeCategory.lean` had a stale ownership sentence saying that the
  unbounded tensor *is* the K-flat construction, even though the root API takes
  an operation and `KFlatBaseChange.lean` is only one source-faithful producer.
  Keep “K-flat producer” and “root operation” distinct in module prose; the
  distinction is what lets exact/open or future higher-categorical producers
  reuse the category construction.
- #1061 adds a family-level S-local slicing API, so the older Phase/Transfer
  wording that put all S-locality outside the categorical layer is now stale.
  The revised wording distinguishes the formal quantifier/uniqueness API from
  the still-explicit geometric restriction witnesses.
- Lean field names that coincide with command keywords can produce misleading
  parser errors: `NoetherianLocalityData.local` was rejected, so the field is
  named `localData`. A failed declaration then generated downstream “invalid
  field” errors; fix the first parser error before chasing projections.
- The filtered Families target may replay over 4,000 cached prerequisites even
  when only one changed module is requested. This remains a targeted module
  build, not a repository build; native PowerShell is the reliable fallback
  when WSL stalls.
- A first S-local slicing placement imported `PhaseTruncation` directly into
  `Families/SLocal.lean` and failed the subject-layering gate: Families must
  not reach the stability tree. Keep phase-level locality in
  `AlgebraicGeometry/DerivedCategory/Stability/SLocal.lean`, with the
  stability umbrella importing it, and let Families own only the t-structure
  quantifier.
- `scripts/precheck.sh --no-build` still runs the non-Lean `local-build` policy
  gate; it skips only the final targeted Lake build. The first invocation was
  mistaken for a repository build and interrupted before this distinction was
  checked.
- The controller's frozen-prefix matcher treats a directory prefix and a
  sibling umbrella file separately. When a chunk changes both
  `DerivedCategory/Stability/SLocal.lean` and
  `DerivedCategory/Stability.lean`, list the umbrella file explicitly or PR
  creation fails closed even though the directory entry is present.

## Time-saving practices

- Use `scripts/precheck.sh` only with a changed-module/targeted Lean selection;
  never run `scripts/gates.sh` locally for this loop. CI remains the full
  repository verdict.
- Run OpenSpec structural/strict validation and the controller unit tests before
  spending time on Lean elaboration. Run the four adversaries on one frozen
  commit, record the ledger, and do not start an unbounded critique loop.
- Keep the protected-base ref explicit after every merge. A branch that is
  “based on main” by intent but not at the exact manifest ref will fail closed.
- Search the roadmap and the source module docstrings together; roadmap
  summaries contain the chronology, while module prose contains the current
  ownership and intentionally uninhabited seams.
- A cold `.lake` cache makes even a narrowly named Families target compile
  thousands of Mathlib prerequisites before reaching the changed modules. The
  first baseline attempt was interrupted after the cache reached roughly
  3,600 targets; treat that as cache warm-up, not as evidence that the whole
  repository target was run, and retain `LEAN_NUM_THREADS=2` for repeatable
  targeted builds.
- The full `StabilityConditionFamilies.lean` audit imports a much larger
  stability graph than the changed base-change modules need. For a local
  completeness check, a generated two-import audit can print only the changed
  declarations and still be passed through `check_audit.py` with its own
  command-count source. Avoid running that slice while another Lake build is
  compiling the same cache: concurrent workers can race on intermediate
  `.olean` paths and report misleading “file not found” failures.
- Historical caution from the pre-follow-up wording: a passing loop ledger
  certifies the reviewed commit and its adversarial checks; it does not
  automatically prove the chunk's OpenSpec checklist or GitHub issue
  acceptance text. At that point the exact producer/audit slice passed while
  tasks 2.1–2.3 still truthfully recorded supplied compactness, generation,
  and coherence obligations. The active five-round contract below records the
  later explicit re-scope; do not silently treat this historical warning as a
  proof of those geometric hypotheses.
- Some completed reviewer turns returned an empty final-message payload from
  the app even though their tool work ended. Record that as a controller
  visibility defect and back any adjudication with independently captured
  command output; do not treat an empty payload as an unexamined PASS.
- Marking OpenSpec task 2.4 complete after the bounded review changed the
  OpenSpec digest after ledger `sf11-1-base-change-categories-v4` was written.
  The controller should therefore reject that old ledger for remote actions;
  reinitialize a fresh frozen ledger after any checklist edit.
- The frozen-scope matcher initially normalized only changed paths with
  `lstrip("./")`, not the manifest prefixes. As a result, `.claude` and
  `.github` entries falsely failed to match their own frozen scope. Normalize
  both paths and prefixes symmetrically, and keep a regression test for
  leading-dot directories; otherwise loop-control debugging can be mistaken
  for a source or mathematical failure.

## SF11.3 observations (2026-09-20)

- The checked-out `IndExtension.lean` imported the object-property theorem file
  named `TStructure/Restriction.lean`, but the one-functor
  `TStructure.Restriction` carrier is owned by `TStructure/Local.lean`.
  The Ind-extension module therefore needed an explicit `Local` import before
  it could expose its proved restriction consequence. Similar filenames are
  easy for an agent to confuse; inspect the namespace before changing an
  import.
- Mathlib's `PreservesColimit` takes the diagram and then the functor:
  `PreservesColimit K F`. The expression `PreservesColimit K (K ⋙ F)` is a
  type error, not the statement that `F` preserves the colimit of `K`.
- In dependent category families, annotate the shift index explicitly as
  `[∀ (i) (n : ℤ), (shiftFunctor (D i) n).Additive]`; leaving `n` implicit
  caused a stuck `HasShift` instance while building the Theorem 5.3 boundary.
- Theorem 5.3's scheme-level flat/fpqc descent, tensor, and four base-change
  comparisons are not available as generic theorems in the current tree. The
  new `Families/Theorem53.lean` therefore exposes actual source-shaped range
  and exactness owner data, while its formal theorems only compose supplied
  comparisons. The OpenSpec task wording was rewritten to say this explicitly;
  it must not be read as a proof of the geometric inputs.
- The focused native builds for the new bridge and Theorem 5.3 modules replay
  roughly 1,747 cached prerequisites. This remains a targeted module build;
  no umbrella or full-repository build was invoked. If WSL stalls during this
  cache traversal, use the native PowerShell `lake.exe` path.
- The official stability audit imports a much broader graph than the new
  #1062 modules; a cold direct run stopped on an unrelated missing
  `FourierMukai` object before reaching the declarations under review. A
  focused temporary audit of the exact bridge/Theorem 5.3 declarations passed
  with only `propext`, `Classical.choice`, and `Quot.sound`, and the permanent
  audit lists were updated separately. Do not mistake the broad audit's import
  failure for a theorem failure or silently skip the focused audit.
- Lean does not generate `.mk.inj`/`.mk.sizeOf_spec` declarations for several
  proposition-valued or proof-irrelevant structures in this boundary. Adding
  those guessed names to the axiom audit produces unknown-constant errors;
  audit only the declarations that actually exist.
- The umbrella/root reachability gate does not treat a declaration-heavy
  `CompactlyGenerated.lean` as the child-directory umbrella: the new
  `IndFilteredColimits` leaf had to be re-exported from the higher
  `CategoryTheory/Triangulated.lean`, and `Families.lean` had to import
  `Theorem53` directly. A targeted module build can pass while the leaf is
  silently absent from the repository build graph, so run the no-build
  umbrella gate before freezing the review head.
- The loop controller's frozen scope matching likewise distinguishes a
  directory prefix from a same-stem umbrella file: `Families` did not admit
  `Families.lean` during PR creation until the exact umbrella path was listed.
  Include both entries when a chunk edits an umbrella beside its child
  directory.

## SF11.3 recut observations (2026-09-21)

- The recut was triggered by a real remote-policy change, not by a missing
  mathematical label: current `origin/main` no longer contains
  `.github/workflows/trust-guard.yml`, and branch protection reports only
  `ci`. The v3 manifest's `trust-surface` requirement was stale state and is
  not carried into v4.
- The first candidate v4 plan ref was found to contain the earlier SF11.3
  implementation commits. Using it as `base_ref` would have hidden the source
  changes from the fresh chunk diff and adversaries. The clean v4 plan starts
  at current `main` and contains only the SF11 OpenSpec/manifest; the v4 run
  branch carries the implementation separately.
- The loop validator rejected an initially redundant manifest requirement
  because it was not named by an OpenSpec requirement. This was a
  documentation/contract mismatch, not evidence that the validator should be
  weakened; the redundant line was removed while the runner still requires
  `ci` explicitly.
- A shell command that created a worktree and then merged without changing its
  working directory merged `origin/main` into the old local v3 worktree. The
  worktree was clean and the merge was unpushed, so no remote state changed,
  but this is an operational footgun: run each git mutation with an explicit
  worktree directory and verify `git branch --show-current` afterward.
- The existing draft PR #1453 is bound to the old v3 branch/manifest. The
  controller's preflight deliberately refuses a second open PR for the same
  issue, so the replacement is prepared as
  `agent/sf11-3-followup-v4-current` and the old draft must be explicitly
  retired before the new PR is created.
- While the first v4 candidate was being checked, `main` advanced from
  `858ca700` to `49c33eda` to delete the remaining trust-surface residue in an
  unrelated manifest. The candidate was discarded rather than reviewed
  against stale main; this current-main plan ref is `d0395054`.
- No reviewer or controller is allowed to infer that “trust surface removed”
  means that audit evidence may be relaxed. The v4 acceptance still requires
  actual AlgebraicGeometry audit records, unchanged missing-declaration
  baseline/ceilings, and no new `sorry`, `admit`, or axiom.

## Follow-up observations (2026-09-19)

- Moving the operation-facing declarations from `KFlatBaseChangeData` to
  `DerivedBaseChangeData` requires a deliberate root/K-flat split. The K-flat
  namespace still owns resolution witnesses and specialized coefficient or
  projection-formula data; generic sequence, decomposition, tensor-duality,
  and detection APIs must name the root carrier explicitly. A blind namespace
  replacement either leaves the audit stale or hides a model-specific
  hypothesis behind a generic-looking theorem.
- Lean parser errors appeared when namespace boundaries and duplicate section
  variables were adjusted in the same patch. Keep namespace moves and
  signature changes mechanically small, and run the affected module before
  changing the next layer.
- The focused axiom audit is substantially cheaper and more reliable for this
  seam than the full stability-family audit: the latter imports the entire
  stability graph and needs unrelated `Moduli` artifacts. Keep the focused
  audit beside the loop ledger, while retaining the repository audit's current
  root/K-flat declaration list so it cannot silently drift.
- In PowerShell, setting `$env:SKIP_ACTIONLINT` did not propagate through the
  repository's nested `bash` invocation. For the local precheck, set it in the
  bash command itself (for example `bash -c 'export SKIP_ACTIONLINT=1; ...'`);
  otherwise a missing local `actionlint` binary looks like a source failure.
- On this checkout, the precheck's `check_layering.py` scan can spend several
  minutes in WSL filesystem I/O after the source-independence gate, with no
  output and an uninterruptible Python process. Treat that as an environment
  stall, stop the owned scanner rather than waiting on it indefinitely, and
  retain the individual gate results already emitted.
- For the five-round follow-up, the no-build gates were run natively with
  PowerShell and `python`, including `check_layering.py`; all passed. The
  default roadmap gate also passed. A scoped roadmap check against a ref with
  no changed roadmap entries reports the intentional “no roadmap items found”
  failure, so that invocation is not evidence of a roadmap defect.

- The issue acceptance and the OpenSpec task wording are not identical. Issue
  #1060 explicitly carries strongness and finite-amplitude facts as downstream
  hypotheses, while tasks 2.2--2.3 ask this tranche to prove the corresponding
  geometric witnesses. The `DerivedBaseChangeData` refactor satisfies the
  carrier/construction boundary, but it does not close those tasks: tensor
  duality, generation propagation, projection approximation/restriction,
  bounded coherence, finite amplitude, and component detection remain visible
  inputs. Do not mark 2.1--2.3 complete or close #1060 from the refactor alone.
- The first adversarial round exposed an operational loop hazard: multiple
  reviewers independently launched broad cold-cache Lean builds despite being
  given frozen targeted evidence. The Codex app currently has no reliable
  cancellation/result-payload path for an active reviewer turn, so a bounded
  run must forbid reviewer builds in the prompt and stop only clearly owned
  process trees after the time budget is exceeded. Do not kill the external
  GitHub runner while cleaning this up.
- A broad diff sent to the local review model was misclassified as an audit-only
  change. For this repository, local adversarial passes are useful only when
  given the actual changed declarations and their acceptance contract in small
  excerpts; the Codex agent remains the mathematical quality gate.

## Historical blocker matrix (round 2)

The following is the boundary reached before the five-round follow-up contract
was written. It is
intentionally declaration-level so a later agent can distinguish a completed
carrier refactor from a theorem that still needs geometric input.

- Task 2.1: `DerivedBaseChangeData` is the sole operation-facing carrier;
  `KFlatBaseChangeData.toDerivedBaseChangeData` is a producer, and
  `DerivedBaseChangeData.ofExactPullbacks` is an exact-pullback producer. The
  root `derivedTensor` field is still an explicit bifunctor interface, not a
  universal-property construction of unbounded `Dqc` tensor. Quasicoherence
  preservation and compact preservation remain explicit where the repository
  has no general theorem.
- Task 2.2: the formal sequence/decomposition chain compiles, but
  `CompactFiberTensorDuality.PushforwardPreservesSourceComponents`,
  `QuasicoherentFullnessPropagationData`,
  `QuasicoherentProjectionApproximationData`,
  `PerfectProjectionRestrictionData`, and
  `DerivedBaseChangeData.PreservesCompactObjects` still carry the corresponding
  duality, fullness, projection, restriction, and compactness witnesses. These
  are visible call-site obligations; they are not concrete proofs of the
  geometric statements.
- Task 2.3: `TargetBoundedTStructure`,
  `DecompositionData.HasFiniteAmplitude`,
  `DecompositionData.PreservesCoherentCohomology`, and bounded-sequence fullness
  remain inputs. The bounded and functor-equivalence APIs are honest conditional
  theorems, but no general target t-structure, finite-amplitude theorem,
  coherent-preservation theorem, or component-detection theorem has been
  constructed by this candidate.

Under the pre-follow-up wording, tasks 2.1--2.3 correctly remained unchecked
until these witnesses were either proved in their geometry owners or explicitly
re-scoped as external hypotheses in the frozen OpenSpec contract. The active
follow-up contract below makes that re-scoping explicit. A passing targeted
build is evidence for the API boundary only; it is not evidence that the
geometric hypotheses themselves are proved.

## Current five-round follow-up contract

The follow-up explicitly re-scopes the supported part of tasks 2.1--2.3:
formal closure, restriction, comparison, and detection theorems are complete
when they consume the named geometry-owner hypotheses above; the hypotheses
are not themselves claimed as proved. The active task wording now records that
boundary and uses the user-authorized five-round cap. The earlier three-round
ledger remains preserved under `.loop-runs/sf11-1-followup/` and is not reused
as evidence for the new candidate.

A tempting but invalid shortcut was to generalize only
`CompactlyGenerated/Brown.lean` from universe zero to the scheme universe.
Its mapping-telescope factorization API is also universe-zero, so a partial
generalization produced cascading universe mismatches. Do not widen one layer
of a universe-sensitive representability construction without first auditing
the entire telescope dependency chain; the attempted edit was reverted.

## SF11.3 follow-up freeze correction (2026-09-21)

The first coding draft removed the projection-only filtered-colimit carriers
from `IndFilteredColimits.lean` and updated the AlgebraicGeometry audit. A
static dependency check then exposed a second audit owner,
`scripts/StabilityConditionAudit/TStructureCore.lean`, which still printed
axioms for the removed declarations. Leaving that file outside the frozen
chunk would make the intended refactor unbuildable and would force an
out-of-scope edit during review. The follow-up was therefore re-frozen as
`sf11-3-followup-v2` from a new immutable plan ref, with that audit directory
explicitly included. The prior draft commit is retained only as a migration
source; its ledger is not reused as review evidence.

The official OpenSpec CLI was installed in an ephemeral `/tmp` toolchain
because the host initially lacked both Node and `openspec`; strict validation
passed for the change and all six repository changes. This environment detail
is operational friction, not a repository dependency, and must be recreated or
replaced by the runner before future local validation.

The reference-base run at `4e56e5ca` compiled the changed module, both audit
libraries, the public `DerivedAlgGeo` umbrella, and the
development/specialization targets. That snapshot is not the reviewed head,
not the current `origin/main`, and not CI evidence. On the round-one
candidate `d8e3d6c1`, the same targeted local builds and the two axiom
transcripts passed with 5,374 AlgebraicGeometry commands and 7,087
StabilityCondition commands; these are local measurements, not claims about a
GitHub run. The environment completeness ratchet measured AlgebraicGeometry
at exactly its recorded ceiling (6,077 public, 5,329 audited, 748 missing),
with no new baseline rows. The 351-declaration failure quoted from PR #1425
therefore came from an older base/audit state; it must not be used as current
evidence after the base refresh. At that v2 snapshot, five stale
single-instantiation baseline rows were visible; the v3 freeze below migrates
only the two rows for declarations deleted by this repair.

Another undocumented prerequisite surfaced: `scripts/EnumDecls.lean` imports
the root `DerivedAlgGeo` and `DerivedAlgGeo.Development` modules, but the
audit-library build does not materialize those umbrella oleans. A clean runner
must build the root and development/specialization targets before running the
completeness sweep; otherwise the command fails with a missing object-file
error despite the audit libraries themselves being green.

## SF11.3 follow-up v3 freeze correction (2026-09-21)

Round-two repository-boundary and mathlib reviews identified that
`scripts/single_instantiation_baseline.txt` is consumed by
`check_single_instantiation.py`, so its two rows for the deleted
`FilteredColimitTruncationData` and
`IndExtensionFilteredColimitData` declarations were operational stale data,
not merely prose. The v3 manifest explicitly freezes that file and migrates
only those two rows. It does not edit `scripts/audit_missing_baseline.txt`,
change a ceiling, add a TODO, or relax the detector threshold. The v2 ledger
and its review evidence are not reused; v3 starts from immutable plan ref
`agent/sf11-3-followup-plan-v3` with a fresh ledger.

The v3 exact-head checks are local measurements, not CI evidence. The targeted
module build, umbrella/development prerequisite build, per-slice axiom audits,
single-instantiation detector, and declaration-completeness sweep are rerun
after the migration on the clean v3 candidate that the new ledger binds to.
