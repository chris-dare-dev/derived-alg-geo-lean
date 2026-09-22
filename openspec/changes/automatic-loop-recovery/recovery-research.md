# Recovery research: bind supporting evidence to its immutable source

Status: proposed recovery plan, **not independently accepted**. Researcher:
`recovery_guidance`. No implementation or provider mutation was performed.
Research target: terminal initial attempt at
`43460a10c42dc092dd911768ada3f132967bc3d0`, against original base
`b8306d6b9775d34fdbbb4504f639fe98085efd38`.

## Evidence and root cause

Read the original proposal, design, tasks and six requirements, and all twelve
verbatim C1/C2/C3 review messages in `.loop-runs/automatic-recovery-review/`.
The negative corpus is C1 boundary/mathematics/style, C2 abstraction, and C3
abstraction/boundary/style. Preserve every complete transcript, including
already-resolved findings, rather than reducing it to the final BR-4 summary.
The C3 style file arrived during research; the earlier eleven-file inventory
was incomplete, not evidence that its review had passed or could be skipped.

C3 repaired obligation inheritance, but reused `backlog_records`, which reads
the current worktree (`scripts/loop_engine.py:1512–1527`). The predicate answers
whether local text mentions a target, not whether the reviewed artifact carries
its disposition. `require_recovery_lift_backlog` invokes that predicate both at
passing adjudication and publication. SHA checks separately bind the code, so
combining the two true predicates does not bind this supporting text to that
SHA. This is a missing evidence-source invariant, not a need for more review
roles or a remote attestation service.

An isolated temporary Git fixture reproduced the following without touching
repository source or contacting GitHub. The fixture used `RecoveryCliTests`
setup and `RecoveryTests.lift_recovery`, gave the successor the fixture's real
HEAD, and retained all inherited findings. Registry lookup/load were isolated
with fixture state; real Git handled the repository and remote lookup.

| Probe | Observed at C3 |
| --- | --- |
| `git show <reviewed-sha>:docs/architecture/generalization-backlog.md` before creating the file | Exit 128: artifact absent |
| Recovery backlog gate with no local entry | Rejected |
| Write target only into an untracked backlog; call the same gate | Accepted |
| Call common recovery publication gate with that state and real Git remote lookup | Accepted |
| Commit backlog at a later HEAD; retain the older reviewed SHA | Backlog gate accepted |
| Replace only the tested backlog gate's candidate SHA with nonexistent `f` repeated 40 times | Backlog gate accepted without consulting object existence |
| Modify an OpenSpec artifact without committing it | `openspec_digest` changes despite its docstring saying “committed” |

The nonexistent-object probe tests the backlog helper, not the entire publication
pipeline. Recording a normal recovery review already uses `cat-file -e`; the
new artifact helper must independently fail closed when its object is absent.
The current positive regression at `test_loop_recovery.py:620` writes an
uncommitted backlog, uses a synthetic review SHA and mocks Git wholesale. It
therefore rewards the weaker property and cannot catch the reported failure.

## Inventory of filesystem evidence

| Input | Present source/binding | Required treatment |
| --- | --- | --- |
| Lift backlog | Worktree read plus substring match | Published disposition is read from the exact candidate/reviewed Git blob; no worktree fallback |
| OpenSpec artifacts | Worktree content digest checked against registered digest on load | Frozen authority is content-bound already; accurately describe this as a content digest, not proof of a committed file. Preserve mismatch rejection |
| Execution manifest | Parsed canonical digest, registered path and contract checks | Preserve the original registered authority. Dirty semantic changes must fail; a published-plan claim needs separate Git evidence, not an inference from its pathname |
| Review input files | Read once, copied verbatim with digest into canonical ledger; final SHA trailer validated | Later file edits must not change recorded evidence. Continue using stored bytes, never reread `finding_source` as authority |
| Resolution JSON and recovery plan/review JSON | Parsed once, stored in canonical state; plan review binds submitted digest | Preserve snapshot ownership and exact plan binding; evidence adequacy remains independent reviewer judgment |
| Historical ledger files | Raw file hash checked on import, snapshot and digest retained | Preserve exact imported bytes/provenance and charged rounds; subsequent source changes cannot refresh the imported snapshot |
| Registry and exported ledger | Shared registry owns state; export is cache | Keep canonical validation/locking; exported edits cannot supply proof |
| PR body file | Validated local content, subsequently consumed by `gh --body-file` | This is outgoing intent, not reviewed backlog proof. Existing recovery PR postcheck validates actual remote body/head and reports races; retain those checks rather than claim atomicity |

The narrow fix is not “make every input a Git blob.” Review transcripts and
research plans are correctly immutable ledger snapshots. Separate the two
evidence classes: frozen authority/transcripts use stored content bindings;
claims about what will ship use Git objects selected by the review SHA. No new
carrier, service, or duplicate ledger is needed.

## Proposed recovery strategy

1. Introduce one controller-side immutable text-artifact reader taking an
   explicit full commit SHA and fixed repository-relative path. Verify that the
   object is a commit and the entry is an ordinary tracked blob; reject absent
   objects, missing paths, symlinks and non-text evidence. Never use HEAD or a
   worktree fallback. Keep Git access out of the pure recovery state machine.
2. Route **both** recovery passing-adjudication and common publication lift
   checks through that reader at `latest_round(state).commit`. Also ensure the
   subsequent generic `pass_with_lift` adjudication branch cannot fall back to
   mutable text for recovery mode. Read once per decision and reuse the bytes.
   Legacy behavior outside recovery remains unchanged unless independently
   reviewed as part of the original acceptance requirements.
3. Preserve C3's whole inherited lift transcripts, per-review resolutions and
   current-manifest prefix intersection. Historical requests outside current
   scope remain obligations to record; they never authorize out-of-scope edits.
   Prepare backlog dispositions before freezing a candidate. A later backlog
   commit needs the next allocated review round, not an unreviewed exception.
4. Distinguish binding from semantics. Replace recovery's inherited substring
   predicate with a narrow structured row check: an actual visible row outside
   code fences must have an exact `proposed ancestor` value and the existing
   required row fields, including a recognized state. Ignore the fenced schema
   example and reject prose/prefix-only matches. Define accepted optional
   backtick quoting explicitly. Independent review still judges rationale and
   substantive adequacy. Do not import the unpublished #1458 parser redesign
   or create new side-artifact publication authority.
   Leave the legacy helper unchanged outside recovery mode. Document recovery
   rows as using the canonical repository-relative target path exactly in
   `proposed ancestor`; existing namespace names or multi-line descriptive
   ancestor values are not silently coerced to paths. Such existing rows remain
   historical context and cannot satisfy a new path-specific recovery claim
   unless a complete exact-path disposition is recorded in the reviewed tree.
5. Correct the “live backlog gate,” “committed OpenSpec digest,” and “missing
   reviewer round is void” descriptions. Their observed implementations differ
   from those claims. Document which artifact owns each fact. Retain all prior
   case-normalization, provider SHA/identity checks and unchanged review grammar.

## Verification matrix for independent acceptance

Use real temporary Git repositories and real commit objects for evidence tests;
mock provider reads/writes only at the provider boundary. No positive case may
mock away the exact Git-artifact reader it is supposed to test.

| Case | Expected result |
| --- | --- |
| Reviewed commit contains the required backlog row | Adjudication and publication succeed, subject to other gates |
| Entry exists only untracked or dirty | Both decisions reject |
| Entry exists at later HEAD but not reviewed SHA | Reject |
| Reviewed SHA has entry; worktree deletes/modifies it or HEAD moves | Artifact result remains determined by reviewed SHA; push/create retain their separate HEAD/cleanliness restrictions |
| Commit, file or ordinary blob absent; path is symlink | Reject, without fallback |
| Remote PR head differs from reviewed SHA | Existing approve/attest/merge/close gates reject before mutation |
| Existing remote PR matches reviewed SHA but local dirty text alone supplies row | Common publication gate rejects for approve, attest, merge and close |
| Local push/create HEAD differs; remote branch changes during create | Retain current prechecks and truthful raced-result reporting |
| Fresh current-panel lift plus earlier PASS reviews | No retrospective finding IDs required; committed row required before passing |
| Partial/failed/imported lift carried through resume | Same finding retained and committed disposition checked |
| Historical lift outside current declared prefix | No new edit authority; disposition obligation retained |
| Prose/prefix-only ancestor mention, fenced schema/example, malformed row/state | Reject; exact visible complete row accepts |
| Fresh lift discovered after freeze, with no existing row | Append row, commit and allocate another panel; old SHA remains nonpublishable and all prior verdicts remain unchanged |
| Review source file changed after recording | Canonical transcript/digest stays unchanged |
| Manifest/OpenSpec semantic content changes after registration | Existing registered-contract checks reject; restoring original content does not replenish rounds |
| All existing loop regressions | Pass; update the misleading dirty-backlog positive test rather than preserve its expectation |

## Recovery admission and bounded continuation

The task checklist says “Max three formal panels,” and the migration paragraph
says three rounds “for this implementation.” Read alone, those phrases are
ambiguous between an initial attempt and the entire objective. The same design
and normative requirement explicitly say three rounds **per attempt** followed
by bounded research, and the user explicitly requested and authorized implementing
automatic recovery after exhaustion without another approval. Thus the initial
attempt remains terminal after C3; a successor can be admitted only by applying
that approved evidence-gated recovery policy, not by silently calling a fourth
panel or changing the task identity. This is an interpretation for independent
review, not the researcher's self-granted authorization.

Adopt a stable manual bootstrap objective `automatic-loop-recovery-core`, with
the exact original file list and acceptance, three already allocated rounds,
at most two recovery episodes, nine total allocated implementation rounds, two
plan submissions per episode, and the approved finite elapsed allowance.
The external `.loop-runs/automatic-recovery-review/objective.json` already
records this manual adoption, three allocated rounds, episode 1 researching,
and an elapsed-budget start of `2026-09-22T16:41:19-04:00` from C1. I verified
its twelve stored texts and SHA-256 hashes against the original review files.
Retain that start and derive the one-week deadline rather than restart the clock.
Research and code
subtasks share those limits; neither gets a new budget. Preserve all C1/C2/C3
commits and transcripts unchanged. No real GitHub issue number has been allocated
for this feature by this research; do not invent one to satisfy a candidate CLI.

The controller under review cannot certify its own authority. The bootstrap
supervisor should maintain an auditable declarative record with hashes of this
plan, the original contract, all twelve review files and its independent plan
review. The candidate engine can be exercised in isolated tests, but must not
authorize its own publication or silently create a canonical production registry
entry. A reviewer distinct from both researcher and implementer must accept the
exact proposed plan and this scope/authority interpretation before source edits.
If rejected, revise research within the same episode's plan allowance. If
accepted, successor code still requires all four independent roles on the same
commit, full inherited dispositions and existing publication permissions.

This report grants no acceptance and no publication authority. New base commits
or other concurrently modified worktrees do not alter the frozen attempt; do
not rebase or merge them as an uncounted repair. If the independent reviewer
cannot reconstruct standing authority for this adoption, report that concrete
authority gap rather than inventing approval. Otherwise execute the already
authorized research/review/resume transitions automatically.
