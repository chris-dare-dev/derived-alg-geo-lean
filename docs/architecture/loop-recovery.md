# Bounded automatic recovery

An exhausted three-round attempt is preserved as failed. For an explicitly
opted-in objective, the supervising agent next investigates the obstacle and
obtains independent review of a concrete recovery plan. An accepted plan permits
another attempt within the original contract; it never turns failed code into
approved code. No routine user approval is needed for these transitions.

## Authority and accounting

Recovery manifests contain exactly one issue and one frozen chunk. Their stable
objective identity is registered in the repository's shared Git directory.
Changing the manifest ID, state path, worktree or chunk name cannot replenish
the allowance for the same issue. Other authorized objectives run independently.
Sequential research and repair subtasks consume their parent objective's budget;
they are not separately initialized objectives.

The shared Git registry holds the canonical ledger. The state file under the
worktree is an exported cache: editing or deleting it does not reset the run.
Re-running initialization restores a missing cache. CLI transitions serialize
through a repository-wide lock and atomically save the canonical record before
the cache. Back up the shared registry as well as review transcripts; this is
local coordination, not protection against an operator deleting Git metadata.

Defaults are two recovery episodes, nine total allocated implementation-review
rounds, two plan submissions per episode, and 604800 seconds of elapsed time.
The manifest may configure finite limits. The attempt cap remains at most three.
Reserve rounds before dispatch: empty and partial panels cost a slot, and
retrying a missing role on the same commit does not discard returned findings.
Check remaining time before dispatch and cap worker duration accordingly.
Budget exhaustion parks this objective; continue other authorized work.

Scope, acceptance requirements, reviewer roles, failed messages and historical
allocations survive every successor. A changed strategy may repair the same
files, but cannot authorize additional scope. A renamed task or a promise to
try harder is insufficient evidence for recovery.

Provider permissions remain separately controlled by the manifest. Publication
requires the full current panel on the exact commit, evidence addressing every
inherited finding, and existing provider checks. Research approval, a local test
pass, or an old passing commit is not publication authority. Local ledgers
provide durable coordination, not cryptographic reviewer attestation.

## Repair after a passed review

Ordinary protected-base revalidation and CI-driven code repair are different
transitions. Revalidation is free only when a passing reviewed change is carried
across protected-base movement without changing its reviewed content. A code
change after a passed ledger must use the original ledger's ordinary review
budget; it cannot be described as revalidation.

The controller admits a CI repair only from a single open, non-draft PR on the
planned `agent/<slug>` branch. The PR's full head SHA must equal the current
source ref. The failed check must report that same SHA and be required by both
the frozen manifest and freshly read branch protection. Check-run/status name,
SHA and provider identity are recorded when available. After fetching the
evidence, the controller rereads matching PRs, PR details, source and base refs,
and branch protection. Any missing, ambiguous, optional, stale, pending,
cancelled or changed evidence rejects admission before ledger bytes are
modified.

Admission appends an event to `ci_failure_repairs` on the same ledger and
reserves the next ordinary review round. Candidate commits must descend from
the failed PR head and change only frozen chunk files. A successful rerun on
the same head creates no event; another failure can be admitted only after a
repair has passed and the later failing check is on the then-current head. If
the original round cap has no slot left, the controller records
`cap_exhausted` and terminal `repair_exhausted` in that same ledger. Ledger
initialization scans nested `.loop-runs` state by issue, slug and chunk identity,
and rejects state-directory overrides outside that root, preventing a renamed
or relocated ledger from restarting the allowance. A ledger created before
this protocol must be upgraded once by rerunning `ledger init`; the migration
adds only missing protocol metadata and retains all prior rounds.

All shipping and issue-closure actions consult the same ledger and reject
pending, exhausted or mismatched repair state. A first draft PR remains possible
before any repair is recorded. Once repair is recorded, push remains bound to
the existing open PR and verifies the remote source head is an ancestor of the
exact reviewed commit; the controller cannot create a replacement PR for that
repair. A passing repair still requires green current required checks on the
exact live PR head before merge. For the operator command and provider-evidence
procedure, see `.claude/loop-specs/README.md`.

## Configuration and commands

The optional manifest section is:

```yaml
recovery:
  objective_id: <stable-objective-name>
  implementer: <implementation-agent-identity>
  max_episodes: 2
  max_total_rounds: 9
  max_plan_submissions: 2
  max_elapsed_seconds: 604800
  history:
    - path: <path-to-original-terminal-ledger>
      sha256: <sha256-of-exact-file-bytes>
```

Use an empty history list only for an objective with no prior attempts. Supply
the complete known historical inventory on adoption, preserving original files.
Digest mismatches and unreadable history fail closed; prior allocated rounds
count before recovery admission. The controller cannot discover omitted private
transcripts, so the supervisor must inventory them rather than assume a new
session is a fresh objective. Explicit legacy manifests retain their recorded
caps and behavior until deliberately adopted under this policy.

In each fresh worktree, install the pinned controller dependencies first:

```bash
python3 -m venv .loop-tools
.loop-tools/bin/python -m pip install -r scripts/requirements-loop.txt
```

Validate and run the read-only preflight before initializing the ledger. Use
`.loop-tools/bin/python` for each recovery command:

```text
.loop-tools/bin/python scripts/loop_engine.py recovery next --ledger <ledger>
.loop-tools/bin/python scripts/loop_engine.py recovery start-round --ledger <ledger> --commit <full-sha>
.loop-tools/bin/python scripts/loop_engine.py recovery submit-plan --ledger <ledger> --file <plan.json>
.loop-tools/bin/python scripts/loop_engine.py recovery review-plan --ledger <ledger> --file <review.json>
.loop-tools/bin/python scripts/loop_engine.py recovery resume --ledger <ledger>
.loop-tools/bin/python scripts/loop_engine.py recovery exhaust --ledger <ledger> --reason "<obstacle>"
```

Execute the next applicable command, not this list unconditionally.
`exhaust` abandons the current attempt, retaining even partial allocations.
The supervising agent polls `next`, dispatches the researcher, dispatches the
independent recovery reviewer, consumes their exact files, and continues.
The CLI persists transitions and next actions; it is not a daemon and does not
dispatch agents itself. A model or session handoff must resume this supervisor.

`next` returns `implement` or `revise` for source work, `review` with missing
roles for an allocated panel, `adjudicate` for a complete panel, `investigate`
for research, `review_plan` for independent research review, `resume` for an
accepted plan, `publish` for the guarded provider workflow, or `park` when this
objective must stop. Read its remaining time before dispatching each worker.

## Research and independent acceptance

The researcher receives the original contract, complete failed reviews,
remaining allowance and stored `recovery.contract_digest`. The `next` response
supplies the findings and contract digest, and the plan digest when a plan is
awaiting review; `ledger show` exposes the full stored state. Its JSON plan has:

- `author`: researcher identity; the implementer may perform this research.
- `cause`: failure classification.
- `diagnosis`: why the previous method failed.
- `evidence`: nonempty list of concrete reproduction or research evidence.
- `strategy`: a substantive changed method within the frozen contract.
- `checks`: nonempty list of verification obligations.
- `finding_ids`: every inherited finding ID.
- `contract_digest`: the exact stored contract digest.

Dispatch a recovery reviewer distinct from both researcher and implementer.
That reviewer checks reproduction evidence, preserved obligations and whether
the new method addresses the failure. Their JSON has `reviewer`,
`plan_digest` (the exact submitted plan's digest), `verdict` (`ready` or
`needs_changes`) and nonempty `assessment`. A rejection consumes the same
episode's plan-submission allowance; submitting a renamed plan does not reset it.
Only `ready` for the exact plan permits `resume`.

Every successor still gets mathematical/source, repository-boundary,
abstraction and mathlib/style review independently on the same commit.
Each passing reviewer supplies `--resolutions-file <json>` to
`ledger record-review`: a JSON object mapping every inherited finding ID to
nonempty resolution evidence. Each negative review message and each inherited
lift obligation is retained as an indivisible finding; addressing only one
criticism in it is insufficient. A fresh lift in the current passing panel
uses the committed backlog gate, not a retrospective resolution demanded of earlier
reviewers who could not yet see it. Failed or abandoned panels carry their lifts
into subsequent research and review. Every current or carried lift must have a
durable backlog entry before passing adjudication/publication; implementation
evidence can be recorded there rather than deleting its provenance. Previously
requested lift prefixes stay usable only within the current manifest's original
declared authority. Imported history grants no additional scope.
The controller verifies structure and binding; reviewers judge substance.

The backlog gate reads `docs/architecture/generalization-backlog.md` from the
exact candidate/reviewed commit's ordinary file blob, at both passing
adjudication and publication. It rejects missing commits/files and symlinks;
there is no HEAD or working-tree fallback. Push, PR creation and later provider
actions accept the exact reviewed commit, or a head that carries the same
change against the base branch tip GitHub reports (a clean rebase, or a merge
of the base into the branch) when the base left the reviewed files, their
direct imports and the pins alone. A head whose change differs needs a new round, and PR creation still
requires a clean checkout. A passing recovery attempt stays terminal; the
revalidation round that reopens an ordinary passed ledger does not apply to
recovery objectives.

A recovery disposition is a complete visible row outside code fences, with
nonempty `chunk`, `reviewing commit`, `found by`, `proposed ancestor`,
`weaker hypotheses`, and `state` fields. Its `proposed ancestor` value must
exactly equal the canonical repository-relative lift target; one enclosing
pair of backticks is permitted. Prefixes, namespace descriptions, incidental
prose and fenced schema examples do not match. State is `UNVERIFIED`,
`CONFIRMED <evidence>`, or `FALSIFIED <counterexample>`, with nonempty evidence
after the latter two. For example:

```text
### 2026-09-22 — example lift
- chunk: example-chunk
- reviewing commit: <commit where the finding was observed>
- found by: abstraction-adversary
- proposed ancestor: DerivedAlgGeo/CategoryTheory/Example.lean
- weaker hypotheses: the concrete weakening proposed by the reviewer
- state: UNVERIFIED
```

The observation commit precedes the commit containing a newly added row; do
not claim its self-referential final SHA was known while writing it. Existing
legacy rows remain historical records, but a descriptive namespace value does
not automatically satisfy a path-specific recovery disposition. The legacy
non-recovery checker retains its existing behavior.

Reserve the backlog path in the original frozen file list if the objective may
need to add rows. A lift finding grants no implicit permission to edit it.
If a new lift is discovered after freezing and no valid row already exists in
that commit, preserve the reviews and record `needs_changes` (or abandon the
incomplete panel). Append the row within authorized scope, commit, and allocate
another full panel on the new SHA. That allocation counts toward both caps;
use automatic research recovery if the attempt is exhausted. Do not rewrite a
review, change its SHA, or publish an unreviewed backlog append. Pre-freeze
advisors and existing committed rows can avoid that extra source revision.

Recovery review text ends with exactly:

```text
Reviewed commit: <full 40-character commit SHA>
Close: <TOKEN>
```

Use the review role's applicable verdict token, without counts, suffixes or
text after the trailer. Counts and explanations belong before it. Preserve the
reviewer's actual message; the supervisor must not rewrite a verdict or invent
resolution evidence.

PR creation checks the remote branch before creating and verifies the returned
PR afterward. GitHub creates by branch name rather than an atomic expected-SHA
condition: a concurrent update can still create an incorrectly bound PR. The
controller reports that PR's URL and fails closed for further publication;
approval, merge and closure independently recheck the reviewed head.

Recovery backlog rows use a plain-Markdown schema. Code fences, HTML comments
and balanced single-line inline code are inert for HTML detection (including
the canonical legend's inline-code placeholders). Other raw HTML tag-like
syntax, declarations and processing instructions make the document ineligible
as recovery evidence. This deliberately fails closed rather than
guessing whether a generic container, attribute or CSS rule hides a row.
Use ordinary Markdown for the backlog; quote HTML examples in inline code or
code fences rather than raw containers. Inline-code recognition is limited to
matched, unescaped opening backtick runs on one line; ambiguous input fails closed.

## Provenance observations

During implementation, active `CONTRIBUTING.md`, `openspec/config.yaml` and
the run-loop skill still instructed five rounds, while `AGENTS.md` and
`CLAUDE.md` said three. The skill also called a missing review's round void.
Those instructions could replenish retries or send two supervisors down
different policies. Active new-work guidance now agrees on three-round
attempts and charged partial panels. Historical OpenSpec designs and explicit
legacy manifests retain their original record.

Record further unclear documentation, stale assumptions and failed probes in
the active change's observation log with the actual evidence and consequence.
Do not infer live issue, PR, CI or publication state from a prior session's prose.
