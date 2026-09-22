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

Validate and run the read-only preflight before initializing the ledger. Then:

```text
python3 scripts/loop_engine.py recovery next --ledger <ledger>
python3 scripts/loop_engine.py recovery start-round --ledger <ledger> --commit <full-sha>
python3 scripts/loop_engine.py recovery submit-plan --ledger <ledger> --file <plan.json>
python3 scripts/loop_engine.py recovery review-plan --ledger <ledger> --file <review.json>
python3 scripts/loop_engine.py recovery resume --ledger <ledger>
python3 scripts/loop_engine.py recovery exhaust --ledger <ledger> --reason "<obstacle>"
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
nonempty resolution evidence. Each negative review message is retained as an
indivisible finding; addressing only one criticism in it is insufficient.
The controller verifies structure and binding; reviewers judge substance.

Recovery review text ends with exactly:

```text
Reviewed commit: <full 40-character commit SHA>
Close: <TOKEN>
```

Use the review role's applicable verdict token, without counts, suffixes or
text after the trailer. Counts and explanations belong before it. Preserve the
reviewer's actual message; the supervisor must not rewrite a verdict or invent
resolution evidence.

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
