# `.claude/` — repository decisions and roadmaps

This directory records why the repository and its formalization tracks are
shaped the way they are. It is not user documentation; `README.md` and
`CONTRIBUTING.md` cover that. Everything here is a decision, a roadmap, or the
evidence behind one.

## Layout

| Path | What it is |
|---|---|
| `decisions/ADR-*.md` | One architectural decision each. Status is `accepted`, `open`, or `superseded`. An `open` ADR names the person who must decide and what changes either way. |
| `roadmap/*.yaml` | Track registries for milestones, epics, and their GitHub numbers. |
| `notes/2026-08-04-*.md` | The four artifacts the 2026-08-04 workflows produced, verbatim. Dated because they are snapshots, not living docs. |
| `open-questions.md` | The decisions blocking work, each with a GitHub issue. |
| `references/mathlib-style.md` | The Mathlib conventions this repo holds itself to, and the deltas it keeps on purpose. The spec `agents/mathlib-reviewer.md` enforces. |
| `agents/` | Repo-local agent specifications. One per file. |
| `skills/` | Repo-local skills, one directory each. `run-loop` works issues or a milestone to merged PRs; `formalize-issue` and `land-pr` are single iterations. |
| `loop-specs/` | Manifests of the retired loop controller. Runs no longer write them; they are kept for the ledgers they produced. |
| `settings.json` | Hooks. Currently: the Mathlib-convention check on every Lean edit. |

OpenSpec's generated Codex skills live in `.agents/skills/` and are refreshed by
`openspec update`; do not hand-edit those generated files. Repository-specific
reviewers and the loop protocol live in `.claude/agents/` and `.claude/skills/`.

## Loop runs and OpenSpec

A loop run follows `skills/run-loop/SKILL.md`:
- it takes GitHub issues or a milestone, researches each issue, and writes its
  plan into the PR description;
- it merges once the four reviewers in `agents/` pass on the same commit and the
  required CI is green;
- the PR description is its record. There is no manifest, ledger or controller
  on the run path.

OpenSpec lives in `openspec/`, with its generated skills in `.agents/skills/`.
It remains available for interactive design work; a run does not use it.

`scripts/loop_engine.py` and the manifests in `loop-specs/` are the retired
manifest controller. It kept a digest-bound review ledger under the ignored
`.loop-runs/` directory and gated every provider action on it. Runs no longer
use it. It is kept, with `docs/architecture/loop-recovery.md`, for the ledgers it
already wrote.

`scripts/loop_tokens.py` is the cost side of the same run. It reconstructs
token totals from the Claude Code and Codex transcripts after the fact, so
neither runtime has to be instrumented in advance, and attributes them to the
frozen chunks recorded in `.loop-runs/`. It reads those ledgers and never
writes to them.

## The artifacts in `notes/`

Produced 2026-08-04 by two multi-agent workflows (34 agents, ~4.2M tokens).
Every claim in the audit was adversarially re-verified against source by a
second agent instructed to default to REFUTED when it could not confirm.

- **`2026-08-04-arxmcp-lean-integration-audit.md`** — what arXMCP and this repo
  actually are today. Eight areas surveyed, each independently re-verified.
- **`2026-08-04-contract-architecture.md`** — the recommended architecture. Four
  designs competed; this is the winner with the runners-up's best ideas grafted in.
- **`2026-08-04-contract-schemas.md`** — the seven contract artifacts as
  copy-pasteable schemas, with a worked end-to-end trace.
- **`2026-08-04-contract-red-team.md`** — 18 ranked gaps in the above. Read this
  before implementing anything in the architecture doc.

### Reading order for an agent picking this up cold

For public API ownership and structural moves, `CLAUDE.md` points to the
versioned [mathematical ownership policy](../docs/architecture/mathematical-ownership.md)
and [placement procedure](../docs/architecture/placement.md). Read those before
using a dated note or issue path as a placement rule. The cutover ledger
distinguishes existing source from proposed destinations.

1. `CLAUDE.md` (the working rules — they are load-bearing and override defaults)
2. `decisions/` in numeric order (~10 min, and it is the whole design)
3. `notes/2026-08-04-contract-red-team.md` (what is wrong with the design)
4. Only then the architecture and schema docs, which are long.

## Dates in this directory are UTC

Everything under `.claude/` is dated **UTC**. The rest of the repo —
`formalization.yaml`, git commits, `notes/` at the top level — is dated
**local (America/New_York)**. So an ADR reading `2026-08-04` and a trust-record
field reading `2026-08-03` can describe the same evening. Do not "fix" one to
match the other.

## Line numbers in `notes/` are snapshots

The audit's citations into **this** repo are valid at commit `fb47a38` only —
the repo moved three times during the audit, and has moved further since
(`SlicingAction`, `PreStabilityAction`, and `ShiftAnalysis` did not exist when
the audit ran, so its "lane-1 step 3 NOT FOUND as code" finding is stale).
Citations into arXMCP are valid at that repo's `3a7d626`.

Do not treat a line number here as current. Re-open the file.

## Where the issues live

All active work for this library is tracked in
[`chris-dare-dev/derived-alg-geo-lean`](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues).
Cross-repository items say so explicitly and link their owning repository.
ADR-0006 records the historical localization and migration decision.
