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
| `references/mathlib-style.md` | The Mathlib conventions this repo holds itself to, and the deltas it keeps on purpose. The spec `agents/mathlib-reviewer.md` enforces. |
| `agents/` | Repo-local agent specifications. One per file. |
| `skills/` | Repo-local skills, one directory each. `run-loop` works issues or a milestone to merged PRs; `formalize-issue` and `land-pr` are single iterations, not for loop runs. |
| `settings.json` | Hooks. Currently: the Mathlib-convention check on every Lean edit. |

Repository-specific reviewers and the loop protocol live in `.claude/agents/`
and `.claude/skills/`. Codex registers repository skills only from
`.agents/skills/`, so
`.agents/skills/run-loop` is a symlink to `skills/run-loop`: one file, visible
to both runtimes. Codex lists a symlinked skill directory but ignores a
symlinked `SKILL.md` (checked with `codex debug prompt-input`), so keep the link
on the directory.

## Loop runs

A loop run follows `skills/run-loop/SKILL.md`:
- it takes GitHub issues or a milestone, researches each issue, and writes its
  plan into the PR description;
- it merges once the four reviewers in `agents/` pass on the same commit and the
  required CI is green;
- the PR description is its record. There is no manifest, ledger or controller
  on the run path.

The manifest controller that preceded the run-loop skill, its manifests and
its OpenSpec change records have been deleted; git history keeps them.

`scripts/loop_tokens.py` is the cost side of the same run. It reconstructs
token totals from the Claude Code and Codex transcripts after the fact, so
neither runtime has to be instrumented in advance, and attributes them to the
frozen chunks recorded in a local `.loop-runs/` ledger when one exists. It
reads those ledgers and never writes to them.

`scripts/loop_transcripts.py` is the behaviour side. `sync` copies every Codex
and Claude Code transcript that touches this repository -- from every Codex
home, archived threads included -- into a local archive outside the working
tree (`~/.loop-runs/transcripts`), groups each root thread with its subagents
into a run, and writes a digest per run: the owner's messages, every point the
run stopped and what it said, the questions it asked, the idle time, and where
its tool calls went. `list`, `stops`, `profile` and `show` read the archive
back after the runtimes have deleted the originals. The archive holds raw
transcripts, so it never belongs in this repository. Loop runs do not need it;
it exists to find out why they stop.

## Review evidence and evaluation

`scripts/check_review_evidence.py docs --base <SHA>` checks required sections
only in new or changed primary module docstrings, preserving existing debt;
new modules with commands also need a primary docstring. Import-only umbrellas
and mid-file section notes do not need the full module template. `inventory`
with `--draft scratch/pr-N.md` reports every inline reference occurrence in
all docstrings in changed Lean modules, changed Markdown sections and the complete draft; `probe`
with `--output scratch/ReferenceChecks.lean --run` checks all declaration tokens
at root scope. Put justified non-declaration classifications in the draft's
`## Reference classifications` table (`Token | Kind | Reason`). Paths are
classified automatically; reviewers still inspect their meaning. Generated
probes stay untracked; durable probes use Development and its sweep route.

`scripts/check_emission_coverage.py --source-only` uses the pinned Lean header
parser to check every tracked obligation against both sweep reachability and
emitter root filters, without certifying axioms or replacing CI emission.

`scripts/review_dispatch.py prepare` emits Codex tool arguments for a fresh,
explicitly selected frontier reviewer on an immutable diff. `verdict` validates
the trailer, commit, and mathematics evidence shape; it does not certify the
mathematics. Claude's Agent/Task pre-tool hook enforces fresh reviewers and
explicit model selection. Codex has no repository hook for collaboration:
submit generated arguments unchanged and examine the archived actual dispatch
metadata. Generated task names start `review_<role with underscores>_` so the
archive can recognize reviewer dispatches. The digest reports requested settings separately from resolved model
and effort; unavailable fields remain unavailable.

`scripts/review_evaluation.py prompt <case> --worktree <path>` emits a synthetic
challenge without answers. Prompts require the pinned Mathlib and each source's content
fingerprint; a changed source makes the case unavailable until re-adjudication.
Dispatch the emitted plaintext, which uses opaque labels; keep descriptive case
ids and the command used to select the case outside the reviewer's context.
A separate reviewer adjudicates each report into a local JSON list with `case`
and `findings`; each finding has `id`, `severity`,
`evidence`, `evidence_supported` (boolean), and an `adjudication` reason. `score
<assessments.json>` reports recall, unsupported findings, severity errors,
recurrence on repaired controls and evidence support. Unassessed cases and
undefined rates are explicit. Keep reports and assessments in ignored scratch
or the owner-only archive; never commit actual archived transcripts. The
fixture's expected ids are for adjudicators, not the reviewer taking the test.

Transcript merge counts require observed GitHub state (`number`, `url`, `state`,
`mergedAt`), not successful auto-merge arming or disarming. Existing archives are
reparsed on the next `sync`; absent output evidence is unknown, not a merge.

## Reading order for an agent picking this up cold

For public API ownership and structural moves, `AGENTS.md` points to the
versioned [mathematical ownership policy](../docs/architecture/mathematical-ownership.md)
and [placement procedure](../docs/architecture/placement.md). Read those before
using a dated note or issue path as a placement rule. The cutover ledger
distinguishes existing source from proposed destinations.

1. `AGENTS.md` (the working rules, which `CLAUDE.md` imports — they are load-bearing and override defaults)
2. `decisions/` in numeric order (~10 min, and it is the whole design)

## Dates in this directory are UTC

Everything under `.claude/` is dated **UTC**. The rest of the repo —
`formalization.yaml` and git commits — is dated
**local (America/New_York)**. So an ADR reading `2026-08-04` and a trust-record
field reading `2026-08-03` can describe the same evening. Do not "fix" one to
match the other.

## Where the issues live

All active work for this library is tracked in
[`chris-dare-dev/derived-alg-geo-lean`](https://github.com/chris-dare-dev/derived-alg-geo-lean/issues).
Cross-repository items say so explicitly and link their owning repository.
ADR-0006 records the historical localization and migration decision.
