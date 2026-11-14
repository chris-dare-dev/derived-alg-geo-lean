# Credo

What this repository holds and what it refuses. Where another file here
disagrees, this one wins.

**MUST**: a change that breaks it does not merge. **SHOULD**: depart from it
only with the reason stated in the pull request.

## 1. The tree holds what a person wrote and would read

- You MUST NOT commit anything a command can regenerate: build output,
  rendered or captured data, run state, logs, measurements, screenshots,
  per-declaration or per-file listings.
- You MUST NOT commit the record of how a change was made: plans, research
  briefs, critiques, reviews, handoffs, transcripts, agent memory. That record
  is the issue, the pull request and the wiki.
- Prose in the tree is limited to the files listed under "In this repository".
- Agent instruction files hold rules, not history. They SHOULD stay under 200
  lines and point here instead of repeating this file.

## 2. A change costs what it touches

- A change that touches neither the product nor a check that judges it MUST
  NOT start a product build.
- Documentation SHOULD travel with the code change it describes. A pull
  request that edits only prose is a sign the prose belongs in the wiki.

## 3. Every check earns its place

- A check MUST state, where it is defined, the one invariant it guards.
- A check that is kept MUST run in CI on every change it can judge. One that
  runs only on a workstation is not a check.
- You MUST NOT add a check whose input is another check's output: evidence,
  receipts, attestations that a run happened.
- Scripts that support the build MUST NOT grow fixtures, golden files or a
  test suite of their own. A script that needs those is a product and lives in
  its own repository.
- An exceptions list (baseline, allowlist, nolint) only shrinks.

## 4. Names and comments say what the thing is

- Identifiers, file names and comments MUST NOT carry issue, pull-request,
  milestone or decision-record numbers, dates, or the names of agents and
  tools. Provenance goes in the commit message.
- A comment explains why the code is the way it is. It does not narrate what
  was tried, what it replaced, or which review asked for it.
- Names SHOULD stay under 60 characters. A longer one means the statement
  wants splitting or an intermediate definition wants a name.

## 5. Changes are small enough to read

- A change SHOULD stay under 400 authored lines and one concern. Larger work
  is split, or starts with a one-paragraph design in its issue.
- A person reads every line before merge. "I do not understand this yet"
  blocks the merge.

## 6. Health is a trend, not a volume

- Progress is not measured in commits, pull requests or lines added.
- The measures are: product share of lines, share of changes that touch the
  product, median change size, size of the exceptions lists, open issues.
  They are computed on demand and never committed.

## In this repository

| | |
|---|---|
| Product | `DerivedAlgGeo/`, `DerivedAlgGeo.lean`, `exe/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` |
| Authored records | `registry/`, `formalization.yaml`, `attest/review.yaml`, `pins.json` |
| Prose allowed in the tree | `README.md`, `CONTRIBUTING.md`, `CREDO.md`, `AGENTS.md`, `CLAUDE.md`, `LICENSE.md`, module docstrings; under `.claude/`, what agents run on: skills, agent definitions, settings |
| Wiki | architecture, placement rules, decision records, roadmap, CI notes |
| Issue or pull request | reviews, handoffs, loop specifications, change proposals |
| Never committed | loop run state, review evidence, publication receipts, hand-kept `#print axioms` lists |

Lean rules:

- The library has no `sorry`, no `admit` and no added axiom.
- Names follow Mathlib's naming conventions. A source is cited in the
  docstring ("Proposition 3.15 of arXiv:1902.08184"), never in the name.
- A theorem that depends on an input the library does not prove takes that
  input as an explicit hypothesis. A structure that packages such inputs ends
  in `Hypotheses`. `Data` is for structures the library constructs at least
  once.
- The axiom audit is produced from the compiled environment by one program.
  No file lists declarations by hand.
- `set_option maxHeartbeats` applies to one declaration with `in`, with a
  comment saying what is slow.

## Not yet met

The repository does not meet these yet. A line is deleted when it becomes
true. Until then the older rule in `AGENTS.md` or `CONTRIBUTING.md` applies to
what that line names and to nothing else.

- `docs/`, `.claude/decisions/` and `.claude/roadmap/` are in the tree, and
  `AGENTS.md`, `scripts/check_layering.py` and `scripts/check_roadmap.py`
  read them (§1).
- `AGENTS.md` is over 200 lines: its subject-ownership rules leave with
  `docs/` for the wiki (§1).
- `scripts/` holds loop, evidence and receipt tooling with its own fixtures
  and tests (§3).
- Some names pass 60 characters (§4).
- Structures that package unproved inputs are named `Data` (Lean rules).
