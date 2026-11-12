# ADR-0005 — Seven axes, four values, no aggregate token

- **Status:** accepted
- **Date:** 2026-08-04
- **Deciders:** Chris Dare
- **Evidence:** `arXMCP/CLAUDE.md` §4.9; this repo's `CLAUDE.md` §2, §3;
  https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/notes/2026-08-04-contract-red-team.md gaps 7, 8

## Context

Two rules, one in each repo, are the same rule seen from two sides.

This repo's `CLAUDE.md` §2 forbids `sorry` outright, because a sorry-backed
declaration *"typechecks, gets imported, and silently launders an unproved claim
into everything downstream."*

arXMCP's `CLAUDE.md` §4.9 forbids any bare "verified": *"No tool response
carries a single 'verified'-style status that collapses distinct trust questions
into one token… no axis is inferred from another."*

Both are about the same failure: a single green token standing in for a
conjunction of unrelated facts, read by something that will not check the
conjuncts. §4.9 also records that enforcement is *"by-reference discipline (no CI
linter or schema validator this track)"* — i.e. it is currently a review habit.

## Decision

**Seven axes. Four values: `pass` / `fail` / `not_run` / `not_applicable`. No
aggregate field, at any level, ever.**

Enforced mechanically, not by habit: every contract schema is JSON Schema
2020-12 with **`additionalProperties: false`**, and no schema defines a property
named `status`, `verified`, `ok`, `passed`, `trusted`, or `result` — checked by
`mfc lint-schemas` with a rejection fixture (`testdata/invalid/aggregate-status`).
That is what turns §4.9 from a review habit into a machine constraint, and it is
the single best idea the design produced.

Supporting rules:

- **Every axis carries `self_attested: bool`** and an `env_digest`.
- **`not_applicable` is first-class** (ADR-0003): a foreign environment yields it,
  never a pass and never a fail.
- **Every record carries a `caveats[]` block generated mechanically** from the
  axis values. A consumer that reads only `caveats[]` is not misled.
- **`relation` is always spelled `relation_claimed`** in machine artifacts. It
  becomes `relation_confirmed` only inside a dated, named human review. That
  naming is the schema-level defence against an LLM reading six greens as
  "verified."
- **Two axes are distinct only if they have distinct evidence-producing
  programs.** This test killed a competing design's three axes
  (`sorry_free` ⊂ `axioms_within_allowlist` ⊂ `no_local_axiom`) that were three
  views of one closure computed by one program — four greens describing two facts.

## Consequences

**The human axis is the bottleneck, and it is the only one that catches the
thing this repo most fears.** `faithfulness` is human-only. It is the sole axis
that can catch `CLAUDE.md` §3's failure — describing `Fin 2 → ℤ` as
`K_num(Ku(X))`. R5 budgets ~2 owner-days for 5–10 reviews against a notebook of
146 papers and 15,280 chunks. Everything else here scales; this does not. See
[`open-questions.md`](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/open-questions.md) Q4.

**§3 is not yet mechanized, and the design overclaimed that it was** (red team,
gap 8). `closed_lanes` checks `forbidden_module_prefixes` against the emission.
That catches §4's hazard — *importing* geometry. It does nothing about §3's
hazard — *claiming* geometry you do not have. `abbrev NumLattice : Type := Fin 2 → ℤ`
imports nothing forbidden, and a doc-comment calling it a Kuznetsov component
passes every check in the design. Two fixes, both required:

1. Invert to an **import allowlist** (`permitted_module_prefixes`) checked
   against `.ilean` `directImports` — bounded, mechanical, and it catches Mathlib
   modules the denylist author never heard of.
2. Add per-topic **`forbidden_vocabulary[]`** (`"Kuznetsov"`, `"Enriques"`,
   `"D^b(Coh"`, `"Chern"`) linted against **declaration names and doc-comments**
   of any declaration whose `frontier` is non-empty. That is §3, mechanized, and
   it generalizes: every low-coverage topic has a list of words its interfaces
   must not claim.

**Axis 6 is human assertion wearing a computed axis's clothes** (red team, gap
7). `frontier[].discharged_by` is hand-edited YAML that `mfc` only aggregates —
nothing checks the named discharger proves anything, and unlike the review axis
it carries no reviewer and no date. Fix: require `discharged_by` to name a
declaration that exists in the emission **and** carries `@[discharges "<id>"]`,
anchoring the edge in `Environment.constants` rather than in prose. Otherwise
label its evidence `asserted` and fold it under the review axis's discipline.

**`faithfulness: agent_drafted` was deliberately rejected** — it would let an LLM
verdict occupy the one human axis. The red team accepts that and points out the
consequence: rejecting it *without a substitute* makes volume unreachable by any
route. The substitute is a separate `kind: sketch` lane that occupies **zero**
axes and is excluded from `required_axes` filtering. See [`open-questions.md`](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/open-questions.md) Q4.
