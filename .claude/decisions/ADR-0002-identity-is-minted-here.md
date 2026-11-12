# ADR-0002 — Identity is minted in the topic repo, never by arXMCP

- **Status:** accepted
- **Date:** 2026-08-04
- **Deciders:** Chris Dare
- **Evidence:** https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/notes/2026-08-04-arxmcp-lean-integration-audit.md §4 (the
  identifier-durability finding); https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/notes/2026-08-04-contract-red-team.md
  gaps 1, 3, 11

## Context

For a Lean declaration to say *"this formalizes that statement in that paper"*,
something must name the statement durably. The audit's central finding is that
**no such identifier exists in arXMCP today, and none of its candidates can be
made into one.**

- `chunk_id` **is** a real content hash —
  `arxiv:<paper_id>:<sha256(preamble_text + NFC(body_text))[:16]>`
  (`ingest/chunker.py:1277-1301`), with determinism tests. But rotation is a
  routine first-party operation: the Makefile's own help for
  `ingest-recover-preambles` reads *"NOTE: triggers chunk_id rotation."*
- There is **no alias table** — no `previous_chunk_id` column anywhere in the
  26-column `CHUNKS_SCHEMA_V1`.
- Rotation **doubles rather than fails**: `merge_insert` has
  `when_matched_update_all` + `when_not_matched_insert_all` and **no delete arm**
  (`ingest/store.py:907-911`), so stale rows stay addressable.
- `chunk_id` is namespace-ambiguous: `equation_id` uses the identical
  `arxiv:<id>:<16hex>` shape and passes `is_valid_chunk_id`.
- `corpus_version` is the LanceDB MVCC integer, not a content commitment; a
  restore-from-backup presents a **lower** version over different bytes.
- `source_span` — the designed durable anchor, which `ingest/schema.py:240-250`
  itself calls "the authoritative resolving key" — is **NULL on 15280/15280 rows**.
- Statements are not first-class objects. `server/proof_linkage.py:19-20` states
  verbatim: *"No column of `CHUNKS_SCHEMA_V1` records document position."*

## Decision

**A citation key contains zero corpus-derived bytes.**

```
key         = "stmt:" registry-id ":" local-label
registry-id = [0-9a-f]{12}          ; minted once by `mfc registry init`
local-label = ^[a-z][a-z0-9._-]{0,63}$
```

Example: `stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2`.

Three sub-decisions, each of which was contested:

**1. The paper coordinate is a set of typed fields, not key segments.**
`scheme` / `id` / `version` / `printed_number` / `locator` live as
schema-validated fields of the registry entry. Three of the four candidate
designs packed `arxiv:<id>v<n>` into a colon-positional key; that survives
`math/0212237` only by luck (no colon in the id) and fails outright on
`textbook:<slug>`, which arXMCP already ships (`ingest/identifiers.py`, live
notebooks `bridgeland-stability-pdfs` and `fourier-duality-pdfs`). Typed fields
also let `version` be `required` when `scheme == arxiv` and absent otherwise.

**2. `registry-id`, not the notebook slug.** Notebook slugs are
`^[a-z][a-z0-9-]{2,30}$` rows in a machine-local, unauthenticated SQLite DB with
no global registry. Two adopters both minting `number-theory` collide. A 12-hex
minted once and checked into git is unique in practice, and a collision is
detectable and fixable.

**3. arXMCP answers exactly one question, and its answer is a file.**
*Does this registry entry's quote still appear in the corpus, and where?*
`tools/statement_resolve.py` — offline, read-only, generic — writes
`resolution.json`, which is committed into **this** repo. arXMCP never issues
identity, and its answer never travels over a socket (ADR-0001).

Drift detection runs the other way from citation: the registry carries a
verbatim `quote` plus `quote_sha256` under a named normalization
(`nfc-ws-collapse/1`), and the resolver matches on the hash.

## Consequences

**It survives what rotates.** No re-ingest, chunker bump, ar5iv re-render,
LaTeXML upgrade, or HTML→MinerU migration can invalidate a string they never
contributed to.

**It deliberately does not survive an arXiv version bump.** `math/0212237v1` §8
Lemma 8.2 and `v2` §8 Lemma 8.2 are different statements if the author
renumbered or edited. A version bump means a **new key** with `supersedes`
pointing at the old one. The old key stays valid forever and keeps its quote.

**The quote guarantee is narrower than first claimed** (red team, gap 11).
`quote_sha256` survives *preamble-class* rotation, which changes `preamble_text`
and leaves `body_text` alone. A **chunker bump changes chunk boundaries**, which
changes `body_text`, which changes the hash exactly as it changes `chunk_id`.
The fix, required before v1: split `quote_as_minted` (byte-equal to the chunk,
hashed, machine-owned) from `quote_as_read` (human-corrected, displayed, not
hashed), and add a `quote_containment` rung to the resolution ladder — that is
what actually survives a merge or split.

**Minting is human labor and does not scale past the low tens of entries.**
This is the design's load-bearing limit; see ADR-0005 and [`open-questions.md`](https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/open-questions.md) Q4.

**Minting tooling belongs in arXMCP, not `mfc`** (red team, gap 3). `mfc`'s
declared deps (`jsonschema`, `pyyaml`, `copier`) can reach neither LanceDB nor a
loopback server, and `--printed-number` needs a lookup that does not exist —
audit §4: *"No tool accepts `printed_number` as an input."* So minting ships as
`arXMCP/tools/statement_mint.py`, offline and read-only, emitting a candidate
YAML fragment a human pastes into `registry/`.
