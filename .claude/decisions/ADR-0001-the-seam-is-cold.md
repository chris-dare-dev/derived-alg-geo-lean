# ADR-0001 — The seam is cold: files, not runtime calls

- **Status:** accepted
- **Date:** 2026-08-04
- **Deciders:** Chris Dare
- **Evidence:** https://github.com/chris-dare-dev/derived-alg-geo-lean/blob/965d62fc66afbbe998482ef0912cacc265a01c5a/.claude/notes/2026-08-04-arxmcp-lean-integration-audit.md §2, §6

## Context

arXMCP and this repo need a contract. The obvious shape is a runtime one: this
repo's CI calls arXMCP, or arXMCP's `lean_verify` checks this repo's
declarations. The audit measured what that would actually inherit:

- arXMCP binds `127.0.0.1:7733` and ships **no authentication of any kind**
  (`SECURITY.md:8`), alongside a 17-route unauthenticated `/ui/api` mutation plane.
- `lean_verify` is `enable_lean: bool = False` by default (`server/config.py:208`).
- Its REPL runs **Lean v4.31.0** from a detached-HEAD directory *outside* the
  arXMCP repo (`plans/lean-verify-continuation/HANDOFF-2026-07-25-…:154-159`);
  this repo pins **v4.29.0** (`lean-toolchain`). An `ok` from that REPL is not
  evidence about this environment.
- `DEFAULT_QUERY_TIMEOUT_S = 30.0` bounds both round-trips, while a cold
  `import Mathlib` measures 14.5 s – 235 s.
- On Windows there is no sandbox: `RLIMIT_AS` is POSIX-only and is skipped with a
  WARN (`server/lean_repl.py:222-228`).
- Neither repo has CI. `.github/workflows/` does not exist in either.

Every runtime coupling inherits all of the above. Every file-based coupling
inherits none of it.

## Decision

**The two repos never call each other.** The contract is a set of versioned,
schema-validated files, exchanged at release time via git tags.

**This is conformance, not innovation** (established while deciding ADR-0007).
The ecosystem already adopted the same principle:
`_pipeline/stage-1-discovery/synthesis/target-architecture.md` §5.1 —
*"Written-artifact contracts over live coupling … Live RPC stays confined to
the MCP surface … Everything persisted, replayed, or audited across the repo
boundary is a file with an envelope. The bridge never crosses the network."*
The reasoning below was derived independently and arrives at the same place,
which is reassuring rather than novel. **Our artifacts must therefore ride that
system's common envelope (§5.2) and its artifact-type registry (§5.3), not a
parallel format of our own** — see ADR-0007.

- This repo publishes an attestation bundle under `attest/` at each tag.
- arXMCP consumes it offline, via an ingest CLI, on the same plane as any other
  corpus artifact — never at request time, never over a socket.
- arXMCP publishes one file back (`resolution.json`, see ADR-0002), which is
  committed into this repo.

No port, no auth, no shared toolchain, no version handshake, no service
discovery. The cross-repo conformance test crosses no network boundary, because
the contract artifact is a file.

## Consequences

**Good.** The contract works with arXMCP uninstalled, not running, or deleted
from the machine — which is also what makes it adoptable by someone who has not
set up arXMCP yet. It satisfies arXMCP's `CLAUDE.md` §4.8 rule 2 ("writes enter
only via offline ingest CLIs or operator-gated `/ui/` console actions") without
argument. It survives arXMCP's lack of CI, because neither side's tests need the
other side running.

**Costs.** Freshness is bounded by release cadence, not by request time: a
statement that drifts in the corpus is not noticed until the next resolver run.
The red team's gap 1 sharpens this — `resolution.json` as specified has no
freshness gate at all, and a resolution produced on mint day stays `pass`
indefinitely. That must be fixed with `corpus_manifest_content_hash` +
`resolution_max_age_days` before v1 ships.

**Rejected alternative.** A typed `arxmcp://` resource surface pinned by a
recorded cassette (the "FROZEN WIRE" design, scored 10/26). Its best idea —
`env_digest` on every axis with `not_applicable` as a fourth value for foreign
environments — was grafted in and is now ADR-0003. What killed it was that its
identity authority lived at `var/arxmcp/notebooks/<slug>/statements.jsonl`, and
`arXMCP/.gitignore:31` is `/var/` — every issued id named a row in a permanently
untracked file on one workstation.
