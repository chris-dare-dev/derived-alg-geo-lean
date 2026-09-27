# R&D handoff: #554 controller preflight closed blockers

Status: research only. The local `agent/loop-preflight-closed-blockers` attempt
is terminal after three critique/revise rounds. Its final commit is
`f2026ca448770a0e26231a0be019d1b22948b189`, based on then-current
`origin/main` `507298894950fcb203539ce391b668e08a0f8648`. No PR was opened.
The 87 focused tests and local no-build precheck passed, but neither is CI.

## Evidence and cause

The controller's `unresolved_blocked_by_entries` accepts a bare `blockedBy`
list and filters each dictionary whose `state` string uppercases to `CLOSED`.
It has no evidence that the list is complete. For a connection object, it
requires `nodes` and `totalCount` to agree, but it still filters a closed node
without a valid issue `number`. The last two adversaries independently found
these fail-open cases after the third round; boundary and style passed. A live
#554 provider query returned a connection with `nodes`, `totalCount`, and a
closed #1495 node. The existing helper also normalizes malformed input to an
empty list outside this gate. The complete review transcripts need a separate
inventory of all three rounds and all four reviewer roles per round before
any successor implementation is admitted; summaries cannot replace available
verbatim reviews.

The failure is at the provider-data boundary: the code asks whether any
visible node is open before proving that the visible nodes form a complete,
well-identified blocker set. A test suite that treats a bare list as a valid
complete response encodes the same gap.

## Re-examination options

1. Preferred: introduce a typed eligibility decoder at the provider boundary.
   Require the requested issue number, valid state and labels, a `blockedBy`
   connection with a nonnegative integer `totalCount`, exactly that many
   `nodes`, and a valid positive issue number plus recognized state for every
   node. Reject bare lists, missing fields, duplicates or malformed nodes.
   Only after decoding may explicitly closed blockers be ignored. This makes
   completeness and identity preconditions of the eligibility decision.
2. Query the GitHub GraphQL connection directly with explicit pagination and
   `pageInfo.hasNextPage`, validating every page and its issue identities.
   This is appropriate if `gh issue view --json blockedBy` cannot reliably
   provide a complete connection. It adds provider and pagination complexity,
   so it should be selected if a provider-contract probe cannot establish
   option 1's completeness invariant.

Changing only the final list filter or adding one more example to the same
tests is a fourth revision of the failed method and is not an admitted
rearchitecture. The legacy controller objective and its review history stay
separate from #1574's mathematical PR.

## Falsification and checks

- Capture the exact live provider shape. The one-node #554 response is a
  positive shape example, not evidence that `gh issue view` never truncates.
  Inspect the pinned `gh` query contract/source for `blockedBy` completeness
  and probe a response larger than one provider page (controlled fixture or
  test issue) to see whether `nodes` covers `totalCount`. If neither can
  establish the invariant, choose explicit paginated GraphQL before coding
  eligibility. Verify the decoder accepts a complete connection with closed
  #1495 while rejecting a bare closed list, integer mismatch, boolean
  `totalCount`, absent/zero/boolean/wrong issue number, unknown state, and
  missing labels or requested issue identity.
- Run preflight through provider fixtures for each negative case, not only a
  standalone helper. Confirm no ledger or provider mutation occurs on reject.
- Preserve the original frozen scope and all three four-role panels, including
  available verbatim messages. Independent plan
  review must accept a changed strategy and complete history before any new
  implementation attempt. Fresh source still requires four same-commit roles
  and actual required CI before publication.

## Friction to retain

The issue-first route made this controller preflight optional for #554, but
investigating its stale closed blocker cost time. A malformed provider response
could be accepted as eligible while focused tests passed. The live response
shape was discovered late. The terminal reviewer findings were not sent
automatically into a resumable research path; this handoff records that gap
without silently repairing the failed source.
