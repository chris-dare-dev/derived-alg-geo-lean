# Automatic recovery observations

## OBS-001 — conflicting caps and void rounds

Active CONTRIBUTING, OpenSpec configuration and run-loop guidance said five
rounds while AGENTS/CLAUDE said three. The skill also described a missing
reviewer's round as void. These ambiguities could reset effort or split agent
behavior. New-work guidance now uses three-round attempts and charges reserved
partial panels; explicit legacy manifests retain their historical policy.

## OBS-002 — canonical registry versus exported ledger

Recovery persistence has two copies: the shared Git-directory registry owns the
state and the selected ledger path is its compatibility view. Treating the
exported JSON as authority would permit rewinds and lost allocations. Use the
controller to load and mutate registered state; never edit or reset either copy
to restart a blocked objective.

## OBS-003 — assumed worktree paths are unreliable

The #1451 change is present in the worktree named
`post-closeout-aut1-serre-hygiene`, on branch
`agent/clean-bootstrap-loop-controller`; directory and branch names differ.
A lookup for its observation log in the new recovery worktree failed because
that unpublished change is absent there. Resolve paths with
`git worktree list --porcelain`, then read the identified checkout.

## OBS-004 — predecessor ledger not located

The #1451 manifest in that worktree declares `state_dir: .loop-runs`, but the
directory is absent. Scoped checks also found no #1451 ledger in the main
checkout, `controller-runtime-evidence`, or `loop-ready-for-review`.
The predecessor observation log records a terminal third review; it does not
replace the exact original ledger required for digest-pinned adoption.
The inventory is incomplete, not evidence of zero historical rounds.

## OBS-005 — similarly named repair is another issue

The ledger in `controller-verdict-path-boundaries` identifies issue #1461,
not #1451. At inspection it was `reviewing` with one allocated round, so even
an earlier description of it as merely initialized was already stale. Do not
import it as the #1451 predecessor or infer live tracker state from this note.

## OBS-006 — frozen code and later handoff differ

C1 implementation review targets `d1ab5554e18b664bf7713b3350042470d691e537`.
This observation log and HANDOFF were authored afterward. Review evidence must
identify its actual commit; adding these files does not automatically certify
a later commit or claim a passing panel.

## OBS-007 — verdict names are an executable contract

C1 mathematics/style reviews found that the supervisor still requested MERGE
and claimed automatic translation, although the controller only recognizes
PASS and related tokens. A plausible-looking instruction could stall a valid
panel. Loop dispatch now explicitly overrides standalone style-review verdicts;
the strict parser remains unchanged.

## OBS-008 — external identities differ from local strings

C1 boundary review reproduced a budget reset via repository-name case alone.
GitHub repository identity is case-insensitive but the registry key was not.
Canonical case-folded keys and comparisons now prevent that alias; regression
tests also cover legacy-manifest bypass attempts.

## OBS-009 — local HEAD is not the provider's PR head

C1 boundary review found that local reviewed HEAD did not certify the remote
branch used by PR creation, or a separately merged PR used for issue closure.
Both now check provider evidence. PR creation has pre/post checks, but no atomic
expected-SHA GitHub operation: report a raced created URL and block further
actions rather than claim nothing was created. Tests simulate stale heads,
creation races, wrong closure identities, and out-of-scope closure.
