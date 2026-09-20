# Self-hosted runner state contract

Runner labels and Actions concurrency are scheduling controls; they do not
prove that two labels are separate machines or that two jobs have separate
writable state. The Windows lane currently has multiple runner processes on one
physical host, so a job is admissible only when its resolved writable roots and
resource reservation are unique.

`python3 scripts/runner_state.py report snapshot.json` validates a report-only
snapshot. Each job record must carry a physical `host_id`, runner/job/run/
attempt identity, a unique namespace, CPU/memory/disk reservations, and
canonical paths for checkout, Git index, `.lake/build`, `.lake/packages`,
`.elan`, temp, output, and artifact roots. The validator resolves aliases and
rejects writable path equality or ancestor overlap. Read-only dependency paths
may be shared, but the snapshot must say so explicitly.

`admit` creates an exact namespace lease with an atomic create; an existing
lease is a fail-closed recovery condition. `release` removes only the exact
namespace lease after verifying its owner. Neither command kills processes,
deletes worktrees, repairs junctions, or changes runner services. A future
bootstrap must inventory and reconcile stale holders under an operator-owned
procedure before it is wired into required CI.

The current CI workflow is intentionally unchanged by this issue. The next
integration slice should collect these records before routing more work to the
shared Windows host and should use a host-level admission service when more
than one runner process can be active. A recent-write heuristic or a runner
label is not an admission lock.
