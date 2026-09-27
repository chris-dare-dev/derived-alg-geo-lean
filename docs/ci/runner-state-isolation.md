# Self-hosted runner state contract

Runner labels and Actions concurrency are scheduling controls; they do not
prove that two labels are separate machines or that two jobs have separate
writable state. The Ubuntu lane has four runner processes on one physical
host; the installation and resource limits are recorded in
[the Ubuntu runbook](ubuntu-runners.md). A job is admissible only when its
resolved writable roots and resource reservation are unique.

`python3 scripts/runner_state.py report snapshot.json` validates a report-only
snapshot. Each job record must carry a physical `host_id`, runner/job/run/
attempt identity, a safe unique namespace, CPU/memory/disk reservations, and
canonical paths for checkout, Git index, `.lake/build`, `.lake/packages`,
`.elan`, temp, output, and artifact roots. Windows records must include both
the observed path and an OS-resolved `resolved_path`; lexical normalization is
not evidence that two junctions are distinct. The validator rejects writable
path equality or ancestor overlap and compares resource reservations per
physical host using `host_capacity`. A job's `.lake/packages` and `.lake/build`
must be writable trees resolving within its own checkout; a symlink to another
worktree is not an immutable dependency cache. All eight required roots are
mutable; an input marking any of them read-only is rejected.
Path collisions are scoped to jobs on the same physical host. POSIX path case
is preserved; Windows records use Windows case normalization.

`admit` takes a fresh physical-host capacity document and holds one exclusive
lock in a host-owned lease directory while it reads **all** active leases,
validates their digests and path identities, reserves the candidate's CPU/RAM/
disk budget, and creates its exact namespace lease. A corrupt or stale lease
fails closed for operator recovery. `release` uses the same lock and removes
only an exact owner match. The lock directory must be an absolute host path
outside every candidate and active job's writable roots, including temp,
outputs, artifacts and elan; all runners on one host must use the **same**
directory. Separate per-runner lease directories would defeat atomic admission.
The candidate's paths are checked before opening the lock and again with all
active leases under the lock. The trusted bootstrap must keep those resolved
identities stable until job exit; this validator cannot prevent a job from
retargeting a symlink after admission.

Example operator sequence, with a capacity file measured for the physical host
immediately before admission:

```bash
python3 scripts/runner_state.py report snapshot.json
python3 scripts/runner_state.py admit candidate.json \
  --lease-dir "$HOME/.local/state/dag-runner-leases" \
  --host-capacity host-capacity.json
python3 scripts/runner_state.py release candidate.json \
  --lease-dir "$HOME/.local/state/dag-runner-leases"
```

`host-capacity.json` maps one physical `host_id` to positive `cpu_threads`,
`memory_bytes` and `disk_bytes` limits. It is a trusted operator input, not PR
content. The reservation may be smaller than physical capacity to leave room
for the desktop and other services. Refresh available disk and host load before
every admission; this library validates the supplied numbers but does not yet
measure them or wire itself into Actions job startup. A runner label is not a
capacity record. Shared downloads need a separate immutable provenance
demonstration; this contract currently requires a copied package tree. A
per-job Git index, elan, temporary and output paths are checked for cross-job
overlap.

The commands do not kill processes, delete worktrees, repair junctions, or
change runner services. After cancellation, an operator must establish that
the prior job's processes have stopped before releasing its lease. A lease
with an unknown owner is retained for investigation; do not remove it to make
another job fit. Bootstrap, exact-target workspace cleanup, live Actions
admission wiring and the two-build cancellation/cold-warm demonstration remain
open in #1435.

The current CI workflow is unchanged by this progress slice. The next slice
must make the host capacity and active-job record collector trusted, bootstrap
isolated workspaces, and call this admission path before a job can write.
Until then, a passing fixture is code-complete evidence, not an applied runner
control. A recent-write heuristic or a runner label is not an admission lock.
