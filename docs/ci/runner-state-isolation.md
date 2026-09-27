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

The report API accepts detached observations. On Ubuntu, admission re-resolves
POSIX entries on the admitting host and rejects a claimed `resolved_path` that
differs from that observation. A double-leading-slash POSIX path is handled as
POSIX, and report namespaces are unique per physical host.

`admit` takes a fresh physical-host capacity document and holds one exclusive
lock in a host-owned lease directory while it reads **all** active leases,
validates their digests and path identities, reserves the candidate's CPU/RAM/
disk budget, and creates its exact namespace lease. A corrupt or stale lease
fails closed for operator recovery. `release` uses the same lock and removes
only an exact owner match. The lock directory must be an absolute host path
outside every candidate and active job's writable roots, including temp,
outputs, artifacts and elan; all runners on one host must use the **same**
directory. Separate per-runner lease directories would defeat atomic admission.
Each lock and lease read/write is bound to the same opened directory inode;
symlinked lease parents are rejected, and the requested path is checked again
while locked. All components must be controlled by the host operator; a process
with the same Unix account and permission to rename the lock parent is outside
this file-lock contract.
The candidate's paths are checked before opening the lock and again with all
active leases under the lock. The trusted bootstrap must keep those resolved
identities stable until job exit; this validator cannot prevent a job from
retargeting a symlink after admission.

Example operator sequence, with a capacity file measured for the physical host
immediately before admission:

```bash
python3 scripts/runner_state.py report snapshot.json
python3 scripts/runner_state.py admit candidate.json \
  --lease-dir /home/chris-dare/.local/state/dag-pickup/leases \
  --host-capacity host-capacity.json
python3 scripts/runner_state.py release candidate.json \
  --lease-dir /home/chris-dare/.local/state/dag-pickup/leases
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

These low-level commands do not kill processes, delete worktrees, repair
junctions, or change runner services. A stale lease needs explicit recovery.
Do not remove it merely to make a new job fit.

## Host-owned Ubuntu agent pickup

`scripts/host_pickup.py` is a host-installed entry point for a committed agent
job. It derives host identity from `/etc/machine-id`, reads physical CPU
affinity, MemAvailable and free disk, reserves headroom, and accounts for each
enabled or active legacy `dag-runner@` service before admission. Profiles are
fixed in the installed script: `probe` (1 CPU, 2 GiB RAM, 2 GiB disk) and
`build` (3 CPU, 12 GiB RAM, 24 GiB disk). The profile is a reservation; systemd
enforces CPU and memory limits. Disk capacity is measured and reserved, but
there is no filesystem quota on this host, so an individual job can still
exceed its disk reservation. The legacy services' 16 GiB disk reservations are
an initial measured upper bound and must be raised if their roots grow.

After the reviewed revision is merged, install both scripts together outside
any job checkout. Create one host-absolute base on the workstation, outside
runner and agent roots, with owner-only permissions:

```bash
install -d -m 0700 /home/chris-dare/.local/lib/dag-pickup/scripts
install -m 0600 scripts/{host_pickup,runner_state}.py \
  /home/chris-dare/.local/lib/dag-pickup/scripts/
install -d -m 0700 /home/chris-dare/.local/state/dag-pickup
install -d -m 0700 /home/chris-dare/.local/state/dag-pickup/jobs
install -d -m 0700 /home/chris-dare/.local/state/dag-pickup/leases
install -d -m 0700 /home/chris-dare/.local/state/dag-pickup/logs
python3 /home/chris-dare/.local/lib/dag-pickup/scripts/host_pickup.py agent \
  --base /home/chris-dare/.local/state/dag-pickup \
  --repo /home/chris-dare/Documents/sourcecode/derived-alg-geo-lean \
  --revision <full-commit-sha> --profile probe -- python3 -m unittest -q
```

The host lease is acquired before the job root is created. The command runs in
a unique systemd user scope with a private checkout, Git index, `.lake/build`,
`.lake/packages`, HOME/elan, cache, temp, outputs and artifacts. The checkout
is cloned using Git transport rather than shared local object links. A tracked
`.lake` build/package symlink is rejected before the command starts. The scope
must be empty before cleanup. Cleanup opens the exact marked root without
following symlinks, checks its device/inode against a host lease sidecar and
checks mount points, removes only
entries below that descriptor, and then releases the exact lease. Other job
roots and existing worktrees are never cleanup targets.

If the controller crashes, the command fails, or cancellation leaves children,
the lease and root remain for evidence and recovery. Inspect
`systemctl --user status dag-pickup-<namespace>.scope`
and its cgroup before stopping it. Preserve needed output/logs from the root,
then run `python3 /home/chris-dare/.local/lib/dag-pickup/scripts/host_pickup.py recover --base
/home/chris-dare/.local/state/dag-pickup <namespace>`. Recovery refuses a live
scope, mismatched lease, missing or mismatched host root identity,
symlinked/replaced root, unexpected mount or owner
marker. If interrupted midway through cleanup, preserve the lease and inspect
the partially cleaned root manually; do not create a replacement directory at
the same path to coerce recovery.

The currently enabled legacy services reserve most of this workstation's
capacity; the `build` profile may deny admission until two idle services are
disabled and stopped under the migration procedure. That denial is deliberate.
An idle service must be **disabled and stopped** before its reservation is
freed; a merely idle or temporarily stopped enabled service still counts.

## One-job runner operator procedure

`runner-once` uses the same host lease and root before requesting a GitHub
registration token, unpacking the pinned runner archive, or starting the runner.
It registers a uniquely named `--ephemeral --disableupdate` runner for one
job. The runner's `_work` directory is a conservative reservation envelope;
`logs/<namespace>/pickup.json` records the actual resolved checkout, Git
index, Lake build/package, elan, temp, output and artifact locations after the
job. Cleanup waits for the scope to empty and the GitHub registration to
disappear. Diagnostics are copied below host `logs/<namespace>/diag/` before the
root is removed. An unresolved registration, missing checkout, path outside
the root, or failed command retains root and lease for investigation.

Use a reviewed, pristine GitHub runner Linux x64 release archive and record
its SHA-256 independently of the downloaded bytes. Keep the archive outside
all job roots; the worker verifies the pinned digest and rejects links or
special files in the tarball. The host account running the controller needs
repository administration permission for the registration-token and runner
list APIs, and `gh` authentication outside the isolated job environment. No
token is printed; it is passed into the configured runner and removed from the
job root after configuration. Rotate/update the pinned archive deliberately
because `--disableupdate` prevents an in-job self-update.

```bash
python3 /home/chris-dare/.local/lib/dag-pickup/scripts/host_pickup.py runner-once \
  --base /home/chris-dare/.local/state/dag-pickup \
  --archive /home/chris-dare/.local/share/dag-pickup/actions-runner-linux-x64.tar.gz \
  --sha256 <independently-recorded-sha256> --label owner-linux
```

This command waits for one assigned job. For continuing service, install a
host-owned user systemd unit with `ExecStart` set to that exact command,
`Restart=always`, `RestartSec=15s`, and `KillMode=control-group`; each restart
gets a new namespace and checkout. Keep the unit file, archive and digest
outside PR worktrees. A service stop may leave a transient child scope; inspect
and stop that scope before calling `recover`. The new scope joins
`dag-runners.slice`, so its CPU/memory ceiling also shares the existing
aggregate slice cap.

Before replacing a service, capture its GitHub `busy` value, MainPID, cgroup,
resolved roots and a free CPU/RAM/disk reading. Choose an idle general runner;
`systemctl --user disable --now dag-runner@general-N` only after confirming it
is still idle. Verify `ActiveState=inactive`, `UnitFileState=disabled` and an
empty cgroup, then start the corresponding new service. The conservative
capacity policy may require staging two idle general services this way before
one `build` profile can fit alongside the remaining old services. Do not
delete either old root, worktree, cache or registration during this trial.
Keep the old service disabled while the new one has a lease; otherwise both
reservations may overcommit the machine. Restore the old service only after
the replacement has stopped, its scope has emptied and its lease is released.
Preserve the old root for rollback.

A job-start hook cannot serve as first-write admission: GitHub's runner
prepares its workspace and downloads actions before invoking that hook. Full
issue closure still needs the live two-job, over-budget, cancellation/restart
and cold/warm demonstration with run IDs, log digests, process/cgroup evidence,
the recorded actual path inventory, and a sentinel in a sibling/user checkout.
No workflow routing changes or live service changes are part of this PR.

The current CI workflow is unchanged. These tests are code-level evidence;
until the entry point is installed and used by relevant agents/runners, and the
live concurrency/cancellation evidence is complete, #1435 remains open. A
recent-write heuristic or runner label is not an admission lock.
