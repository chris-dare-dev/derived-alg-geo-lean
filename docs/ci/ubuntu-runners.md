# Ubuntu workstation runners

The owner retired the Windows workstation setup on 2026-09-21 and authorized
four runners on the personal Ubuntu PC. Windows is no longer a required
platform for this repository. This operator-directed replacement is distinct
from the hosted-Linux benchmarking and broader CI1 rollout in #1436.

| Runner | Custom scheduling label | Work |
| --- | --- | --- |
| chris-ubuntu-main-runner | owner-linux-main | main push and main manual runs |
| chris-ubuntu-runner-1 | owner-linux | manual runs on other refs |
| chris-ubuntu-runner-2 | owner-linux | manual runs on other refs |
| chris-ubuntu-runner-3 | owner-linux | manual runs on other refs |

All also have the standard `self-hosted`, `Linux`, `X64` labels and a unique
runner-name label for operator smoke tests. No general runner carries the main
label. PR and merge-group builds continue on `ubuntu-latest`; branch pushes
alone do not trigger CI. Existing `ci` protection stays in place. No runner targets the retired employer-issued Mac.

## State and resource boundaries

Installation root: `~/.local/share/github-runners/`. The four children are
`main`, `general-1`, `general-2`, and `general-3`. Each owns a distinct `home/`,
`home/.elan/`, `_work/`, `tmp/` and `cache/`. There are no writable cache or
package symlinks between runners or into developer checkouts. Downloads may be
copied, never linked into another runner's mutable build tree.

The host has 16 logical CPUs and approximately 60 GiB RAM. Initial policy:
`LEAN_NUM_THREADS=3` per self-hosted build, systemd CPUQuota=300% per service,
MemoryHigh=10G and MemoryMax=12G per service. The aggregate runner slice is
limited to CPUQuota=1200%, MemoryHigh=40G and MemoryMax=48G. These are initial
capacity limits, not benchmarked throughput guarantees. An oversized job may
fail at its memory cap; use actual peak measurements before raising concurrency
or limits. Four registrations are four processes on one physical machine.

## Read-only inventory, 2026-09-27

At 05:24 UTC, the GitHub runner API reported all four registrations online;
the main runner was busy and the three general runners idle. `systemctl --user`
reported four active services with separate main PIDs. Each runner's
`_work/derived-alg-geo-lean/derived-alg-geo-lean`, `home/.elan`, `tmp`, and
`cache` resolved under its own
`/home/chris-dare/.local/share/github-runners/{main,general-1,general-2,general-3}/`
root. The four resolved `.lake/packages` paths were distinct directories, not
symlinks. This is a point-in-time inventory, not a proof about future jobs.

The host measured 16 logical CPUs, 65,374,400,512 bytes of RAM and
141,614,346,240 bytes of available filesystem space. The live service
settings were three CPU seconds per second and 12 GiB maximum memory each;
the shared runner slice was capped at 12 CPU seconds per second and 48 GiB.
Those values bound the starting host-wide reservation policy, subject to
fresh free-space/load readings and throughput measurements. Do not multiply
capacity by the four runner labels.

A separate read-only scan of this clone's 219 registered agent worktrees found
three resolved `.lake/packages` targets shared by multiple worktrees (groups
of 38, 22 and 19). These are not the runner package directories. They must
not be treated as immutable merely because a worktree's `.lake/packages` is a
symlink; the new admission preflight rejects such paths for a writable job.
Migrate an idle agent non-destructively: create a new isolated worktree and
job-owned package tree, copy from an idle verified donor if needed, compare
the pin/toolchain inputs, run the focused build, then switch the pickup path.
Keep the old checkout and cache until the new one is verified. No active
service, checkout or cache was changed for this inventory.

A read-only rescan on 2026-09-28 found 246 registered worktrees, 223 existing
paths, and 107 `.lake/packages` links resolving to four shared targets. These
are existing user worktrees; neither the runner installation nor the new
worktree seeder deletes or rewrites them. On an idle migration, preserve the
old worktree, create a new worktree at its commit, and run
`bash scripts/seed_worktree_cache.sh --dry-run` followed by
`bash scripts/seed_worktree_cache.sh` in the new one. The default seeder now
requires private package/build caches and verifies their receipt. Compare the
new source and Git index with the old worktree, carry any uncommitted and
untracked work deliberately, and move the pickup path only after verification.
An old linked `.lake` refuses seeding in place, including with `--force`.
Each migrated worktree needs its own disk space; the current seeder checks
headroom and refuses before publication when it is insufficient.

The user services invoke the runner's `runsvc.sh` entrypoint and restart after
failures. User lingering makes them start at boot and survive logout. Inspect:

```bash
systemctl --user status dag-runner@main dag-runner@general-{1,2,3}
journalctl --user -u dag-runner@main -n 80
loginctl show-user "$USER" -p Linger
gh api repos/chris-dare-dev/derived-alg-geo-lean/actions/runners
```

Services intentionally use runner-owned HOME values and a minimal PATH; the
owner's gh keyring/config and personal Lean installation are not copied. Jobs
still run as the same Unix account: separate directories and cgroup budgets
are operational isolation, not a security boundary against hostile code.

## Operation and recovery

Wait for an idle runner before stopping or changing its service. On a failed
job, inspect its log and service memory events; do not erase a sibling's state.
Stop/start a specific service with `systemctl --user stop/start dag-runner@NAME`.
Systemd's control-group shutdown reaps that service's child processes. Runner
auto-updates retain the same directory and service identity.

Required host packages include build-essential, python3-venv, python3-pip,
pkg-config, libgmp-dev, unzip, zstd and the runner's ICU/OpenSSL runtime
libraries. Lean setup follows the committed toolchain through lean-action.

If routing must be rolled back, use hosted Ubuntu through a reviewed change;
do not recreate the Windows registrations or assign their labels to Linux.
This migration does not claim completion of CI1 host-admission tooling,
trusted-cache consolidation, cold/warm parity or the week-long rollout study.
