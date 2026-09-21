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
alone do not trigger CI. Existing `ci` and `trust-surface` protection stays in
place. No runner targets the retired employer-issued Mac.

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
