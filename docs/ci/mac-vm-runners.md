# Mac VM runners

Added by the owner on 2026-11-08. Two runners, `chris-mac-vm-runner-1` and
`chris-mac-vm-runner-2`, run on the owner's Intel MacBook Pro (i9-9880H,
8 cores and 16 threads, 32 GB, macOS 15.5). Like the Ubuntu runners, they are
registered only to the private mirror described in
[the owner lane](owner-lane.md), never to this repository.

## Why a Linux VM

The runners run in an Ubuntu VM on the Mac, not on macOS itself:

- `roadmap` runs `scripts/tests`, which assume Linux.
- The `Restore build output` step of `build` runs on Linux only.
- On the same platform as the Ubuntu runners (Linux x86_64, same toolchain), a
  runner's `.lake` can be copied from one host to the other; see
  [Seeding](#seeding).
- The jobs get their own users and resource limits without changing the Mac.

## The VM

Lima 2.3.0 runs the VM with Apple's Virtualization framework (`vz`), from
Lima's Ubuntu 26.04 template:

```bash
limactl create --name=dag-ci --vm-type=vz --plain --cpus=8 --memory=24 --disk=200 template:ubuntu-26.04
limactl start dag-ci
```

`--plain` turns off Lima's host directory mounts, port forwarding and
containerd, so jobs cannot read the Mac's files.

`--plain` does not isolate the network. The VM reaches the internet through
the Mac, and without a rule a job could also reach:

- the Mac itself at `host.lima.internal` (192.168.5.2), which Lima maps to the
  Mac's loopback, so services that listen only on the Mac's `127.0.0.1` too;
- the Mac's home-network and Tailscale addresses;
- the home router;
- the Ubuntu PC over Tailscale.

A runner account reached all of these on 2026-11-08.

An nftables rule in the VM now refuses connections from the two runner users
to private, link-local, Tailscale (100.64.0.0/10) and multicast addresses,
IPv4 and IPv6. Their own loopback inside the VM stays open, and so does DNS,
because `systemd-resolved` sends the upstream queries as its own user.
Internet hosts are unaffected. The rule is `/etc/dag-runner-egress.nft`:

```nft
table inet dag_runner_egress {
	chain output {
		type filter hook output priority filter; policy accept;
		meta skuid { "dag-mac-1", "dag-mac-2" } jump runner
	}

	chain runner {
		oifname "lo" return
		ip daddr { 0.0.0.0/8, 10.0.0.0/8, 100.64.0.0/10, 169.254.0.0/16, 172.16.0.0/12, 192.168.0.0/16, 224.0.0.0/4, 240.0.0.0/4 } counter reject with icmpx admin-prohibited
		ip6 daddr { fc00::/7, fe80::/10, ff00::/8 } counter reject with icmpx admin-prohibited
	}
}
```

The file deletes and recreates the table, so it can be reloaded in place. The
oneshot unit `dag-runner-egress.service` loads it at boot. A drop-in,
`/etc/systemd/system/dag-runner@.service.d/egress.conf`, makes each runner
`Requires=` and `After=` that unit. A runner therefore does not start without
the rule, and stops if the rule's unit is stopped. Check it with:

```bash
limactl shell dag-ci -- sudo nft list table inet dag_runner_egress
```

Each `counter` shows how many packets were refused.

Other users in the VM, such as the Lima login user, are not restricted. The
rule matches addresses, not names: a public host the jobs need keeps working,
and a name that resolves to a private address is refused.

## Inside the VM

Each runner has its own system user, `dag-mac-1` or `dag-mac-2`, with no
password and no `sudo`. Its tree is `/srv/dag-runners/mac-N/`, with `home/`,
`cache/`, `tmp/` and `_work/` at mode 700. On the Ubuntu PC the four services
share one Unix account; here the two runners are separate users, and neither
can read the other's tree.

The packages are those listed in
[the Ubuntu runner notes](ubuntu-runners.md#operation-and-recovery), plus `git`,
`curl`, `jq` and the `en_US.UTF-8` locale. `gh` comes from GitHub's apt
repository (`https://cli.github.com/packages`), not Ubuntu's archive, for the
reason given under [Runners](owner-lane.md#runners). The runner's own
`bin/installdependencies.sh` adds its ICU and OpenSSL libraries. The runner
tarball is checked against its published SHA-256 before it is unpacked.

Each runner is a system service, `dag-runner@mac-1` and `dag-runner@mac-2`,
from one template unit, `/etc/systemd/system/dag-runner@.service`:

```ini
[Unit]
Description=DerivedAlgGeo Mac VM runner %i
After=network-online.target
Wants=network-online.target
StartLimitIntervalSec=0

[Service]
Type=simple
User=dag-%i
Group=dag-%i
WorkingDirectory=/srv/dag-runners/%i
ExecStart=/srv/dag-runners/%i/runsvc.sh
Environment=HOME=/srv/dag-runners/%i/home
Environment=ELAN_HOME=/srv/dag-runners/%i/home/.elan
Environment=XDG_CACHE_HOME=/srv/dag-runners/%i/cache
Environment=TMPDIR=/srv/dag-runners/%i/tmp
Environment=PATH=/usr/local/bin:/usr/bin:/bin
Environment=LEAN_NUM_THREADS=3
CPUQuota=300%
MemoryHigh=10G
MemoryMax=11G
KillMode=control-group
KillSignal=SIGTERM
TimeoutStopSec=5min
Restart=always
RestartSec=10
UMask=0077
NoNewPrivileges=yes

[Install]
WantedBy=multi-user.target
```

The CPU limit and thread cap match the Ubuntu runners. `MemoryMax` is 11G
rather than 12G, so that two runners and the VM's own system fit in 24 GiB.

Each runner was registered from the Mac, in a clean environment as its own
user. The registration token reaches `config.sh` on standard input, never on
a command line. For `mac-1`:

```bash
gh api -X POST repos/chris-dare-dev/derived-alg-geo-lean-ci/actions/runners/registration-token --jq .token \
  | limactl shell --workdir / dag-ci -- sudo -u dag-mac-1 -H env -i \
      PATH=/usr/local/bin:/usr/bin:/bin LANG=en_US.UTF-8 HOME=/srv/dag-runners/mac-1/home \
      bash -c 'cd /srv/dag-runners/mac-1 &&
        ACTIONS_RUNNER_INPUT_TOKEN=$(cat) ./config.sh --unattended \
          --url https://github.com/chris-dare-dev/derived-alg-geo-lean-ci \
          --name chris-mac-vm-runner-1 \
          --labels owner-ci,owner-mac-vm,chris-mac-vm-runner-1 \
          --work _work --replace'
limactl shell --workdir / dag-ci -- sudo systemctl enable --now dag-runner@mac-1
```

## Starting and stopping

`limactl autostart enable dag-ci` installed the login agent
`io.lima-vm.autostart.dag-ci`, which starts the VM when the owner logs in. The
runners come online about 20 seconds after the VM starts.

```bash
launchctl kickstart gui/$(id -u)/io.lima-vm.autostart.dag-ci   # start the VM now
limactl stop dag-ci                                             # stop it
limactl shell dag-ci -- systemctl status dag-runner@mac-1 dag-runner@mac-2
limactl shell dag-ci -- journalctl -u dag-runner@mac-1 -n 80
```

Wait until both runners are idle before stopping the VM:

```bash
gh api repos/chris-dare-dev/derived-alg-geo-lean-ci/actions/runners \
  --jq '.runners[] | select(.name | startswith("chris-mac-vm")) | "\(.name) \(.status) busy=\(.busy)"'
```

Stopping the VM frees its memory, and the two runners go offline. Jobs routed
to `owner-ci` then run on the Ubuntu PC.

The VM can use up to 24 GiB of the Mac's 32 GB. A running job fails if the Mac
sleeps, for example when its lid is closed. The Mac's idle sleep is off.

## Seeding

On 2026-11-08 each runner's mirror workspace,
`_work/derived-alg-geo-lean-ci/derived-alg-geo-lean-ci`, was seeded with a copy
of `chris-ubuntu-runner-3`'s workspace, taken just after that runner's first
build in the mirror: 12 GB, with 1,422 `DerivedAlgGeo` `.olean` files. All
three runners were idle and stopped during the copy, and the checkout's
credential header was removed from the copy. Lake rechecks every trace against
the source it finds, so a stale file is rebuilt, never trusted.

This does not need repeating unless a runner's tree is lost. A Mac runner that
has to build from cold will probably exceed `build`'s 90-minute timeout; see
[Speed](owner-lane.md#speed).
