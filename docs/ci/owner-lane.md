# Owner CI lane: self-hosted runners in a private mirror

Adopted by the owner on 2026-11-08. This completes the zero-registration end
state of [the hosted cutover](hosted-cutover.md) for this repository and gives
the owner's hardware a lane that untrusted code cannot reach. It supersedes the
scheduling topology in [the Ubuntu runner notes](ubuntu-runners.md); their
host isolation and resource limits still apply.

## The boundary

This public repository has **no** self-hosted runner registrations. A pull
request can edit its own copy of `ci.yml`, `runs-on` included, so the workflow
text cannot keep it off a registered runner. With nothing registered, a job
that asks for `self-hosted` gets no runner and stays queued. Check it with:

```bash
gh api repos/chris-dare-dev/derived-alg-geo-lean/actions/runners --jq .total_count   # must print 0
```

The owner's runners are registered only to the **private** repository
`chris-dare-dev/derived-alg-geo-lean-ci`. Only accounts with write access to a
private repository can trigger its workflows, which makes this the
provider-enforced runner boundary the cutover requires. Outside contributors
are unaffected: their pull requests here run on hosted runners, which are free
for a public repository, and forks run on their own hosted runners.

## Routing

`build`, `roadmap` and `ci` in `ci.yml` take their runner from the repository
variable `OWNER_CI_RUNS_ON`, a JSON list of runner labels:

```yaml
runs-on: ${{ vars.OWNER_CI_RUNS_ON && fromJSON(vars.OWNER_CI_RUNS_ON) || 'ubuntu-latest' }}
```

| Repository | `OWNER_CI_RUNS_ON` | Jobs run on |
| --- | --- | --- |
| `chris-dare-dev/derived-alg-geo-lean` (public) | unset | `ubuntu-latest` |
| any fork, and fork pull requests (they read the base repository's variables) | unset | `ubuntu-latest` |
| `chris-dare-dev/derived-alg-geo-lean-ci` (private) | `["self-hosted","owner-ci"]` | the owner's runners |

`cache-warm.yml` and `docs.yml` skip their jobs when the variable is set. In
the mirror nothing reads the hosted Linux cache, the Pages site is not
published, and a hosted job in a private repository bills minutes.

Every owner runner carries the `owner-ci` label. To keep jobs on one host
while it is being proven, narrow the variable to that host's label:
`["self-hosted","owner-mac-vm"]` for the Mac, or
`["self-hosted","owner-linux"]` for the three general Ubuntu runners. Both
hosts report `Linux`, so that label does not separate them. Restore
`["self-hosted","owner-ci"]` when the run being proven has finished. Never set
the variable in the public repository. That fails closed,
with jobs queued for a runner that isn't there, but it stops CI for everyone.

## Runners

Six runners, all registered to the mirror on 2026-11-08:

| Host | Runners | Labels | Notes |
| --- | --- | --- | --- |
| Ubuntu PC | `chris-ubuntu-main-runner`, `chris-ubuntu-runner-1`..`-3` | `owner-ci`, `owner-linux-main` or `owner-linux`, and the runner name | [Ubuntu runner notes](ubuntu-runners.md) |
| Intel MacBook Pro, 32 GB | `chris-mac-vm-runner-1`, `chris-mac-vm-runner-2` | `owner-ci`, `owner-mac-vm`, and the runner name | in a Linux VM; [Mac VM runner notes](mac-vm-runners.md) |

All six also carry `self-hosted`, `Linux` and `X64`. The Mac runners run in an
Ubuntu VM, not on macOS: `roadmap` runs `scripts/tests`, which assume Linux,
and the `Restore build output` step of `build` runs on Linux only.

`LEAN_NUM_THREADS=3` still applies to every self-hosted job (the first step of
`build`). Labels are not capacity: four runners on the Ubuntu PC are four
processes on one machine, and the two Mac runners share one VM.

Every runner host needs a current `gh`. `scripts/check_roadmap.py` asks for
the `parent` and `blockedBy` issue fields, which the `gh` 2.46 in Ubuntu's own
archive does not know, and `roadmap` runs it with `--require-api`, so an old
`gh` fails the job. Both hosts install `gh` from GitHub's apt repository at
`https://cli.github.com/packages`.

### Speed

Measured on 2026-11-08, on `main` at `2f7f7c22`. Each runner's `.lake` is kept
between jobs, so a warm build compiles only what changed.

| Job | Ubuntu PC | Mac VM |
| --- | --- | --- |
| `build`, total | 44 min, cold | 60 min, warm |
| `lean-action` (the library build) | 29.0 min, cold | 2.5 min, warm |
| `build`, after the library build | 15 min | 57 min |
| algebraic-geometry and stability-condition axiom audits | 4.2 and 2.6 min | 9.3 and 5.7 min |
| `Audit completeness` and `Single instantiation` | 0.7 and 0.7 min | 5.3 and 5.1 min |
| `Emit combined environment` | 2.6 min | 14.1 min |
| `Emitter reproducibility` | 2.7 min | 13.2 min |
| `roadmap` | 0.9 min | 4.4 min |

After the library build the Mac VM is about four times slower overall, from
about twice as slow on the axiom audits to about seven times on
`Audit completeness` and `Single instantiation`. The two whole-environment emit
steps take the most time. The VM's memory limits were not the cause. The build
job peaked at its 10 GiB `MemoryHigh` and was held back by memory pressure for
about 7 seconds in all, with no OOM kill.

`build` times out after 90 minutes on hosted runners and after 180 minutes on
the owner's runners. The timeout reads the routing variable:

```yaml
timeout-minutes: ${{ vars.OWNER_CI_RUNS_ON && 180 || 90 }}
```

The extra time is for a cold build on a Mac runner, such as the first build
after a Mathlib bump. No such build has been measured yet. Of the 180 minutes,
the Mac's 57 minutes after the library build leave 123 for the library build
itself. That is about four times the Ubuntu PC's cold 29 minutes, the same
ratio as the Mac's steps after the library build. If a build still runs out of
time, the partial `.lake` is kept, so the next job on that runner continues
from where it stopped.

## Using the lane

The mirror is a second remote on the owner's checkout. Push a branch there and
dispatch CI on it:

```bash
git push ci <branch>
gh workflow run ci.yml --ref <branch> -R chris-dare-dev/derived-alg-geo-lean-ci
```

Keep the mirror's `main` equal to this repository's, because the roadmap
check scopes branch runs against it:

```bash
git push ci origin/main:main
```

A push to the mirror's `main` also runs `ci.yml` there, as it does here.

Whoever can push to the mirror decides what the owner's runners execute.
Pushing agent branches there is a choice to run agent-produced code on the
owner's hardware.

## What the lane does not do

- **It cannot satisfy this repository's required `ci` check.** Branch
  protection pins `ci` to the GitHub Actions app on this repository, and a run
  in another repository cannot post that check here. Loosening the pin would
  undercut the gate-provenance work in #1434. Pull requests here are still
  gated by hosted CI. The lane adds coverage, such as branches with no pull
  request yet and heavier sweeps; it does not replace the hosted gate.
- **It does not trigger on branch pushes.** `ci.yml` fires `push` on `main`
  alone, in the mirror as here. An automatic mirror-only branch trigger would
  need a separate caller workflow, whose skipped runs would show on every push
  to this repository. Any such workflow must never produce a check named `ci`,
  because a skipped required check does not block a merge. Deferred until
  dispatch proves too slow.

## Enabling and rolling back

Enabled on 2026-11-08, on `main` at `2f7f7c22`. The mirror's Actions were
turned on in the order below. Two runs of `ci.yml` in the mirror then passed
on that commit:

| Run | Variable at dispatch | `build` | `roadmap` | `ci` |
| --- | --- | --- | --- | --- |
| 42488589144 (`main` push) | `["self-hosted","owner-ci"]` | `chris-ubuntu-runner-3` | `chris-ubuntu-runner-2`, on re-run | `chris-ubuntu-runner-1` |
| 42492738556 (dispatch) | `["self-hosted","owner-mac-vm"]` | `chris-mac-vm-runner-2` | `chris-mac-vm-runner-1` | `chris-mac-vm-runner-1` |

The first attempt of `roadmap` failed on the Ubuntu PC's `gh` 2.46 (see
[Runners](#runners)); it passed once `gh` was upgraded. The public
repository's runner count stayed 0 throughout.

The mirror was created with Actions disabled. To enable it again, wait until
this routing is on `main`, then run these in order, so that no job falls back
to hosted minutes:

```bash
gh variable set OWNER_CI_RUNS_ON -R chris-dare-dev/derived-alg-geo-lean-ci --body '["self-hosted","owner-ci"]'
git push ci origin/main:main
gh api -X PUT repos/chris-dare-dev/derived-alg-geo-lean-ci/actions/permissions -F enabled=true -f allowed_actions=all
```

To roll back, disable Actions in the mirror (`-F enabled=false`). This
repository is unaffected either way. Do not re-register any runner to this
repository as a rollback; that reopens the path the cutover closed.
