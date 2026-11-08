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

`scripts/host_pickup.py runner-once` registers to the mirror, and
`scripts/tests/test_host_pickup.py` refuses the public repository as its
target.

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

Every owner runner carries the `owner-ci` label. To keep jobs on one platform
while another is being proven, narrow the variable, for example
`["self-hosted","owner-ci","Linux"]`. Never set the variable in the public
repository. That fails closed, with jobs queued for a runner that isn't there,
but it stops CI for everyone.

## Runners

| Host | Runners | Labels |
| --- | --- | --- |
| Ubuntu PC | `chris-ubuntu-main-runner`, `chris-ubuntu-runner-1`..`-3` | `owner-ci`, `owner-linux-main` or `owner-linux`, and the runner name |
| Intel MacBook Pro | two, planned | `owner-ci` and per-runner names, to be recorded when registered |

`LEAN_NUM_THREADS=3` still applies to every self-hosted job (the first step of
`build`). Labels are not capacity: four runners on the Ubuntu PC are four
processes on one machine.

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

The mirror was created with Actions disabled. Enable it only after this routing
is on `main`, and in this order, so that no job falls back to hosted minutes:

```bash
gh variable set OWNER_CI_RUNS_ON -R chris-dare-dev/derived-alg-geo-lean-ci --body '["self-hosted","owner-ci"]'
git push ci origin/main:main
gh api -X PUT repos/chris-dare-dev/derived-alg-geo-lean-ci/actions/permissions -F enabled=true -f allowed_actions=all
```

To roll back, disable Actions in the mirror (`-F enabled=false`). This
repository is unaffected either way. Do not re-register any runner to this
repository as a rollback; that reopens the path the cutover closed.
