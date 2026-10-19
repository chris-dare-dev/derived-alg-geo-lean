# CI1.10: audit and exception record contention, 2026-10-19

## Measurement and the pilot boundary

The baseline is main `ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788`. Count a
path once for each of the 223 first-parent integrations after
`c7e4bfcf21823744661bc4acd20d100ebdbe5ac8` that changed it.
The lower boundary is the exclusive first-parent predecessor selected by
2026-09-20 00:00 UTC: it was committed at 2026-09-19 23:46:58 UTC, and
the next first-parent commit at 2026-09-20 01:08:44 UTC. The upper boundary
is the pinned 2026-10-02 main tree. `--first-parent` counts mainline
integrations instead of side-branch ancestors; `--diff-merges=first-parent`
compares merge commits with their first parent. `--no-renames` treats old and
new paths separately. Switching that flag changes one unrelated path count
but none of the named hotspots. Touches are a contention proxy, not observed
Git conflicts.

This single probe replays the path counts, integration digest, PR match and
overlapping open-to-merge windows. It requires the pinned Git history and an
authenticated `gh` CLI. The GitHub merge-date search is fixed at the upper
boundary's calendar date; the SHA-match assertions reject PRs outside the
pinned range, including any later same-day merge.

```bash
python3 - <<'PY'
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
import subprocess

lo = 'c7e4bfcf21823744661bc4acd20d100ebdbe5ac8'
hi = 'ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788'
raw = subprocess.check_output([
    'git', 'log', '--first-parent', '--diff-merges=first-parent',
    '--no-renames', '--format=@@@%H', '--name-only', f'{lo}..{hi}'
], text=True)
paths = {}
commit = None
for line in raw.splitlines():
    if line.startswith('@@@'):
        commit = line[3:]
        paths[commit] = set()
    elif line and commit:
        paths[commit].add(line)
digest = sha256(''.join(sha + '\n' for sha in sorted(paths)).encode()).hexdigest()
print('integrations', len(paths), 'digest', digest)
assert len(paths) == 223
assert digest == 'e4a76253d464254f4fee4dd259582ebeb2ef1d96f7024d8e42c5b9aabe7a2596'
names = (
    'scripts/StabilityConditionAudit/CategoricalCohomology.lean',
    'scripts/StabilityConditionAudit/TStructureCore.lean',
    'scripts/AlgebraicGeometryAudit/Core.lean',
    'scripts/AlgebraicGeometryAudit/ModuleFlatGenerators.lean',
    'scripts/single_instantiation_baseline.txt',
    'scripts/audit_missing_baseline.txt',
    'scripts/StabilityConditionAudit.lean',
    'scripts/AlgebraicGeometryAudit.lean',
)
counts = Counter(path for touched in paths.values() for path in touched)
for path, expected in zip(names, (28, 15, 11, 6, 4, 1, 1, 1)):
    print('touch', counts[path], path)
    assert counts[path] == expected
prs = json.loads(subprocess.check_output([
    'gh', 'pr', 'list', '--repo', 'chris-dare-dev/derived-alg-geo-lean',
    '--state', 'merged', '--base', 'main',
    '--search', 'merged:2026-09-20..2026-10-02', '--limit', '500',
    '--json', 'number,createdAt,mergedAt,mergeCommit'
], text=True))
matched = {pr['mergeCommit']['oid']: pr for pr in prs
           if pr['mergeCommit'] and pr['mergeCommit']['oid'] in paths}
print('PR query', len(prs), 'matched', len(matched),
      'direct', sorted(set(paths) - set(matched)))
assert len(prs) == len(matched) == 222
assert set(paths) - set(matched) == {'47db217d78f55a45f0899281649d643347159253'}
def overlaps(a, b):
    return a['createdAt'] < b['mergedAt'] and b['createdAt'] < a['mergedAt']
for path, excluded, expected in (
    (names[0], 1619, (28, 30, 18)),
    (names[1], 1479, (15, 8, 1)),
    (names[4], None, (3, 0, 0)),
):
    touched = [pr for sha, pr in matched.items() if path in paths[sha]]
    pairs = [(a, b) for a, b in combinations(touched, 2) if overlaps(a, b)]
    without = [(a, b) for a, b in pairs
               if excluded not in (a['number'], b['number'])]
    print('windows', len(touched), len(pairs), len(without), path)
    assert (len(touched), len(pairs), len(without)) == expected
PY
```

At the pinned range the probe reports 223 integrations, with the SHA-256 of
the sorted newline-terminated integration SHAs
`e4a76253d464254f4fee4dd259582ebeb2ef1d96f7024d8e42c5b9aabe7a2596`.
The GitHub query returns 222 PRs and matches all 222 `mergeCommit.oid`
values. The one unmatched integration is direct main commit
`47db217d78f55a45f0899281649d643347159253`. These are PR integration
commits, not 222 Git merge commits; most were squashed.

| Path | Integrations touching it | Interpretation |
| --- | ---: | --- |
| `scripts/StabilityConditionAudit/CategoricalCohomology.lean` | 28 | Mostly serial #554/SF11 work in one broad slice; independent subowners need declaration-level evidence before another split. |
| `scripts/StabilityConditionAudit/TStructureCore.lean` | 15 | Shared area, retained for later source-owner review. |
| `scripts/AlgebraicGeometryAudit/Core.lean` | 11 | Residual broad area slice. |
| `scripts/AlgebraicGeometryAudit/ModuleFlatGenerators.lean` | 6 | Residual broad area slice. |
| `scripts/single_instantiation_baseline.txt` | 4 | Shared exception append point; the pilot gives new records subject-owned paths. |
| `scripts/audit_missing_baseline.txt` | 1 | Keep the global identity ratchet. |
| `scripts/{StabilityCondition,AlgebraicGeometry}Audit.lean` | 1 each | Contract prose, not routine record append points. |

Issue #480, implemented by PR #546, already split the former large audit
files into per-area leaves. This pilot does not repeat that migration. The
mode-only CI1.02 prerequisite is present: `scripts/check_audit_complete.py`
has mode 100755 at the baseline revision.

The probe reports 28 matched PRs and 30 overlapping open-to-merge pairs for
CategoricalCohomology (18 pairs excluding long-lived #1619), 15 PRs and eight
pairs for TStructureCore (one excluding long-lived #1479), and three PRs
with zero pairs for the exception baseline. A pair means that both PRs
touched the path and their `createdAt`–`mergedAt` intervals overlapped.
This does not show that Git reported a conflict. Direct main commits are
excluded from pair counts. The audit leaves are follow-up candidates after
their source-owner boundaries are checked; the bounded exception pilot does
not claim to remove those overlaps.

## Independently owned exception records

The first column of each single-instantiation exception is the **source module
subject** emitted by `EnumInhabitants`, not a prefix guessed from the
declaration name. For example, an Algebra-owned record may name a declaration
in the `CategoryTheory` namespace. The historical file remains readable, but
new records are written by `--relax` to
`scripts/single_instantiation_records/<subject>.txt`. The CategoryTheory and
Algebra shards are the bounded pilot. Exactly one existing record of each
owner moved out of the historical file, so the gate consumes real shards now.

The aggregator sorts shard paths and record names. It rejects a malformed
row, unknown subject, unexpected shard file, row/shard owner mismatch,
duplicate name (including a duplicate across the old file and a shard), or a
live name whose recorded owner disagrees with its emitted module. It reports
both locations for a duplicate rather than allowing a set union to discard
one. `--relax` preserves all existing records, including five current
above-threshold exceptions reserved for #1394, and writes a new reason as a failing TODO
in the new subject shard. Adding one new exception therefore changes only its
subject file. A reviewer must replace that TODO with a reason before the gate
passes.

The seeded local cache initially omitted two current SphericalTwist structures
from the root-only `EnumInhabitants` sweep. That partial sweep counted 98 thin
names, three above threshold, and two absent from the emitted environment. A
targeted SphericalTwist build and explicit-import scratch sweep found those two,
but still used other stale imports. The first root-target rebuild then failed
because two unchanged defining modules had old compiled imports. Compiling
those modules from current source, rebuilding the five affected consumers, and
rebuilding the root succeeded (6109 Lake jobs). The standard sweep from that
rebuilt root counts 98 thin names, five above-threshold records, and zero
absent baseline names. Two Serre-functor records moved from thin to above
threshold when their producer imports refreshed. The gate now reports absent
names separately from above-threshold ones, so stale imports cannot masquerade
as resolved exceptions. Required PR CI remains the full audit verdict.

The before/after `(name, reason)` set contains the same 103 records. Its
sorted, newline-terminated TSV SHA-256 is
`22316b595351b6289a383cf9c13bd07f2fe748f4b6d301996adfa96629ec3daf`
on both revisions. The strict live-owner check found one old label drift:
`CategoryTheory.DGFunctor.PreservesConeTriangles` is emitted from
`DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Functor`, so its
record owner changes from `CategoryTheory` to `Algebra`, with its name and
reason preserved. The sorted `(subject, name, reason)` TSV SHA-256 changes from
`cc60104600aad5dd42cc9cdff30653b91b2113ad1bb1a83fe668eb93131e3b4a`
to `85a71ee1f707e6388b0b220ff5723bff7d9549e454bc6f1b1df764fa294043f7`.
The historical file has 101 rows afterward, and the two shards have one each.
The 1040-name missing baseline is untouched, with sorted-set digest
`dae436c2a9d5ecb0b0688f1b11af83329325531355b21a30cb2a2338b341c5a6`.
The audit source files are untouched: the AlgebraicGeometry, StabilityCondition
and DGCategory unique-name sets have 5664, 7435 and 1376 entries and digests
`b6c93a85f4616c227f4ae5675155525169b013cc5c338ddff4b71ba52e98a965`,
`06b0afbb15746279ff095d4d7365988cdeab2dd597353d1be0b9a8c0ebe37f97`
and `3ff49a81e41fcdaff254b0a4c62db0ac53d7fb2ff498c729ad89010e67b151c9`.
No ceiling or audit command is removed. The declaration-owner witness source
`scripts/check_umbrella_coverage.py` is untouched, with blob SHA-256
`4f4df28fab66486332f0aeb516fd03cc8b10023bcdb78eb197fd0306fcbde18e`.

The focused fixture creates two Git branches from one baseline. One adds a
CategoryTheory exception and changes only `CategoryTheory.txt`; the other adds
an Algebra exception and changes only `Algebra.txt`. A normal Git merge
contains both records. Other fixtures drop and rename a record, duplicate it,
misassign an owner or corrupt a row; the gate rejects each bad state. The
required PR `ci` result, including all three full axiom audits and the
completeness ratchet, is the final verification of this pilot.

At 2026-10-19 18:34 UTC, frozen draft PR #1847's
[CI run 39298977534](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/runs/39298977534)
had a successful `roadmap` job and an in-progress `build` job; it had no full
audit verdict. That run belongs to the frozen attempt. The successor branch
had no PR or CI run at that observation. Its own required PR checks must pass
before normal merge; the loop-state comment records subsequent observed state.

## Integration ownership and next decision

The active milestone-54 loop coordinator is the **single integration owner**
for global audit umbrellas, the missing-name identity baseline, dependency
pins and roadmap files. Parallel producers may prepare disjoint source and
record leaves; the coordinator admits one candidate at a time, refreshes only
it against main, compares before/after record sets, and records the exact
reviewed and published revisions. A meaningful conflict resolution that
changes a candidate's own content returns to four independent same-commit
reviewers. No `--ours`/`--theirs` shortcut may discard a record, lower a reason
obligation or raise a ratchet ceiling. A handoff must be recorded on #1429
before this role changes.

**Go for the bounded exception pilot** when its PR checks and four reviewers
pass. **No go for a global audit migration now:** the current audit text
contains five repeated AlgebraicGeometry commands and twelve repeated
StabilityCondition commands, while the source-owner meaning of the busy
CategoricalCohomology slice has not been split. Those existing duplicates and
the remaining shared slices stay in #1439 for a separately scoped follow-up;
the pilot's duplicate rule applies to exception records only. A future audit
aggregation change must review the duplicate locations, preserve the unique
declaration set and full output count, and prove that independently owned
source areas truly write distinct files. Pin and roadmap changes likewise
stay under the single integration owner rather than a mechanical split.
