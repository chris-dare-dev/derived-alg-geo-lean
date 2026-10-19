# CI1.10: audit and exception record contention, 2026-10-19

## Measurement and the pilot boundary

The baseline is main `ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788`. Count a
path once for each of the 273 main commits since 2026-09-20 that changed it.
This measures touch frequency, not simultaneous-edit conflicts. The following
query fixes the revision and date; its output is sorted by descending count:

```bash
python3 - <<'PY'
from collections import Counter
import subprocess

raw = subprocess.check_output(
    ['git', 'log', 'ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788',
     '--since=2026-09-20', '--format=@@@%H', '--name-only'], text=True)
commits = []
paths = None
for line in raw.splitlines():
    if line.startswith('@@@'):
        if paths is not None:
            commits.append(paths)
        paths = set()
    elif paths is not None and line:
        paths.add(line)
if paths is not None:
    commits.append(paths)
counts = Counter(path for paths in commits for path in paths)
print('commits:', len(commits))
for path, count in sorted(counts.items(), key=lambda item: (-item[1], item[0])):
    if path.startswith('scripts/') and (
        'Audit/' in path or path.endswith('Audit.lean') or 'baseline' in path
    ):
        print(count, path)
PY
```

| Path | Commits | Interpretation |
| --- | ---: | --- |
| `scripts/StabilityConditionAudit/CategoricalCohomology.lean` | 28 | Mostly serial #554/SF11 work in one broad slice; independent subowners need declaration-level evidence before another split. |
| `scripts/StabilityConditionAudit/TStructureCore.lean` | 13 | Shared area, retained for a later source-owner review. |
| `scripts/AlgebraicGeometryAudit/{Core,ModuleFlatGenerators}.lean` | 11 each | Residual broad area slices. |
| `scripts/single_instantiation_baseline.txt` | 5 | One shared exception append point; the bounded pilot below gives new records subject-owned paths. |
| `scripts/audit_missing_baseline.txt` | 1 | Keep the global identity ratchet; a new unaudited name must not be added by hand. |
| `scripts/{StabilityCondition,AlgebraicGeometry}Audit.lean` | 1 each | Contract prose, not routine record append points. |

Issue #480, implemented by PR #546, already split the former large audit
files into per-area leaves. This pilot does not repeat that migration. The
mode-only CI1.02 prerequisite is present: `scripts/check_audit_complete.py`
has mode 100755 at the baseline revision.

The merged-PR windows give a second, closer contention proxy. Match each
commit's touched paths to the `mergeCommit.oid` of PRs merged from 2026-09-20
through the pinned main commit's date, 2026-10-02:

```bash
gh pr list --repo chris-dare-dev/derived-alg-geo-lean --state merged \
  --base main --search 'merged:2026-09-20..2026-10-02' --limit 500 \
  --json number,createdAt,mergedAt,mergeCommit
```

The query returns 222 PRs. For each path, count a pair when both PRs
changed it and their open-to-merge time intervals overlapped. The
CategoricalCohomology leaf has 30 such pairs (18 after excluding long-lived
PR #1619); TStructureCore has eight (one after excluding long-lived PR #1479).
The single-instantiation baseline has no overlapping pair among the three
matched PRs that touched it. These are opportunities for a shared-file
conflict, not evidence that Git actually reported one; direct main commits do
not contribute to this count. The high-touch
audit leaves, especially CategoricalCohomology, are the better candidates for
the follow-up audit cut after source-owner boundaries are checked. The
exception pilot below proves the record pattern on a smaller, safer surface;
it does not claim to eliminate those audit overlaps.

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
