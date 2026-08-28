# Working in DerivedAlgGeo

## Repository shape

This repository contains one public Lean library: `DerivedAlgGeo`. Its source
root is `DerivedAlgGeo/` and its all-library umbrella is `DerivedAlgGeo.lean`.
The layout follows Mathlib's subject hierarchy.

The principal areas are:

- `DerivedAlgGeo/AlgebraicGeometry/` for coherent sheaves, cohomology,
  divisors, duality, intersection theory, numerical geometry, and
  Riemann--Roch;
- `DerivedAlgGeo/CategoryTheory/DGCategory/` for dg-category theory;
- `DerivedAlgGeo/CategoryTheory/Triangulated/TStructure/` for t-structures;
- `DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/` for
  Bridgeland stability foundations and applications;
- `DerivedAlgGeo/LinearAlgebra/` for lattice and matrix prerequisites;
- `DerivedAlgGeo/Development/` for code intentionally excluded from the stable
  root.

Never add imports or namespaces rooted at `CohLean`, `DGLean`, or
`BridgelandStabLean`; those migration artifacts are retired.

## Editing rules

- Prefer the narrowest import and the nearest umbrella.
- Before introducing a public structure, class, quotient carrier, or category,
  follow `docs/architecture/abstraction-tree.md`: reuse one canonical root and
  make specializations reach it by an instance, projection, abbreviation, or
  proved comparison.
- Use Mathlib's namespace for extensions of an existing Mathlib API.
- Keep generic layers independent of specialized geometric applications.
- Preserve explicit trust boundaries; do not use `sorry`, `admit`, or a hidden
  axiom to cross an unfinished mathematical seam.
- Do not edit generated build artifacts by hand.
- Do not alter unrelated work in a dirty tree.

Read `CONTRIBUTING.md` before creating a new directory or publishing a
change; it owns the human-facing placement and contribution rules.

## Required verification

**Full verification runs on the self-hosted Windows runners, not on your machine.**
`.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]`, and it triggers on `agent/**`. So pushing an agent
branch already runs the whole gate there; to get a verdict without pushing, use

```bash
gh workflow run ci.yml --ref <branch>
```

**This is enforced, not advised.** A `PreToolUse` hook on `Bash`, wired in the
tracked `.claude/settings.json` so it reaches every worktree, runs
`scripts/check_local_build.py` and refuses two commands:

* `scripts/gates.sh`, in any mode;
* `lake build` with **no target**.

Advice was what this section used to give, and advice is what failed: on
2026-08-27 an agent read "the normal build stays local", ran a whole-library
`lake build` on a cold tree, and spent three hours of the developer's machine on
work the runners were idle and waiting to absorb.

`gates.sh` was already discouraged here for a second reason worth keeping: several
agent lanes share one Mac, Lake takes one core per job by default, and four
concurrent full gates oversubscribe a 14-core machine five times over — that is
how a ten-minute gate becomes an hour.

Neither the local script nor the runner lane is CI-equivalent on its own, and the
difference has bitten: every gate in `gates.sh` runs in CI, but CI also runs the
`mfc` contract tooling, which the script does not reproduce. Say "N gates pass",
not "CI is green". See `CONTRIBUTING.md`.

Build locally by **naming a target**, which the hook allows:

```bash
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
```

`LEAN_NUM_THREADS=2` limits Lake to two concurrent `lean` processes; without it
Lake takes one per core. It is set for every agent session in
`~/.claude/settings.json`, so a plain `lake build <Target>` is already capped —
set it explicitly if you are building from a shell that does not inherit that.

`lake env lean scratch.lean` is **not** restricted and is not meant to be. It is
the seconds-long probe interactive proof work depends on; routing each attempt at
a lemma through CI would be a ~12 minute round trip and would stop anyone writing
a proof at all.

### The olean asymmetry, and why the rule still stands

Lean's `.olean` files are platform-specific, so the Windows runners can never warm
this checkout: a local build is the only way to get local oleans, and a targeted
build still compiles its dependencies. **After a cache loss, naming a target does
not make the cost go away.** That is the honest limit of this rule, and the answer
is not to quietly run the whole-library build anyway — it is to take the verdict
from the runners, which need no local oleans at all:

```bash
gh workflow run ci.yml --ref <branch>
```

When a local build genuinely cannot be avoided, `DAG_ALLOW_LOCAL_BUILD=1`
overrides the hook for one command. **Using it is a reportable event**: say so in
the pull request or the session report, because a whole-library local build is
precisely what this rule exists to keep off the developer's machine.

Useful focused commands are:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake exe runLinter DerivedAlgGeo
lake exe lint-style
python3 scripts/check_source_independence.py
python3 scripts/check_coverage_map.py
```

New public declarations must be added to the relevant audit. The declaration
sweep in `scripts/EnumDecls.lean` and
`scripts/check_audit_complete.py` guards the opposite direction, so renames
must update both the source declaration and its audit record.

`DerivedAlgGeoSweep.lean` is verification-only. It imports the stable root and
development probes for full emitter coverage; do not treat it as a public
package boundary.
