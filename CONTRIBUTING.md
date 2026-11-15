# Contributing to DerivedAlgGeo

[CREDO.md](CREDO.md) is one page on what this repository holds and what it
refuses. It overrides this file. Its "Not yet met" list names the rules that
are not in force yet; for those, this file still applies.

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`, whose layout follows
Mathlib's broad subjects and the APIs it directly extends. Do not add new top-level
libraries or restore retired repository roots; a new top-level subject must be
a Mathlib subject and is added to `scripts/check_layering.py` by name.

The placement rule has two tiers, stated in full in
[placement.md](docs/architecture/placement.md). The subject/application
boundaries and compact issue/PR decision record are maintained in
[mathematical-ownership.md](docs/architecture/mathematical-ownership.md).
`AGENTS.md`, which `CLAUDE.md` imports, summarizes the same rules for coding
agents.

1. **An extension of a Mathlib API lives at that API's Mathlib path**, under
   `DerivedAlgGeo/`, in that API's namespace. Derived categories, `Ext`, and
   K-projectives extend `Mathlib/Algebra/Homology/DerivedCategory/` and live in
   `Algebra/Homology/DerivedCategory/`; sheaves of modules on a ringed site
   extend `Mathlib/Algebra/Category/ModuleCat/Sheaf/` and live there; Čech
   cohomology on a site lives under `CategoryTheory/Sites/SheafCohomology/`;
   `PrimeSpectrum.basicOpen` lives under `RingTheory/Spectrum/Prime/`. Neither
   the abstraction level of a statement nor the weakest vocabulary in its
   signature moves it away from its carrier's definition site.
2. **A subject Mathlib lacks is placed by the nearest Mathlib precedent.** A
   structure on an abstract triangulated category goes under
   `CategoryTheory/Triangulated/<Name>/` like `TStructure/`; a weakened or
   strengthened variant of a named concept is a child directory named by its
   adjective, like `MetricSpace/Pseudo/`, so weak stability is
   `Triangulated/StabilityCondition/Weak/`; compatibility between two
   independent structures is `Monoidal/<Other>.lean` like
   `Monoidal/Preadditive.lean`; a geometric realization of a categorical
   interface lives with the geometric object under `AlgebraicGeometry/`, as
   `Algebra/Category/ModuleCat/Abelian.lean` lives with `ModuleCat`. Within
   this tier, identify the independently useful mathematical subject and use
   sufficient hypotheses to separate foundations from applications. Merely
   using a Mathlib carrier does not make a new concept a direct extension of
   its elementary API. Do not order subjects by their weakest vocabulary.

`AlgebraicGeometry/` is organized by geometric object and never mirrors
`CategoryTheory/`. Inside an object directory, files are named by the
structure they add:
`DerivedCategory/{Basic,Coherent,Dqc,Families,FourierMukai,Stability}`. The
`Stability/` child is the only part of `DerivedCategory/` that imports
stability conditions; the `DerivedCategory` umbrella omits it and the
`AlgebraicGeometry` umbrella imports it, so scheme-derived categories stay
importable without Bridgeland stability. Geometric semistable loci, probes,
finite-type openness, and relative HN filtrations live under
`AlgebraicGeometry/Moduli/`.

There are no `Instances/` directories below a generic subject. The former
`CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves are retired;
their contents live with the geometric objects they were about, and the
layering gate rejects any path of that shape.

Use Mathlib's established namespace when extending a Mathlib concept. A
declaration in a geometric file may keep the namespace of the categorical
structure it extends so that dot notation resolves. Add a same-named umbrella
for a new non-leaf directory and export stable leaves through their nearest
existing umbrellas. A neutral core may omit an application only with a
documented exact exception in the coverage gate and another stable export/build
route for that application. Check transitive imports through umbrellas.

The dependency contract is `docs/architecture/layers.md`: only
`AlgebraicGeometry/` and `Development/` import geometry, `Development/` is a
leaf, geometry outside the eight subcomponents that exist to consume stability
never reaches the stability tree, weak stability never imports Bridgeland
stability, and retired paths stay retired. Subjects are otherwise free to
import one another as they do in Mathlib. The stability exemption is named by
subcomponent, not by top-level subtree: `Moduli/PerfectComplex/`,
`Moduli/Quot/`, `Numerical/Core/`, `Numerical/Mukai/`,
`Numerical/RiemannRoch/` and `Numerical/Specializations/` are held neutral even
though their parents are not. A same-named umbrella over an exempt
subcomponent is exempt as an umbrella; its other children are not. Those are
still broad mechanical checks. The finer root/consumer boundaries in the
ownership policy remain review obligations until their own source cutovers add
focused checks; a green gate does not certify every placement decision.

Charge construction is one focused enforced boundary: paired-functional,
quadratic bounds and Hodge input live under `LinearAlgebra/`; additive charge
families and exponential/numerical/divisorial constructors live under
`CategoryTheory/Triangulated/StabilityCondition/CentralCharge/`; `Walls/`
contains the downstream loci, `Support/` the support predicates, and
`AlgebraicGeometry/Numerical/` the geometric realizations. The layering gate
checks these import closures and retired owner paths.

Derived-category theory is built once: Mathlib constructs `DerivedCategory C`,
this repository extends it under `Algebra/Homology/DerivedCategory/`, geometry
proves `Abelian (Coh X)` and defines `Dᵇ(Coh X)` as an abbreviation under
`AlgebraicGeometry/DerivedCategory/`. Keep the bounded-coherent and
compact/perfect identifications in `Dqc.lean` as explicit propositions, and
read the perfect-complex ledger in `docs/architecture/placement.md` before
relating perfect notions.

## Choose the common root before the leaf

Read [the canonical-root policy](docs/architecture/abstraction-tree.md) before
adding a public structure, class, quotient carrier, category, or parallel
presentation of an existing object.  The pull request must name the canonical
root and explain how the specialization projects or compares to it.

Keep three answers separate: which subject owns the declaration, which
modules it imports, and which Lean map connects its specialization to the
root. Comparisons import both presentations downstream; generic foundations
must not import their special cases to state their agreement. Charge
construction precedes walls, and general derived operations and perfectness
precede their Fourier–Mukai and moduli consumers. The ownership policy gives
the remaining subject examples and the hypotheses that a move must preserve.

Do not create a paper-specific or geometry-specific sibling of an existing
generic object.  In particular, use Mathlib's `Preadditive`/`Linear` hierarchy,
the repository's `GrothendieckPresentation` specializations, and the generic
site/descent stack roots.  When two presentations are independently useful,
prove their comparison and agreement instead of selecting one silently.  When
an apparent unification is mathematically false, record the obstruction and
keep the leaves separate.

## Proof and trust policy

Committed library code must not use `sorry`, `admit`, or hidden axioms. Explicit
mathematical hypotheses and structure fields are acceptable; proof holes are
not. Keep conditional geometry honest by recording the exact hypothesis that a
later realization must supply.

The axiom audit needs nothing from you. CI emits the compiled environment
(`exe/Emit.lean`) and `scripts/check_emission_coverage.py` fails when any
constant, private ones included, depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. No file lists declarations by hand.

Every gate script under `scripts/` prints through `scripts/_output.py`: a new
`scripts/check_*.py` must `from _output import force_utf8_output` and call
`force_utf8_output()` as the first statement of its `if __name__ == "__main__":`
block. While the self-hosted runners ran Windows (until 2026-09-21), their
console was cp1252, and a gate that printed a declaration name such as
`chi₂_eq` without this died with a `charmap` traceback instead of its finding
(#868, #869); any non-UTF-8 console still does. `python3 scripts/_output.py`
checks every script for the call and reproduces the crash to prove the helper
prevents it; it runs near the front of `scripts/gates.sh`, of
`scripts/precheck.sh`, and in CI.

## Where verification runs

**Full verification runs in CI, not on your machine.** Since 2026-09-19
`.github/workflows/ci.yml` triggers `push` on `main` alone, so **pushing an
agent branch is no longer a gate run — opening the pull request is.** The
`pull_request` lane runs the identical job set on `ubuntu-latest`, and over the
195 commits both lanes used to build it was the faster of the two (20.8 min
median against 40.2) as well as the one branch protection reads.

To run CI on a branch without a pull request, dispatch it by hand. The build
uses hosted Ubuntu:

```bash
gh workflow run ci.yml --ref <branch>
```

This is enforced rather than advised. A `PreToolUse` hook in the tracked
`.claude/settings.json` runs `scripts/check_local_build.py`, which refuses
`scripts/gates.sh` in any mode and refuses `lake build` with no target.
`DAG_ALLOW_LOCAL_BUILD=1` overrides it for one command; say so in the pull
request when you use it.

For a local pre-flight that the hook allows, run:

```bash
python3 -m venv .loop-tools
source .loop-tools/bin/activate
python -m pip install -r scripts/requirements-loop.txt
scripts/precheck.sh
```

Keep this environment activated for local precheck: the scripts invoke
`python3`, which will then resolve to the same environment that received the
parser dependency.

It runs every gate in `scripts/gates.sh` that needs no Lean build — workflows,
`--diff-only` style on your own lines, source-independence, layering, the
neutral derived-category Stability import closure, umbrella coverage, root
reachability, coherent families, coverage map, pin, nolints,
roadmap and tree areas — then a targeted `lake build` of the modules
you changed. About a minute plus that build, against twenty minutes or more for
CI. It is a cheap green, not a green: the
library build, the ratchets, the linters and the emitter's axiom audit all need
the library elaborated and run on the runners.

### Writing issues

The issue body is the specification of the work, so write it to be worked from
without asking. Use the [formalization issue template](.github/ISSUE_TEMPLATE/formalization.md);
an agent fills in a copy, deletes its front matter, and files it with
`gh issue create --title <title> --body-file <file>`, because
`gh issue create --body` ignores templates. Each field prevents a known
failure:

| Field | What it prevents |
| --- | --- |
| Outcome, first consumer, complete or progress | losing the big picture across PRs |
| Versioned source, theorem numbers, proof route, conventions | re-derived or invented routes, repeated unversioned fetches |
| API verified at the pin (path:line), or "absent at the pin" | guessed names |
| Each hypothesis load-bearing (with a witness) or weakenable | false "X fails" claims, over-hypothesis rounds |
| Placement tier, files, namespaces, shared files | refactor rounds, cross-issue coupling |
| Definition of done as named declarations, docstrings or gates | dropped acceptance items |
| Non-goals and trust boundaries | conclusions smuggled in as fields or hypotheses |
| Dependencies as issue numbers | misread blockers |
| Known traps | repeating a failed route |
| No process text | runs reverting to retired process |

Before filing, check that dependencies
resolve to issue numbers, every path and name the issue cites exists at the pin
(or is marked absent), and the placement agrees with
`docs/architecture/placement.md`. The filing agent does this, not the owner.

On a roadmap-owned milestone, a new issue needs its `.claude/roadmap/*.yaml`
entry, and a native blocked-by link must match its entry's `blocked_by`. CI's
`roadmap` job reads the live tracker (RM-05, RM-06) and fails every open pull
request until the two agree, so open the roadmap PR immediately after filing
or linking, and merge it first.

Labels gate nothing. `blocked` follows the blocked-by links;
`research` means the first deliverable is a written verdict in the issue
thread; `in-progress` expires when no PR is open.

A milestone description carries the context its issues share. Paste this and
fill it in:

```markdown
**Goal.** <What exists when this milestone closes, and its first consumer; or
"foundational vocabulary: nothing is blocked on it".>

**Source.** <Versioned reference(s), sections and theorem range, conventions
every issue shares.> Pins: the Mathlib revision in `lake-manifest.json`.

**Roadmap.** `.claude/roadmap/<file>.yaml`, entry `<id>` (or "none").

**Issues.** GitHub blocked-by links decide the order; this list only
summarises them.
1. #A <title>
2. #B <title>: needs #A
3. #C <title>: independent of #B
Shared files: `<umbrella>` is created by #A; later issues append.

**Out of scope.** <Each excluded result, and where it lives or why it cannot be
done at the pin.>

**Traps for every issue here.** <Shared conventions, false routes, hypotheses
that look droppable but are not.>

**Done when.** <All issues closed, plus any milestone-level statement.>

**State.** Not kept here; the issues and their pull requests hold it. Put no
dated baselines, SHAs or "run X before Y" instructions in this description.
```

Issue closure for code work requires a merged PR.

This section previously read "Build the stable root while developing:
`lake build`", and told you to run the fast gate before review and the full gate
before merge. All three instructions are withdrawn. `CLAUDE.md` was corrected
first, in `c91374a`, and this file was left behind — so for a while the two
disagreed about the most basic question a contributor asks. AGENTS.md
§"Required verification" (which `CLAUDE.md` imports) is the fuller statement;
this is the short form.

## Local workflow

Build only what you changed, and probe freely:

```bash
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
lake env lean scratch.lean
```

`lake env lean` on a scratch file is deliberately unrestricted: it is the
seconds-long probe interactive proof work depends on, and a push per attempt
would make writing a lemma impractical.

`scripts/gates.sh` remains the readable list of what is checked — read it, with
the caveat in the next section that it is neither a subset nor a superset of CI
— but let the runners run it. Reading it is allowed: the hook refuses running
the file, not `cat`, `grep`, `diff` or `git ls-tree` over it.

The full gate includes:

- Mathlib-style and environment linting for `DerivedAlgGeo`, including the
  `scripts/style-baseline.json` ratchet;
- source-independence, pin, paper-coverage, and no-lint checks;
- roadmap/tracker agreement, when `gh` is available;
- the repository-wide emission, its module coverage and its axiom allowlist.

**Neither list contains the other.** This file used to say the containment ran
one way — "every gate in the script also runs in CI" — and that was false in
both directions.

CI has what the script does not: the `Contract gates` step runs the `mfc`
contract tooling — `validate`, `env`, `bundle`, `lint`, and
`check-ilean-coverage` against the pinned registry — from a virtualenv it builds
per run, and the script reproduces none of it. Expect to learn about those
failures from CI. A green `scripts/gates.sh` is not a green CI.

The script has gates `ci.yml` does not:

| Gate | Why it is not in `ci.yml` |
| --- | --- |
| `workflows` | a workflow too invalid to parse is too invalid to run the job that would check it |
| `mathlib-style` | **only partly.** Its `--self-test` fixtures and its `--check-baseline` ratchet both run in `ci.yml`; what stays local is the `--diff-only` pass over the branch diff, which is a pre-push linter by design |
| `emit-build` | runs in `cache-warm.yml` instead; linking is expensive on a cold tree |

`scripts/precheck.sh` runs the first two. A summary sentence that claims
coverage the files do not have hides a gate that runs nowhere, so verify the
list before citing it.

## Emitter sources

Local precheck and CI run `emission-sources` (tracked obligations, sweep
imports, and emitter eligibility using pinned Lean's header parser). It is a
source check; the emitted artifact and axiom verdict still require CI. Keep
permanent probes in Development with its verification export route.

## Documentation

Module docstrings should explain the mathematical statement, assumptions,
conventions, and relationship to surrounding APIs. Avoid provenance language
such as “the old CohLean version”; Git already records that history. The
same holds for names and comments: no issue or pull-request numbers and no
dates.

Prose in the tree is limited to the files `CREDO.md` lists. Reviews, handoffs
and change proposals go in the issue or the pull request,
not in a file. Architecture notes and decision records are moving to the wiki.
Until `CREDO.md` drops that line from "Not yet met", change
`docs/architecture/` and `.claude/decisions/` only in the pull request that
changes the code they describe; a decision with no code yet stays in its
issue.

Build generated API documentation through the nested package:

```bash
cd docbuild
lake build DerivedAlgGeo:docs
```

## Changes that move declarations

Structural changes must update imports, umbrellas, audit names, registry
bindings, source-independence checks, documentation, and CI paths in the same
change. A move is complete only when CI passes on the pushed branch from a clean
checkout — not when a local `scripts/gates.sh` goes green, which is neither
permitted here nor sufficient.

Mark completed and newly confirmed ownership defects in
`docs/architecture/cutover-ledger.md`. Do not use the ledger as an exception:
new declarations must go directly to their canonical owner.

Identify each path as current, confirmed target or proposed split. Use the
existing root until its coordinated cutover; do not add a competing root at
the proposed destination. Update affected issue path contracts and keep
GitHub milestone membership, native dependencies and roadmap entries in
agreement. A source-implementation issue stays open when only its policy or
plan has been documented.

The ledger's "agreed owners and cutover map" section settles the destination of
every confirmed 2026-09-13 ownership finding at declaration granularity. If you
are moving code that appears there, the destination is already agreed and the
pull request implements it; if you are moving code that does not, add the row
rather than inventing a destination in the pull request description. Two rules
in that section bind every structural change: paths move while fully qualified
declaration names stay, and a proposed new carrier needs a consumer outside the
module it was extracted from or it is replaced by a theorem or an `abbrev`.

Repository documents are the canonical record of these practices. GitHub
Discussions can propose changes or explain a decision; link the versioned
policy there rather than maintaining a second, divergent rulebook.
