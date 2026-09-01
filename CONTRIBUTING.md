# Contributing to DerivedAlgGeo

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`, whose layout mirrors
Mathlib's subject hierarchy directory for directory. Do not add new top-level
libraries or restore retired repository roots; a new top-level subject must be
a Mathlib subject and is added to `scripts/check_layering.py` by name.

The placement rule has two tiers, stated in full in
`docs/architecture/placement.md` and `CLAUDE.md`.

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
   this tier, the weakest vocabulary sufficient for the full public type is
   the tie-breaker.

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
existing umbrellas.

The dependency contract is `docs/architecture/layers.md`: only
`AlgebraicGeometry/` and `Development/` import geometry, `Development/` is a
leaf, geometry outside `Moduli/`, `Numerical/`, and
`DerivedCategory/Stability/` never reaches the stability tree, weak stability
never imports Bridgeland stability, and retired paths stay retired. Subjects
are otherwise free to import one another as they do in Mathlib.

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

Public declarations belong in the appropriate hand-maintained axiom audit:

- `scripts/AlgebraicGeometryAudit.lean`
- `scripts/StabilityConditionAudit.lean`
- `scripts/DGCategoryAudit.lean`

The completeness ratchet rejects growth in unaudited public declarations. When
the ratchet improves, lower its ceiling; never raise one to make a change pass.

## Where verification runs

**Full verification runs on the self-hosted Windows runners, not on your
machine.** `.github/workflows/ci.yml` routes `push` and `workflow_dispatch` to
`["self-hosted", "owner-win"]` and triggers on `agent/**`, so pushing an agent
branch already runs the whole gate there. For a verdict without pushing:

```bash
gh workflow run ci.yml --ref <branch>
```

This is enforced rather than advised. A `PreToolUse` hook in the tracked
`.claude/settings.json` runs `scripts/check_local_build.py`, which refuses
`scripts/gates.sh` in any mode and refuses `lake build` with no target.
`DAG_ALLOW_LOCAL_BUILD=1` overrides it for one command; say so in the pull
request when you use it.

This section previously read "Build the stable root while developing:
`lake build`", and told you to run the fast gate before review and the full gate
before merge. All three instructions are withdrawn. `CLAUDE.md` was corrected
first, in `c91374a`, and this file was left behind — so for a while the two
disagreed about the most basic question a contributor asks. `CLAUDE.md`
§"Required verification" is the fuller statement; this is the short form.

## Local workflow

Build only what you changed, and probe freely:

```bash
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
lake env lean scratch.lean
```

`lake env lean` on a scratch file is deliberately unrestricted: it is the
seconds-long probe interactive proof work depends on, and a push per attempt
would make writing a lemma impractical.

`scripts/gates.sh` remains the definition of what CI runs — read it to know what
will be checked — but let the runners run it.

The full gate includes:

- Mathlib-style and environment linting for `DerivedAlgGeo`;
- all three axiom audits and the audit-completeness ratchet;
- source-independence, pin, paper-coverage, and no-lint checks;
- roadmap/tracker agreement, when `gh` is available;
- repository-wide emission and `sorryAx` coverage checks.

**A green `scripts/gates.sh` is not a green CI.** The containment runs one way:
every gate in the script also runs in CI, but CI runs more than the script does.
CI's `Contract gates` step additionally runs the `mfc` contract tooling —
`validate`, `env`, `bundle`, `lint`, and `check-ilean-coverage` against the
pinned registry — from a virtualenv it builds per run, and the script does not
reproduce any of it. Expect to learn about those failures from CI.

This file previously called the script "the complete CI-equivalent gate". It was
not, and the difference is not academic: a roadmap entry left at `planned` after
its issue closed reddened CI on `main` and on every open pull request while
`scripts/gates.sh` stayed green on all of them. The `roadmap` gate above closes
that particular hole; the `mfc` steps remain CI-only.

For a focused audit run:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake env lean scripts/StabilityConditionAudit.lean \
  > /tmp/stability-condition-audit.txt 2>&1
python3 scripts/check_audit.py /tmp/stability-condition-audit.txt
```

## Documentation

Module docstrings should explain the mathematical statement, assumptions,
conventions, and relationship to surrounding APIs. Avoid provenance language
such as “the old CohLean version”; Git already records that history.

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
