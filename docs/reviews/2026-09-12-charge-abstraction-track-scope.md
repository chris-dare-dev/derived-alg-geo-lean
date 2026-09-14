# Scoping: a tracker milestone and issue series for the charge-abstraction work

This proposes how to turn the 2026-09-12 abstraction audit into tracked work. It
is a scope, not a change: no milestone, issue or roadmap file is created by this
document.

Read with `2026-09-12-abstraction-generalization-audit.md` (the audit),
`2026-09-12-abstraction-audit-critic.md` (what the audit got wrong), and
`2026-09-12-abstraction-audit-remediation.md` (the repairs and the revised PR
plan, whose slice numbering this reuses).

## 1. Why a new track rather than an extension of an existing one

`.claude/roadmap/numerical-k-theory.yaml` already owns the numerical lane, and it
contains the exact question this audit answers. Its fourth assumption reads:

> The fourfold numerical formulas admit the same uniform shape as the surface and
> threefold ones, so one indexed type covers all three.

It is marked **FALSIFIED 2026-08-27**, with the reason that the Chern-character
coefficients are not uniform in dimension, and `numerical-k-theory-e5` is parked
as a result.

That falsification is correct and this audit does not overturn it. What the audit
adds is the reason it was falsified: **dimension was the wrong index.** The
uniform object is the charge polynomial indexed by *truncation degree* `m`, and
the geometric transport carries the dimension `n` separately. The clearest
evidence is that the cubic-threefold tilt charge is `(n, m) = (3, 2)`: a family
indexed by dimension alone cannot state it, which is why every attempt to unify
`SurfaceNum`, `ThreefoldNum` and `FourfoldNum` by dimension failed.

So the relationship is: the new track **unparks** `numerical-k-theory-e5` by
changing its index, and should say so in its brief and link it. It does not
re-open the old assumption.

A separate track is right because the work is not confined to the numerical lane.
It spans `CategoryTheory/Triangulated/StabilityCondition/Walls/`,
`LinearAlgebra/Lattice/` and `LinearAlgebra/QuadraticForm/`, and
`AlgebraicGeometry/Numerical/`, and its acceptance conditions are about the shape
of the tree rather than about K-theory.

**Proposal: one new track, `.claude/roadmap/charge-abstraction.yaml`, slug
`charge-abstraction`.** The non-charge findings do not belong in it; section 6
places them.

## 2. The gate constraint that shapes everything below

`scripts/check_roadmap.py` enforces seven rules, and two of them bind here.

- **RM-06**: no live issue on a roadmap-owned milestone may go unreferenced by
  the roadmap. So the milestone, the issues, and the roadmap YAML entries must
  land **together**. Creating the issues first and writing the YAML afterwards
  reddens CI on `main` and on every open pull request in the interval. This is
  not hypothetical; `CONTRIBUTING.md` records it happening.
- **RM-07**: an entry's `status` must agree with its issue being open or closed,
  so entries start at `planned` and are advanced by the PR that closes them.

`RM-02`, `RM-03` and `RM-04` fix the shape: a `milestone` item carries
`gh_milestone`; an `epic` carries `gh_issue` plus `gh_sub_issues` that must equal
its GitHub children in both directions; a `task` is milestone-direct with no
GitHub parent.

**Therefore the first unit of work is one pull request** that creates the
milestone and issues and adds the roadmap file referencing them, verified with
`python3 scripts/check_roadmap.py --require-api` before it merges.

## 3. The milestones

Four, sequenced. The names follow the existing `NK1`/`SF1`/`DG3` convention.

### CA1 — One charge, indexed by truncation degree

The root lands and the existing leaves reach it. This is the milestone that pays
for the track: after it, a new dimension supplies a polarization and inherits the
charge instead of adding a polynomial.

Acceptance:

- `Wall.Exp.ofMoments` exists once and the surface, threefold and slope charges
  are proved equal to it at `m = 2, 3, 1`.
- The divisorial charge is a proved instance of the same kernel at the
  intersection-form moments, not a parallel definition.
- The `κ` slot has a real inhabitant: the transport at `√td` is proved equal to
  the existing Mukai charge on the rank-one slice, for any surface and with no K3
  hypothesis.
- `Δ_H` has exactly one owner. A grep for a second discriminant definition on
  H-degrees returns nothing.
- No declaration added by this milestone duplicates an existing one without a
  proved comparison theorem in the same pull request.
- Zero `sorry`. All gates green including `check_roadmap.py --require-api`.

### CA2 — The tilt node, and the rotation that was missing

Acceptance:

- `threefoldTruncate` exists and the `(3, 2)` tilt family is the existing surface
  family pulled back along it, with no new polynomial.
- The rotation is present and is proved to be the existing `phaseTiltRotation`,
  not a copy; walls are proved invariant under it and phases are proved not to
  be.
- Exactly one of the three candidate spellings of the tilt charge survives, with
  comparisons proved to the others or the others deleted.
- `Threefold.nu` is tied to the charge slope, and the `Threefold.nu` versus
  `BMT.nu` question is settled in writing.

### CA3 — The lattice root and the pairing bridge

Acceptance:

- `Lattice.pairCharge` exists and both the period-domain and exponential charges
  are proved to be it.
- `Mukai.Graded.pairing` at `n = 2` is a comparison theorem, never a second
  definition.
- The Mukai pairing is generalized over its coefficient ring in place; no new
  name is introduced.
- The two-consumer obligation for any new structure is answered in writing in the
  pull request, because `check_single_instantiation.py` does not scan these
  paths.

### CA4 — Noncommutative varieties

Entirely blocked today, and the milestone exists to hold that fact rather than to
schedule it. Acceptance is that each blocker is either discharged or recorded as
an external dependency with the statement it needs.

## 4. The issue series

`kind` is the roadmap kind. Sizes follow the existing files. Every entry starts
`status: planned`.

### CA1

| id | kind | title | size | blocked_by |
|---|---|---|---|---|
| `charge-abstraction-m1` | milestone | CA1 — One charge, indexed by truncation degree | — | — |
| `charge-abstraction-e1` | epic | The exponential charge kernel, with two inhabitants | M | — |
| `charge-abstraction-e2` | epic | The divisorial keystone reaches the kernel | M | e1 |
| `charge-abstraction-e3` | epic | The polarised transport, one map for every (n, m, κ) | L | e1 |
| `charge-abstraction-e4` | epic | The κ slot inhabited at √td | S | e3 |
| `charge-abstraction-e5` | epic | One discriminant owner, and the inert β dropped | M | — |
| `charge-abstraction-e6` | epic | The twist and its two real gaps | M | e1 |
| `charge-abstraction-e7` | epic | The fourfold layer, at zero polynomial cost | S | e3 |

Mapping to the remediation's slices: e1 is PR-1, e2 is PR-2, e3 is PR-6, e4 is
PR-6b, e5 is PR-4 together with PR-14, e6 is PR-5, e7 is PR-7.

e5 merges two slices deliberately. PR-14 generalizes the Mukai pairing in place
and PR-4 states the discriminant comparisons against it; splitting them would
land a discriminant statement against a root that does not yet accept the
coefficient ring it needs.

e6 carries the two real `sorry`s, an ℝ-side Vandermonde identity and a Cauchy
product. It is the only CA1 epic that contains unproved mathematics, so it should
be sequenced last within the milestone and may slip to CA2 without blocking
anything else.

### CA2

| id | kind | title | size | blocked_by |
|---|---|---|---|---|
| `charge-abstraction-m2` | milestone | CA2 — The tilt node, and the rotation that was missing | — | — |
| `charge-abstraction-e8` | epic | The charge-family rotation, as the existing tilt rotation | S | — |
| `charge-abstraction-e9` | epic | The tilt family by truncation, and ν | M | e8 |
| `charge-abstraction-e10` | epic | Adjudicate the three tilt spellings and the two ν | S | e3, e9 |

e8 and e9 are PR-8 split, because PR-8 proposes two files with different imports
and the second depends on the first. e10 is the open obligation the remediation
attached to whichever of PR-6 and PR-8 lands second; it is better as its own
issue than as a footnote on both.

Note for e8: the rotation file must not be merged into `Walls/ChargeFamily.lean`,
which today imports only Mathlib and must stay stability-neutral.

### CA3

| id | kind | title | size | blocked_by |
|---|---|---|---|---|
| `charge-abstraction-m3` | milestone | CA3 — The lattice root and the pairing bridge | — | — |
| `charge-abstraction-e11` | epic | The pairing bridge as theorems about the existing root | S | — |
| `charge-abstraction-e12` | epic | The lattice charge root | M | e11 |

e11 is PR-16 and e12 is PR-3. The order is deliberate and inverts the audit's:
PR-3 is blocked on a two-consumer obligation that PR-16 does not have, because
PR-16 states theorems about the root that already exists. Landing e11 first
either supplies e12's second consumer or demonstrates that e12 is not needed.

### CA4

| id | kind | title | size | blocked_by |
|---|---|---|---|---|
| `charge-abstraction-m4` | milestone | CA4 — Noncommutative varieties | — | — |
| `charge-abstraction-e13` | epic | Cubic threefold Ku(X), by the rotated tilt charge | L | e9 |
| `charge-abstraction-e14` | epic | Cubic fourfold Ku(X): the charge on the algebraic lattice | L | e12 |
| `charge-abstraction-e15` | epic | Cubic fourfold Ku(X): the period domain on the A₂ complement | L | e12 |

e14 and e15 are two issues and not one because they live on two different
lattices that are orthogonal complements for a very general cubic fourfold, so no
comparison theorem between them can exist. Filing them as one issue would invite
exactly the fusion the audit refuted.

All three carry external blockers. e13 needs the statement that the rotated
charge is a stability function on the tilted heart, which no repair proved and
which is not a wall-level fact. e14 and e15 need the Mukai lattice of the
component, its signature, and the `A₂` sublattice, none of which exist in the
tree. These belong in `blocked_by` as prose obligations, and the roadmap schema
supports recording them in the entry summary.

## 5. Sequencing

Four waves. Wave 0 is the tracking change itself.

0. The milestone, the issues and `charge-abstraction.yaml`, in one pull request,
   green under `check_roadmap.py --require-api`.
1. e1, then e2 and e3 in parallel, then e4 and e7. e5 and e8 are independent of
   all of these and can run alongside from the start.
2. e9, then e10. e6 whenever convenient.
3. e11, then e12.
4. CA4, if and only if its external obligations are discharged.

The critical path to the visible payoff is e1 → e3 → e7: after those three, a new
dimension costs one polarization.

## 6. Where the non-charge findings go

The audit produced 75 distinct findings. The charge track absorbs roughly a third
of them. The rest should not be forced into it.

- **Fourier–Mukai compositor transport.** The largest single cluster, 24 classes
  in a directory no lane had examined, and it includes one unbridged duplicate.
  It is not charge work. **Proposal: its own track**, or an epic on the existing
  `projective-families` track if that lane claims the convolution API. It also
  carries a negative result worth recording first: the pseudofunctor lane cannot
  own those classes.
- **Weak-stability and tilting duplication** (the ambient class datum, the
  `relativePhase` move, the fourth semistability copy). These belong to the
  existing `stability-families` track as epics.
- **Serre duality bridge and the coherent twist owner.** These belong to whichever
  track owns `AlgebraicGeometry/Duality/`; neither is charge work, and one is
  blocked on a bounded-versus-unbounded question that should be its own issue.
- **`Moduli/Semistability` restructure and the site-generic representation.**
  Low value, self-contained. File as `good first issue` candidates rather than
  epics. The second is CI-blocked: the move needs a second inhabitant or a
  baseline entry in the same change.

## 7. One issue that is not a slice

**A second-pass audit.** Coverage was 383 distinct files of 1053, and 75
directories were never examined. The first pass found its largest cluster in a
directory no lane had opened, which is evidence that the remainder is not empty.
The critic named the largest untouched ones: intersection theory, morphisms, the
slicing foundation, spectral sequences, and projective-spectrum modules.

This should be filed as a `type:spike` with a stated budget, not left as a
sentence in a report. Its scope is the complement of the 136 directories already
cited, and it should reuse the three-lens refutation shape, which killed 6 of 89
candidates and corrected many more.

## 8. What I would not do

- Do not file one issue per confirmed finding. Seventy-five issues on a tracker
  whose largest existing milestone holds four open items would bury the lane.
  The epics above each absorb several findings, and the reports remain the record.
- Do not open CA4 as actionable work. Every one of its three issues is blocked on
  something outside the tree, and an open unblockable issue trains people to
  ignore the tracker.
- Do not let the roadmap file lag the issues by even one merge. RM-06 is the rule
  that turns that lag into red CI for everyone.
