# Abstraction audit — review handoff

Everything below is already in `main`. This is a post-merge handoff: what
landed, which judgement calls a reviewer should second-guess, and what went
wrong on the way.

Companion to `2026-08-27-architecture-audit-dispositions.md`, which records the
findings themselves. This one is about the review surface.

| | |
| --- | --- |
| unaudited AlgebraicGeometry declarations | 1059 → 1027 |
| Grothendieck group constructions | 2 → 1 |
| axiom triples in `AlgebraicGeometry` | 3 → 0 |
| gates | +3 |
| findings retracted on contact | 5 |

## 1. What landed

| PR | What | Effect |
| --- | --- | --- |
| 772 | `heartDatum` — the second `ClassDatum` instantiation | weak and strict stability become one structure at two data; the unification was `rfl`-level |
| 773 | `K₀dg` — Grothendieck group of a dg category | the dg layer's first downstream declaration |
| 775, 804 | umbrellas: two written, then seventeen gaps closed plus a gate | **104 declarations were outside the declaration sweep** |
| 783, 792, 799 | the `numerical-k-theory` track; e5 parked | 261 files that no roadmap owned |
| 784, 787, 790 | NK1 — invariants become homs, the second K-group deleted, the fork merged | 1059 → 1027 |
| 793, 800 | NK2 — one `RealExtension`; `Fin (n+1) → ℤ` | ~134 lines of additivity boilerplate → ~31 |
| 804, 809 | three gates: subject layering widened, umbrella coverage, single-instantiation | recurrence prevention |
| 817, 819 | F07 charge layer moved; F11 `strictImage` deduplicated | 11 declarations moved; 52 lines deleted |
| 778, 805, 827 | roadmap unblocked; a false docstring corrected; dispositions recorded | see §3, §4 |

## 2. Judgement calls to second-guess

These are the places where I chose and a reasonable reviewer could choose
otherwise. They are the review surface.

### The single-instantiation baseline is 45% of the generic tree

54 of 117 structures and classes in the generic subjects have at most one
inhabitant, so the gate is a baseline rather than a rule: the 54 are named, and
only a *new* name fails.

**This is the number to push back on.** If 45% is too permissive, the fix is not
a stricter threshold — it is working the list down, and each entry is a real
question about whether that abstraction earns its generality.

### Three heuristics that could be wrong

- **`GENERIC_SUBJECTS` excludes `AlgebraicGeometry`.** My call that a structure
  describing a particular geometric situation having one witness is normal rather
  than a smell. Widening it is a one-line change.
- **Theorems count as inhabitants.** Required for `Prop`-valued classes like
  `QuasiAbelian`, but it means a theorem whose conclusion heads a data structure
  would also count. I found none; I did not prove there are none.
- **"Declares nothing" identifies an umbrella.** This is why
  `Foundation/Slicing.lean` is correctly skipped. A genuinely empty
  umbrella-to-be would also be skipped.

### F07 moved 11 declarations of 36, and stopped

`StabilityFunctionOn` and `WeakStabilityFunctionOn` stayed under `Triangulated/`.
They have generic signatures and **54 extension declarations** — `IsSemistable`,
`IsStable`, `charge`, `slope` — in `CategoryTheory.Triangulated.*`. Moving the
structures orphans dot-notation on all 54, and
`CategoryTheory.WeakStabilityFunctionOn.IsSemistable` reads worse than what was
there. Generic in signature, specific in theory. If you disagree, the move is
mechanical but touches 54 audit records.

### The dg layer's two importers are fine

Both are non-mathematical — the umbrella re-export and the audit script. That is
the expected state at DG2: the epics that give the layer consumers (e9 the seam
theorem, e12/e13 transport) are planned mathematical work, not a refactor
waiting to happen.

## 3. Errors I made

Two reached `main`. Both have the same shape: a tool too weak for the claim,
trusted without a known-answer test.

**A false claim merged in a docstring.** I wrote that `QuasiAbelian` had no
instance and called it "checked". It has one,
`Slicing.intervalCat_quasiAbelian`. My grep matched one line at a time and the
instance carries its type on the next:

```lean
noncomputable instance Slicing.intervalCat_quasiAbelian (s : Slicing C) :
    QuasiAbelian (s.IntervalCat C a b) where
```

Corrected in #805, found while prototyping the inhabitant detector.

**The first inhabitant detector counted consumers as producers.** It reported
`def IsPositive (D : ClassDatum O G) : Prop` as an instantiation of
`ClassDatum`. Rewritten to read the elaborated environment and test the head of
the conclusion. Validating it against `QuasiAbelian` — an answer I already knew
— then caught a second bug: `Prop`-class instances are theorems, and I was
scanning definitions only.

**Three self-inflicted delays.** I invalidated a gate run by committing and
rebasing in the same worktree while it executed, then reported its failures as
real. I nearly force-pushed over a merged PR; `--force-with-lease` stopped it.
And I ran full local `gates.sh` for almost every change, which `CLAUDE.md` now
explicitly warns against — several agent lanes share one Mac, and concurrent
full gates turn a ten-minute run into an hour.

*For the next lane:* push the branch and let the Windows runners verify. Say
"N gates pass", not "CI is green".

## 4. Retracted findings

Recorded with disproofs in `2026-08-27-architecture-audit-dispositions.md`.

| Claim | Why it is wrong |
| --- | --- |
| `Enhancement` should be a `class` | uniqueness-of-enhancements is a statement about *two inhabitants*; a class cannot express it. An enhancement is data, not a property. |
| `Foundation/Slicing.lean` is a broken umbrella | it declares `Slicing` and `HNFiltration`; re-exporting its children inverts the dependency |
| Chern-character formulas unify across dimension | the repository's own docstring already said the fourfold terms do not follow the pattern; `SurfaceNum` carries different formulas for different surfaces |
| F07's file is generic | 11 of 36 declarations were |
| **F12: 22% of `Foundation/Deformation` is off-topic** | **1%** — one file of 43, 156 lines of 12,074 |

Four of the five came from critics that never ran the code. Every one was caught
by building or counting the thing rather than reading about it — and F12, the
only finding never independently checked before being queued, is the one that
did not survive checking.

## 5. What remains

**Nothing as cleanup.** The tree-level defects are fixed and three gates prevent
their recurrence. The three real continuations, in order of value:

1. **Work the 54-entry single-instantiation baseline down.** Each entry is an
   abstraction with at most one inhabitant that someone decided was acceptable.
   Some are statement layers; others may be the next `ClassDatum`. This is the
   disease itself rather than its symptoms, and the gate makes each decision
   explicit.
2. **`dg-enhancements` e9, e12, e13.** The seam theorem and transport are what
   give the dg layer consumers. Mathematical work, already on the roadmap.
3. **Two critic claims never verified** — a heart-construction duplication and a
   `Support/` fork. Spot-checks did *not* reproduce the second; the named
   declarations are not in either file. Treat both as unchecked, not
   outstanding.

**One gap I left.** #809's gate went red on `main` within hours of merging, on a
structure from a pull request already in flight. The gate worked; I shipped it
without a note telling in-flight authors what to do when it first fires at them.
Another session hit it and resolved it correctly, but that was luck rather than
design — worth fixing before the next baseline-style gate lands.
