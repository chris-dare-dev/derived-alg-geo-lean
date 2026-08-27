# Architecture audit — what shipped, what did not, and what was wrong

An adversarial architecture audit ran on 2026-08-26 against `3079d8a`: four
critics over the tree, each required to run a mathematical soundness gate and
drop any unification that would force a `sorry`. This note records what became
of each finding, including the ones that did not survive contact with the code.

The retractions are the point of the note. Five findings — four of them from the
critics, one of them mine — were confidently stated and turned out wrong or
overstated. They are recorded here with their disproofs so nobody re-proposes
them from the same evidence.

## Shipped

| finding | outcome |
| --- | --- |
| F01 `ClassDatum` at one instantiation | `heartDatum` written; the unification was `rfl`-level (#772) |
| F02 a second, hand-rolled Grothendieck group | `CoherentGrothendieckGroup` deleted for `K₀Ab (Coh X)` (#787) |
| F03 the axiom triple carried as data | `SlopeData` (#766), `NumericalData` (#784), `CoherentAdditiveInvariant` (#787) |
| F04 the dg layer has no consumer | `K₀dg` written (#773); see the retraction below |
| F05 `ReconstructionSystem` forked | one declaration, in neither lane (#790) |
| F06 `RealMukai` / `RealExtension` | one real quadratic extension (#793) |
| F07 a generic file under `Triangulated/` | 11 of 36 declarations moved (#817); see below |
| F08 dimension as tuple arity | `Fin (n+1) → ℤ` (#800); the formula half falsified, see below |
| F09 umbrellas omitting leaves | two written (#775), seventeen more plus a gate (#804) |
| F10 a live layering violation | file split, guard widened past its `CategoryTheory`-only test (#804) |
| F11 `strictImage` declared twice | one declaration (#819) |

Unaudited public declarations fell 1059 → 1027 over the numerical lane alone.
Three gates were added: umbrella coverage, widened subject layering, and
single-instantiation (#804, #809).

## Retracted, with the disproof

**`Enhancement` should be a `class`.** It should not. `dg-enhancements-e15` is
Canonaco--Neeman--Stellari uniqueness — a statement about *two inhabitants* of
`Enhancement T`. A class cannot express that: instance resolution picks one, and
a theorem proved that way is about *some* enhancement, which is the ambiguity
e15 exists to study. An enhancement is data, not a property. The audit engaged
with the Lean mechanism and not the mathematics.

**`Foundation/Slicing.lean` is a broken umbrella.** It is not an umbrella. It
declares `structure Slicing` and `structure HNFiltration` plus seven theorems,
and `Foundation/Slicing/` holds theorems *about* them. Re-exporting its children
would invert the dependency. A module sharing a name with a directory of its
consequences is the ordinary Mathlib shape.

**The Chern-character formulas unify across dimension.** They do not.
`Fourfold/LinearSection.lean:54` already recorded that the `7/12` and `-3/2` in
entries 3 and 4 "do not follow the threefold pattern". The `/d` normalisation
sits in the top slot, so "entry 3" denotes different things in dimension 3 and
4. Independently: `SurfaceNum` is shared by `ProjectivePlane.lean` and
`Abelian.lean` with *different* formulas, so these were never
one-formula-per-dimension types. Parked as `numerical-k-theory-e5`; the type
half shipped as e6.

**F07's file is generic.** Only 11 of its 36 declarations were.
`StabilityFunctionOn` and `WeakStabilityFunctionOn` have generic signatures and
54 extension declarations in `CategoryTheory.Triangulated.*` — `IsSemistable`,
`IsStable`, `charge`, `slope`. Moving the structures orphans all 54, and
`CategoryTheory.WeakStabilityFunctionOn.IsSemistable` is worse naming than what
was there. Generic in signature, specific in theory.

**F12: `Foundation/Deformation` is a dumping ground, 22% of it off-topic.**
Not reproduced. Measured 2026-08-27: **one file of 43, 156 lines of 12,074 — 1%**
— never mentions deformation. The other three claims in the finding hold exactly
(43 files and 12,074 lines; four `PhiPlus*` files totalling 1,092 lines for a
`phiPlus` defined in `Foundation/StabilityFunction/` and `Metric/Distance/`, not
here; `LocalSurjectivity` at 71 lines and one declaration beside
`LocalInjectivity` at 720 and twelve). What survives is a naming inconsistency
and an unfinished half, not a placement defect. **Do not schedule F12 as
written.**

## The pattern in the retractions

Four of the five were stated by critics that never ran the code; the fifth was
mine. Each was found by going and looking — building the thing, or counting the
thing, rather than reading about it. F12 in particular was the one finding never
independently checked before scheduling, and it is the one that did not survive
being checked.

Two of this session's own errors have the same shape and are recorded where they
happened: a single-line `grep` that missed a two-line signature and produced a
false claim in a merged docstring (#805), and a first-pass instantiation detector
that counted consumers as producers (#809). Both were caught by testing against
an answer known in advance.
