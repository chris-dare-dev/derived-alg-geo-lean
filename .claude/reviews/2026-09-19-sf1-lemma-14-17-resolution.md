# SF1 Lemma 14.17 resolution, and the §14 coverage promotion

Date: 2026-09-19

Source: arXiv:1902.08184v4, pinned by `registry/coverage-1902.08184v4.json`

Scope: the two open source-fidelity findings of
`.claude/reviews/2026-08-14-sf1-source-closeout.md`, which this review
supersedes for Lemma 14.17. Sections 14.1 through 14.2 re-read directly from
the pinned artifact; §14.3 remains out of scope and out of the epic.

## Verdict

**PROMOTE `sec-14-weak-stability-tilting` from `mapped` to `reviewed`.**

The 2026-08-14 closeout withheld promotion because `IsPhaseTiltTypeTwo` carried
two fields absent from the printed case (2) of Lemma 14.17. That review treated
them as one finding. They are two findings with opposite resolutions, and both
are now resolved:

- the phase-free field was a genuine over-strengthening; it is derived and
  removed (resolution 1, code merged);
- the Hom-vanishing implication is load-bearing; the printed statement is false
  without it (resolution 2, owner accepted).

This promotes to `reviewed`, not `formalized`. `formalized` additionally
requires `evidence.owner_accepted` in the entry and is not claimed here.

## What the printed lemma says

Lemma 14.17, v4 page 74, case (2), verbatim:

> or ℑZ(E) < 0 and E is an extension
>
>     U[1] → E → V
>
> where U ∈ A is a Z-semistable object and V ∈ A₀; moreover, if either
> ℑZ^{♯β}(E) > 0 or E is Z^{♯β}-stable, then Hom(V′, E) = 0, for all V′ ∈ A⁰.

Definition 14.2, v4 page 71, is the decisive supporting text:

> μ_Z(E) := −ℜZ(E)/ℑZ(E) if ℑZ(E) > 0, and +∞ otherwise

with semistability defined as μ_Z(F) ⩽ μ_Z(E/F) for every proper subobject F.
`WeakStabilityFunction.slope`
(`Weak/Basic/Definitions.lean`) implements exactly this convention, returning
`⊤` when the imaginary part is not positive, so the arguments below transfer to
the Lean statements without a convention shift.

## Finding 1 (2026-08-14 §"Lemma 14.17", field 1): resolved by derivation

The printed case (2) asks only that `U` be a Z-semistable object of the original
heart. The free-class membership `phaseFree sigma.slicing beta U` was an extra
hypothesis, and it is automatic — from strictly less than the printed data,
since neither the semistability of `U` nor the zero charge of `V` is needed:

1. `E` lies in the tilted heart, so `E ∈ P((β, β+1])`
   (`phaseTiltHeart_interval`).
2. `V` lies in the original heart, so `V ∈ P((0, 1])` and `V[-1] ∈ P(⩽ 0)`,
   hence `V[-1] ∈ P(⩽ β+1)`.
3. Inverse rotation turns `U[1] → E → V` into `V[-1] → U[1] → E`, and the upper
   phase cut is closed under distinguished extensions
   (`Slicing.leProp_of_triangle`), so `U[1] ∈ P(⩽ β+1)`.
4. Shifting back gives `U ∈ P(⩽ β)`; with `U` in the heart that is exactly
   `U ∈ P((0, β]) = F^β`.

Recorded as `phaseFree_of_tiltHeart_triangle` in
`Weak/Tilting/Semistable/TiltedHeart.lean`. The field is gone from
`IsPhaseTiltTypeTwo`, and `isSemistable_of_isPhaseTiltTypeTwo` derives it from
its own standing hypotheses. Merged 2026-09-17 in PR #1383, squash commit
`2d66007c`.

## Finding 2 (2026-08-14 §"Lemma 14.17", field 2): resolved by reading

The 2026-08-14 review read the `moreover` clause as a conclusion drawn after an
already-established biconditional, and therefore read the Lean field as an
over-strengthening of the constructive direction. That reading makes the printed
lemma false.

Counterexample. Take `U ∈ F^β` Z-semistable with `φ(U) < β`, take `V ∈ A⁰`
nonzero, and set `E = U[1] ⊕ V`.

- `E ∈ A^{♯β}` and `Z^{♯β}(E) = Z^{♯β}(U[1]) ≠ 0`, so `E ∉ (A^{♯β})⁰`: the
  standing hypothesis of the lemma holds.
- `ℑZ(E) = −ℑZ(U) < 0`, and the split triangle `U[1] → E → V` has `U ∈ A`
  Z-semistable and `V ∈ A⁰`. So `E` satisfies printed case (2) literally.
- `θ = φ(U) + 1 − β < 1`, so `ℑZ^{♯β}(E) > 0` and `μ_{Z^{♯β}}(E/V) = μ(U[1])`
  is finite, while the subobject `V ⊆ E` has `μ_{Z^{♯β}}(V) = +∞` by
  Definition 14.2.
- Therefore `E` is not `Z^{♯β}`-semistable.

The `moreover` clause is what excludes this, so it belongs to the right-hand
side of the biconditional rather than after it. The Lean field

    0 < ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
      ∀ V0 : C, sigma.zeroCharge V0 → ∀ a : V0 ⟶ E, a = 0

carries only the `0 < ℑZ^{♯β}(E)` disjunct of the printed refinement hypothesis,
not the `or E is Z^{♯β}-stable` disjunct. That is the weaker of the two possible
hypotheses and is exactly enough to exclude the counterexample, so the rendering
is faithful and minimal rather than convenient.

**Owner disposition: accepted 2026-09-19.** This is resolution 2 of issue #208
("a source erratum/authoritative clarification establishes that the stronger RHS
is intended"), discharged on the counterexample above rather than on
correspondence with the authors.

## Findings carried forward unchanged

The 2026-08-14 review's other sections stand and are not re-litigated here:
Definitions 14.1–14.3, Definition 14.6 and the termination layer, display
(14.1), Definition 14.12, and Proposition 14.16, including the explicit
nonclaim that the literal statements of Lemmas 14.8 and 14.11 remain undeclared
and that downstream arguments consume explicit chain-termination hypotheses
instead.

## Two source defects worth recording

- v4 **omits the proof of Lemma 14.17**, citing [PT19, Lemma 2.19]
  ("Semistable objects can then be easily classified: we omit the proof"). The
  finding-1 derivation above is self-contained and does not depend on
  reconstructing that proof; any further obligation must be sourced from
  Piyaratne–Toda rather than from this paper.
- Case (2) writes `V ∈ A₀` while the `moreover` writes `V′ ∈ A⁰`. These are the
  same zero-charge subcategory of Definition 14.3; the subscript is a v4
  typography slip, not a second object.

## Epic exit criteria (#192)

| Criterion | Binding |
| --- | --- |
| Ordinary stability embeds into the weak structure | `StabilityFunction.toWeak`, `toWeak_Z` |
| Zero-charge subcategory closure properties | `zeroCharge_left`, `zeroCharge_right`, `zeroCharge_extension`, `zeroCharge_phaseTors`, `zeroCharge_mem_P_one` |
| HRS construction connected to the textbook heart | `tilt_heart_iff`, `phaseTiltHeart_iff_phaseShiftHeart` |
| Every theorem bound to a reviewed v4 coordinate | this review |
| No geometric substrate assumed or smuggled in | `check_layering.py`: weak stability is independent of, and structurally parented by, Bridgeland stability |

## Verification of the merged state

Run on the #1383 tree, whose content is on `main`:

- `lake build`: 5908 jobs, exit 0.
- `lake exe runLinter DerivedAlgGeo`: clean.
- `StabilityConditionAudit` + `check_audit.py`: 7035 declarations, all within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, count matching the
  registered commands.
- `check_audit_complete.py`, `check_single_instantiation.py`,
  `check_mathlib_style.py`, `check_layering.py`, `check_umbrella_coverage.py`,
  `check_root_reachability.py`: pass.

## Pages checked

- Page 71: Definitions 14.1–14.3, including the `μ = +∞` convention that
  finding 2 turns on.
- Page 72: Definition 14.6, Remark 14.7, Lemma 14.8, Remark 14.9, Lemma 14.11.
- Page 73: display (14.1), Definition 14.12, Remarks 14.14–14.15,
  Proposition 14.16, and the opening of Lemma 14.17.
- Page 74: Lemma 14.17 cases (1) and (2) with the `moreover` clause, and the
  proof of Proposition 14.16.
