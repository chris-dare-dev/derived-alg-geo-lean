# Threefold gap analysis: Fano threefolds and threefolds of general type

Snapshot: 2026-09-20. Written against
`.claude/notes/2026-09-20-handoff-threefold-gap-analysis.md` (the task) and
the twelve milestones of `.claude/roadmap/exotic-stability-targets.yaml`
(merged to `main` as #1414, commit `2d81d45d`). Untracked working note
(`.claude/notes/` is in `.git/info/exclude`); a copy is force-added to the
branch `agent/roadmap-threefold-gap` beside the roadmap file it justifies.

**Method.** Repository substrate re-verified against `origin/main` at
`4bed5192`. Literature: arXiv abstract pages plus the *page images* of seven
papers read directly (list in §8). Two automated PDF summaries produced by the
fetch tool were flatly wrong (one said Schmidt blew up a *line*; one invented
a "Theorem 6.2" in Koseki), so **every number below was re-derived by hand
from the page images, and every quotation is from a page I read**. "Open"
below means "not found in the sources listed in §8", never "verified absent".
No sub-agents were fanned out; the deconfliction against the twelve
milestones in §5.6 is mine.

---

## 0. Verdicts

**Direction 6b, threefolds of general type: the gap the handoff expected is
closed, and what remains is not repository-shaped.**

- *Existence* of a Bridgeland stability condition on `Dᵇ(X)` for *every*
  smooth projective variety `X/ℂ` — general-type threefolds included — is
  **Chunyi Li, arXiv:2601.22994, Theorem 1.1 (30 January 2026)**, by
  restricting stability conditions from `ℙⁿ` along a closed embedding. Yiran
  Cheng gives a second proof for the `ℙⁿ` input (arXiv:2607.05344, 6 July
  2026). Laura Pertusi's survey (arXiv:2602.24016, Theorem 5.7) already
  records it as the state of the art.
- *The BMT double-tilt* is now known to exist on every smooth projective
  threefold for large `a`: **Cheng–Feyzbakhsh, arXiv:2607.04788, Theorem 1.2
  (6 July 2026)** identifies Li's induced heart with the double-tilted heart
  `(Coh(X)^{Z⁽¹⁾_b})^{Z⁽²⁾_{a,b}}` for `a > a(X,H)`, and Corollary 1.3
  derives a *twisted, weak* Bayer–Macrì–Toda inequality (coefficient `a²/2`,
  strict, Chern character twisted by `td(N_{X/ℙⁿ})⁻¹`). Their footnote 1 is
  explicit that the *strong* conjecture (BMT14 Conjecture 1.3.1, coefficient
  `1/18`, non-strict) is a different statement.
- What is still open on general-type threefolds is therefore: the strong BMT
  inequality per family (Koseki, arXiv:2008.09799 §1.3, states the
  `ch₃`-conjecture on hypersurfaces `X_d ⊂ ℙ⁴` is "solved only when
  `d ≤ 5`"; nothing I found moves that for `d ≥ 6`); the small-`α` region;
  and the global structure of `Stab`. Each needs sheaf-level tilt-stability
  or Clifford-type curve inequalities, none of which exists at the pin, and
  each is occupied by the people who built the tools (Feyzbakhsh, Koseki,
  Liu, Rekuski; Li; Cheng). **No R&D milestone and no Lean milestone.**

**Direction 6a, Fano threefolds: existence has been closed since 2017; the
"which Fano threefolds satisfy BMT" lead is real but mis-framed; one small
Lean milestone survives, and one low-odds R&D question.**

- Existence on *all* Fano threefolds is **Bernardara–Macrì–Schmidt–Zhao,
  arXiv:1607.08199, Theorem 1.1 (2016/17)**, for the polarization
  `H = −K_X/i_X`, by proving a *corrected* inequality with a curve class `Γ`;
  Li 2026 now covers every polarization.
- The handoff's framing "true in Picard rank 1, false in Picard rank 2, so
  classify by rank" is wrong in the invariant. `ℙ¹ × ℙ²` and
  `ℙ¹ × ℙ¹ × ℙ¹` have Picard rank 2 and 3 and satisfy the *original*
  inequality for *every* polarization (BMSZ Theorem 5.1). What kills the
  original inequality is a **divisorial contraction to a point**:
  Martinez–Schmidt(–Das), arXiv:1708.08567, Theorem 1.1. And there is "still
  no known counterexample in Picard rank one" (same paper, p. 2).
- The genuinely open question is BMSZ's own, §6: *what is the optimal
  correction class `Γ`, and does `Γ·H = 0` always suffice?* It has been
  quiet since 2018 and was reopened on the singular side in May 2026
  (Liu–Mao, arXiv:2605.13808). It is a numerical-feasibility question with a
  one-week kill, which is the only reason it gets a `could` entry.
- **The one thing that survives fully is Lean-shaped**: the repository's
  `BMTData` docstring says the inequality is false on `Bl_pt ℙ³` and cites
  Schmidt, but the library cannot *exhibit* that — it has no threefold model
  above Picard rank one. Schmidt's counterexample is four rational numbers
  and one quadratic form; BMSZ's correction on the same class is one more
  rational parameter. Both are pure arithmetic on a six-dimensional
  intersection ring. §5 has the complete data sheet; every number in it was
  checked by Hirzebruch–Riemann–Roch on six classes.

**Theorem A yields nothing on the ambient derived category of any threefold.**
On `Dᵇ(X)`, `S = (− ⊗ ω_X)[3]` acts on `K_num` by a scalar only when `ω_X`
is numerically trivial; then `ε = −1`, every `F` with `S(F) ≅ F[a]` has
`a = 3`, and `(−1)³ = ε`. Fano and general-type threefolds are not scalar
cases at all. On Kuznetsov components the test is already Candidate 3 of the
first scoping note, and Fan–Liu–Ma (arXiv:2310.16950) is the state of the art
there. §4.

**Relation to E6.** Everything here is about *compact* threefolds and the
numerical layer `Numerical/{Models,Examples}/Threefold/` plus `BMT.lean`. E6
is the non-compact `ω_Z`, and its Lean milestone is a lattice/transvection
substrate under `LinearAlgebra/` and `SphericalTwist/`. No file, root or name
is shared; see §5.6.

---

## 1. What changed since the handoff's priors

| Handoff belief (§6) | Finding | Source read |
|---|---|---|
| Existence on a general-type threefold "is open in general" | Closed for every smooth projective variety over `ℂ` | Li 2601.22994 Thm 1.1 (pp. 1–4 read) |
| "If Koseki's hypersurface work covers all degrees, `d ≥ 6` may be settled" | Koseki proves the *classical* strong Bogomolov–Gieseker bound (a `ch₂` bound for slope-semistable sheaves, Thm 1.2) on hypersurfaces of any degree; the `ch₃` conjecture on `X_d ⊂ ℙ⁴` is stated there as solved only for `d ≤ 5` | Koseki 2008.09799 §1.1, §1.3 (pp. 1–3 read) |
| BMSZ 1607.08199 "scope not confident" | Existence on all Fano threefolds via a `Γ`-corrected inequality, `H = −K/i_X`; original inequality for toric `X` with `H·D² ≥ 0` + extremality, in particular `ℙ¹×ℙ²`, `ℙ¹×ℙ¹×ℙ¹` for all `H`, `Bl_line ℙ³` for `ah+bf`, `a ≤ b`, *not* anticanonical | BMSZ pp. 1–4, 16–22 read |
| "Which Fano threefolds satisfy BMT: rank 1 done, one rank-2 counterexample" | Rank is the wrong invariant. Fails whenever an effective divisor `D` with `−D` `f`-ample contracts to a point, for *some* `H` (MSD Thm 1.1); holds on rank-2 and rank-3 products for all `H`; no counterexample in rank 1 | MSD 1708.08567 pp. 1–3 read |
| Sun's "some threefolds of general type" (1907.08379) | **Withdrawn** (v2, 2020-06-01: "temporarily withdrawn owing to a gap in the proof") | arXiv abstract page |
| Products of curves | Existence by Liu (Crelle 2021) by a non-BMT route; stability conditions on products of positive-genus curves are determined by central charge and the phase of skyscrapers (Li–Macrì–Perry–Stellari–Zhao 2512.14207); every stability condition is geometric when the Albanese map is finite (Fu–Li–Zhao 2103.07728) | abstracts |
| Weak vs strong BMT | Weak (`1/2`, strict, twisted) holds on every smooth projective threefold for large `a`; strong (`1/18`) open | Cheng–Feyzbakhsh 2607.04788 Cor 1.3 + footnote 1 (pp. 1–6 read) |
| Kuznetsov–Liu–Perry sequel on inducing stability conditions | Not found as of 2026-09-20 | searches only |

---

## 2. Direction 6b: threefolds of general type

### G1 — Existence of a Bridgeland stability condition

**Statement.** For every smooth projective threefold `X` of general type over
`ℂ`, `Stab(Dᵇ(X)) ≠ ∅`.

**Status: closed.** Li 2601.22994 Theorem 1.1: "Let `X` be a smooth
projective variety over `ℂ`. Then there exists a stability condition on
`Dᵇ(X)`." Proof strategy as stated on his p. 3: Liu's `σ^{a,b}` on `Eⁿ`
(`E` elliptic), invariance under `(ℤ/2)ⁿ ⋊ S_n` and the support property
from FLZ22 / LMP⁺25, descent to `ℙⁿ = Eⁿ/((ℤ/2)ⁿ ⋊ S_n)` (his Theorem 6.3),
then restriction along any closed embedding `ι : X ↪ ℙⁿ` provided the
`ℙⁿ`-stability condition has his *Bayer property* and *Restriction-N
property* (Theorem 6.5). He describes the Bayer property as "slightly
stronger than requiring all skyscraper sheaves to be stable". Cheng
2607.05344 reproves the `ℙⁿ` step.

**Collision.** Not applicable; done.

**Repository fit.** None. The construction is categorical (Polishchuk
induction along finite morphisms, families of t-structures); nothing at the
pin carries `Dᵇ(X)` for a threefold, let alone a finite-morphism induction.

**Verdict: neither.**

### G2 — Bayer–Macrì–Toda-type inequalities on general-type threefolds

**Precise statements, three strengths.** Fix `(X,H)` a smooth polarized
threefold; `ν_{α,β}` the tilt slope; `E ∈ Coh^β(X)` tilt-semistable with
`ν_{α,β}(E) = 0`.

- *Strong* (BMT14 Conj. 1.3.1): `ch₃^β(E) ≤ (α²/6)·H²·ch₁^β(E)`.
  Equivalently, for all `(α,β)` and all `ν_{α,β}`-semistable `E`,
  `Q_{α,β}(E) = α²Δ_H(E) + 4(H·ch₂^β)² − 6(H²·ch₁^β)(ch₃^β) ≥ 0`
  (Schmidt 1602.05055 Conjecture 2.2; this is the repository's `Threefold.Q`).
- *Corrected* (BMSZ Thm 1.1 / MSD Question 2.6): there is `Γ ∈ A₁(X)_ℚ`,
  depending at most on `H` and `B₀`, with `Γ·H ≥ 0`, such that
  `ch₃^β(E) ≤ Γ·ch₁^β(E) + (α²/6)·H²·ch₁^β(E)`. Quadratic form on BMSZ p. 3:
  `Q^Γ_{α,β}(E) = α²(Δ̄_H + 3(Γ·H/H³)(H³ch₀^β)²) + 2(Hch₂^β)(2Hch₂^β − 3Γ·H·ch₀^β) − 6(H²ch₁^β)(ch₃^β − Γ·ch₁^β) ≥ 0`.
- *Weak, twisted* (Cheng–Feyzbakhsh Cor. 1.3): with `c̃h^{bH} = e^{−bH}·td(N_{X/ℙⁿ})⁻¹·ch` and `a > a(X,H)`, if
  `H·c̃h₂^{bH}(E) = (a²/6)H³c̃h₀^{bH}(E)` then `c̃h₃^{bH}(E) < (a²/2)H²c̃h₁^{bH}(E)`.

**Status.** Strong: open for general type; known false for some non-Fano
threefolds (Weierstraß elliptic CY3 over a del Pezzo, MSD Thm 1.1; CY3
containing a plane, Koseki as reported by MSD p. 2). On `X_d ⊂ ℙ⁴` known for
`d ≤ 5` (Macrì `d=1`, Schmidt `d=2`, Li `d=3,4` via Picard rank 1 Fano,
Li 1810.03434 `d=5` in a *stronger* form), open for `d ≥ 6` (Koseki §1.3,
May 2022; nothing later found). Corrected: proved for Fano threefolds with
`H = −K/i_X` (BMSZ) and for singular Fanos (Liu–Mao 2605.13808 Thm 1.6);
open in general (MSD Question 2.6). Weak twisted: proved for every smooth
projective threefold, `a` large.

**Collision.** High and current: Cheng–Feyzbakhsh (July 2026) thank Bayer,
Li, Yucheng Liu, Zhiyu Liu, Thomas; FKLR (2509.24990) reduce the CY3 case to
Brill–Noether inequalities for curves and are the obvious group to try
general type next; Liu–Mao (May 2026) on the `Γ` form.

**Repository fit.** The *statements* fit: `Threefold.Q` exists, and the
corrected form is the same polynomial with one extra codimension-two class.
The *content* does not: tilt-semistability is an opaque field, and the
Clifford / Brill–Noether inputs are sheaf theory. A Lean milestone could only
ever carry the corrected polynomial and arithmetic on it, which is exactly
what §5 proposes on the Fano side, where a computed witness exists.

**Verdict: R&D no (occupied, long, not our tooling); Lean only through §5.**

### G3 — Structure of `Stab` on a general-type threefold

**Statement.** For which general-type threefolds is every stability condition
geometric; is the geometric chamber connected / contractible; what is the
component of the double-tilt conditions?

**Status.** Products of positive-genus curves: every stability condition is
geometric (FLZ 2103.07728, finite Albanese), and the stability condition is
determined by central charge plus skyscraper phase (LMPSZ 2512.14207).
Hypersurfaces and everything else: open. On `ℙ³` even contractibility of the
principal component is a stated conjecture (Wu–Zhang 2408.00519); Rekuski's
surface contractibility has no threefold analogue I could find.

**Collision.** Occupied (Li's real-reduction programme 2506.21995; LMPSZ).

**Repository fit.** The repository has a distance on `Stab` and the
`GLTilde` action, no manifold, no components (the exotic roadmap's `wont`
list already says so).

**Verdict: neither.**

---

## 3. Direction 6a: Fano threefolds

### F1 — Which Fano threefolds satisfy the *original* inequality, for which `H`?

**Statement.** For each of the 105 deformation families and each ample `H`:
does `Q_{α,β}(E) ≥ 0` hold for all `(α,β)` and all `ν_{α,β}`-semistable `E`?

**Known** (all read):

| `X`, `H` | original (`Γ = 0`) | source |
|---|---|---|
| Picard rank 1, any `H` | holds | Li 1510.04089 (cited by BMSZ p. 3 as `Γ = 0`) |
| `ℙ¹ × ℙ²`, every `H` | holds | BMSZ Thm 1.2 / 5.1 |
| `ℙ¹ × ℙ¹ × ℙ¹`, every `H` | holds | BMSZ p. 3, Thm 5.1 |
| `Bl_line ℙ³`, `H = ah + bf`, `a, b > 0`, `a ≤ b` | holds | BMSZ p. 16 |
| `Bl_line ℙ³`, `H = −K = 3h + f` | not covered | BMSZ p. 16 ("not covered by the above result") |
| threefolds with nef tangent bundle | holds | Koseki 1811.03267 (abstract) |
| `Bl_pt ℙ³`, `H = 2L − E = −K/2` | **fails** on `O(L)` | Schmidt 1602.05055 Thm 3.1 |
| any `X` with `f : X → Y` birational, `D` effective, `−D` `f`-ample, `f(D)` a point | **fails** on `O_D`, for *some* `H` | MSD Thm 1.1 |

MSD's hypothesis is "very weak, and such a divisor exists for any birational
divisorial contraction, where `Y` is normal and `ℚ`-factorial" (their p. 2),
so every Fano threefold obtained by blowing up a point, and more, fails for
some polarization. What is *not* in print: a per-family, per-polarization
table, or a conjectured characterization (e.g. "fails for `H` iff …").

**Collision.** Schmidt, Martinez, Piyaratne 2016–2018; quiet since; the
2025 ResearchGate item "Bridgeland Stability Conditions on Fano Threefolds:
Extended Study and Perspectives" cites an arXiv id (2509.06045) that resolves
to an unrelated statistics paper and I could not locate the preprint it
claims to extend — treat that item as unreliable.

**Repository fit.** The library *asserts* the failure in a docstring and
cannot exhibit it. Filling that is §5.

**Verdict: R&D neither (a table nobody is asking for, whose interest was
removed by the corrected inequality); Lean yes, §5.**

### F2 — The optimal correction class, and whether `Γ·H = 0` suffices

**Statement (open, with quantifiers).** Does there exist a smooth projective
threefold `X` with ample `H` such that for every `Γ ∈ A₁(X)_ℚ` with
`Γ·H = 0` there are `(α,β)` and a `ν_{α,β}`-semistable `E` with
`ν_{α,β}(E) = 0` and `ch₃^β(E) − Γ·ch₁^β(E) − (α²/6)H²ch₁^β(E) > 0`?
(Equivalently: is BMSZ's remark "a condition that is coherent with the case
of Picard rank 1 would be `Γ·H = 0`", p. 21, ever violated?)

**Status.** Open. BMSZ Thm 1.1 produces `Γ` with `Γ·H ≥ 0` for Fano `X`,
`H = −K/i_X`; their Prop. 6.1 checks *line bundles and `O_e` only* on
`Bl_pt ℙ³` with `Γ = k(h² + 2e²)`, `1/48 ≤ k ≤ 3/98 + 2√2/147`, `Γ·H = 0`;
BMSZ p. 3: "all known counter-examples … do satisfy a stronger inequality
for some choice of `Γ` with `Γ·H = 0`". MSD Question 2.6 asks for `Γ·H ≥ 0`
on every threefold. Pertusi p. 24 says a more general conjectural form is
Bayer–Macrì ICM 2023 Conjecture 4.7, which I have **not** read (§6).

**Why it is the one live question with a repository shape.** A *negative*
answer is a finite certificate: finitely many objects whose tilt-stability
is proved (line bundles at large `α`, structure sheaves of contracted
divisors, Schmidt-style nested-wall arguments) and whose constraints
`Q^Γ ≥ 0` are jointly infeasible in `Γ` on the hyperplane `Γ·H = 0`. That is
linear-quadratic feasibility in the Picard-rank-many coordinates of `Γ`, and
its certificate is arithmetic the library can check. A *positive* answer for
a given `X` is a theorem about all objects and is not ours.

**Collision.** Moderate: nobody has written on the smooth case since 2018;
Liu–Mao (May 2026) is on the singular case with the `Γ` form and would be
the natural group to return. BM23 Conj. 4.7 may already fix the shape.

**Repository fit.** Only downstream of a certificate. Nothing to formalize
until the R&D half produces one.

**Verdict: R&D `could`, size S, lane later, one-week kill; Lean gated.**

### F3 — Kuznetsov components of Fano threefolds

Already claimed by Candidate 3 of the first scoping note (the `ε`-table
includes `Ku(cubic)` and `Ku(GM)`); the current state of the art there is
Fan–Liu–Ma 2310.16950 (Serre-invariant iff homological dimension `≤ 2`;
Serre-invariant conditions form a contractible component, for cubic
threefolds, quartic double solids, GM threefolds). For Picard rank `≥ 2`
Fano threefolds I could not verify a single source enumerating the
semiorthogonal decompositions of all 88 families (Kuznetsov 0809.0225 is
Picard number 1 only); the one family I checked (Fanography 2-35,
`Bl_pt ℙ³`) has a full exceptional collection, so there is no residual
category to test. **Verdict: nothing additional to Candidate 3.**

---

## 4. Theorem A on threefolds: a computed negative

Theorem A (net-new-results note) needs `S` to act on `Λ = K_num` by
`ε·id`, `ε ∈ {±1}`, and one `F ≠ 0` with `S(F) ≅ F[a]`, `(−1)^a ≠ ε`.

- `Dᵇ(X)`, `X` a smooth projective threefold: `S = (− ⊗ ω_X)[3]`, so
  `S_* = −(− ⊗ ω_X)_*` on `K_num`. This is a scalar iff `ω_X` is numerically
  trivial. **Fano and general-type threefolds are excluded at the first
  hypothesis.**
- `ω_X ≡ 0` (Calabi–Yau, or torsion canonical class): `ε = −1`. If
  `S(F) ≅ F[a]` then `F ⊗ ω_X ≅ F[a − 3]`; comparing cohomology sheaves,
  the set of `i` with `H^i(F) ≠ 0` is invariant under translation by `a − 3`,
  so boundedness forces `a = 3` and `(−1)³ = ε`. **No obstruction, as it
  must be**: BMS16 construct stability conditions on abelian threefolds and
  some quotients.
- Kuznetsov components: Candidate 3, unchanged.

So the `ε`-form of Theorem A has no threefold application outside the table
Candidate 3 already owns. Recorded so the next session does not re-run it.

---

## 5. The Lean milestone that survives: a rank-two threefold model with Schmidt's certificate

### 5.1 Substrate, re-verified on `origin/main` (`4bed5192`)

All paths in the handoff's §4 exist. The threefold layer is: three models
(`Models/Threefold/{ProjectiveSpace,LinearSection,CalabiYau}.lean`, all
built on the *monogenic* ring `ℚ[t]/(t⁴)`), two demonstrations
(`Examples/Threefold/{ProjectiveSpaceWalls,CalabiYauWalls}.lean`), the
`(α,β)` numerical class and charge
(`CentralCharge/Numerical/Threefold.lean`), the wall/tilt layer
(`Walls/Threefold/{Basic,Tilt,TiltComparison}.lean`), the transport
(`Stability/{ThreefoldWallTransport,ThreefoldTiltTransport}.lean`), and
`Stability/BMT.lean` with `Threefold.Q`, `Threefold.nu`, `discrHBeta`
(β-inert, proved) and `BMTData` (supplied, uninhabited, documented as
false in general). The only inhabitant anywhere is
`ProjectiveSpaceWalls.p3BMTSanity`, whose `TiltSemistable` is *defined* as
the conclusion.

`MonogenicRing.lean`'s own docstring is the reason the gap exists: "for
`n ≥ 3` the rank of `N¹(X)` says nothing about `N²(X)`… a model built here
is therefore not licensed by exhibiting a variety of Picard rank one."
There is no threefold ring in the library with `dim A² > 1`. `Bl_pt ℙ³` has
`dim A¹ = dim A² = 2`.

### 5.2 Data sheet (every line checked by hand)

Ring `A = ℚ⟨1, L, E, L², E², pt⟩`, graded `0,1,1,2,2,3`, with
`L·E = 0`, `L·L = L²`, `E·E = E²`, `L·L² = pt`, `E·E² = pt`,
`L·E² = E·L² = 0`, degree `pt ↦ 1`. (As a quotient: `ℚ[L,E]/(LE, L³ − E³, L⁴)`.)
The bespoke six-field carrier of `Examples/Surface/BlowUpPlane.lean`'s kind
is the right implementation; the docstring there explains why the
nested-dual-number trick does not extend, and the same holds here.

Canonical class and Todd class (supplied, then checked):
`K = −4L + 2E`, `c₂ = 6L²` (the point blow-up does not change `c₂` on a
threefold), so
`td = 1 + (2L − E) + ((11/6)L² + (1/3)E²) + pt`, and
`∫td₃ = c₁c₂/24 = 24/24 = 1 = χ(O_X)`.

Polarization: `H = 2L − E = −K/2`. `H³ = 8 − 1 = 7`, `H²·L = 4`,
`H·L² = 2`, `H·E² = −1`, `H²·E = 1` (from `E³ = 1`, `L·E = 0`).

Lattice: six classes in linear-section style, so that `χ` is integral by
construction as in `Models/Threefold/LinearSection.lean`:

| class | `ch` | `χ` (HRR, checked) |
|---|---|---|
| `[O_X]` | `1` | `1` |
| `[O_L]` (pulled-back plane) | `L − L²/2 + L³/6` | `11/6 − 1 + 1/6 = 1` |
| `[O_E]` (`E ≅ ℙ²`) | `E − E²/2 + pt/6` | `1/3 + 1/2 + 1/6 = 1` |
| `[O_ℓ]` (pulled-back line) | `L² − pt` | `2 − 1 = 1` |
| `[O_m]` (line in `E`) | `−E²` | `−E²·(2L − E) = E³ = 1` |
| `[O_pt]` | `pt` | `1` |

(`ch₃(O_C) = χ(O_C) + K·C/2` for a smooth curve `C`; `K·ℓ = −4`,
`K·m = 2E·m = −2`, giving `−1` and `0`.) Two further checks:
`χ(O(L)) = 1/6 + 1 + 11/6 + 1 = 4` and `χ(O(−E)) = 1 − 1/6 − 1/2 − 1/3 = 0`.
The Chern characters are triangular with unit diagonal against the ring
basis, so the six classes are a `ℚ`-basis of `A`; that they generate
`K_num` over `ℤ` is supplied, exactly as `LinearSection.lean` supplies it.

Schmidt's class: `[O(L)] = [O_X] + [O_L] + [O_ℓ] + [O_pt]`, transported to
the four-coordinate class `(∫H³ch₀, ∫H²ch₁, ∫H·ch₂, ∫ch₃) = (7, 4, 1, 1/6)`.
Then `Δ_H = 16 − 14 = 2`, `H²ch₁^β = 4 − 7β`,
`H·ch₂^β = 1 − 4β + (7/2)β²`, `ch₃^β = 1/6 − β + 2β² − (7/6)β³`, and

```
Q_{α,β}(O(L)) = 2α² + 2β² − β,
```

which is Schmidt's `α² + (β − 1/4)² ≥ 1/16` after dividing by 2 and
completing the square. At `(α, β) = (1/8, 1/4)` it equals `−3/32`.

BMSZ's correction on the same class. With `Γ = k(L² + 2E²)`:
`Γ·H = 2k − 2k = 0` and `Γ·L = k`, so on `O(L)` the corrected form
collapses to `Q^Γ = Q + 6(H²ch₁^β)(Γ·ch₁^β) = Q + 6(4 − 7β)k`, i.e.

```
Q^Γ_{α,β}(O(L)) = 2α² + 2β² − (1 + 42k)β + 24k,
```

nonnegative on the whole half-plane iff `1764k² − 108k + 1 ≤ 0`, i.e.
`k ∈ [(9 − 4√2)/294, (9 + 4√2)/294] ≈ [0.0114, 0.0499]`. **The upper
endpoint is exactly BMSZ's `3/98 + 2√2/147`** (Prop. 6.1). I did not expect
that and have not explained it (Prop. 6.1 is about the linear inequality at
`ν = 0` for `O(mh)`, `m ≤ 0`, on a hyperbola; this is the quadratic form on
one class over the whole plane). The lower endpoints differ because BMSZ's
`1/48` comes from other objects. In Lean the statement needs no irrational:
for `k : ℚ`, `(∀ α β, Q^Γ ≥ 0) ↔ 1764k² − 108k + 1 ≤ 0`.

### 5.3 What the milestone proves, and what it supplies

Proved (arithmetic, no geometry):

1. the ring, grading, degree map, Chern/Todd data and `SatisfiesHRR` for
   the six-class lattice;
2. the four transported degrees of every class, in the style of
   `p3_toNumClass_deg*`;
3. `Q_{α,β}(v) = 2α² + 2β² − β` for Schmidt's class `v`, and
   `Q_{1/8,1/4}(v) = −3/32 < 0`;
4. hence, for every `B : BMTData V P` (the *existing* structure, untouched):
   `¬ B.TiltSemistable (1/8) (1/4) v` — **any inhabitant of the supplied
   datum on this model must declare Schmidt's class tilt-unstable at a
   point where Schmidt proves the line bundle is tilt-stable.** This is the
   "supplied-and-false" status of `BMTData` as a theorem instead of a
   docstring, and it is the only honest way the library can say it;
5. the corrected quantity `Q^Γ` (new definition in `BMT.lean`, one extra
   codimension-two class with a `Γ·H ≥ 0` hypothesis where the literature
   has it), `Q^Γ` at `Γ = 0` is `Q` (rfl or `simp`), and the interval
   theorem of §5.2 on Schmidt's class.

Supplied, as explicit hypotheses or docstring-only:

- the identification of the carrier with `Bl_pt ℙ³` (no scheme-level
  blow-up exists; same status as `BlowUpPlane.lean`);
- that `O(L)` is `ν_{α,β}`-stable at some point of the open disc
  `α² + (β − 1/4)² < 1/16` (Schmidt Thm 3.1). Theorem 4 above is stated
  at one point and is insensitive to which point Schmidt's argument
  actually certifies; the docstring must say so;
- that `K_num` is generated by the six structure sheaves.

Also in scope, because it is overdue: **refresh the `BMT.lean` module
docstring.** Its "known for" table stops at abelian threefolds and its
prose says existence is open; both were already stale when written. Add:
BMSZ 2017 (existence on all Fano threefolds by the corrected inequality;
original for `ℙ¹×ℙ²`, `ℙ¹×ℙ¹×ℙ¹`, some `H` on `Bl_line ℙ³`), Koseki 2020
(nef tangent bundle), Sun 2021 (semistable tangent bundle and vanishing
Chern classes), Li 2019 (quintic, stronger form), MSD 2017 (fails for any
divisor contracting to a point, for some `H`; Weierstraß CY3), Li 2026
(existence on every smooth projective variety), Cheng–Feyzbakhsh 2026 (weak
twisted BMT on every threefold, large `a`), and the fact that there is no
known counterexample in Picard rank one. Keep the thesis: `BMTData` is
false in general and never to be treated as a fact.

### 5.4 Placement (checked against `layers.md` rules 3 and 7, `placement.md`)

- Ring, grading, degree, Chern/Todd, lattice, HRR:
  `AlgebraicGeometry/Numerical/Models/Threefold/BlowUpSpace.lean` — a formal
  ring/grading/degree/Chern/Todd package is a **Model** (rule 7 / MO1.06),
  stability-neutral, imports only `Numerical/Core` and
  `Models/MonogenicRing` or nothing; add to `Models/Threefold.lean`.
- Polarization, transport, `Q` evaluation, the negative theorem, the
  interval theorem:
  `AlgebraicGeometry/Numerical/Examples/Threefold/BlowUpSpaceWalls.lean` —
  `Examples/Threefold/` may import the stability tree (rule 3); imports
  `Stability/ThreefoldWallTransport` like `ProjectiveSpaceWalls.lean`; add
  to `Examples/Threefold.lean`.
- `Q^Γ`: `Numerical/Stability/BMT.lean`, beside `Q`; the class `Γ` enters
  as `(Γ : A) (hΓ : Γ ∈ V.ring.piece 2)` or as a small structure mirroring
  `Polarization`, whichever the root-and-consumer test prefers; no second
  carrier for the codimension-two class.
- Audit: new slices `scripts/AlgebraicGeometryAudit/BlowUpSpaceWalls.lean`
  and an addition to the `BMT` records in
  `scripts/AlgebraicGeometryAudit/NumericalStability.lean` (per #480,
  a *new* file for the new modules; the `Q^Γ` records may go in a new
  `NumericalStabilityCorrected.lean` to avoid touching a slice another
  branch appends to).
- Names: mirror `Examples/Surface/BlowUpPlane.lean` (`BlowUpSpace.Ring`,
  `BlowUpSpace.numericalVariety`, `BlowUpSpace.halfAnticanonicalPolarization`,
  `BlowUpSpace.lineBundleClass`). **Nothing named `Schmidt`, `BMSZ`,
  `Martinez`, `Gamma`, `Fano`, `delPezzoThreefold`, `toric`,
  `counterexample`** outside docstrings and bibliography comments. The
  file name `BlowUpSpace` follows the `BlowUpPlane` precedent, whose
  docstring already states the carrier is not identified with a scheme.

### 5.5 Size and risk

Size M. The ring is a six-field carrier with a 36-entry multiplication
table proved by `decide`, as `BlowUpPlane.lean` does with 25; the lattice
and HRR are `push_cast; ring` after `Finset.sum_range_succ`, as in
`LinearSection.lean`; the two headline theorems are `norm_num`/`nlinarith`
on explicit rationals. No new supplied datum enters the *theory* layer; the
only supplied facts are the three listed in §5.3. Nothing here can be
scooped, because nothing here is new mathematics; its value is that the
library stops asserting in prose what it can now exhibit.

### 5.6 Deconfliction against the twelve E-milestones

| shared root or file | any E-milestone? | this milestone |
|---|---|---|
| `LinearAlgebra/BilinearForm/Lorentzian/` (e3-lean) | yes | not touched |
| `Models/Surface/BlowUpPlaneRank.lean` (e1-lean) | yes | not touched; the threefold ring is a different carrier and is not a "second arbitrary-rank blow-up model" (that root is a *surface* lattice) |
| `Models/Surface/HyperbolicPlane.lean`, `SmoothQuadric.lean` (e5-lean) | yes | not touched |
| `Symmetry/Combined/SerreInvariance.lean` (e5-lean) | yes | not touched |
| `Walls/Spherical/RankZero.lean`, `RootSystem/` (e2-lean) | yes | not touched |
| `SphericalTwist/CalabiYauThree.lean`, `Transvection.lean` (e6-lean) | yes | not touched |
| `Numerical/{Models,Examples}/Threefold/`, `Stability/BMT.lean` | **no E-milestone names them** | owned here |

No E-milestone imports or extends anything under the threefold directories;
none proposes a threefold ring; `BMTData` is mentioned by none. The one
soft interaction is prose: e5-lean calls `HyperbolicPlane.lean` "the first
Picard-rank-two MODEL in `Numerical/Models/`"; this milestone lands the
first threefold model with `dim A² > 1`. Both sentences stay true.

---

## 6. Could not verify

1. **Li 2601.22994 is a single version (v1, "comments are very welcome!"),
   no erratum, eight months old.** It is relied on as a theorem by
   Cheng–Feyzbakhsh (July 2026) and by Pertusi's survey (Theorem 5.7). Li
   himself notes that the arXiv version of his 2506.21995 §6 "contained a
   mistake", corrected on his website and included in 2601.22994. I read
   the statements and the proof strategy, not the proofs.
2. Cheng–Feyzbakhsh 2607.04788: statements read, proofs not.
3. Whether Li's induced stability condition on a general-type threefold is
   geometric (skyscrapers stable): his Bayer property is described as
   slightly stronger than that, and Cheng–Feyzbakhsh identify the heart
   with the double tilt for large `a`; I did not verify either proof.
4. Bayer–Macrì ICM 2023 Conjecture 4.7 (the general corrected form, per
   Pertusi p. 24): not read. It may already fix the `Γ` shape that F2 asks
   about; **read it first if F2 is ever started.**
5. Koseki 2022 (CY double/triple solids): original or corrected inequality
   — not checked.
6. A per-family table of the original inequality across the 105 Fano
   families: none found; my table in §3 is what the read sources state.
7. Whether `Bl_pt ℙ³` fails for *every* polarization: Schmidt uses
   `H = −K/2`; MSD give "some `H`". Not established in what I read.
8. Whether Schmidt's `O(L)` is tilt-stable on the *whole* open disc or only
   at some points: Thm 3.1 says "there exists". The Lean statement in §5.3
   is written not to depend on this.
9. The Kuznetsov–Liu–Perry sequel on inducing stability conditions: not
   found on 2026-09-20.
10. The ResearchGate "Extended Study and Perspectives" (Sept 2025) and its
    cited arXiv:2509.06045: the id resolves to an unrelated paper; could not
    locate the preprint by title search.
11. Jardim–Lo–Maciocia–Martinez 2503.20008 (DT/PT wall on Picard-rank-1
    threefolds): hypotheses not checked; listed for completeness only.
12. Semiorthogonal decompositions of all 88 Picard-rank-`≥2` Fano families:
    only 2-35 checked (Fanography: full exceptional collection).
13. Feyzbakhsh's 2026 arXiv listing (author page returned 404); coverage of
    her 2026 output is by search only.
14. The coincidence of the upper endpoint in §5.2 with BMSZ Prop. 6.1: the
    arithmetic is mine and checked twice; the *reason* is not.
15. That the six structure sheaves generate `K_num(Bl_pt ℙ³)` over `ℤ`
    (rank 6 is consistent with the full exceptional collection and
    `e(X) = 6`); supplied, not verified.

---

## 7. Recommendation, by expected value per hour, cheapest kill first

1. **Kill G1–G3 now (done in this note; zero further hours).** Existence on
   general-type threefolds is closed; the remaining questions there are
   not the repository's. Do not schedule a scout.
2. **Kill the "classify Fano threefolds by Picard rank" framing (done).**
   The invariant is a divisorial contraction to a point, and rank 1 has no
   counterexample.
3. **Do the Lean milestone in §5 (`threefold-f1-lean`, size M, `should`).**
   Zero research risk, zero collision, closes a documented gap in the
   library's own honesty story, lands the first threefold model with
   `dim A² > 1`, and refreshes a stale docstring that currently
   under-reports what is known. Every number is on this page.
4. **F2 as a `could` R&D item with a one-week kill (`threefold-f2-rd`).**
   Day 1: read BM23 Conj. 4.7 and BMSZ §6 in full. Days 2–5: for
   `Bl_pt ℙ³` and `Bl_line ℙ³` with a one-parameter family of
   polarizations, list the objects whose tilt-stability is *proved*
   (line bundles for `α ≫ 0`, `O_E`, Schmidt's `O(L)`), write the
   `Q^Γ ≥ 0` constraints on the hyperplane `Γ·H = 0`, and decide
   feasibility by hand or Sage. **Abandon if feasible in every case
   tried** — the expected outcome. A single infeasible case is a
   theorem-shaped negative and becomes a Lean certificate.
5. **Nothing else.** Theorem A has no threefold application (§4);
   Kuznetsov components stay with Candidate 3.

---

## 8. Sources, by how they were read

**Page images read (statements quoted from the page):**
Schmidt, arXiv:1602.05055 v1, pp. 1–3 (all).
Bernardara–Macrì–Schmidt–Zhao, arXiv:1607.08199 v5, pp. 1–4, 16–24.
Martinez–Schmidt (appendix Das), arXiv:1708.08567 v2, pp. 1–3.
Koseki, arXiv:2008.09799 v2, pp. 1–3.
Li, arXiv:2601.22994 v1, pp. 1–4.
Cheng–Feyzbakhsh, arXiv:2607.04788 v1, pp. 1–6.
Pertusi, arXiv:2602.24016 v1, pp. 1–3, 23–40.

**Abstract page only:** Li 1810.03434; Fan–Liu–Ma 2310.16950; Koseki
1811.03267; Sun 2006.00756, 2201.13251, 1907.08379 (withdrawn); Piyaratne
1607.07172 (withdrawn), 1705.04011; Fu–Li–Zhao 2103.07728; Li 2506.21995;
Li–Macrì–Perry–Stellari–Zhao 2512.14207; Feyzbakhsh–Koseki–Liu–Rekuski
2509.24990; Liu–Mao 2605.13808 (html summary); Cheng 2607.05344; Wu–Zhang
2408.00519; Jardim–Lo–Maciocia–Martinez 2503.20008; Yang 2402.18098;
Kuznetsov 0809.0225; Fanography family 2-35.

**Search summaries only (nothing above rests on them alone):** Liu, Crelle
770 (2021); Koseki's publication list; the ResearchGate item of §3.

**Repository files read on `origin/main` `4bed5192`:** `CLAUDE.md`,
`docs/architecture/{layers,placement}.md`, `abstraction-tree.md` (rule
sections), `Numerical/Core/Definitions.lean`, `Numerical/Stability/{BMT,
BogomolovGieseker,Slope,ThreefoldWallTransport,ThreefoldTiltTransport}.lean`,
`Numerical/Models/{MonogenicRing}.lean`, `Models/Threefold/*`,
`Examples/Threefold/*`, `Examples/Surface/{BlowUpPlane,SmoothQuadric}.lean`
(headers and declaration lists), `CentralCharge/Numerical/Threefold.lean`,
`Walls/Threefold/*` (headers), `scripts/check_roadmap.py`, the audit slices
naming `BMTData`, and the two 2026-09-19 scoping notes.
