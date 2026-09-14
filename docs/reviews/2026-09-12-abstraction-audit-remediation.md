# Abstraction audit remediation

Snapshot: 2026-09-12 EDT

This document supersedes the central-charge design in
`docs/reviews/2026-09-12-abstraction-generalization-audit.md` §2 and answers
`docs/reviews/2026-09-12-abstraction-audit-critic.md`.  Where this document and
§2 disagree, this one holds: every claim below was either proved in Lean against
the real declarations or verified by reading the tree, and each was then
re-checked independently by two verifiers who re-ran the elaborations and
re-greped the citations.  Where a verifier found a claim unsound the corrected
claim is stated here, marked, with what the verifier found.

It is read by people and by later stages.  Nothing is capped or summarized away:
every repair, adjudication, new finding, negative result and checker verdict
appears.

## 1. What changed and why

The critic found five defects in the first design and all five have now been
answered, but not all in the direction the critic expected.  The κ slot is
**fixed**: `wallChargeFamily V P V.sqrtToddComp 2` is proved equal to the
repository's `ChernCharacter.mukaiCharge` at `R.sqrtTodd` on the rank-one slice,
for any surface and with no K3 hypothesis, so §2.4's "κ = √td" line is now
backed by a theorem; the accompanying charge that the tree "leaves two unrelated
√td data standing" is **half refuted** — the bridge already exists at
`Numerical/Stability/DivisorialMukai.lean:69,86`, and the real defect was that
the design cited neither file and wrote the K3 √td as an H-degree vector
`(1,0,1)` when in that convention it is `(∫H², 0, 1)`.  The unbridged second
Mukai pairing is **fixed and convicting**: `Mukai.Graded.pairing 2` is proved to
be `Mukai.realPairing (LinearMap.mul ℝ ℝ)`, so the n = 2 layer declares nothing
new and must land as a comparison; the graded pairing survives only for n ≠ 2,
and only because two further unifications are **refuted** (the odd-degree form
is alternating and no real Mukai extension can carry it; the H-compression is
non-injective at Picard rank ≥ 2, so the multi-divisor pairing does not factor
through `HDeg 2`).  The cubic-fourfold justification is **refuted** twice over —
`pairing_comm_parity` at n = 4 is a statement about a 5-dimensional space while
H̃(Ku X, ℤ) has rank 24, and symmetry is not a hypothesis of the period-domain
route at all — and is replaced by a proved signature-additivity transfer; but
R4's fourfold line splits into two leaves on two different lattices and both
remain **open** geometry obligations, so PR-12 is blocked end to end.  The −i
rotation is **fixed**: it is `phaseTiltRotation (1/2)` (`TiltGeometry.lean:42`,
not `:43`), it is free on walls by `ChargeFamily.wall_smul` and in fact fixes the
wall *expression*, and it is **not** free on phases — dropping it keeps the walls
and loses the stability condition.  The two rival parents are **adjudicated**:
`lattices-02`'s fixed-arity Mukai self-pairing wins in corrected form,
`walls-02`'s dimension-indexed Δ_H loses and is recorded as a negative result
because `pairing 3 v v = 0` identically.  Three things are **not** fixed and are
carried forward openly: the design's two REAL `sorry`s at `design-final.lean:161`
and `:168` are untouched, the (3,2) tilt charge now has three unbridged spellings
across the design and the repairs, and the repair work itself introduced one new
duplicate — an abbrev `polDiv` that is character-for-character
`NumericalRealization.realizePolarization`
(`Numerical/Stability/DivisorialChargeNumerical.lean:106`) — which must be
removed before PR-6b lands.

## 2. The corrected central-charge tree

### 2.1 The tree, with every amendment applied

```text
R0  Wall.ChargeFamily P N                                              EXISTS, unchanged
    Walls/ChargeFamily.lean:49
    reindex :67 (change of chart) · pullback :72 (change of class map)
    wall :129 · wallValue :118 · pullback_wall :338 · reindex_wall :329
    smul :302 · wallValue_smul :317 · wall_smul :322
    Every node below is an inhabitant, a reindex, a pullback, or a scalar act of R0.
│
├─ R0a  abstract charge on a triangulated category                     EXISTS
│   PreStabilityCondition.WithClassMap   Foundation/PreStabilityCondition.lean:42
│   StabilityCondition.WithClassMap      Foundation/StabilityCondition.lean:41
│   WithClassMap.preimage i h            Phase/Transfer/PreStability.lean:94
│                                        charge unchanged, class map v ∘ K₀.map i
│
├─ R1  Wall.Exp.ofMoments m μ = -∑_{j≤m} (-1)^j/j! · μ j               NEW, one definition
│   │  indexed by truncation degree m, never by ambient dimension n
│   │  keystone stated on the TRIPLE (Mukai.RealExtension D), not on a ChernCharacter
│   ├─ R1a  scalar moments μ j = w^j · d_{m-j} on HDeg m = Fin (m+1) → ℝ
│   │   ├─ m = 1   slope        SlopeData.charge          Weak/…/Slope.lean:154
│   │   ├─ m = 2   surface      stChargeFamily            Numerical/ChargeFamily.lean:59
│   │   ├─ m = 3   threefold    Threefold.chargeFamily    Threefold/Basic.lean:174
│   │   ├─ m = 4   fourfold     free, no new polynomial                 NEW
│   │   └─ (n,m) = (3,2) tilt   Ku(cubic threefold) ambient charge, ROTATED  NEW
│   │        = (stChargeFamily.reindex Prod.swap).pullback threefoldTruncate
│   │        rotation = phaseTiltRotation (1/2) = ·(1/i) = ·(-i)   TiltGeometry.lean:42
│   │        walls fixed (wall_smul :322); chargeSlope NOT fixed — N-fu8-b
│   └─ R1b  intersection-form moments μ0 = ch₂, μ1 = ⟨w,ch₁⟩, μ2 = ⟨w,w⟩·rk
│       ChernCharacter.centralCharge     Divisorial/Charge.lean:333     keystone
│       StabilityParameters / rankOne    Divisorial/Charge.lean:197,209
│       OrthogonalSlice.Point            Divisorial/Slice.lean:94
│       mukaiCharge / mukaiChargeFamily  Divisorial/Mukai.lean:173,224
│       smooth quadric, ℙ², blow-up of ℙ²                Picard rank ≥ 2 leaves
│       the multi-divisor pairing does NOT factor through HDeg 2 — N17
│
├─ R1↔R2 bridge  Mukai.Graded                                   NEW for n ≠ 2 ONLY
│   exp_charge_eq_pairCharge, pairing_comm_parity, dualClass_ne_self
│   pairing 2 IS Mukai.realPairing (LinearMap.mul ℝ ℝ) — PROVED, no weight, no
│     hypothesis; so n = 2 declares NOTHING new and pairing_comm_even is
│     realPairing_comm at mul_comm
│   weighted general-V form: pairing 2 (comp_H v) (comp_H w)
│     = (∫H²) · Mukai.realPairing b v w   on the rank-one slice c = x·H — PROVED
│   discr_eq_pairing_self is RETIRED in favour of
│     NumClass.discr v = Mukai.realPairing (mul) v v   (discr-01, PROVED)
│   threefold_discr_eq_pairing_truncate likewise restated on realPairing
│
├─ R2  Lattice.pairCharge b x y v = ⟪x,v⟫ + i⟪y,v⟫                     NEW root
│   │  b is NOT assumed symmetric; that is what admits odd n
│   ├─ PeriodDomain.centralCharge        QuadraticForm/CentralCharge.lean:61
│   │  │  support property neg_of_centralCharge_eq_zero :109 stays here
│   │  ├─ Mukai.expCharge / expChargeHom  Lattice/Mukai/CentralCharge.lean:36,44
│   │  ├─ Ku(cubic fourfold) charge      H̃_alg(Ku X), sig (2,ρ); = A₂ for very general X
│   │  └─ Ku(cubic fourfold) period      A₂^⊥ ⊆ H̃(Ku X), sig (2,20), rank 22 — NOT the charge
│   └─ packaged as R0 inhabitants under Walls/, never under LinearAlgebra/
│
├─ R3  geometric transport, one map for every (n, m, κ)                NEW
│   corrComp V κ E k = ∑_{j≤k} chComp E j · κ(k-j)       κ on the RIGHT slot
│   hDegrees V P κ m E k = ∫ H^(n-k) · (ch·κ)_k          slot index = CODIMENSION
│   wallChargeFamily := (Exp.chargeFamily m).pullback (hDegreesHom …)
│   ├─ Surface.toNumClass    WallTransport.lean:112             (n,m,κ) = (2,2,1)  PROVED
│   ├─ Threefold.toNumClass  ThreefoldWallTransport.lean:146    (3,3,1)            PROVED
│   ├─ degH                  Slope.lean:116    k = 1, by corrComp_unitCorr then rfl
│   ├─ κ = √td is INHABITED   corrComp V V.sqrtToddComp = mukaiComp (VectorClass.lean:54), rfl
│   │  = mukaiCharge at R.sqrtTodd on rankOne   DivisorialMukai.lean:69; PROVED, general surface
│   │  SqrtTodd = IMAGE of κ under NumericalRealization, NOT a truncation of it
│   └─ grandchildren: K3, ℙ³, quintic (existing); ℙ⁴, sextic (new)
│
└─ R4  noncommutative varieties: no new root, no KuznetsovChargeData
     cubic threefold  n odd ⇒ alternating ⇒ no period domain; tilt route forced
                      induced from the (3,2) TILT charge rotated by 1/i, not from
                      BMT's ch₃ charge
     cubic fourfold   TWO leaves, both OPEN OBLIGATIONS; parity is irrelevant to both
                      (a) charge  on H̃_alg(Ku X), sig (2,ρ); plain pairCharge, no restriction
                      (b) period  on A₂^⊥ ⊆ H̃(Ku X), sig (2,20); pairCharge.restrict along ↪
                      (b)'s HasSignatureTwo is PROVED from sig H̃ = (4,20) + A₂ posDef rank 2
                      via QuadraticMap.sigPos_eq_add (SignatureAdditive.lean:202)
```

### 2.2 Corrected `Canonical spine` block for `docs/architecture/abstraction-tree.md`

This replaces the §2.4 block of the audit in full.  The `LinearAlgebra` fragment
is inserted as a third child of that node; the `Walls` fragment under
`Category ▸ Preadditive ▸ Triangulated category`; the `AlgebraicGeometry`
fragment replaces the two numerical K-theory lines and the final
stability-consuming line.

```text
LinearAlgebra
├─ bilinear form on a lattice
│  └─ Lattice.pairCharge b x y v = ⟪x,v⟫ + i⟪y,v⟫   central-charge root; b not symmetric
│     ├─ PeriodDomain.centralCharge                 quadratic-space presentation
│     │  ├─ support property on HasSignatureTwo     ker Z = span(x,y)ᗮ negative definite
│     │  ├─ signature additivity                    QuadraticMap.sigPos_eq_add :202 supplies
│     │  │                                          HasSignatureTwo on an orthogonal complement
│     │  ├─ Mukai.expCharge                         Bridgeland Z(β,ω), exponential plane
│     │  ├─ noncommutative: Ku(X) charge            H̃_alg(Ku X) sig (2,ρ); NOT a child of expCharge
│     │  └─ noncommutative: Ku(X) period domain     A₂^⊥ ⊆ H̃(Ku X) sig (2,20) by sigPos_eq_add
│     └─ Mukai.Graded.pairing n                     ⟪v,w⟫ = (-1)ⁿ⟪w,v⟫; odd n alternating
│        n = 2 is Mukai.realPairing, not a new form  comparison theorem, never a definition
└─ Mukai.pairing / selfPairing                      Lattice/Mukai/Basic.lean:56,143
   ARITY IS FIXED AT THREE; generalise over the coefficient ring, never over dimension
   canonical root of the Bogomolov/Mukai discriminant (discr-01); no dimension-indexed
   generalisation of it exists — pairing 3 v v = 0 identically

Triangulated category
└─ Wall.ChargeFamily P N                       parameterized additive charges; wall loci
   ├─ reindex / pullback                       change of chart / change of class map
   ├─ smul c / phaseRotate beta                wall_smul :322; normSq = 1 ⇒ wallValue fixed too
   │  └─ phaseRotate = phaseTiltRotation       TiltGeometry.lean:42, proved comparison, not a copy
   ├─ Wall.Exp.ofMoments m                     -∑_{j≤m} (-1)^j/j! · μ j, one polynomial
   │  ├─ scalar moments on Fin (m+1) → ℝ       compressed H-degrees of a polarised n-fold
   │  │  ├─ m = 1 slope   m = 2 surface        SlopeData.charge / stChargeFamily
   │  │  ├─ m = 3 threefold                    Threefold.chargeFamily
   │  │  ├─ m = 4 fourfold                     no new polynomial
   │  │  └─ (n,m) = (3,2) tilt charge          = stChargeFamily ∘ Prod.swap ∘ threefoldTruncate
   │  │     rotated by 1/i for Ku(cubic threefold)   ν = α · chargeSlope of the UNrotated one
   │  └─ intersection-form moments             Picard rank ≥ 2, no compression
   │     ├─ Divisorial.ChernCharacter.centralCharge   proved instance of the kernel
   │     ├─ StabilityParameters / rankOne      (B,ω) chart; w = β + iα fixed once here
   │     ├─ mukaiCharge / SqrtTodd             κ is a pullback, never a coefficient
   │     │  SqrtTodd = IMAGE of κ under NumericalRealization (DivisorialMukai.lean:69),
   │     │  not a truncation                   toSqrtTodd is lossy on slots 0 and 2
   │     └─ quadric, ℙ², blow-up of ℙ²         rank-one slice reaches the scalar branch
   ├─ Wall.Exp.twist / discr                   e^{-βH} action and Δ_H, stated once
   └─ Spherical half-wall                      R0 wall against the point class, cut by a sign
                                               inclusion plus sign, never equality

AlgebraicGeometry
├─ numerical K-theory
│  ├─ Euler quotient
│  ├─ Riemann--Roch and Mukai transfer
│  └─ Polarised.hDegrees / wallChargeFamily    one transport for every (n, m, κ)
│     ├─ n = 2, 3 existing; n = 4 free         K3, ℙ², quadric, ℙ³, quintic, ℙ⁴, sextic
│     ├─ κ = √td is INHABITED                  corrComp V V.sqrtToddComp = mukaiComp, rfl
│     │  = mukaiCharge at R.sqrtTodd on rankOne   proved, any surface, no K3 hypothesis
│     └─ κ = 1 and κ = √td are two pullbacks   different walls; not one family
└─ stability-consuming children                DerivedCategory/Stability/, Moduli/,
                                               Numerical/, Stability/ — four, not one
```

The last line corrects a documented fact, not only a placement: the spine today
reads "`DerivedCategory/Stability/`, the one stability-consuming child", while
`scripts/check_layering.py:99-108` defines `STABILITY_CONSUMING_GEOMETRY` with
four entries and `docs/architecture/layers.md:67` names three.

### 2.3 Nodes removed, and the negative results that replace them

| Removed from §2 | Replaced by | Status |
|---|---|---|
| §2.3 line 155 / §2.4 line 188 — one fourfold node justified by "n even ⇒ symmetric" | two leaves on two lattices (H̃_alg sig (2,ρ); A₂^⊥ sig (2,20)) plus N11b | **refuted**: `pairing 4` lives on `Fin 5 → ℝ`; and `PeriodDomain.polarBilin_isRefl` (`PeriodDomain.lean:144`) makes symmetry automatic, so parity is vacuous even on the right space |
| §2.5 line 249 (R1a table) — `Wall.NumClass.discr` routed to a new `discr_eq_pairing_self` | `NumClass.discr v = Mukai.realPairing (LinearMap.mul ℝ ℝ) v v`, the existing root | **proved**; carriers are defeq (`Walls/Numerical/Basic.lean:104` vs `RealForm.lean:82`), so there is no transport |
| walls-02's `Δ_H` on H-degree vectors | discr-01 at the fixed-arity `Mukai.pairing` | **refuted** as NR-D1: `pairing 3 v v = 0` for every class, by expansion |
| §2.6 N8's gloss "K3's √td = (1,0,1)" | `(1,0,1)` as a CODIMENSION vector; as an `HDeg 2` it is `(∫H², 0, 1)` | **refuted** as stated; `dualClass_k3` itself stands |
| §2.7 PR-13 "independent, low priority" | PR-6b, landing with PR-6 | re-scoped: it is the theorem that inhabits the κ slot |
| §2.5 line 305 "`degH` is `hDegrees … 1` by **rfl** (which requires ℕ, not `Fin`)" | "by `corrComp_unitCorr`, then `rfl`"; `Fin (m+1)` indexing is no obstruction | **falsified on both halves** |
| §2.6 N4's naive reading `slopeH = d₁/d₀` | `slopeH = ∫Hⁿ · (d₁/d₀)`, proved | the naive reading is **false** on every polarisation of degree ≠ 1, including this lane's own K3 witness |
| §2.7 PR-8's `Exp`-kernel dependency for the tilt node | `Walls/Rotation.lean` + `Walls/Threefold/Tilt.lean`, no `Exp` import | the (3,2) family needs no new polynomial: it is `stChargeFamily` reindexed and pulled back |
| geometry-derived-06's `structure GeometricSerreFunctor` | a bridge obligation onto `SerreFunctorData`, no new structure | **replaced**: fails the Adoption clause (`abstraction-tree.md:356-357`) on both branches |

## 3. Repair results

Five follow-ups were executed as repairs.  Each produced a scratch Lean file
under
`/private/tmp/claude-501/-Users-chris-dare-Personal-SourceCode/c05f8e40-4e0b-4b29-8e2f-b2d8a4ed3897/scratchpad/`.
None is committed; no repository file was edited by any of them.  All five
elaborate with `EXIT=0` and **zero** `sorry`, and both verifiers re-ran all five
themselves.  The line numbers cited inside the scratch files below are the
verifier-corrected ones: the first verifier found systematic drift of a few
lines in `repair-fu2-sqrttodd.lean` and about +7 in `repair-fu7-fourfold.lean`,
and exact self-citation in the other three.

### 3.1 fu2 — instantiate κ at √td and close the two-√td split

**Outcome: proved.**  The κ slot is inhabited by a proved comparison, and the
critic's "two unrelated √td data" is half refuted — the repository already
bridges them, and the design cites neither file.

**Lean evidence.**  `repair-fu2-sqrttodd.lean`, 480 lines, `grep -c sorry` = 0.

```
$ LEAN_NUM_THREADS=2 lake env lean .../scratchpad/repair-fu2-sqrttodd.lean
EXIT=0
'Fu2.expCharge_eq_ofMoments' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.expCharge_rankOne_eq_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.corrComp_sqrtToddComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.hDegrees_sqrtToddComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.wallChargeFamily_sqrtToddComp_eq_mukaiCharge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.wallChargeFamily_sqrtToddComp_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.toSqrtTodd_sqrtToddComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.corrHDeg_sqrtToddComp_k3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fu2.Polarised.corrHDeg_sqrtToddComp_ne_one_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Sorries: none.**  The two REAL `sorry`s of the design
(`design-final.lean:161` `Exp.twist_twist`, `:168` `Exp.charge_twist`) are
outside this follow-up and remain open.

**Findings.**

1. **The κ slot is inhabited, and provably so.**
   `wallChargeFamily_sqrtToddComp_eq_mukaiCharge` (`repair-fu2-sqrttodd.lean:327`,
   equation at `:332`) proves, sorry-free, that
   `(wallChargeFamily V P V.sqrtToddComp 2).charge (alphaBetaChart (a,b)) E =
   R.chernCharacter.mukaiCharge R.divisorSpace R.sqrtTodd (StabilityParameters.rankOne … a b) E`
   for **any** surface `NumericalVarietyData 2` carrying a `NumericalRealization`
   — no K3 hypothesis.  The K3 corollary `wallChargeFamily_sqrtToddComp_k3`
   (`:340`) then gives `= centralCharge − rank` through
   `NumericalRealization.mukaiCharge_of_isK3`
   (`AlgebraicGeometry/Numerical/Stability/DivisorialMukai.lean:124`).
2. **The "two unrelated √td data" charge is refuted as a statement about the
   repository.**  `NumericalRealization.sqrtTodd : SqrtTodd D`
   (`DivisorialMukai.lean:69`) is built from `V.sqrtToddComp 1` and
   `V.ring.degree (V.sqrtToddComp 2)`, and `sqrtTodd_eq_k3` (`:86`) proves it
   equals `SqrtTodd.k3` on a K3, from `K3.sqrtToddComp_one`
   (`Numerical/Mukai/SqrtTodd.lean:204`) and `K3.degree_sqrtToddComp_two`
   (`:212`).  `toSqrtTodd_sqrtToddComp` (`repair:387`) proves
   `DivisorialMukai.lean:69` **is** the general adapter at κ = √td, by `rfl`.
   The defect is that the design cites neither file, so §2 reads as if the
   bridge had to be invented.
3. **`corrComp` is a third declaration of an existing one — the audit's own
   disease inside the design.**  `corrComp_sqrtToddComp` (`repair:158`) proves
   `corrComp V V.sqrtToddComp E k = V.mukaiComp E k` by `rfl`: the design's new
   `corrComp` (`design-final.lean:512`) at κ = √td is definitionally
   `NumericalVarietyData.mukaiComp` (`Numerical/Mukai/VectorClass.lean:54`).
   PR-6 must land `corrComp` with that `rfl` comparison, not as a fresh
   convolution.
4. **Indexing convention settled: slot index = codimension, in all three
   places.**  `NumericalVarietyData.sqrtToddComp : ℕ → A` (`SqrtTodd.lean:181`)
   has `sqrtToddComp 0 = 1` (`:185`); `Exp.HDeg m` slot `k` is `∫H^(n−k)·(·)_k`
   (`design-final.lean:519-522`); `SqrtTodd`'s two fields
   (`Walls/Divisorial/Mukai.lean:77`) are codimension 1 (`divisor : D`) and
   codimension 2 (`number : ℝ`, already integrated).  `SqrtTodd.k3 = ⟨0,1⟩`
   (`:91`) and the codimension vector `(1,0,1)` denote the same class — `⟨0,1⟩`
   drops slot 0 because `sqrtToddComp 0 = 1` is forced, and slot 2 is compared
   after `V.ring.degree`, which is what `toSqrtTodd` applies.
5. **`![1,0,1]` is a type-level error in the sketch's own convention.**
   `corrHDeg_sqrtToddComp_k3` (`repair:425`) proves that √td read as an
   `Exp.HDeg 2` in the transport's convention is `![∫(H²), 0, 1]`;
   `corrHDeg_sqrtToddComp_ne_one_zero_one` (`repair:442`) proves the two differ
   whenever `∫H² ≠ 1`.  `design-final.lean:459-460` and report line 376 conflate
   a codimension vector with an H-degree vector.  The `dualClass_k3` **theorem**
   still stands; only the √td identification in its docstring was wrong.
6. **`SqrtTodd` is not a truncation of κ — keep it.**  `toSqrtTodd_congr`
   (`repair:394`) and `toSqrtTodd_update_zero` (`repair:403`) prove the adapter
   is lossy: it sees codimension 1 realized into `D` and the *integral* of
   codimension 2, and is blind to codimension 0 and to everything above 2.
   `SqrtTodd`'s fields live in `D` and `ℝ`, κ lives in the graded ring `A`, and
   the map between them is the `NumericalRealization`, which `Walls/**` cannot
   import under the `layers.md` geometry firewall.
7. **The keystone had to be restated on the triple, not the character.**  The
   design's `centralCharge_eq_ofMoments` (`design-final.lean:286`) is stated for
   a `ChernCharacter`, so it cannot reach `mukaiCharge`, which is the same
   `Mukai.expChargeHom` applied to a different triple
   (`Walls/Divisorial/Mukai.lean:173`).  `expCharge_eq_ofMoments` (`repair:88`)
   and `expCharge_rankOne_eq_charge` (`repair:113`) prove the keystone and the
   rank-one collapse on a bare `Mukai.RealExtension D`, subsuming both
   `centralCharge_eq_ofMoments` and `moments_rankOne` (`design-final.lean:300`).
8. **Parameter spaces do not match globally, and that is intrinsic.**
   `wallChargeFamily … : ChargeFamily ℂ N` (`design-final.lean:537`) is the
   polarised branch; `mukaiChargeFamily … : ChargeFamily (StabilityParameters D) N`
   (`Walls/Divisorial/Mukai.lean:224`) is the intersection-form branch with
   independent `B, ω ∈ D`.  No equality of `ChargeFamily`s is typable; the
   honest statement is the pointwise one on `StabilityParameters.rankOne`
   (`Walls/Divisorial/Charge.lean:209`).
9. **Citation drift corrected.**  `mukaiCharge_trivial` is at
   `Walls/Divisorial/Mukai.lean:183`, not `:187ff` as the critic wrote.  All
   other cited lines verified exact: `structure SqrtTodd` `:77`, `k3` `:91`,
   `mukaiVector` `:112`, `mukaiCharge` `:173`, `mukaiCharge_k3` `:213`,
   `mukaiChargeFamily` `:224`, `sqrtToddComp` `SqrtTodd.lean:181`, `mukaiComp`
   `VectorClass.lean:54`, `DivisorialMukai.lean:69/86/115/124`,
   `K3MukaiComparison.lean:97`.
10. **PR-13 is mis-scoped and mis-prioritised.**  Report line 488 calls the K3
    agreement theorem "independent, low priority"; it is the theorem that
    inhabits the κ slot and backs the §2.4 "κ = √td" spine line.  It becomes
    PR-6b and lands with PR-6.

**Negative results.**

- `wallChargeFamily V P κ 2 = mukaiChargeFamily ch S t` as an equation of
  `ChargeFamily`s is **false by type** and cannot be stated: the parameter
  spaces are `ℂ` and `StabilityParameters D`.  The unification survives only as
  the pointwise rank-one statement proved here; the general Picard-rank case is
  a genuine R1b sibling.
- `Walls/Divisorial/Mukai.SqrtTodd` is **not** the m = 2 truncation of κ,
  contrary to the framing of the critic's finding (3)(a)
  (`critic.md:227`).  A truncation would be injective on slots 0..2; the adapter
  loses slot 0 entirely and compresses slot 2 through `V.ring.degree`.  Verdict:
  **keep** `SqrtTodd`, with the proved comparison `toSqrtTodd_sqrtToddComp`.
- The design's `√td = (1,0,1)` (`design-final.lean:459`) is **false** as a
  statement about `Exp.HDeg 2`.  It is true only as a codimension vector, where
  it agrees with `SqrtTodd.k3 = ⟨0,1⟩`.  `Polarization.degree_pow_pos`
  (`Numerical/Stability/Slope.lean:94`) only bounds `∫H²` below by 0.
- The critic's charge that the tree "bridges neither" √td datum is **refuted**
  about the repository: `DivisorialMukai.lean:69,86` are exactly that bridge and
  `Examples/Surface/K3MukaiComparison.lean:97` carries it to the integral Mukai
  lattice.
- `corrComp` is **not** a new abstraction at κ = √td; landed without its `rfl`
  comparison it would be this audit's own failure mode.

**Open obligations.**

- PR-6 must land `corrComp` together with `corrComp_sqrtToddComp` (`rfl`) and
  `corrComp_unitCorr`, or `mukaiComp` becomes a duplicate of it.
- PR-2 should land the triple-level keystone `expCharge_eq_ofMoments`; the
  `ChernCharacter`-level statement then follows by `ch.toRealExtension`.
- The general-Picard-rank Mukai charge stays outside the scalar kernel.  A κ
  statement off the rank-one slice would need an intersection-form κ (a
  `SqrtTodd`-valued correction in `D`), not `κ : ℕ → A`; no such object exists
  and none is proposed.
- `abstraction-tree.md`'s two-independent-consumers rule: the κ slot now has
  exactly two — κ = 1 (`WallTransport.lean:112`) and κ = √td (this comparison).
  That satisfies the rule, but it must be written into the root-review note,
  since `check_single_instantiation.py` cannot see it (`corrComp` is a `def`,
  and `GENERIC_SUBJECTS` excludes `AlgebraicGeometry`).
- **New, from the verifiers.**  `polDiv` (`repair:227`, body
  `R.divisorClass ⟨P.cls, P.cls_mem⟩`) duplicates
  `NumericalRealization.realizePolarization`
  (`Numerical/Stability/DivisorialChargeNumerical.lean:106`), which the repair
  file already has in scope.  It appears in the **statement** of
  `wallChargeFamily_sqrtToddComp_eq_mukaiCharge` and its K3 corollary, so PR-6b
  must be restated with `R.realizePolarization P`.  The same file also carries
  `realizeBField` (`:102`), `parameters` (`:111`) and an existing rank-one-slice
  comparison `centralCharge_eq_ofNumericalDataB` (`:202`) that fu2 never cites.
- **New, from the verifiers.**  The proposed `Polarised.wallChargeFamily`
  (`design-final.lean:537`) carries the same name as the existing
  `Surface.wallChargeFamily`
  (`Numerical/Stability/WallTransport.lean:156`, `= Wall.stChargeFamily.pullback
  (toNumClassHom V P)`) in a sibling namespace, and no repair proves the
  family-level comparison — fu3 proves only the class-level
  `surface_toNumClass_eq`, and the charts differ (`ℝ × ℝ` against `ℂ`), so a
  `reindex` is needed.  Report line 300's "becomes the reindexed root family"
  remains prose.

**Checker verdicts.**  Both verifiers: **sound**.  Both re-ran the elaboration
(EXIT=0, nine axiom lines, zero `sorry`) and re-verified every repository
citation.  Corrections applied above: self-citation drift inside the scratch
file (`corrComp_sqrtToddComp` `:158` not `:177`; the headline theorem `:327` not
`:352`; the K3 corollary `:340` not `:364`; `expCharge_rankOne_eq_charge` `:113`
not `:116`; `toSqrtTodd_sqrtToddComp` `:387` not `:389`; `toSqrtTodd_congr`
`:394` not `:400`; `toSqrtTodd_update_zero` `:403` not `:413`;
`corrHDeg_sqrtToddComp_k3` `:425` not `:436`;
`corrHDeg_sqrtToddComp_ne_one_zero_one` `:442` not `:455`), design-sketch drift
(`centralCharge_eq_ofMoments` `:286`, `moments_rankOne` `:300`,
`wallChargeFamily` `:537`), and `Polarization.degree_pow_pos` at
`Slope.lean:94`, not `:96`.  The second verifier also recorded that the claim
"`SqrtTodd.k3 = ⟨0,1⟩` and `(1,0,1)` denote the same class" is true only after
applying `V.ring.degree` to slot 2; finding 4 above now says so.

### 3.2 fu3 — discharge the two transport comparisons

**Outcome: proved.**  Both transport comparisons and the corrected N4 slope
theorem are proved with zero sorries, and the report's §2.5 claim that
`degH = hDegrees … 1` "by rfl (which requires ℕ, not `Fin`)" is falsified on
both halves.

**Lean evidence.**  `repair-fu3-transport.lean`, 207 lines, 12 declarations,
`grep -c sorry` = 0.

```
$ cd /Users/chris.dare/Personal/SourceCode/dag-abstraction-audit && \
  LEAN_NUM_THREADS=2 lake env lean .../scratchpad/repair-fu3-transport.lean; echo "EXIT=$?"
EXIT=0

(no output lines at all: no errors, no warnings, no `sorry` lines)
```

**Sorries: none.**

**Findings.**

1. **Discharged.**  `Polarised.surface_toNumClass_eq` — the design's ROUTINE
   `sorry` at `design-final.lean:553` — is proved at
   `repair-fu3-transport.lean:80`.  `Surface.toNumClass V P E`
   (`Numerical/Stability/WallTransport.lean:112`) is literally
   `(hDegrees V P (unitCorr A) 2 E 0, … 1, … 2)`: slot 0 is `hDegrees_zero` plus
   `mul_comm`, slot 1 is `degH` (`Slope.lean:116`) by `rfl` after the
   convolution collapse, slot 2 by `norm_num`.
2. **Stated and proved.**  The n = 3 twin, which the critic correctly said was
   only a code comment (`design-final.lean:560-561`), is now
   `Polarised.threefold_toNumClass_eq` (`repair:111`): `Threefold.toNumClass V P E`
   (`ThreefoldWallTransport.lean:146`) `= (hDegrees V P (unitCorr A) 3 E 0, …, … 3)`
   — slot 0 = `∫H³·rank`, slots 1–3 = `∫H^(3−k)·ch_k`.
3. **The load-bearing new lemma** both comparisons factor through is
   `corrComp_unitCorr` (`repair:51`): `corrComp V (unitCorr A) E k = V.chComp E k`,
   proved once by `Finset.sum_eq_single` for every n and k.  The design proved
   only the k = 0 instance inline inside `hDegrees_zero`.  Grep confirms the
   repository contains no declaration named `corrComp`, `unitCorr` or
   `hDegrees`, so nothing here duplicates an existing name.
4. `hDegrees_zero` was re-proved rather than copied (`repair:64`) via
   `corrComp_unitCorr`, `V.chComp_zero` (`Numerical/Core/Definitions.lean:125`)
   and `NumericalRingData.degree_algebraMap_mul` (`:93`).  The design's version
   is correct as written.
5. **N4 corrected and proved.**  `slopeH_eq_degree_mul_ratio` (`repair:167`)
   proves `(slopeH V P E : ℝ) = ∫Hⁿ · (d₁ / d₀)` for every n ≥ 1, where
   `slopeH = degH / rank` (`Slope.lean:133`) and `d₀ = rank · ∫Hⁿ`.  `∫Hⁿ ≠ 0`
   comes from `Polarization.degree_pow_pos` (`Slope.lean:94`).
6. The N4 theorem needs **no** `rank E ≠ 0` hypothesis.  At rank 0 both sides
   are Lean's junk `0`, matching the junk `slopeH` already documented at
   `Slope.lean:129-132`; the rank-zero case is handled visibly in the private
   `ratio_aux` (`repair:156`) rather than hidden inside `field_simp`.
7. Slot 1 = `degH` is now an n-uniform declaration, `hDegrees_one`
   (`repair:146`), for every n ≥ 1; it did not exist in the design at all, and
   it is what makes N4 statable outside n = 2, 3.
8. **Citation correction.**  The threefold transport docstring is at
   `ThreefoldWallTransport.lean:143-145` ("The first slot carries `∫H³`"), not
   `:141`.  The `def toNumClass` line `:146` is correct, as are
   `WallTransport.lean:112` and `Slope.lean:133`.

**Negative results.**

- **Falsified (first half).**  Report §2.5 lines 305-306 say `degH` is
  `hDegrees … 1` "by **rfl** (which requires the root to be indexed by `ℕ`, not
  `Fin`)".  The `Fin` clause is false: `hDegrees_one` is stated on the
  `Fin (m+1)`-indexed `Exp.HDeg` with the index written `⟨1, by omega⟩`, and it
  closes.  PR-6's parenthetical at report line 452 is an unnecessary constraint
  on the root.
- **Falsified (second half).**  The word "rfl" is also wrong on the nose.
  `hDegrees V P (unitCorr A) n E ⟨1,_⟩` unfolds to
  `degree (corrComp V (unitCorr A) E 1 * P.cls ^ (n-1))`, and `corrComp … 1` is
  `∑ j ∈ Finset.range 2, chComp E j * κ (1-j)`, which is not defeq to
  `chComp E 1` in a general `CommRing A`.  The honest phrasing is "by
  `corrComp_unitCorr`, then `rfl`".  The first verifier reproduced this
  independently: replacing the step with `:= rfl` fails with a type mismatch.
- **Refuted as an identity, and the refutation is itself proved.**
  `slopeH_ne_ratio_of_degree_ne_one` (`repair:187`) shows that whenever
  `∫Hⁿ ≠ 1` and `slopeH E ≠ 0`, `slopeH E ≠ d₁/d₀`.  The naive reading N4 warns
  about is false on every polarisation of degree ≠ 1, which includes this lane's
  own K3 witness (`∫H² = 2d`).
- **Not unified, deliberately.**  No attempt was made to make `slopeH` an
  `abbrev` for `d₁/d₀`; the two differ by `∫Hⁿ`, so an `abbrev` would be false
  and both declarations must stay.
- **No other sorry was touched.**  The two REAL sorries remain open, and nothing
  proved here depends on either — the rank-slot convention is tied to both
  leaves without any twist or Cauchy-product machinery.

**Open obligations.**

- `Exp.twist_twist` (`design-final.lean:161`) and `Exp.charge_twist` (`:168`),
  both REAL, are untouched and still open.
- The proposed root module
  `AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean` (which does
  not exist today) sits under `AlgebraicGeometry`, excluded from
  `GENERIC_SUBJECTS`, so the two-independent-consumers test is a review
  obligation.  This follow-up supplies the evidence: `surface_toNumClass_eq` and
  `threefold_toNumClass_eq` are two independent existing consumers, both proved.
- `Exp.HDeg` is copied into the repair file as an `abbrev` purely so the
  statements typecheck; the real placement decision for `HDeg` is untouched.
- **New, from the verifiers.**  fu3's amendment to report line 79 inserts
  `surface_toNumClass_eq` and `threefold_toNumClass_eq` into a list that is
  explicitly about `design-final.lean`, where `:553` still carries its `sorry`,
  while its amendment to report line 68 deletes that `sorry` row.  The two
  amendments describe two different artifacts; PR-6 must say which.  The
  family-level `Surface.wallChargeFamily` comparison (see fu2's open
  obligations) is likewise still owed.

**Checker verdicts.**  Both verifiers: **sound**, with every self-citation exact
and the two falsifications reproduced independently.  The threefold-docstring
correction (`:143-145`, not `:141`) was confirmed by both.

### 3.3 fu6 — bridge or refute `Mukai.Graded.pairing` against the existing root

**Outcome: partial.**  The bridge is proved and it convicts the design at n = 2;
the graded pairing survives for n ≠ 2 because two further unifications are
refuted; the n = 4 layer has no counterpart in the tree at all.

**Lean evidence.**  `repair-fu6-pairing-bridge.lean`, 289 lines,
`grep -c sorry` = 0.

```
$ cd /Users/chris.dare/Personal/SourceCode/dag-abstraction-audit
$ LEAN_NUM_THREADS=2 lake env lean .../scratchpad/repair-fu6-pairing-bridge.lean
EXIT=0

(no output at all: zero errors, zero warnings, zero sorry lines)
```

**Sorries: none.**

**Findings.**

1. **Duplication confirmed at n = 2.**  `gpairing_two_eq_realPairing` (`:97`)
   proves `Mukai.Graded.pairing 2 d e = Mukai.realPairing (LinearMap.mul ℝ ℝ)
   (d 0, d 1, d 2) (e 0, e 1, e 2)` with no weight, no hypothesis and no
   correction: both `-∑_k (-1)^k v_k w_{2-k}` and `b c c' - r s' - r' s` expand
   to `v₁w₁ - v₀w₂ - v₂w₀`.  The bundled form matches too:
   `gpairing_two_eq_realBilin` (`:106`) against `Mukai.realBilin`
   (`LinearAlgebra/Lattice/Mukai/RealForm.lean:100`).
2. The design's `pairing_comm_even` (`design-final.lean:392`) is not a new fact:
   `gpairing_two_comm` (`:113`) derives it by rewriting through the bridge into
   `Mukai.realPairing_comm` (`RealForm.lean:94`) at `mul_comm`.
3. **The ∫H² weight, written explicitly.**  `gpairing_comp_rankOne` (`:130`):
   for any real bilinear `b` on `V`, any `H : V`, and the H-degree compression
   `comp b H v = ![b H H * v.1, b H v.2.1, v.2.2]`, on the rank-one slice
   `c = x • H` we get `gpairing 2 (comp v) (comp w) = b H H · Mukai.realPairing b v w`.
   The weight is `∫H² = b H H`, to the first power.
4. **N9's factor of two is precisely the `realForm` halving and nothing else.**
   `gpairing_comp_self_eq_two_mul_realForm` (`:150`):
   `gpairing 2 (comp v) (comp v) = 2 · b H H · Mukai.realForm b v`, via
   `Mukai.realForm_apply` (`RealForm.lean:116`).  Unweighted form at `:158`.
5. **`NumClass.discr` needs no new pairing.**  `numClass_discr_eq_realPairing_self`
   (`:185`): `Wall.NumClass.discr v = Mukai.realPairing (LinearMap.mul ℝ ℝ) v v`,
   with **zero** transport, because `Wall.NumClass`
   (`Walls/Numerical/Basic.lean:104`) and `Mukai.RealExtension ℝ`
   (`RealForm.lean:82`) are the same type.  `NumClass.discr` is at
   `Walls/Numerical/Discriminant.lean:70`.  Also `numClass_discr_eq_realForm_two`
   (`:194`).
6. **`Exp.discr` against `Mukai.selfPairing` on the integral lattice.**
   `discr_compZ_rankOne` (`:209`): for `b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ`,
   `discr 2 (compZ b H (r, x • H, s)) = (b H H : ℝ) · (Mukai.selfPairing b (r, x • H, s) : ℝ)`.
   `Mukai.selfPairing` is at `LinearAlgebra/Lattice/Mukai/Basic.lean:143`
   (`selfPairing_mk` at `:150`).  Same single power of the weight as the
   bilinear case — the two are one equation.
7. `discr_eq_gpairing_self` (`:166`) and its restatement on the existing root
   `discr_eq_realPairing_self` (`:176`) are the design's `discr_eq_pairing_self`
   (`design-final.lean:471`) with its right-hand side replaced by a declaration
   that already exists.
8. **The report contradicts itself and the design took the wrong branch.**
   Finding `lattices-02` (report line 2021) states under **Projections** the
   exact identity `Wall.NumClass.discr v = Mukai.realPairing (mul) v v` and says
   under **Proposed root** "corrected: the root exists".  §2.5's R1a table
   nevertheless routes `Wall.NumClass.discr` to a NEW `discr_eq_pairing_self`.
   That is the internal inconsistency the critic detected, settled in Lean in
   favour of `lattices-02`.
9. **Verdict on canonical ownership.**  `Mukai.realPairing` / `realBilin` /
   `realForm` / `selfPairing` remain the canonical owner of the even, n = 2
   form.  `Mukai.Graded.pairing` must not be declared at n = 2 as a second
   owner: it reaches the root by `gpairing_two_eq_realPairing`, and every n = 2
   consumer (`pairing_comm_even`, `discr_eq_pairing_self`,
   `threefold_discr_eq_pairing_truncate`) should cite `Mukai.realPairing`
   directly.  `Mukai.Graded.pairing n` earns its existence only for n ≠ 2, and
   only because of N16.
10. **Citation corrected.**  `Mukai.realForm` is at `RealForm.lean:113`, not
    `:112` (`realPairing` `:87`, `realPairing_comm` `:94`, `realBilin` `:100`,
    `realForm_apply` `:116`).  The report's N9 already cites `:113` correctly.

**Negative results.**

- **N16 — refuted: the odd-degree unification is false, and this is what saves
  `Mukai.Graded.pairing` from deletion.**  `gpairing_three_self_eq_zero`
  (`:262`) proves `gpairing 3 v v = 0` identically, while
  `realPairing_has_neg_two` (`:272`) proves that for **every** `V` and **every**
  `b`, `Mukai.realPairing b (1,0,1) (1,0,1) = -2`.  `odd_gpairing_not_realPairing`
  (`:281`) combines them: given any `V`, any `b`, and any surjective repackaging
  `e : HDeg 3 → Mukai.RealExtension V` intertwining the two forms, `False`.
- **N17 — refuted: the multi-divisor pairing does not factor through the scalar
  n = 2 form.**  `compression_not_injective` (`:240`) exhibits, for `V = ℝ × ℝ`
  with the standard form and `H = (1,0)`, the classes `(0,(0,1),0)` and
  `(0,(0,0),0)`: equal H-compressions, self-pairings `1` and `0`.
  `realPairing_not_factoring` (`:253`) sharpens it: for **no**
  `F : HDeg 2 → HDeg 2 → ℝ` does `Mukai.realPairing dot2 v w = F (comp v) (comp w)`
  hold for all `v, w`.  So `Mukai.realPairing` at Picard rank ≥ 2 is a genuine
  R1b sibling of the scalar form, mirroring the R1a/R1b split the design already
  makes for charges.  Consequence: the n = 2 bridge is correct only on the
  rank-one slice of a general `V` and must not be promoted to a general-`V`
  claim.
- **Not refuted but scoped:** the ∫H² weight cannot be normalised away.
  `gpairing_comp_rankOne` carries `b H H` to the first power, so the two agree
  on the nose only when `∫H² = 1`.  Any claim that `Mukai.Graded.pairing 2` "is"
  `Mukai.realPairing` for a polarised surface with `H² ≠ 1` is false by the
  scale factor.

**Open obligations.**

- The bridge is proved for n = 2 (equality) and for the rank-one slice of
  general `V` (weighted equality).  **No comparison is offered for n = 4** — the
  fourfold graded pairing has no repository counterpart at all, so PR-7's
  fourfold layer would inherit an uncompared form.  That is a gap, not a
  contradiction, and is recorded rather than shipped silently.  It interacts
  with fu7: the fourfold node needs `HasSignatureTwo` on a rank-22 lattice, not
  a form on `HDeg 4`, so the uncompared form has no fourfold consumer either.
- **Corrected phrasing, from the second verifier.**  "Remove
  `Mukai.Graded.pairing 2` from the proposed `Graded.lean`" is not actionable:
  `pairing` is a single n-generic `def` (`design-final.lean:347`), so there is
  no separate n = 2 definition to remove.  The instruction is: declare
  `pairing n` once, land `gpairing_two_eq_realPairing` as a **mandatory**
  comparison in the same PR, and route every n = 2 consumer to
  `Mukai.realPairing`.
- **Blocker, not an open item.**  `Mukai.Graded.pairing n` still lacks its two
  independent consumers under `abstraction-tree.md:356-357`.  N16 supplies the
  mathematical justification for n ≠ 2, but the only n ≠ 2 consumers the design
  names are `pairing_self_eq_zero_odd` (a negative result about itself) and the
  not-yet-existing fourfold layer.  `abstraction-tree.md:351-352` requires this
  answered **before** implementation, so PR-3 does not pass root review as
  drafted.
- `ChernCharacter.discriminant` (`Walls/Divisorial/Discriminant.lean:227`) and
  `ChargeCoordinates.discr` (`:288`) were not verified by elaboration in this
  follow-up; they are proved in the fu4 adjudication file (`leaf4`, `leaf3`).

**Checker verdicts.**  Both verifiers: **sound**, both re-ran the elaboration
and re-verified all 17 self-citations as exact.  Two corrections applied above.
(i) The headline's claim that `Exp.HDeg 2` and `Mukai.RealExtension ℝ` are
"both `ℝ × ℝ × ℝ`" with "no transport" is false for `HDeg 2`, which is
`Fin 3 → ℝ`: the n = 2 theorem goes through the repackaging `toExt` (`:84`), as
the file itself states.  The no-transport claim is true only for
`Wall.NumClass` (finding 5).  (ii) The R1a table row routing
`Wall.NumClass.discr` to `discr_eq_pairing_self` is report line **247**, not
249 (line 249 is the `Threefold.betaTwist` row); the `Threefold.discr` row is
line 255.

### 3.4 fu7 — fix the cubic-fourfold justification in R4

**Outcome: partial.**  The parity justification is false and is replaced by a
proved signature-additivity transfer.  R4's fourfold line becomes two leaves on
two different lattices, and both are open geometry obligations.

**Lean evidence.**  `repair-fu7-fourfold.lean`, 339 lines, `grep -c sorry` = 0.

```
$ cd /Users/chris.dare/Personal/SourceCode/dag-abstraction-audit && \
  LEAN_NUM_THREADS=2 lake env lean .../scratchpad/repair-fu7-fourfold.lean
EXIT=0
(no output at all: no errors, no warnings, no sorry lines)
```

**Sorries: none.**

**Findings.**

1. **Critic (3)(d) confirmed independently.**  `Mukai.Graded.pairing n` is
   `LinearMap.BilinForm ℝ (Exp.HDeg n)` (`design-final.lean:347`) and
   `Exp.HDeg m := Fin (m+1) → ℝ` (`:127`), so `pairing_comm_parity` at n = 4
   (`:359`) is a statement about a 5-dimensional space.  It cannot bear on
   H̃(Ku X, ℤ), which has rank 24.  The sketch's justification at
   `design-final.lean:654-657` is deleted.
2. **Second, independent reason the parity argument is empty.**  Symmetry is not
   a hypothesis anywhere on the period-domain route:
   `PeriodDomain.polarBilin_isRefl`
   (`LinearAlgebra/QuadraticForm/PeriodDomain.lean:144`) proves every
   `QuadraticForm.polarBilin` is symmetric automatically.  What `PeriodDomain`
   requires is `HasSignatureTwo` — an indices-of-inertia statement
   (`PeriodDomain.lean:100-104`) — not symmetry.
3. **What the fourfold actually needs, and the repository already has the
   engine.**  `QuadraticMap.sigPos_eq_add`
   (`LinearAlgebra/QuadraticForm/SignatureAdditive.lean:202`),
   `sigPos_eq_finrank_of_posDef` (`:247`) and
   `nondegenerate_restrict_of_isCompl` (`:305`) are exactly the three lemmas
   needed.  `PeriodDomain.hasSignatureTwo_restrict_of_posDef_rankTwo`
   (`repair-fu7-fourfold.lean:123`) and its specialisation
   `hasSignatureTwo_orthogonal_a2` (`:148`) derive, from `IsCompl A P`,
   orthogonality, `(Q.restrict A).PosDef`, `finrank A = 2`, `Q.Nondegenerate`,
   `sigPos Q = 4` and `sigNeg Q = 20`: `HasSignatureTwo (Q.restrict P)`,
   `finrank P = 22`, `finrank M = 24`.  No parity, no `Exp.HDeg`, no new
   carrier.
4. **The anti-duplication step the critic said was missing.**
   `pairCharge.restrict` (`design-final.lean:65`) was a generic `.comp f` with
   no fourfold inhabitant.  `PeriodDomain.centralCharge_restrict` (`repair:83`)
   proves `centralCharge (Q.restrict N) x y v = centralCharge Q ↑x ↑y ↑v`, and
   `centralChargeHom_restrict_eq` (`:92`) proves the sublattice charge **equals**
   `Lattice.pairCharge.restrict Q.polarBilin ↑x ↑y N.subtype` as
   `AddMonoidHom`s.  The sublattice node is a restriction of an existing charge,
   proved, not a second declaration.
5. **The support property transfers, but not "with no new proof".**
   `neg_of_centralCharge_restrict_eq_zero` (`repair:178`) gives `Q (v : M) < 0`
   in ambient Mukai terms from `HasSignatureTwo (Q.restrict P)` plus a positive
   pair in P.  It consumes the sublattice signature witness, which is the new
   theorem above.  Report lines 285-286 overstate this.
6. **Non-vacuity of the charge leaf.**  `a2RealForm := weightedSumSquares ℝ ![1,1]`
   (`repair:255`) satisfies `HasSignatureTwo` (`:258`, same shape as the
   repository's `stdForm_hasSignatureTwo`, `PeriodDomain.lean:426`), and
   `a2RealForm_no_sphericalClass` (`:271`) proves the cut is empty — the right
   picture for a very general cubic fourfold, where H̃_alg(Ku X) = A₂ is positive
   definite of rank 2 and there are no walls.  The **shape** is inhabited; the
   geometry is not.  Both are `example`s, not theorems, and are labelled as
   shape-inhabitation.
7. **The repository has nothing Kuznetsov-specific, re-verified.**
   `grep -rni kuznetsov DerivedAlgGeo` returns exactly two disclaimers:
   `AlgebraicGeometry/Surface/Enriques/Residual.lean:20` and
   `LinearAlgebra/Lattice/Numerical/RankTwo.lean:13`.  `RankTwo.lean:11-21` is a
   rank-2 model for K_num(Ku X) ≅ ℤ² that explicitly refuses to discharge the
   identification ("tracked as an assumption-frontier obligation — never
   discharged here", `:17`).  No `KuznetsovChargeData` is introduced, per N12.
8. **A defect outside the assigned sections.**  Report lines 2652-2653 state
   that "H̃(Ku(X),ℤ) is an even lattice of signature `(2,·)` containing `A₂`".
   That is wrong in the same way as §2.3/§2.4: H̃(Ku X, ℤ) has signature (4,20)
   (the critic says so at `critic.md:288`).  The signature-(2,·) lattices are
   A₂^⊥ (2,20) and H̃_alg (2,ρ), both strictly smaller.  `charges-03` in §3.A
   needs the same correction.

**Negative results.**

- **N-fu7-1 refuted:** `pairing_comm_parity` at n = 4 ⟹ the fourfold node.
  False two ways — wrong lattice (dim 5 against rank 24, with no map between
  them constructed anywhere) and wrong predicate (symmetry is automatic, so
  parity is vacuous even on the right space).
- **N-fu7-2 refuted:** the fourfold charge leaf and the fourfold period-domain
  leaf are one node.  The stability charge of Ku(X) lives on H̃_alg(Ku X),
  signature (2,ρ), which for a very general cubic fourfold **is** A₂ — rank 2,
  positive definite.  The period domain lives on A₂^⊥, rank 22, signature
  (2,20).  For a very general X the two are orthogonal complements inside
  H̃(Ku X)⊗ℝ, so the only linear map between them is zero and **no comparison
  theorem can exist**.  They share only the parent (`HasSignatureTwo` plus a
  positive pair ⟹ `PeriodDomain.centralCharge`).  §2.3 line 169 as written puts
  the charge on the wrong one of the two.
- **N-fu7-3 confirmed-negative** (report §2.6 N11 is right; §2.3 line 155
  contradicts it): neither fourfold leaf is a child of `Mukai.expCharge`.
  `expCharge`'s pair is the exponential pair on a `Mukai.RealExtension V`
  (`LinearAlgebra/Lattice/Mukai/CentralCharge.lean:36`); neither the (Re ℧, Im ℧)
  plane in H̃_alg nor the period plane in A₂^⊥ is exponential.  Sibling, not
  child.
- **Not refuted but not dischargeable: the geometry.**  F1 existence of
  H̃(Ku X, ℤ); F2 its signature (4,20); F3 the distinguished A₂ and positive
  definiteness of its real form; F4 `IsCompl` with orthogonality; F5 that
  (Re ℧, Im ℧) is a positive pair for the charge leaf.  All five are geometry
  upstream of this repository — the same class of obligation
  `RankTwo.lean:13-17` already refuses to discharge.  R4's fourfold line is an
  **open-obligation node**, not a delivered leaf.

**Open obligations.**  F1–F5 as above, each stated as a hypothesis of the proved
theorem and none discharged.  Plus:

- **Placement (review obligation, not a gate).**  `centralCharge_restrict` and
  `centralChargeHom_restrict_eq` extend `PeriodDomain.centralCharge`, so by
  `placement.md` tier 1 they belong beside it in
  `LinearAlgebra/QuadraticForm/CentralCharge.lean`, and
  `hasSignatureTwo_restrict_of_posDef_rankTwo` beside `sigPos_eq_add` in
  `SignatureAdditive.lean`.  Landing them requires making
  `QuadraticMap.polar_restrict` (`SignatureAdditive.lean:62`) non-private rather
  than adding a second copy — the repair file restates it locally as
  `polar_restrict'` (`repair:77`) only because it is a scratch file.
- **Root review.**  No new structure is proposed, so the two-consumers rule is
  not triggered.  If anyone later proposes a fourfold carrier, its two candidate
  consumers do not share a lattice, and N12 already refuses it.
- **From the verifiers.**  `outcome: partial` must not be read as "half
  delivered": what is delivered is a lattice-theoretic transfer every one of
  whose hypotheses is an open geometry obligation, so PR-12b is blocked end to
  end.  The §2.3/§2.4 amendments state the H̃_alg and A₂^⊥ signatures as facts
  in the tree diagram; they are assumption-frontier claims and are marked as
  such in §2.1 above.  The N11b amendment text should also carry the second half
  of N-fu7-2 (no comparison between the two new leaves can ever exist).

**Checker verdicts.**  Both verifiers: **sound**; both re-ran the elaboration
and verified every repository citation, including the two-disclaimer grep and
the three `SignatureAdditive` lemmas.  Self-citation drift of about +7 inside
the scratch file was corrected (`centralCharge_restrict` `:83` not `:85`;
`centralChargeHom_restrict_eq` `:92` not `:94`;
`hasSignatureTwo_restrict_of_posDef_rankTwo` `:123` not `:130`;
`hasSignatureTwo_orthogonal_a2` `:148` not `:155`;
`neg_of_centralCharge_restrict_eq_zero` `:178` not `:187`; `a2RealForm` `:255`
not `:262`; `a2RealForm_hasSignatureTwo` `:258` not `:266`;
`a2RealForm_no_sphericalClass` `:271` not `:279`).  Both verifiers recorded that
F1–F5 and the "H̃_alg = A₂ for a very general X" claim are external mathematics,
not repository facts.

### 3.5 fu8 — carry the −i rotation into the exemplar

**Outcome: proved.**  The rotation is `phaseTiltRotation (1/2)`, it is free on
walls and **not** free on phases, and the (3,2) tilt charge is not a new
polynomial at all.

**Lean evidence.**  `repair-fu8-rotation.lean`, 333 lines, `grep -c sorry` = 0.

```
$ cd /Users/chris.dare/Personal/SourceCode/dag-abstraction-audit && \
  LEAN_NUM_THREADS=2 lake env lean .../scratchpad/repair-fu8-rotation.lean
(no output — 0 bytes on stdout+stderr)
EXIT=0
$ grep -c sorry repair-fu8-rotation.lean
0
```

**Sorries: none.**

**Findings.**

1. **Citation confirmed and corrected.**  `phaseTiltRotation` is at
   `Weak/Tilting/Semistable/TiltGeometry.lean:42` (the report's `:43` is off by
   one); `:48` is `phaseTiltRotation_apply`, `:53` is `phaseTiltCharge`.  It is
   `z ↦ z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)`, never zero.
2. The BLMS rotation is `beta = 1/2`: `phaseTiltRotation (1/2) z = -Complex.I * z`
   and `-Complex.I = 1 / Complex.I` (`repair:59`, `:44`), so it is "division by
   i" as BLMS write it.
3. **Vehicle confirmed:** `ChargeFamily.smul` (`Walls/ChargeFamily.lean:302`) is
   the right vehicle, not the general `linearAct` (`:273`).  `smul` multiplies
   on the left while `phaseTiltRotation` multiplies on the right; ℂ is
   commutative and the identification is **proved**, not assumed
   (`phaseRotate_charge`, `repair:97`).
4. `ChargeFamily.wall_smul` (`Walls/ChargeFamily.lean:322`) is the theorem that
   makes walls invariant; its hypothesis `c ≠ 0` is discharged by
   `Complex.exp_ne_zero` (`repair:66`, `:103`).
5. **Stronger than wall-invariance:** the rotation fixes every wall
   *expression*, not only the zero locus, because `Complex.normSq (exp(-πβi)) = 1`
   (`repair:48`, `:109`, via `wallValue_smul`, `ChargeFamily.lean:317`).  No
   wall-radius, nesting or semicircle statement changes under it.
6. **No-duplication bridge:** `ChargeFamily.phaseRotate` is tied to the
   pre-existing `phaseTiltCharge` (`TiltGeometry.lean:53`) by a proved
   comparison — on the constant family of a `WeakPreStabilityCondition`'s charge
   the two agree on the nose (`phaseRotate_constFamily`, `repair:148`).  No
   second rotation is introduced.
7. **The (3,2) tilt family needs no new polynomial and no `Exp` kernel.**
   `Tilt.tiltFamily = (stChargeFamily.reindex Prod.swap).pullback threefoldTruncate`
   (`repair:182`), using only declarations that exist today: `stChargeFamily`
   (`Walls/Numerical/ChargeFamily.lean:59`) and a four-to-three coordinate drop.
   Verified by reading both polynomials: `reZ s t v = -ch2 + s·deg - s²/2·rk + t²/2·rk`
   (`Walls/Numerical/Basic.lean:124`) is the threefold tilt real part at
   (s,t) = (β,α), and `imZ s t v = t·(deg - s·rk)` (`:128`) is its imaginary
   part.  The chart transposition PR-8 anticipates is exactly the `Prod.swap`.
8. **The truncation map the report says does not exist** is built and proved
   additive as `Tilt.threefoldTruncate : Threefold.NumClass →+ NumClass`
   (`repair:173`), `v ↦ (v.deg0, v.deg1, v.deg2)`.  It needs nothing from
   `Walls/Exp/`, so PR-8's tilt node does **not** depend on PR-1..PR-5.
9. **`Threefold.nu` and the (3,2) tilt charge are not the same object** — nu is
   a real slope, the charge is a `Threefold.NumClass →+ ℂ`.  The relation is
   proved twice: `nu_eq_tilt_slope` (`repair:234`), `Threefold.nu α β v = -(α · Re Z) / Im Z`
   for `α ≠ 0`; and `chargeSlope_tilt` (`:242`),
   `chargeSlope (tiltFamily.charge (α,β) v) = ν/α` for `0 < α` and `0 < Im`.
   Supporting computations at `:190` and `:199` match `Threefold.nu`
   (`Walls/Threefold/Basic.lean:208`) term for term.
10. **The §2.5 formula is correct but under-specified.**  `ν = α · chargeSlope(…)`
    on `0 < im` is true, but only for the (3,2) tilt charge, never for
    `Threefold.charge` (`Walls/Threefold/Basic.lean:148`), whose real part
    carries `-deg3`.  The row as written names no charge, which is how the ch₃
    charge and the tilt charge got conflated.  `chargeSlope` is at
    `Weak/Foundation/StabilityFunction/WeakSlopeGeometry.lean:63`.
11. **Wall transfer to the surface theory is now a one-line consequence:**
    `rotatedTiltFamily_wall_eq_preimage` (`repair:223`) proves every rotated
    ν-wall is `Prod.swap ⁻¹'` of an existing `stChargeFamily` wall, via
    `reindex_wall` (`ChargeFamily.lean:329`) and `pullback_wall` (`:338`).
    PR-8's stated motive — applying `walls_nested_of_discr_nonneg`
    (`Walls/Numerical/Nested.lean:179`), `wall_circle_eq`
    (`Walls/Numerical/Basic.lean:183`) and `wall_eq_of_meet` (`:473`) to ν-walls
    — is discharged by this one theorem.  All three citations verified.
12. **Placement.**  Nothing here is a new structure, so
    `check_single_instantiation.py` and the two-consumer rule are not engaged.
    `Walls/ChargeFamily.lean` today imports only `Mathlib.Data.Complex.Basic`
    and `Mathlib.Tactic`, so the `phaseTiltRotation` bridge must **not** go
    there; `Walls/` may import `Weak/` (precedent:
    `Walls/Divisorial/Support.lean:7`; `layers.md:141-142` names `Weak` the
    dependency parent), so the rotation belongs in a new `Walls/Rotation.lean`
    and the threefold tilt leaf in a new `Walls/Threefold/Tilt.lean`.  No
    geometry import anywhere, so the firewall is untouched.

**Negative results.**

- **N-fu8-a falsified:** "the (3,2) tilt family is a chart change of
  `Threefold.chargeFamily`".  The two have genuinely different wall loci.
  Witness proved at `repair:280` with both sides computed: at (α,β) = (1,0),
  `v = (0,0,1,0)`, `w = (0,0,0,1)`, the tilt wall expression is 0 (`:259`) and
  the full threefold one is 1 (`:267`, via `Threefold.chargeFamily_wallValue`,
  `Walls/Threefold/Basic.lean:183`).  Reason: the (3,2) charge never reads
  `deg3`.  So the tilt node is a real additional leaf under R1a, and §2.3/§2.4
  may not present it as a reindexing of the m = 3 node.
- **N-fu8-b falsified:** "the rotation is cosmetic, so the report can omit it".
  Walls are invariant but **phases are not**: `chargeSlope` changes.  Proved at
  `repair:298` — at the same (1,0) and `v = (0,0,1,0)` the tilt charge is −1
  (Im = 0, so `chargeSlope = ⊤`, the real boundary) while the rotated charge is
  i (Im = 1 > 0, `chargeSlope = 0`).  This is precisely why BLMS rotate.
  Dropping it, as `design-final.lean:567-569` does, keeps the walls and loses
  the stability condition.
- **Not falsified, but unproved in the design:** the design carries two routes
  to the same (3,2) object — `tiltWallChargeFamily := wallChargeFamily V P κ 2`
  at the R3 level (`design-final.lean:567-569`) and the R1a
  `Exp.tiltChargeFamily` (`:196-200`).  Neither is compared to the other, nor to
  the `Walls`-level route proved here.

**Open obligations.**

- `phaseRotate` must land in a new `Walls/Rotation.lean`, **not** in
  `Walls/ChargeFamily.lean`: adding a `Weak/Tilting/` import to that root would
  make the wall root stability-aware.
- **Three unbridged spellings of the (3,2) charge.**  `tiltWallChargeFamily`
  (`design-final.lean:567`), `Exp.tiltChargeFamily` (`:197`) and `Tilt.tiltFamily`
  (`repair:182`) are three routes with no comparison between any pair.  Both
  verifiers flagged this as the one live duplication risk in the repair set.  It
  is promoted here from a note to a **blocking obligation** on whichever of PR-6
  and PR-8 lands second.
- The rotation is proved free on **walls** only.  The BLMS statement that the
  rotated charge is a stability function on the tilted heart is not proved here
  and is not a wall-level fact: it needs
  `phaseTiltCharge_im_pos_of_phaseTors` (`TiltGeometry.lean:278`) and the
  `WeakUpperClosed` machinery (`TiltGeometry.lean:68`).  PR-11 owns it.
- `Threefold.nu` may exist a second time as `BMT.nu` (`Stability/BMT.lean:111`,
  per report line 3051).  **Unconfirmed** — sourced to the report, not to the
  tree, and the first verifier explicitly did not check it.  Whoever lands
  `nu_eq_tilt_slope` must grep `BMT.lean` first and state the projection for
  whichever of the two survives, retiring the other, or this repair adds a third
  slope.

**Checker verdicts.**  Both verifiers: **sound**; both re-ran the elaboration
and found every self-citation exact, and both independently confirmed the two
witness-based negative results.  Three repository citations corrected:
`ChargeFamily.reindex_wall` is `Walls/ChargeFamily.lean:329`, not `:331`; `imZ`
is `Walls/Numerical/Basic.lean:128`, not `:131`; `WeakUpperClosed` is
`TiltGeometry.lean:68`, not `:70`.

## 4. Adjudications

### 4.1 fu4 — walls-02 against lattices-02

**Decision.**  `lattices-02`'s parent **wins**, in corrected form.  `walls-02`'s
proposed Δ_H on H-degree vectors **loses** and is recorded as a negative result.
One parent: the **fixed-arity** Mukai triple self-pairing
`q_b(r, c, s) = b(c,c) − 2rs`, which already exists twice — `Mukai.selfPairing`
over ℤ (`LinearAlgebra/Lattice/Mukai/Basic.lean:143`) and `Mukai.realPairing`
over ℝ (`RealForm.lean:87`) — and is to be **generalised in place over the
coefficient ring**, not re-declared.  Both are **not** needed: walls-02's Δ_H is
that same root at `V = ℝ`, `b = mul` (proved), and is strictly narrower.  A
"third parent" in the sense of a new object also loses: the only thing the
existing root lacks is coefficient-ring genericity, and that is a generalisation
of an existing declaration.

The merged finding is `discr-01` and it supersedes both.  It replaces report
lines 942-1010 (`walls-02`) and 2021-2085 (`lattices-02`).

**Evidence.**  `adj-discr.lean`, 209 lines, 17 theorems plus one example,
EXIT=0, no sorries, no warnings; re-run by both verifiers.  All eight leaf
projections compile:

| # | Leaf | Location | Projection (all proved) |
|---|---|---|---|
| 1 | `Wall.NumClass.discr` | `Walls/Numerical/Discriminant.lean:70` | `= realPairing (mul ℝ ℝ) v v`; carriers defeq, no equivalence needed |
| 2 | `Wall.Threefold.discr` | `Walls/Threefold/Basic.lean:204` | `= realPairing (mul) (v.1, v.2.1, v.2.2.1) (…)` — the codimension-2 **truncation** of the 4-slot class; plus `Threefold.discr (betaTwist β v) = Threefold.discr v` |
| 3 | `ChargeCoordinates.discr` | `Walls/Divisorial/Discriminant.lean:288` | at `(hyperplaneSquare · rank E, degree E, chTwo E)` |
| 4 | `ChernCharacter.discriminant` | `Walls/Divisorial/Discriminant.lean:227` | `= realPairing S.intersection (ch.toRealExtension E) (…)`, through the existing `toRealExtension` (`Charge.lean:108`) |
| 5 | `NumericalVarietyData.discriminant` | `Numerical/GrothendieckGroup/Discriminant.lean:31` | `R = M = A`, `b = mul A A`, triple `(algebraMap ℚ A (rank E), chComp E 1, chComp E 2)`; needs `map_mul, map_ofNat` — **not** `rfl` |
| 6 | `Surface.discrH` | `Numerical/Stability/Slope.lean:174` | `R = M = ℚ`, triple `(degree (P.cls^2) · rank E, degH V P E, degree (chComp E 2))` |
| 7 | `Threefold.discrHBeta` | `Numerical/Stability/BMT.lean:103` | `R = M = ℚ`, triple `(degree (P.cls^3) · rank E, degH1Beta β E, degH2Beta β E)`; β provably inert |
| 8 | `ChernCharacter.barDiscriminant` | `Walls/Divisorial/Discriminant.lean:240` | at `(ω·ω·rank E, ω·ch₁^B, ch₂^B)` |

**Rationale.**

- **walls-02 and lattices-02 are not rivals.**  They are the same equation at
  different generality.  `Wall.NumClass` is `abbrev NumClass : Type := ℝ × ℝ × ℝ`
  (`Walls/Numerical/Basic.lean:104`) and `Mukai.RealExtension V` is
  `abbrev … := ℝ × V × ℝ` (`RealForm.lean:82`); at `V = ℝ` the carriers are
  defeq, so leaf 1 needs no equivalence.  walls-02 proposing a new Δ_H is
  exactly the two-declarations-of-one-equation error the audit exists to stop,
  committed by the audit — the critic's charge is upheld.
- **lattices-02 wins rather than tying** because its root's middle slot is a
  module with a bilinear form, and walls-02's is a scalar.  Leaf 4's middle slot
  is `S.pair (ch.chOne E) (ch.chOne E)` with `S.intersection` on an unrestricted
  `DivisorSpace D` (`Charge.lean:60`, no Picard-rank assumption).  A scalar-slot
  root cannot express it; walls-02 concedes this in its own text and thereby
  abandons 2 of the 7 leaves it claims.
- **lattices-02 needed correcting.**  Its text scopes the root to "every
  ℝ-valued leaf", but three of its listed leaves are not ℝ-valued:
  `Surface.discrH : ℚ`, `Threefold.discrHBeta : ℚ`, and
  `NumericalVarietyData.discriminant : A` for a `CommRing A` with `Algebra ℚ A`.
  `Mukai.realPairing` is hard-wired to ℝ and `Mukai.pairing` to ℤ, and no
  ℚ-valued Mukai pairing exists in the tree.  Its claim that those three are
  "pointwise identities" is false as stated.  The fix is one generalisation, not
  a fourth copy.
- **The N5 collapse decides the arity, and is verified rather than quoted.**
  `pairing_three_self_eq_zero` proves `pairing 3 v v = 0` for **every** v by
  expansion.  So the parent has fixed arity three, and the threefold leaf is
  rescued by **truncation** (`leaf2`), not by an n = 3 form.  This kills the
  sketch's implied route and vindicates N5 verbatim.  It also means
  `Mukai.Graded.pairing` may own the charge and the parity theorem but must
  **not** own the discriminant.
- **The weights.**  Leaves 3, 5, 6, 7, 8 carry an `∫H^k` (or `ω²`) factor that
  lattices-02 glossed over.  It goes in the **rank** slot, never the middle
  slot.
- **Placement.**  `placement.md` tier 1 ("Lattices, bilinear forms … →
  `LinearAlgebra/`") puts the root where `Mukai.pairing` already is.  The
  `layers.md` firewall is satisfied.  `check_single_instantiation.py` is not
  engaged: the root is a `def`, no new `structure` head.  The bundled
  `QuadraticForm` walls-02 wanted to reuse, `DivisorSpace.realDiscriminant`
  (`Walls/Divisorial/Support.lean:92`), **cannot** be the root in place —
  `Support.lean:5` imports `Walls/Divisorial/Discriminant.lean`, so it sits
  downstream of two leaves it would parent, violating `abstraction-tree.md`
  root-review item 5.  Its body is one line, so it moves up to `RealForm.lean`
  beside `realForm` with zero new imports; `realDiscriminant_eq_self` proves the
  move is content-free.
- **Already-correct leaf, mis-listed.**  lattices-02 lists
  `Wall.Spherical.selfPairing_mk` (`Walls/Spherical/Basic.lean:132`) as a
  declaration to re-root.  It is already rooted: `Spherical.pairing` (`:117`) is
  `abbrev pairing v w := Mukai.realPairing q v w`, and its docstring (`:108-116`)
  records this exact merge having been done once before.  Cite it as the
  pattern, not as a duplicate.

**Mandatory bridges** (all compiled in `adj-discr.lean`, so the merged finding
never proposes an unbridged duplicate): `candidate_eq_realPairing` and
`candidate_eq_selfPairing` (the ring-generic root reduces to the two existing
roots on the nose); `graded_two_eq_realPairing` (the sketch's
`Mukai.Graded.pairing` at n = 2 is not a new object — this closes the critic's
unbridged-pairing charge for the discriminant half); `realDiscriminant_eq_self`;
and `realForm_is_half` (N9 confirmed — `realForm` is **not** the root, and
taking it would silently scale every wall child by 2).

**The losing option, recorded per `abstraction-tree.md:365`.**

- **NR-D1.**  Rejected: any parent of the discriminant family indexed by the
  ambient dimension — walls-02's `HDegree.discrForm n`, and equally
  `Δ_H := Mukai.Graded.pairing n v v`.  Counterexample, proved not quoted:
  `pairing 3 v v = 0` for every class, by expansion over `Fin 4`.  The graded
  Mukai pairing is symmetric in even dimension and **alternating** in odd
  dimension, so its self-pairing vanishes identically whenever n is odd — fatal
  for `Wall.Threefold.discr`.  Consequence, not a dead end: the parent has fixed
  arity three and the threefold leaf reaches it by truncation.
- **NR-D2.**  Rejected: merging `discDegH` (`Slope.lean:143`,
  `V.ring.degree (V.discriminant E * P.cls ^ (n - 2))`) into this family.  It is
  not the same polynomial as `discrH` (`Slope.lean:174`): the two differ by the
  Hodge-index defect, and `discrH_nonneg`
  (`Stability/BogomolovGieseker.lean:135-140`) spends a full
  `HodgeIndexStatement` plus `BogomolovGiesekerData` plus `nlinarith` to cross
  between them.  The repository's own docstring records this at
  `Slope.lean:167-173`.
- **NR-D3.**  Rejected: lattices-02's stated projection that
  `ChargeCoordinates.discr`, `discrH` and `discrHBeta` are "pointwise
  identities" against `Mukai.realPairing`.  Three of the seven shared leaves do
  not reach the root as lattices-02 states it.  This is not a falsified
  unification — it is repaired by the coefficient-ring generalisation — but the
  original claim is false and is recorded as such.  Additionally, none of the
  five weighted leaves is an identity without moving the `∫H^k` factor into the
  rank slot.
- **NR-D4.**  `Wall.Spherical.selfPairing_mk` is not a duplicate; no work is
  owed on it.

**Tree amendments.**  Record `Mukai.pairing` / `selfPairing`
(`Lattice/Mukai/Basic.lean:143`), generalised over the coefficient ring, as the
canonical root of the Bogomolov/Mukai discriminant, **with the note that its
arity is fixed at three** and that no dimension-indexed generalisation of it
exists (NR-D1).  Record that `Mukai.Graded.pairing n`, if it lands, owns the
charge and the parity theorem and explicitly does **not** own the discriminant,
with `pairing_three_self_eq_zero` as the stated reason.  Strengthen §2.6 N5's
second sentence from "would silently collapse to 0 for every odd n" to "is
identically zero for every odd n and for every class, by expansion — proved".

**Checker verdicts.**  Both verifiers: **sound**; both re-ran `adj-discr.lean`
and re-verified all eight leaf citations, the import-direction defect
(`Support.lean:5`), and the mis-listed Spherical leaf.  Both raised the same
**internal inconsistency, corrected above**: the decision text says "no new
declaration is created" and "generalise in place", while the verification file
introduces `mukaiSelfPairingOf` and the replacement text calls it "the candidate
shape".  Landed as a `def`, it would be a third spelling beside `Mukai.pairing`
and `Mukai.realPairing` — bridged, since both comparisons are compiled, but
still a third name.  The finding must ship shape (a): **generalise
`Mukai.pairing`'s binders over `CommRing R` and make `Mukai.realPairing` an
`abbrev` for it at R = ℝ**.  The declaration list, not only the rationale, must
say so.  The second verifier also noted that the root-review "adoption" item
counts the ℚ and A lanes as adopters of a root that does not yet exist in
generalised form; that is adoption of the *proposed* root and should be said
plainly.  One citation corrected: the `discrH` docstring runs `Slope.lean:164-173`
with the quoted sentence beginning at `:167`, not `:168-175`.

### 4.2 fu9 — root review of geometry-derived-06

**Decision: REPLACE.**  Reject `structure GeometricSerreFunctor`; the finding
becomes "supply a bridge to the existing root and add no structure."  Kind
changes existing-root-unused → **missing-bridge**; impact **HIGH → MEDIUM**;
confidence 0.8 → 0.85 for the corrected claim.  The underlying observation
(geometric Serre duality never reaches `SerreFunctorData`) survives and is
verified.  The proposed remedy fails the Adoption clause
(`abstraction-tree.md:356-357`) on both of its branches and would add a **third**
bare `Coh X → Coh X` canonical-twist function to a tree that already carries
two.

**The six clauses of `abstraction-tree.md:349-368`.**

1. **Canonical owner.**  Two existing roots cover the proposal.  The duality half
   is `CategoryTheory.SerreFunctor.SerreFunctorData`
   (`SerreFunctor/Basic.lean:72`) with its autoequivalence strengthening
   `SerreCategoryData` (`:102`); the proposed `serre` field is that structure
   verbatim.  The twist half is owned by
   `AlgebraicGeometry.SmoothProperVariety.CanonicalSheafData`
   (`Duality/Canonical/Basic.lean:48`), which already holds ω_X as
   `canonicalLineBundle` (`:64`) and `canonicalSheaf` (`:69`) and already places
   it in the derived category as `canonicalCohObject` (`Canonical/Derived.lean:67`)
   and `dualizingComplex` (`:72`).
2. **Adoption — the clause the finding fails, on both branches.**
   *Branch A, "name two independent consumers": not satisfiable.*  The only
   consumer of the distinguishing `twist`/`twistIso` fields is
   `Duality.Serre.BilinearData` (`Duality/Serre/Bilinear.lean:104`), whose
   `canonicalTwist : Coh X → Coh X` (`:116`) the root would duplicate — and
   `BilinearData` is itself referenced by no module outside its own file, so a
   root whose sole leaf is an unconsumed leaf has adoption zero.  Every other
   candidate is refuted: `Duality.Serre.Data` (`Serre/Cohomology.lean:114`)
   states `duality` (`:127-128`) against `FiniteCohomology.moduleH` in
   `X.Modules`, not against `Hom` in any derived category; `DerivedStatement`
   (`:61`) is functor-level with `rHomDualizing` supplied; and
   `EnriquesSurface.IsotropicCollection.PaperCategoryData`
   (`Surface/Enriques/PaperObjects.lean:60`) — the one geometric consumer that
   genuinely wants a Serre functor on Dᵇ(Coh Y) — **already takes the old root**,
   at `ambientEnriques : TwoEnriquesCategoryData k (DerivedCat Y)` (`:63`), which
   is `SerreCategoryData k (Dᵇ(Coh Y))` by `EnriquesCategoryData … extends
   SerreCategoryData` (`SerreFunctor/Enriques.lean:38-39`, `abbrev` `:44`) at
   `DerivedCat Y = SchemeBoundedCoherentDerivedCategory Y`
   (`Surface/Enriques/Exceptional.lean:61-62`).  It uses no twist; adopting the
   new root would give it nothing.  The audit's grep was string-level and missed
   the `extends`.
   *Branch B, "statement-layer data whose purpose is to compare multiple
   inhabitants": also not satisfiable*, because the **old** root already is
   that: `SerreFunctor.Uniqueness.exists_uniqueIso (D D' : SerreFunctorData k C) :
   Nonempty (D.S ≅ D'.S)` (`Uniqueness.lean:200`) is the comparison, proved
   generically.  On a fixed X there is nothing further to compare, and the
   wrapper adds no inhabitant: nothing in the tree constructs a
   `SerreFunctorData` or a `SerreCategoryData` — both sit on
   `scripts/single_instantiation_baseline.txt:14,16` at the ≤ 1 threshold, i.e.
   only their own `.mk`.
   This also corrects the audit's repository verdict (report lines 1946-1947),
   which carried the finding on the claim that "the bridge gives the
   already-baselined `SerreFunctorData` a second inhabitant".  That is wrong
   twice: it would be the first, not the second, and a structure **field** is a
   consumer rather than an inhabitant — the exact mistake the gate's own
   docstring names at `check_single_instantiation.py:29-36`.
   CI cannot catch this: `GENERIC_SUBJECTS` (`:55-58`) excludes
   `AlgebraicGeometry` and the proposed module is
   `AlgebraicGeometry/Duality/Serre/SerreFunctor.lean`.  The obligation is
   entirely on review.
3. **Projection.**  The single claimed projection is not writable as the report
   states it, on two counts, both checked by elaboration.
   *(3a) The sketch is ill-typed.*  It puts
   `serre : SerreCategoryData k (SchemeBoundedCoherentDerivedCategory X)` and
   then writes `serre.serre.S.obj ((single _ 0).obj E)` in that category, but
   `DerivedCategory.singleFunctor (Coh X) 0` lands in the **unbounded**
   `SchemeCoherentDerivedCategory X` (`Coherent.lean:51`), not in
   `SchemeBoundedCoherentDerivedCategory X` (`:56-58`), and no
   `Coh X ⥤ Dᵇ(Coh X)` exists in the tree (`exact?` fails; boundedness is
   supplied per object, e.g. `LineBundleData.boundedDerivedObject`, `:230`).
   This is a real fault line: the existing `Duality` lane is stated on the
   unbounded category (`Serre/Cohomology.lean:64,68`; `dualizingComplex`,
   `Canonical/Derived.lean:72-73`), while `PaperCategoryData` and
   `Surface/Spherical` live on the bounded one.
   *(3b) Root ⟹ `BilinearData` is not a forgetful projection.*
   `BilinearData.extComparison` (`Bilinear.lean:108`) is only an iso of
   `AddCommGrpCat` after `forget₂`, so a *supplied* `BilinearData` can never be
   shown to be the Hom-realization — the k-structure is not comparable.  The
   writable bridge instead *defines* the realization:
   `extSpace E F j := ModuleCat.of k ((single 0 E) ⟶ (single 0 F)⟦j⟧)`, with
   `extComparison` obtained by forgetting `Abelian.Ext.homLinearEquiv` (the route
   already used at `HomFinite.lean:103,139`) and `extFinite` from
   Hom-finiteness.  That is a legitimate `def` — a theorem about the **old**
   root requiring no new structure, which is the whole of the corrected finding.
   Prerequisites, both verified absent by `exact?`:
   `HomFiniteBounded k (Dᵇ(Coh X))` and its heart-level input
   `DerivedCategory.ExtFiniteBounded (Coh X)` (`HomFinite.lean:75`, route at
   `:400`).  What **is** available, also verified: `Linear k (Dᵇ(Coh X))` and
   `HasShift (Dᵇ(Coh X)) ℤ` both synthesize.
4. **Diamond.**  Required, non-trivial, and absent from the report.
   `Bilinear.lean:66-97` documents that `HasExt` must be passed explicitly in
   this lane because the small-site `HasExt.{u}` would name different groups than
   the `HasExt.{u+1}` these statements mean, and it declares its own named
   `local instance` twice (`:76`, `:96`); `HasDerivedCategory.standard` is
   likewise `local` (`Serre/Cohomology.lean:41`, `Coherent.lean:36`).  Any bridge
   transporting `Module.Dual k (extSpace E F i)` to
   `Module.Dual k (single E ⟶ (single F)⟦i⟧)` crosses exactly that diamond, so
   the acceptance criterion is a compile-time agreement test.
5. **Dependency direction.**  Satisfied, and unaffected by dropping the
   structure.  `Duality/Serre/` already imports
   `AlgebraicGeometry/DerivedCategory/Coherent.lean` (`Serre/Cohomology.lean:6`)
   and would add `CategoryTheory/Triangulated/SerreFunctor/Basic.lean`, which
   imports no geometry (`Basic.lean:5-7`).  The firewall runs in the correct
   direction (`layers.md:29-34`), `Duality/` stays stability-neutral (`:57-59`),
   and no leaf is imported (`:177`).  Placement under
   `AlgebraicGeometry/Duality/Serre/` is correct by the gate script's own rule
   (`check_single_instantiation.py:51-54`).  `proposition-classes.md` does not
   apply — nothing proposed is a Prop-valued class.
6. **Negative results.**  Four, recorded rather than hidden.

**Negative results.**

- **N1.**  `Duality.Serre.Data` does **not** project from any categorical Serre
  functor and must stay separate.  Its `duality` field
  (`Serre/Cohomology.lean:127-128`) is
  `Module.Dual k ((D.moduleH i).obj F) ≃ₗ[k] extSpace F (n - i)`, where
  `moduleH` is a `FiniteCohomology` realization on `X.Modules`.  Deriving it from
  `SerreFunctorData.eta` requires `H^i(X,F) ≃ₗ[k] Hom_D(𝒪_X, F⟦i⟧)`, which the
  tree does not have anywhere.  A genuine falsified unification.
- **N2.**  `DerivedStatement` neither implies nor is implied by a pointwise Serre
  functor.  It is functor-level (`Cohomology.lean:61-77`) and its module
  docstring (`:24-27`) records the upstream reason: the pinned Mathlib has no
  derived global-sections functor into `D(k)`, no coherent `RHom`, and no
  Grothendieck-duality theorem.  `SerreFunctorData` is deliberately pointwise
  (`SerreFunctor/Basic.lean:43-49`).
- **N3, corrected by both verifiers.**  The audit justifies a bare
  `twist : Coh X → Coh X` on the ground that "there is no `−⊗ω_X` functor on
  `Coh X`" (report lines 1940-1942) / "no tensor endofunctor on `Coh X`
  anywhere" (`:1951`).  The original repair text called the second claim false,
  citing `Scheme.Modules.tensorLeftFunctor` (`Modules/Tensor/Invertible.lean:40`).
  **That refutation does not hold**: `tensorLeftFunctor` is an endofunctor of
  `X.Modules`, not of `Coh X`, and fu9's own `exact?` failure on
  `IsCoherent (ω_X ⊗ F)` confirms no endofunctor of `Coh X` exists today.  What
  survives, and is what matters, is verified: the gap is exactly **one**
  coherence-preservation lemma, `IsCoherent F → IsCoherent (L ⊗ F)` for
  invertible `L`, which the tree already re-supplies as data twice
  (`TwistContext.twistFamily`, `IntersectionTheory/Surface/Number.lean:254`;
  `isCoherent_tensor_linePower`,
  `Stability/Gieseker/HilbertPolynomial.lean:156`).  So the correct action is W2
  below, not a third bare function beside `BilinearData.canonicalTwist`
  (`Bilinear.lean:116`) and `LocallyFreeSpecialization.dualCanonicalTwist`
  (`Serre/Cohomology.lean:194`).  `tensorLeftFunctor` is additive (`:112`),
  preserves monos (`:160`), homology (`:166`), finite limits (`:173`) and short
  exact sequences for an invertible argument (`:207`).
- **N4.**  No comparison theorem is possible for the proposed root as sketched,
  because it is ill-typed (see 3a).  Recorded as a negative rather than silently
  repaired: the bounded/unbounded split is a real fault line in this lane and
  must be settled before any bridge is written, not hidden inside a new
  structure's field types.

**What to do instead — two work items, no new name.**

- **W1 (bridge).**  In `AlgebraicGeometry/Duality/Serre/SerreFunctor.lean`, a
  `def` taking `SerreFunctorData k (Dᵇ(Coh X))` plus the Ext-finiteness input and
  producing a `BilinearData`, with the `HasExt`/`HasDerivedCategory` agreement
  test of clause 4.  Settle the bounded/unbounded mismatch first — either give
  the tree a `Coh X ⥤ Dᵇ(Coh X)`, or state the bridge on
  `SchemeCoherentDerivedCategory X` where `singleFunctor` already lands.
- **W2 (twist owner).**  Prove `IsCoherent F → IsCoherent (L ⊗ F)` for
  invertible `L` once, next to `tensorLeftFunctor` in
  `Modules/Tensor/Invertible.lean`, then add
  `CanonicalSheafData.canonicalTwist : Coh X ⥤ Coh X` and migrate
  `BilinearData.canonicalTwist` and `LocallyFreeSpecialization.dualCanonicalTwist`
  onto it.  That retires the existing duplication instead of adding to it.

**Tree amendments.**  Record in `abstraction-tree.md` that Dᵇ(Coh X) reaching
`SerreFunctorData` is a **bridge** obligation, not a new root, naming the two
blockers by declaration (`ExtFiniteBounded` / `HomFiniteBounded`,
`HomFinite.lean:75,400`; and the absent `Coh X ⥤ Dᵇ(Coh X)`).  Add under "Root
review before a new structure" that a field of type `R` inside a proposed
structure is a **consumer** of `R`, never an inhabitant, cross-referencing
`check_single_instantiation.py:29-36`; this finding was carried 2–1 on exactly
that conflation.  Record the canonical owner of the geometric twist as
`CanonicalSheafData` and the two existing bare-function duplicates as a known
duplication awaiting the coherence lemma.  Record the bounded/unbounded fault
line.  Amend the `GENERIC_SUBJECTS` comment at
`check_single_instantiation.py:51-54` to say plainly that the
`AlgebraicGeometry` exclusion makes one-inhabitant geometric roots a **review**
obligation under `abstraction-tree.md:356-357`, with no gate behind it.

**Checker verdicts.**  Both verifiers: **sound**; both reproduced the two `exact?`
probe files exactly, including the failures (`fu9-serre.lean` exits 1 on the
`IsCoherent (ω ⊗ F)` goal alone, so the four probes above it elaborated;
`fu9-serre2.lean` exits 1 on exactly `HomFiniteBounded` and `ExtFiniteBounded`),
and both re-verified the `PaperObjects.lean:63` / `Enriques.lean:38-39` chain
that closes Adoption branch A.  Two corrections applied above: N3 is restated
(the report's claim is true as written; the inference from it was wrong), and
`isCoherent_tensor_linePower` is at
`AlgebraicGeometry/Stability/Gieseker/HilbertPolynomial.lean:156`, not under
`Moduli/`.  Both verifiers noted two limits on the evidence: the zero-producer
claim for `SerreFunctorData` / `SerreCategoryData` rests on a
declaration-pattern grep rather than on `scripts/EnumInhabitants` (the gate's own
criterion), and the W1 bridge is argued, not compiled.  Neither limit affects
the REPLACE verdict, which turns on Adoption, not on the bridge being written.

## 5. New coverage

Two follow-ups surveyed ground no lane reached.  Their findings are additional
to the 89 of the audit and are not counted in §6's de-duplication of those 89.

### 5.1 fu1 — `DerivedCategory/FourierMukai/`, the largest uncovered cluster

Zero of its 10 files were cited by any lane.  It holds 24 `^class Has`
declarations — verified exactly: `grep -rn '^class Has'` returns **24** in
`FourierMukai/` and **26** in all of `AlgebraicGeometry/`.  (The brief's further
claim that the directory holds 26 declarations is wrong: the per-file
declaration counts are DerivedTensorCoherence 17, KernelAdjunction 16,
KernelComposition 2, KernelAssociativity 8, KernelCorrespondence 32,
KernelConvolution 16, KernelSwap 19, KernelDualizingTwist 12,
KernelUnitConvolution 8, KernelUnit 9 — about 140 top-level declarations, four
to five times what the brief implies.  An earlier draft of this section said
"~114"; that figure was inconsistent with its own per-file list and is
withdrawn.)

Family key: **A** compositor at a commuting triangle · **B** unitor at an
identity · **C** base-change square · **D** projection formula · **E**
monoidal-compatibility record already bridged · **F** functor-supplying contract
(a root itself) · **G** adjunction/duality.

| # | class | file:line | family | how it reaches a root | root |
|---|---|---|---|---|---|
| 1 | `HasPullbackFactorization` | KernelAssociativity.lean:87 | A | `def` constructor (**not** `instance` — see the negative results) from the existing compositor + `subst comm` | `boundedCoherentDerivedPullbackComp`, Families/CoherentPullbackCoherence.lean:141 |
| 2 | `HasPushforwardFactorization` | KernelAssociativity.lean:101 | A | `def` constructor, **after** a missing bridge instance | `boundedCoherentDerivedPushforwardComp`, Families/CoherentPushforwardCoherence.lean:137 |
| 3 | `HasPullbackSwap` | KernelSwap.lean:112 | A | `def` constructor, `.symm` of #1's iso — literally #1 at `T:=Z, U:=X, π:=σ, r:=q` | same as #1 |
| 4 | `HasPushforwardSwap` | KernelSwap.lean:125 | A | `def` constructor, `.symm`, after the bridge | same as #2 |
| 5 | `HasCommonPullbackRoute` | KernelConvolution.lean:275 | A | `def` constructor: **two** compositors glued at the common composite `π₁ ≫ p₁` | same as #1 |
| 6 | `HasCommonPushforwardRoute` | KernelConvolution.lean:294 | A | same shape as #5, after the bridge | same as #2 |
| 7 | `HasPullbackRetraction` | KernelUnit.lean:114 | B | `def` constructor: #1 at `r := 𝟙 X`, then `≪≫` the existing unitor | `boundedCoherentDerivedPullbackId`, CoherentPullbackCoherence.lean:130 |
| 8 | `HasPushforwardRetraction` | KernelUnit.lean:128 | B | same, after the bridge | `boundedCoherentDerivedPushforwardId`, CoherentPushforwardCoherence.lean:126 |
| 9 | `HasFlatBaseChange` | KernelConvolution.lean:184 | C | **no root reached.**  Not a compositor: its guard is a *square*, not a triangle, and its iso mixes the two variances | none — negative result |
| 10 | `HasProjectionFormula` | KernelConvolution.lean:164 | D | candidate: projection of a bifunctorial root (strictly stronger) | none today |
| 11 | `HasProjectionFormulaRight` | KernelConvolution.lean:256 | D | candidate: the other projection of the same root | none today |
| 12 | `HasTensorUnit` | KernelUnit.lean:91 | E | **already bridged** — `hasTensorUnitOfCoherent`, KernelUnit.lean:103 | `HasCoherentDerivedTensor`, DerivedTensorCoherence.lean:57 |
| 13 | `HasDerivedPullbackTensor` | KernelConvolution.lean:201 | E | **already bridged** — `hasDerivedPullbackTensorOfMonoidal`, :211 | `HasMonoidalDerivedPullback`, DerivedTensorCoherence.lean:159 |
| 14 | `HasDerivedTensorAssoc` | KernelConvolution.lean:229 | E | **already bridged** — `hasDerivedTensorAssocOfCoherent`, :240 | `HasCoherentDerivedTensor` |
| 15 | `HasUnitPullbackRightUnitor` | KernelUnitConvolution.lean:81 | E | **already bridged** — `hasUnitPullbackRightUnitorOfMonoidal`, :103 | `HasMonoidalDerivedPullback` |
| 16 | `HasUnitPullbackLeftUnitor` | KernelUnitConvolution.lean:93 | E | **already bridged** — `hasUnitPullbackLeftUnitorOfMonoidal`, :112 | `HasMonoidalDerivedPullback` |
| 17 | `HasDerivedPushforward` | KernelCorrespondence.lean:108 | F | **unbridged duplicate.**  Supplies an opaque functor already declared as `boundedCoherentDerivedPushforward` (Families/CoherentPushforward.lean:171); bridge provable but absent | `boundedCoherentDerivedPushforward` |
| 18 | `HasDerivedTensor` | KernelCorrespondence.lean:169 | F | **already bridged** — `hasDerivedTensorOfCoherent`, DerivedTensorCoherence.lean:102 | `HasCoherentDerivedTensor` |
| 19 | `HasCoherentDerivedTensor` | DerivedTensorCoherence.lean:57 | F | *is* a root — `extends MonoidalCategory` | Mathlib `MonoidalCategory` |
| 20 | `HasMonoidalDerivedPullback` | DerivedTensorCoherence.lean:159 | F | *is* a root — `extends (boundedCoherentDerivedPullback f).Monoidal` | Mathlib `Functor.Monoidal` |
| 21 | `HasDerivedPullbackAdjunction` | KernelAdjunction.lean:107 | G | one field `adj : Lf^* ⊣ Rf_*`; thin wrapper, not a duplicate | Mathlib `CategoryTheory.Adjunction` |
| 22 | `HasKernelDual` | KernelAdjunction.lean:133 | G | chosen object + `Adjunction`; the rigidity slot | none (Mathlib `Monoidal.Rigid` is the unused precedent) |
| 23 | `HasTwistedInversePullback` | KernelAdjunction.lean:162 | G | `IsRightAdjoint`-shaped but deliberately names the adjoint | Mathlib `CategoryTheory.Adjunction` |
| 24 | `HasDualizingTwist` | KernelDualizingTwist.lean:112 | G | refines #23 with a shape claim; reaches #23 by a field, not a root | `HasTwistedInversePullback` (#23) |

Family counts: A = 6, B = 2, C = 1, D = 2, E = 5, F = 4, G = 4.

**Inhabitation sweep** (the review obligation `check_single_instantiation.py`
cannot discharge: `GENERIC_SUBJECTS` at `:55-58` omits `AlgebraicGeometry`,
`THRESHOLD = 1` at `:59`).  A tree-wide scan of every `instance` whose
conclusion names each class:

| inhabitants | count | classes |
|---|---|---|
| **0** | 18 | #1–#11, #17, #19–#24 |
| **1** | 6 | #12–#16 and #18 — each exactly one adapter from a coherent root |

**Every one of the 24 has ≤ 1 inhabitant**; had `AlgebraicGeometry` been in
`GENERIC_SUBJECTS`, all 24 would trip the gate.  `HasCoherentPullback` itself
(`Families/BoundedGeometry.lean:81`) also has zero instances anywhere in
`DerivedAlgGeo/`.  This does not condemn the classes — several are legitimate
statement-layer contracts — but the `abstraction-tree.md` adoption obligation has
never been discharged for any of them, and the tree cannot discharge it.  (An
earlier draft of this table gave the buckets as 19/5 and omitted #18 while
counting `HasCoherentPullback`, which is not one of the 24; both verifiers caught
it, and 18/6 above is the corrected partition.  The prose conclusions are
unchanged.)

**Lean evidence.**  `fm-compositor-root.lean`, 255 lines, EXIT=0, zero sorry,
importing the real `FourierMukai` and `Families` modules so the constructors
target the real classes: `pullbackCompositorAt` (`:44`),
`pushforwardCompositorAt` (`:58`), four pullback constructors (`:94`, `:106`,
`:118`, `:130`), `hasDerivedPushforwardOfCoherent` (`:170`),
`pushforwardCompositorAt'` (`:181`), two pushforward constructors (`:196`,
`:215`).

#### FM-A1 — six classes are one datum, and that compositor already exists

**Kind** duplicate-declaration / existing-root-unused · **Impact** high ·
**Confidence** 0.93 · **Existing root reached: YES — do not invent a parallel
root.**

All six carry `{comm : a commuting triangle, iso : two-step composite ≅ one-step}`.
`HasPullbackSwap` is `HasPullbackFactorization` verbatim at
`T:=Z, U:=X, π:=σ, r:=q` with the iso reversed — two declarations of one
equation.  `HasCommonPullbackRoute` is two of them glued.  The datum is the
compositor of the derived-pullback pseudofunctor presentation, and the
repository **already declares it**:
`SchemeBaseChange.boundedCoherentDerivedPullbackComp`
(`Families/CoherentPullbackCoherence.lean:141`, `pb g ⋙ pb f ≅ pb (f ≫ g)`) and
`boundedCoherentDerivedPushforwardComp`
(`Families/CoherentPushforwardCoherence.lean:137`).  The only thing genuinely
missing is a transport reading the compositor at a renamed target `r`.

**Proposed root** (a transport `def` in those two existing files, not a new
structure or class): `SchemeBaseChange.pullbackCompositorAt` /
`pushforwardCompositorAt`, taking `(π : T ⟶ Z) (p : Z ⟶ U) (r : T ⟶ U)
(comm : π ≫ p = r)` and the instance at `r` as an **explicit** argument,
proved by `subst comm; exact boundedCoherentDerivedPullbackComp π p`.

**Projections** (all elaborated): `HasPullbackFactorization`,
`HasPullbackSwap` (`.symm`), `HasPullbackRetraction` (at `r := 𝟙 X`, then the
unitor), `HasCommonPullbackRoute` (two compositors at the common composite), and
the four pushforward mirrors via FM-F1's bridge.

**False-unification risk, and why it shapes the signature.**
`HasCoherentPullback` is heavy **data** (`BoundedGeometry.lean:81`, eleven
fields), so two instances at the same morphism need not agree, and there is **no
closure instance** — zero `instance … : HasCoherentPullback` anywhere;
`HasCoherentPullback (f ≫ g)` and `HasCoherentPullback (𝟙 T)` appear as explicit
hypotheses at 13 sites.  Stating the transport with `[HasCoherentPullback r]` as
an instance binder would silently compare the caller's instance against whatever
search finds, producing a diamond.  Second, recorded failure: the four
constructors **cannot** be `instance`s — `comm` occurs in no instance-implicit
argument and not in the return type, so Lean rejects them ("This instance has 1
argument that cannot be inferred using typeclass synthesis"), a failure both
verifiers reproduced.  The route to the root is an explicit constructor `def`,
and the classes stay classes carrying their guard.  This vindicates the
`KernelAssociativity.lean:102-106` and `KernelConvolution.lean:283-285`
docstrings' worry about `eqToHom` transport, but not their conclusion: `subst`
on the guard discharges it cleanly.

**Landing note.**  `pullbackCompositorAt` belongs in
`CoherentPullbackCoherence.lean` beside the compositor, not in `FourierMukai/`,
or it becomes a second place the compositor is named.

#### FM-B1 — the two retraction classes are that compositor at r = 𝟙

**Kind** duplicate-declaration / existing-root-unused · **Impact** medium ·
**Confidence** 0.9 · **Existing root reached: YES** —
`boundedCoherentDerivedPullbackId` (`CoherentPullbackCoherence.lean:130`) and
`boundedCoherentDerivedPushforwardId` (`CoherentPushforwardCoherence.lean:126`).

`HasPullbackRetraction δ p` has `comm : δ ≫ p = 𝟙 X` and
`iso : pb p ⋙ pb δ ≅ 𝟭`.  That is `HasPullbackFactorization δ p (𝟙 X)`
post-composed with the existing identity unitor.  Family B is not independent of
family A.  `KernelAssociativity.lean:104-106` declines to route these through
`HasCommonPullbackRoute` because that "would demand a pullback-along-identity
input plus unitor transport at every use site"; that objection is correct about
`HasCommonPullbackRoute` and misdirected about the compositor — the
pullback-along-identity input is `[HasCoherentPullback (𝟙 X)]`, which the
repository already demands at 13 sites, and the unitor transport is one `≪≫`
against a declaration that already exists.  Elaborated.

**Cost, stated honestly.**  The `[HasCoherentPullback (𝟙 X)]` instance is
genuinely new data at each use site and is **not** derivable — no
`instance : HasCoherentPullback (𝟙 T)` exists.  Folding B into A therefore adds
a hypothesis to every consumer rather than removing one.  That is a real reason
to keep the retraction class as a named abbreviation; it is not a reason to keep
it as an independent supplied datum.

#### FM-F1 — `HasDerivedPushforward` is an unbridged second declaration

**Kind** duplicate-declaration, no comparison theorem · **Impact** high ·
**Confidence** 0.9 · **Existing root reached: PARTLY** — the functor root
exists (`Families/CoherentPushforward.lean:171`) and is not reached.

`HasDerivedPushforward` (`KernelCorrespondence.lean:108`, functor accessor
`derivedPushforward` `:123`) supplies an opaque
`Dᵇ(Coh T) ⥤ Dᵇ(Coh U)` with `Additive`, `CommShift ℤ` and `IsTriangulated`
fields.  The `Families` layer already declares that functor as
`boundedCoherentDerivedPushforward` with those three instances proved (`:177`,
`:182`, `:202`) plus a compositor and a unitor.  Nothing in the repository
relates the two — grep for `HasCoherentPushforward` in `FourierMukai/` returns
zero hits.  This is two declarations of one functor with no comparison theorem,
and it is why every pushforward-side class in families A and B is stranded.  The
bridge **is** provable and elaborates; with it in scope,
`pushforwardCompositorAt'` and constructors for `HasPushforwardFactorization`
and `HasPushforwardSwap` all elaborate.

**False-unification risk.**  Land it as a `def` or a scoped instance, **not** a
global instance.  `HasDerivedPushforward` is deliberately opaque —
`KernelCorrespondence.lean:100-107` argues the derived functor is the primitive
object because pushforward of a coherent sheaf is not coherent, so the class is
meant to admit inhabitants that are not degreewise coherent pushforward.  A
global instance would make every `HasCoherentPushforward`-carrying morphism
silently pick that model and would diamond against any caller supplying a
different one.  The tree does the same shape correctly one-way at
`DerivedTensorCoherence.lean:102` ("deliberately one-way").

**Citation defect, recorded rather than suppressed.**  The
`HasCommonPushforwardRoute` docstring (`KernelConvolution.lean:289-293`, the
false sentence at `:291-293`) asserts "there is no existing composition contract
at all — nothing in the repository names `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*`".  The
repository does name it, at `CoherentPushforwardCoherence.lean:137` (coherent
level `:113`, unitor `:126`).  The claim is true only of the opaque
`derivedPushforward`, which is this finding.  Correct the docstring when the
bridge lands.

#### FM-PSEUDO — negative result: the Pseudofunctor lane cannot own families A and B

**Impact** high · **Confidence** 0.95 · This is the false-unification control of
the whole follow-up.

The hypothesis — that families A and B are the compositor/unitor datum of a
pseudofunctor `SchemeBaseChange S → Cat` owned by the existing `Pseudofunctor`
lane — is **false**, for three independently sufficient reasons.

1. **`Transport.lean` declares no compositor root.**  It is a namespace
   (`CategoryTheory/Bicategory/Functor/Cat/Transport.lean:19`), not a structure:
   its declarations all **take** a presentation `(e : F ⋙ G ≅ H)` as an argument
   and transport it through equivalences.  The shape matches families A and B
   exactly — which is why the resemblance is compelling — but there is nothing
   there to instantiate.  Its imports are only `CancelIso`, `Equivalence` and
   `Slice`; it never mentions the Mathlib `Pseudofunctor` type.
2. **Mathlib's `Pseudofunctor` at the pin requires a total map**
   (`Prelax.lean:26` for `map`; `Pseudofunctor.lean:60-61` for `mapId`/`mapComp`
   at every object and composable pair).  `boundedCoherentDerivedPullback`
   (`BoundedGeometry.lean:160`) is defined only under `[HasCoherentPullback f]`,
   and there is **zero** such instance in the tree — no closure under `𝟙` or
   `≫`.  The presentation is partial and has no total extension to exhibit.
3. Even granting 1 and 2, the source would have to be
   `LocallyDiscrete (SchemeBaseChange S)ᵒᵖ` for pullback and
   `LocallyDiscrete (SchemeBaseChange S)` for pushforward — two different
   pseudofunctors — so one `Pseudofunctor` root could not own both halves of any
   paired class.

**Conclusion.**  Keep the leaves in the geometry layer and route them to the
compositor declarations that already exist there.  Do **not** build a
pseudofunctor.  Instead of a new spine node, add to `abstraction-tree.md`'s
Fourier–Mukai node (lines 130-136, which today lists only the categorical side)
a geometric-convolution child pointing at `CoherentPullbackCoherence.lean:141` /
`CoherentPushforwardCoherence.lean:137` as the compositor owners for the ten
kernel-ledger guard classes.  An audit that stopped at shape-matching would have
proposed the pseudofunctor root, discovered mid-implementation that `map` cannot
be total, and either weakened the root to a bare `Iso` or invented closure
instances for `HasCoherentPullback`.

*(Citation corrected: `Pseudofunctor.ObjectProperty.universallyStable` is the
`def` at `Cat/ObjectProperty/UniversallyStable.lean:33`; `:29` is a `variable`
line.  `Transport.lean` holds six declarations — three defs, three theorems.)*

#### FM-D1 — held back: two projection-formula classes, one bifunctorial statement

**Kind** candidate unification · **Impact** medium · **Confidence** 0.55 ·
**Status: NOT LANDABLE.  Both verifiers marked this item unsound, and the
corrected version is below.**

`HasProjectionFormula.iso` at (B, A) reads `q_*(q^*B ⊗ A) ≅ B ⊗ q_*A`;
`HasProjectionFormulaRight.iso` at (A, E) reads `q_*(A ⊗ q^*E) ≅ q_*A ⊗ E`.
These are the left-slot and right-slot forms of one classical projection
formula, so the docstring's substantive claim at `KernelConvolution.lean:253-255`
("not a consequence of `HasProjectionFormula` plus a braiding") needs a
qualifier.  Its **stated reason** is nevertheless correct and decisive: the
first is a family indexed by B of natural isos in A, the second a family indexed
by A of natural isos in E, and converting requires joint naturality in both
variables, which neither family alone carries.  A unified root — a natural iso
of bifunctors `Dᵇ(Coh Z) × Dᵇ(Coh U) ⥤ Dᵇ(Coh U)` — would project to both by
currying, but is a genuinely **stronger** hypothesis on every caller.

**What the verifiers found.**  The proposed `HasProjectionFormulaBifunctorial`
has no compiled root and neither currying projection is proved; the item's own
text says "NOT YET VERIFIED IN LEAN".  Under the standard this document is held
to, it must not land: it would be a new declaration standing over two existing
ones with no proved comparison.  The risk is not hypothetical — the two classes
are consumed at **different morphisms** (`HasProjectionFormula` at `πYW`,
`HasProjectionFormulaRight` at `πXW`, per `KernelConvolution.lean:253-255`), so
if the bifunctorial iso is not constructible at both, the unification forces
every such caller to prove a statement it does not need at a morphism where it
may be false.

**Corrected disposition.**  Record FM-D1 as a candidate and keep the two classes
separate with a cross-reference.  It becomes landable only when the bifunctorial
iso is actually constructed **at both consumption morphisms** and both currying
instances are proved, in the one-way style of
`DerivedTensorCoherence.lean:102`.  Merging into one class with two independent
fields is the wrong fix, for the reason the docstring gives: one field would be
unconsumed at each of the two instance sites.  Note that the tensor side already
has a bundled bifunctorial root in this very directory
(`HasCoherentDerivedTensor`, `DerivedTensorCoherence.lean:57`), so the precedent
exists.

#### Other negative results from fu1

- **`HasFlatBaseChange` reaches no root and should not be forced into family A.**
  Its guard is a commuting **square** (`u ≫ q = q' ≫ v`), not a triangle, and its
  iso `q_* ⋙ v^* ≅ u^* ⋙ q'_*` mixes the two variances, so no compositor of
  either presentation produces it.  Mathlib has the Beck–Chevalley precedent at
  `Mathlib/CategoryTheory/Adjunction/Mates.lean`, but `HasFlatBaseChange` asks
  for a chosen iso rather than the mate of a pair of adjunctions, and the
  repository imports nothing from `Mates.lean`.  Keep it a leaf; record
  `Mates.lean` as its nearest Mathlib precedent for placement purposes.
- **Family E is already correctly rooted** — five classes, five bridges, all
  verified to exist (`KernelUnit.lean:103`; `KernelConvolution.lean:211`, `:240`;
  `KernelUnitConvolution.lean:103`, `:112`), plus `HasDerivedTensor` at
  `DerivedTensorCoherence.lean:102`.  These belong to the **monoidal** root, not
  to any pseudofunctor unitor; routing them through a pseudofunctor lane would
  be a second, parallel root — precisely the error under audit.
- **The four constructors cannot be `instance`s** (reproduced by a verifier).
  Applying `proposition-classes.md`: these classes pass rule 1 (they can fail)
  and rule 2 (they are selected, consumed at 4–12 binder sites each) but **fail
  rule 3**, because instance search cannot carry them — with zero instances in
  the tree, every consumer threads them as explicit binders and no search ever
  succeeds.  Under that document's ordering the correct carrier would be an
  explicit hypothesis, but these are data-valued, not Prop-valued, so the
  document does not literally bind them.  The honest recommendation is to keep
  them as classes carrying the guard and add the constructor `def`s.

### 5.2 fu10 — the four sibling sets the twelve lanes failed to enumerate

31 declarations classified across four sweeps: (a) the ambient
charge/phase/`IsSemistable` calculus; (b) the alleged seventh preimage-data
structure; (c) `Moduli/Semistability` index decorations; (d) stacks diagonal
representability.  Five scratch files, all re-run by the verifiers: `fu10a`,
`fu10b`, `fu10d`, `fu10e` at EXIT=0, and `fu10c` at EXIT=1 on a single
deliberate `#check` of a wrongly-namespaced `heartDatum` — which is itself the
evidence that the `ambientDatum` definition above it elaborated with
`SkewedStability` as the only project import.

| Declaration | file:line | Sweep | How it reaches the root |
|---|---|---|---|
| `classOf` | `Triangulated/GrothendieckGroup/Basic.lean:204` | (a) | **is** the class-map root; `classOf_isZero`/`_triangle`/`_iso`/`_shift_one`/`_shift_neg_one`/`_postnikovTower_eq_sum` (`:210`–`:228`) are its generic lemma family |
| `ClassDatum` | `Weak/Charge.lean:91` | (a) | **is** the carrier root (fields `Relevant`, `cl`); already in `SkewedStability.lean`'s import closure |
| `heartDatum` | `Weak/Foundation/StabilityFunction/HeartDatum.lean:57` | (a) | existing `ClassDatum C (K₀ C)` inhabitant |
| `abelianDatum` | `Weak/Foundation/StabilityFunction/Basic.lean:61` | (a) | existing `ClassDatum A (K₀Ab A)` inhabitant |
| `PreStabilityCondition.WithClassMap.charge` | `Foundation/PreStabilityCondition.lean:70` | (a) — **missed by weak-tilting-03** | `= σ.Z ((ambientDatum C v).cl E)` by `rfl` |
| `SkewedStabilityFunction.charge` | `Foundation/Deformation/SkewedStability.lean:49` | (a) — **missed by weak-tilting-03** | `= F.W ((ambientDatum C v).cl E)` by `rfl` |
| `WeakStabilityFunction.charge` | `Weak/Basic/Definitions.lean:149` | (a) | `= chargeOf C (AddMonoidHom.id (K₀ C)) W.Z E` by `rfl` |
| `WeakStabilityFunctionOn.charge` | `Weak/…/WeakSlopeGeometry.lean:184` | (a) | `Z ((abelianDatum A).cl E)` |
| `StabilityFunction.charge` | `Weak/…/StabilityFunction/Basic.lean:88` | (a) | same, at `abelianDatum` |
| `relativePhase` | `Foundation/Deformation/RelativePhase.lean:22` | (a) | **is** the phase root; imports only `Mathlib.Analysis.SpecialFunctions.Complex.Arg` |
| `SkewedStabilityFunction.phase` | `SkewedStability.lean:53` | (a) | `relativePhase (F.charge E) F.α` — already at the root, general `α` |
| `StabilityFunction.phase` | `Weak/…/StabilityFunction/Basic.lean:123` | (a) — **does not reach** | `= relativePhase (Z.charge E) 0`, proved |
| `SkewedStabilityFunction.IsSemistable` | `SkewedStability.lean:102` | (a) — **NEGATIVE** | 5-field `structure` indexed by a phase `ψ` and an interval of a pre-existing `Slicing`; does not reach the calculus |
| `IsSemistable` | `Weak/Basic/Definitions.lean:198` | (a) | heart-triangle 2-clause `Prop` |
| `IsSemistable` | `Weak/…/WeakSlopeGeometry.lean:233` | (a) | `Subobject` slope form |
| `IsSemistable` | `Weak/…/StabilityFunction/Basic.lean:141` | (a) | `Subobject` phase form |
| `Slicing.PreimageData` | `Phase/Transfer/Basic.lean:84` | (b) — **NEGATIVE** | input hypothesis package consumed by `Slicing.preimage` (`:101`) |
| `SlicingOrderPreimageData` | `Phase/Order/Functoriality.lean:46` | (b) — **NEGATIVE** | output characterisation of a slicing *operation* |
| `Slicing.preimageOrderData` | `Phase/Transfer/Phase.lean:209` | (b) | sole inhabitant; its `semistable_iff` is `Iff.rfl` |
| `Slicing.InducedTStructures` | `Phase/Transfer/InducedTStructures.lean:46` | (b) — **already rooted** | cited in the report at line 4061 as `s.InducedTStructures Φ` |
| `InducedTStructuresLarge` | `Phase/Transfer/Inducing.lean:248` | (b) — **already rooted** | extension of the bounded shape; comparison proved both ways |
| `toInducedTStructures` / `ofInducedTStructures` | `Inducing.lean:292` / `:305` | (b) | the two proved comparisons |
| `NormalizedShift` | `Phase/NormalizedShift.lean:36` | (b) — **NEGATIVE** | `ℝ ≃o ℝ` with `f(φ+1)=f(φ)+1`; no functor, no slicing, no preimage |
| `CofiltrationData` | `Phase/Order/Cofiltration.lean:47` | (b) — **NEGATIVE** | cone-by-cone triangle tower; already on `single_instantiation_baseline.txt:23` |
| `SchemeSemistableLocusIndex` | `Moduli/Semistability/Locus.lean:49` | (c) | **is** the index root; consumed by `Locus.lean` and `LocusProbes.lean` |
| `SchemeGenericSemistableLocusIndex` | `Locus.lean:61` | (c) | reaches the root through a plain field `index`, not `extends` |
| `FiniteTypeSchemeSemistableLocusIndex` | `FiniteType.lean:58` | (c) | `index` + `IsFiniteTypeBaseChange index.baseChange` (`:63`) |
| `FiniteTypeSchemeGenericSemistableLocusIndex` | `FiniteType.lean:66` | (c) | `index` + `IsFiniteTypeBaseChange index.index.baseChange` (`:71`) — same predicate, one accessor deeper, no projection to the row above |
| `StackMorphism.FiberRepresentation` | `Sites/Descent/StackInGroupoids/Morphism.lean:76` | (d) | **is** the site-generic representation root |
| `StackMorphism.IsRepresentable` | `Morphism.lean:86` | (d) | `Nonempty (f.FiberRepresentation y)` over the root |
| `StackMorphism.FiberRepresentationWithProperty` | `Stacks/Algebraic.lean:209` | (d) | `extends f.FiberRepresentation y` (`:213`) — the pattern of reaching the root exists |
| `StackMorphism.HasRepresentableProperty` | `Algebraic.lean:220` | (d) | `Nonempty` over the above |
| `StackInGroupoids.DiagonalFiberRepresentation` | `Algebraic.lean:315` | (d) — **does not reach** | field-for-field a site-generic structure; `Equiv` with both inverses `rfl` verified |
| `StackInGroupoids.HasRepresentableDiagonal` | `Algebraic.lean:330` | (d) — **does not reach** | `Nonempty` over the above; cannot be `IsRepresentable Δ_F` — no stack product exists |
| `representableZariskiDiagonalFiberRepresentation` | `Algebraic.lean:339` | (d) | the sole inhabitant of the diagonal structure anywhere in the tree |

#### fu10-a1 — two ambient charge carriers missing from weak-tilting-03

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.92 ·
**Existing root reached: YES** — `ClassDatum` (`Weak/Charge.lean:91`) plus
`classOf` (`GrothendieckGroup/Basic.lean:204`) and its six generic lemmas.  No
new root is proposed.

weak-tilting-03 enumerated the three **abelian** charge sites and missed the two
**ambient** ones.  `WithClassMap.charge` (`σ.Z (classOf C v E)`) and
`SkewedStabilityFunction.charge` (`F.W (classOf C κ E)`) are the identical
function of `(Z, E)` written twice, and `WeakStabilityFunction.charge` is the
same at `v = id`.  All three collapse onto `chargeOf C v Z E := Z (classOf C v E)`
by `rfl` (`fu10a.lean`, EXIT=0), and all three equal `Z ((ambientDatum C v).cl E)`
by `rfl` for `ambientDatum C v : ClassDatum C Λ := ⟨fun E => ¬IsZero E, classOf C v⟩`
(`fu10b.lean`, EXIT=0).

The companion lemmas are the visible cost: each site re-proves a different
subset of the same six generic `classOf_*` lemmas by `congrArg Z` —
`charge_triangle` twice (`SkewedStability.lean:71`, `Definitions.lean:153`, plus
`charge_triangle'` at `:159`), `charge_isZero` twice
(`PreStabilityCondition.lean:84`, `Definitions.lean:165`), `charge_eq_of_iso`
twice, `charge_postnikovTower_eq_sum` once.  No site has the full set, so a
consumer at one carrier cannot use a lemma proved at another.

**Deliverable:** one more `ClassDatum` inhabitant beside `heartDatum`, placed in
`HeartDatum.lean` (**not** in `Weak/Charge.lean`, which deliberately imports only
`Complex.Arg` and `Hom.Defs` and states "Nothing here is categorical"), plus
adding these two ambient declarations to weak-tilting-03's existing
`ClassDatum.charge` deliverable.

**Citation correction, load-bearing.**  `ClassDatum.charge` **does not exist**
anywhere in the tree.  `Weak/Charge.lean:91` is `structure ClassDatum` with
exactly two fields, `Relevant` and `cl`; grep for `ClassDatum` returns only
`Weak/Charge.lean:91,101,105,109,113`, `StabilityFunction/Basic.lean:35,42,49,55,61`
and `HeartDatum.lean:12,32,56,57`.  The critic's phrase "i.e. exactly
`ClassDatum.charge` (Weak/Charge.lean:91)" names a declaration that is not
there; it is a *proposed* root inside weak-tilting-03.  Both verifiers
reproduced this.

**False-unification risk.**  `heartDatum t` has
`Relevant E := t.heart E ∧ ¬IsZero E` while the ambient carriers constrain
nothing beyond nonvanishing, so `ambientDatum` is **not** a specialization of
`heartDatum` and `heartDatum t` is **not** `ambientDatum id`: the comparison is
one-directional and **no `Equiv` may be stated**.  Separately,
`SkewedStabilityFunction.nonzero` quantifies over `(E, φ)` pairs relative to a
pre-existing slicing, so the **carrier** does not reach the `IsPositive` /
`PositiveCharge` root — weak-tilting-04's adoption verdict (report line 3324)
already refuted that, and this finding does not reverse it.  This finding is
about the `charge` abbrev and its lemma family only.

#### fu10-a2 — `relativePhase` is the general phase root, buried under `Deformation/`

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.85 ·
**Existing root reached: YES** (`RelativePhase.lean:22`).  The deliverable is a
placement **move** plus one comparison theorem; no new root.

The critic reads SkewedStability's branch-centred `phase` as a **copy** of the
ordinary phase.  The direction is the reverse, and that is the useful result:
`relativePhase w α` is strictly more general and the ordinary normalised phase is
its `α = 0` instance.  Proved (`fu10b.lean`, EXIT=0):
`relativePhase w 0 = Complex.arg w / Real.pi` and
`Z.phase E = relativePhase (Z.charge E) 0`.  So `StabilityFunction.phase`
(`Basic.lean:123`) fails to reach an existing root, and its consumers re-derive
branch facts that `relativePhase_mem_Ioc` (`RelativePhase.lean:27`) and
`relativePhase_polar` (`:44`) already prove for all α.

The reason the abelian lane never saw the root is a **placement** defect:
`relativePhase` is a pure statement about `Complex.arg` — the file imports only
`Mathlib.Analysis.SpecialFunctions.Complex.Arg` and its docstring says "Keeping
this branch-control layer independent of categories" — yet it sits under
`StabilityCondition/Foundation/Deformation/` where no abelian-side file would
look.  Under `placement.md` tier 1 the carrier in its public type is
`ℂ`/`Complex.arg`, so the repository path is
`DerivedAlgGeo/Analysis/SpecialFunctions/Complex/`.  With zero category imports
there is no `layers.md` obstruction either before or after the move.

**False-unification risk.**  The two phases agree **only** at α = 0; for α ≠ 0
`relativePhase w α` differs from `arg w / π` by an integer, so any simp lemma
rewriting `phase` to `relativePhase` must pin α = 0 or it will fire in the
deformation lane and change meaning.  Do **not** make `StabilityFunction.phase`
an `abbrev`: the tighter range lemmas `phase_pos` (`:126`) and `phase_le_one`
(`:131`) are stated on the strict half-plane and would become confusable with the
general `relativePhase_mem_Ioc`.  A comparison theorem, not a definitional
identification.  The move itself is a move under `CONTRIBUTING.md`: imports,
umbrellas and the audit records under `scripts/StabilityConditionAudit/` land
together.

This also supplies the missing half of weak-tilting-03's projection line
"`StabilityFunction.phase` and `WeakSlopeData.phase` join the same root": the
report routes them to a proposed `ClassDatum.phase`, but the ℂ-level branch
primitive they actually share is already written.

#### fu10-c — the semistable-locus index root is reached, but by a plain field

**Kind** leaf-copies-root · **Impact** low · **Confidence** 0.7 ·
**Existing root reached: YES** (`Locus.lean:49`, two independent consumers:
`schemeSemistableLocus` `Locus.lean:75` and the probe family at
`LocusProbes.lean:36-138`).  This is **not** a missing-root finding.

The residual defect is narrower and real.  (i) None of the three decorations
uses `extends`, so there is no parent projection and every consumer spells
`j.index.baseChange` or `j.index.index.baseChange`.  (ii) The **same** predicate
`IsFiniteTypeBaseChange` is applied at two different accessor depths in two
structures — `index.baseChange` at `FiniteType.lean:63` and
`index.index.baseChange` at `:71` — which is one equation written twice.
(iii) grep for `toFiniteType` over `Moduli/Semistability/` returns **zero**, so
there is no projection between the two finite-type structures and the hypothesis
cannot be transported between the six theorems that consume them
(`FiniteType.lean:93, :101, :110, :119, :167, :171`).  The `extends` restructure
plus the missing projection compiles (`fu10d.lean`, EXIT=0); the projection is a
structure-update term with no proof obligation.

**False-unification risk.**  Do **not** collapse the generic and finite-type
decorations into one parameterised carrier: `genericPoint` is data while
`finiteType` is a `Prop`, so a single carrier would be `Type`-valued and would
lose proof irrelevance for the finite-type half.  Do **not** introduce a
Prop-class for `IsFiniteTypeBaseChange` on indices: every consumer receives the
witness as an explicit structure field, so it fails
`proposition-classes.md`'s "needs instance search" test.
`check_single_instantiation.py` excludes `AlgebraicGeometry`, so CI reports
nothing here; that is why this set slipped past every lane.  The restructure
touches four public structures and every consumer spelling, so under
`abstraction-tree.md:369-371` and `CONTRIBUTING.md` it is a move.

#### fu10-d — `DiagonalFiberRepresentation` is a misplaced site-generic structure

**Kind** leaf-copies-root · **Impact** medium · **Confidence** 0.8 ·
**Existing root reached: NO**, and the reason is a genuine blocker.

The shape duplication is real: (`DiagonalFiberRepresentation`,
`HasRepresentableDiagonal`) is the third instance of `representing : Over S` plus
a Yoneda comparison plus a `Nonempty` class, after (`FiberRepresentation`,
`IsRepresentable`) and (`FiberRepresentationWithProperty`,
`HasRepresentableProperty`) — and it is the only one of the three not rooted.
But the duplication is a **placement** duplication, not a mathematical one: the
diagonal structure contains nothing scheme-specific.  Verified by re-declaring
it verbatim over an arbitrary site `(C, J)` and constructing an `Equiv` with the
existing declaration whose `left_inv` and `right_inv` are both `rfl`
(`fu10e.lean`, EXIT=0) — field for field, the `AlgebraicGeometry` declaration
**is** the site-generic one at `(Scheme, Scheme.zariskiTopology)`.

**Proposed root:** `StackInGroupoids.IsomorphismRepresentation` /
`HasRepresentableIsomorphisms` in
`CategoryTheory/Sites/Descent/StackInGroupoids/Morphism.lean` — `placement.md`
tier 1 puts sites, descent and stacks there — with the two `AlgebraicGeometry`
names kept as `abbrev`s at the Zariski site, which tier 2 explicitly permits.

**The blocking negative.**  The unification the brief suggests — that the
diagonal pair is literally `FiberRepresentation` / `IsRepresentable` at the
diagonal morphism — is **refuted**.  `FiberRepresentation` requires a
`StackMorphism F G`; the diagonal needs `Δ : F ⟶ F × F`, and grep over
`Sites/Descent/StackInGroupoids/` returns **zero** hits for
prod/Prod/diagonal/Diagonal — there is no product of stacks in the tree, so `Δ_F`
cannot be formed.  Even once it can, the shapes differ:
`FiberRepresentation.fiberEquivalence` is an equivalence of **categories**
`Discrete (T ⟶ representing) ≌ f.FiberCategory y T` with `FiberCategory` a
`Core (StructuredArrow …)` (`Morphism.lean:69`), whereas `isomorphismEquiv` is a
bare `Equiv` of **types** onto an Iso-set.  Bridging them needs a proved
groupoid comparison — true, but a theorem about contractible choice of the
middle object, not `rfl`.  Do not claim
`HasRepresentableDiagonal = IsRepresentable Δ` until the product stack with its
descent proof, the diagonal strong transformation, and that comparison all
exist.

**Blocker, promoted from a note on both verifiers' advice.**  Moving the
structure into `CategoryTheory/` brings it **inside** `GENERIC_SUBJECTS`
(`check_single_instantiation.py:55-58`) with `THRESHOLD = 1`, and its only
inhabitant anywhere is `representableZariskiDiagonalFiberRepresentation`
(`Algebraic.lean:339`).  The move therefore **fails CI** unless a second
inhabitant or a `single_instantiation_baseline.txt` entry lands in the same
change, and `abstraction-tree.md:356-357` is likewise unmet —
`HasRepresentableIsomorphisms` is the root's own packaging and
`ZariskiStackPresentation.schemeDiagonal` (`Algebraic.lean:388`) is one
consumer, not two.  Today the one-inhabitant fact is invisible precisely because
the declaration sits in `AlgebraicGeometry/`.

#### Negative results from fu10

- **(a)** `SkewedStabilityFunction.IsSemistable` (`SkewedStability.lean:102`) is
  **not** a fourth copy of the enumerated `IsSemistable` calculus, and declaring
  it one would be exactly the false unification this audit exists to prevent.
  Four differences read off the source: it is a `structure` with five fields
  (`interval`, `nonzero`, `charge_ne`, `phase_eq`, `phase_le_of_triangle`) while
  the other three are two-clause `Prop` `def`s; it takes a third argument, a
  target phase `ψ`, which none of the others has; its `interval` field is
  membership in `s.intervalProp C a b E` for a **pre-existing** `Slicing`, and a
  `ClassDatum` carries no slicing at all, so there is no datum at which the field
  could be stated; and its comparison quantifies over distinguished triangles
  with both ends constrained to the interval.  Unifying it would need a slicing
  parameter, an interval predicate and a phase index on top of the class datum —
  strictly larger than the obligation weak-tilting-03's own adoption verdict
  already flagged.  Keep it separate.
- **(b)** `SlicingOrderPreimageData` (`Functoriality.lean:46`) is **not** a
  seventh one-field wrapper around `Slicing.PreimageData` and does not belong in
  geometry-derived-04.  The two are the **input** and the **output** of one
  construction.  `PreimageData` (`Transfer/Basic.lean:84`) has two fields,
  `hom_vanishing` and `hn_exists`, and is the hypothesis package you discharge to
  build `Slicing.preimage` (`:101`).  `SlicingOrderPreimageData` has three fields
  about an **abstract** operation `op : Slicing C → Slicing D` plus an object map,
  and its sole inhabitant `Slicing.preimageOrderData` (`Transfer/Phase.lean:209`)
  is constructed **from** a family of `PreimageData`, with `semistable_iff` =
  `Iff.rfl`.  A structure whose only inhabitant is built from another structure
  is a consumer of it, not a copy.  Its docstring (`Functoriality.lean:15-24`)
  says so and cites destination issue #211; it is already on
  `single_instantiation_baseline.txt:41`.
- **(b)** `InducedTStructuresLarge` (`Inducing.lean:248`) and
  `Slicing.InducedTStructures` (`InducedTStructures.lean:46`) are a genuine
  sibling pair on which the repository has **already performed the root review**.
  Two comparison maps are written and proved (`:292`, `:305`), and the docstring
  at `:240-247` states the negative result explicitly with its counterexample
  (π_* for a field extension ℓ/k sends no nonzero object of Dᵇ(Coh X_ℓ) into Q,
  so the bounded shape cannot even be stated).  Nothing to report.
- **(b)** `NormalizedShift` (`NormalizedShift.lean:36`) and `CofiltrationData`
  (`Cofiltration.lean:47`) are not preimage-data structures in any sense.  Their
  only shared property with the (b) set is absence from the report, which is not
  by itself a defect.
- **Citation correction against the critic.**  The claim that
  `Slicing.InducedTStructures` "appears NOWHERE in the report" is false for the
  notion and true only for the qualified spelling: report line 4061 contains
  "`preimageData : s.PreimageData Φ` or `inducedTStructures : s.InducedTStructures Φ`".
  `InducedTStructuresLarge`, `NormalizedShift`, `CofiltrationData` and
  `SlicingOrderPreimageData` are genuinely absent.
- **Brief corrections, all verified.**  weak-tilting-03's third `IsSemistable`
  site is `Weak/Foundation/StabilityFunction/Basic.lean:141`, not
  `Weak/Basic.lean:141` — that file is 8 lines long.  `FiberRepresentation` and
  `IsRepresentable` are under `CategoryTheory/Sites/Descent/…`, not under
  `AlgebraicGeometry/`.  `StabilityFunction.phase` is at `:123`, not `:122`.
- **Gate note.**  `check_single_instantiation.py:55-58` omits
  `AlgebraicGeometry`, so neither (c)'s four index structures nor (d)'s diagonal
  pair was ever counted by CI or by any lane.

**Checker verdicts for §5.**  Both verifiers marked fu1 and fu10 **sound**
overall and each individual finding sound **except FM-D1**, which both marked
**unsound** as an actionable proposal; §5.1 now states the corrected
disposition.  Corrections applied in §5: the 18/6 inhabitation partition (was
19/5, omitting #18 and counting a non-member); the declaration-count figure
withdrawn; `universallyStable` at `UniversallyStable.lean:33`; the
`HasCommonPushforwardRoute` docstring span `:289-293`;
`Slicing.preimageOrderData` at `Phase/Transfer/Phase.lean:209`;
`relativePhase_mem_Ioc` at `:27` and `relativePhase_polar` at `:44`; the two
`finiteType` fields at `FiniteType.lean:63` and `:71`; and
`FiberRepresentation.FiberCategory` at `Morphism.lean:69`.  One verifier noted
that fu1's inhabitation table was spot-verified rather than run through
`scripts/EnumInhabitants`; the "≤ 1 inhabitant for all 24" conclusion is
unaffected but the exact per-class counts are not gate-verified.

## 6. De-duplicated counts (follow-up 5)

The report's headline **83 confirmed / 31 high** double-counts.  The seven
clusters below are merged; five of them the report already admits in its own
prose, and two are settled by the adjudications in §4.

| Merge | Finding ids (report lines) | Effect |
|---|---|---|
| 1 | `charges-01` (502) = `walls-01` (884) = `docs-02` (2521) — "This is the same parent as charges-01 seen from the wall lane" (line 896-897); "Identical to charges-01 and walls-01, found a third time from the documentation side" (line 2536) | 3 → 1: **−2**, both removed are HIGH |
| 2 | `numerical-nfold-01` (596) = `surf-08` (4612) — "the same parent as numerical-nfold-01 seen from the surfaces lane" (line 4130) | 2 → 1: **−1** MEDIUM |
| 3 | `charges-02` (2585) = `walls-03` (2988) — same four β-twist declarations, same parent equation | 2 → 1: **−1** MEDIUM |
| 4 | `dg-04` (3693) = `sites-06` (4835) — "the declarations, parent structure and proposed root are identical and are not repeated here" (line 4352) | 2 → 1: **−1** MEDIUM |
| 5 | `numerical-nfold-06` (2816) folds into `charges-01`'s R3 node — same two declarations (`WallTransport.lean:112`, `ThreefoldWallTransport.lean:146`) | **−1** MEDIUM |
| 6 | `lattices-05` (4161) folds into `lattices-01` (1957) — the verdict itself says "the finding is folded into lattices-01" | **−1** MEDIUM |
| 7 | `walls-02` (942) + `lattices-02` (2021) → `discr-01`, per §4.1 | 2 → 1: **−1**, removed is HIGH |

Arithmetic: **83 − 2 − 1 − 1 − 1 − 1 − 1 − 1 = 75**.

**75 distinct findings of 89 reported.**

Impact: 31 high − 2 (merge 1) − 1 (merge 7) = 28, then **−1** for
`geometry-derived-06`, downgraded HIGH → MEDIUM by the §4.2 adjudication, giving
**27 high**.  Medium: 45 − 5 (merges 2, 3, 4, 5, 6) + 1 (the downgrade) = **41**.
Low unchanged at **7**.  27 + 41 + 7 = 75.  (The critic estimated "roughly 76 …
roughly 27"; the exact arithmetic is 75 and 27.)

Corrected per-lane table.  A merged finding is counted once, in the lane that
first reported it; `discr-01` is counted in the lane of the winning parent
(`lattices`).

| Lane | Reported | Confirmed (was) | Confirmed (distinct) | Refuted | High | Medium | Low |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| charges | 6 | 6 | 6 | 0 | 1 | 3 | 2 |
| walls | 8 | 7 | 4 | 1 | 0 | 4 | 0 |
| numerical-nfold | 8 | 8 | 7 | 0 | 4 | 3 | 0 |
| weak-tilting | 8 | 7 | 7 | 1 | 3 | 3 | 1 |
| symmetry-metric | 6 | 5 | 5 | 1 | 2 | 3 | 0 |
| dg | 7 | 6 | 6 | 1 | 2 | 3 | 1 |
| triang | 8 | 7 | 7 | 1 | 3 | 4 | 0 |
| geometry-derived | 6 | 5 | 5 | 1 | 3 | 2 | 0 |
| lattices | 8 | 8 | 7 | 0 | 3 | 4 | 0 |
| surf | 8 | 8 | 7 | 0 | 3 | 4 | 0 |
| sites | 8 | 8 | 7 | 0 | 2 | 4 | 1 |
| docs | 8 | 8 | 7 | 0 | 1 | 4 | 2 |
| **Total** | **89** | **83** | **75** | **6** | **27** | **41** | **7** |

Two further count integrity notes the report does not disclose.  `sites-06`'s
Mathematics verdict is in full "survives, with the same corrections as dg-04" —
no lens checked its equation, because it *is* dg-04.  And two verdicts admit an
unchecked step outright and were still confirmed: `dg-06` Mathematics ("survives
at low, with the caveat that only one of the two compatibilities was checked")
and `dg-04` Adoption ("`commShift_naturality` was NOT verified — three attempts
left a residual goal").

**New findings from this remediation, additional to the 89 and not merged into
the table above:** FM-A1 (high), FM-B1 (medium), FM-F1 (high), fu10-a1 (high),
fu10-a2 (medium), fu10-c (low), fu10-d (medium) — **7 confirmed** — plus FM-D1
recorded as a **withheld candidate** (§5.1), and four new negative results
(FM-PSEUDO, N15/N16/N17 from fu6, N-fu7-1/2/3, NR-D1..D4, N1..N4 from fu9).

**Coverage, restated honestly.**  The report's "997 file-examinations" is a
double-counted sum, and it is smaller than the tree it claims to have covered.
The tree holds **1,053** `.lean` files in **211** directories under
`DerivedAlgGeo/` (file count re-verified for this document).  The critic
measured, by re-reading the report, **383 distinct files cited anywhere in §1–§7
(36%)** and **379 distinct files in §1–§4** — the confirmed and refuted findings,
i.e. what survived review.  **136** directories have at least one cited file;
**75 directories have zero cited file.**  Any reader who takes 997 as near-total
coverage is wrong by a factor of about 2.7.  §6 of the report should state the
distinct-file figure alongside the examinations figure, and say which of the two
a downstream consumer should use.  This remediation adds coverage for two of
those 75 directories (`DerivedCategory/FourierMukai/`, `Moduli/Semistability/`)
and for parts of three more (`Foundation/Deformation/`, `Phase/Order/`,
`Stacks/`); the rest remain unsurveyed.

## 7. Revised migration plan

Slices are restated in landing order.  Each says plainly whether it is
**unchanged**, **amended**, **blocked**, or **new**, and any slice whose
correctness depends on an open obligation says so in its first sentence.

**PR-1 · `Walls/Exp/Kernel.lean` — the root, with two inhabitants.  Unchanged.**
`coeff`, `ofMoments`, `ofMoments_add`, `HDeg`, `moments`, `moments_add`,
`charge`, `chargeFamily`, `stChart`, `alphaBetaChart`, `surfaceVec`,
`threefoldVec` and the four comparison theorems, all proved.  Imports only
`Walls/ChargeFamily.lean` and Mathlib.  One amendment: the `Fin (m+1)` indexing
stands — fu3 withdrew the claim that the root must be ℕ-indexed.

**PR-2 · `Walls/Exp/Divisorial.lean` — the keystone.  Amended.**  Land the
**triple-level** `expCharge_eq_ofMoments` and `expCharge_rankOne_eq_charge`
(fu2, proved on a bare `Mukai.RealExtension D`) rather than the
`ChernCharacter`-level `centralCharge_eq_ofMoments`; the latter then follows by
`ch.toRealExtension`.  Without this the keystone cannot reach `mukaiCharge`,
which is the same `expChargeHom` on a different triple.

**PR-3 · `LinearAlgebra/Lattice/Mukai/Graded.lean` and
`LinearAlgebra/BilinearForm/CentralCharge.lean`.  BLOCKED on a root-review
obligation.**  `Mukai.Graded.pairing n` still has no two independent consumers
(`abstraction-tree.md:356-357`, which requires the answer before
implementation): its only named n ≠ 2 consumers are a negative result about
itself and the not-yet-existing fourfold layer.  When it lands, `n = 2` must land
as a **comparison theorem** (`pairing 2 = Mukai.realPairing (LinearMap.mul ℝ ℝ)`,
proved) and never as a second definition, together with the weighted rank-one
bridge and the `realForm` factor-of-two lemma; `Lattice.pairCharge`,
`centralCharge_eq_pairCharge`, `expCharge_eq_pairCharge`, `dualClass_ne_self`,
`dualClass_k3` and `exp_charge_eq_pairCharge` are unchanged.  N1, N2, N8, N9,
N15, N16, N17 go in the module docstring — the last three are the refuted
unifications that justify the module existing at all.  Review gate:
`check_single_instantiation.py` does not scan this module, so the two-consumer
test is a human obligation.

**PR-4 · `Walls/Exp/Discriminant.lean` and the inert-β fix.  Amended.**  `discr`,
`discr_twist`, and the discriminant comparisons stated against the **existing**
root per `discr-01`: `NumClass.discr v = Mukai.realPairing (mul ℝ ℝ) v v` and the
threefold truncation form — all proved — plus the integral bridge
`discr (comp_H v) = (∫H²) · Mukai.selfPairing b v` on the rank-one slice, plus
dropping the inert `β` argument from `Threefold.discrHBeta` (`BMT.lean:103`).
`discr_eq_pairing_self` against a new graded pairing is **not** landed: it would
be a second owner of `Mukai.selfPairing_mk` (`Lattice/Mukai/Basic.lean:150`).

**PR-5 · `Walls/Exp/Twist.lean`.  Unchanged, and still carries the two REAL
sorries.**  `twist`, `twist_twist`, `charge_twist` and the two leaf comparisons.
`design-final.lean:161` and `:168` are unproved; `twist_add_beta` is not
reusable over ℝ (N6).

**PR-6 · `AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean`.
Amended; correctness of two of its deliverables depends on open obligations
(the `Surface.wallChargeFamily` name collision and the three-route tilt
duplication).**  `corrComp`, **`corrComp_unitCorr`**, `hDegrees` (`Fin (m+1)`),
`hDegreesHom`, `wallChargeFamily`, `hDegrees_zero` (proved), **`hDegrees_one`**
(proved), `tiltWallChargeFamily`, and the `n = 2, 3` comparisons
`surface_toNumClass_eq` and `threefold_toNumClass_eq` (both proved, no `sorry`).
`corrComp` must land **with** `corrComp_sqrtToddComp` (`rfl` against
`NumericalVarietyData.mukaiComp`, `Mukai/VectorClass.lean:54`) and
`corrComp_unitCorr`, or it is a third spelling of an existing convolution.
`tiltWallChargeFamily` must ship with a proved comparison to PR-8's `tiltFamily`,
or be dropped.  The new `wallChargeFamily` shares a name with the existing
`Surface.wallChargeFamily` (`WallTransport.lean:156`) in a sibling namespace and
needs the family-level `reindex` comparison that no repair has proved.  Retires
`tc0..tc3` and gives `BMT.degH1Beta` and its siblings one owner.

**PR-6b · NEW; lands with PR-6; this is what backs the §2.4 "κ = √td" line.**
In the same module: `wallChargeFamily_sqrtToddComp_eq_mukaiCharge` —
`(wallChargeFamily V P V.sqrtToddComp 2).charge (alphaBetaChart (a,b)) E =
R.chernCharacter.mukaiCharge R.divisorSpace R.sqrtTodd (rankOne … a b) E` for any
surface realization, no K3 hypothesis — plus the K3 corollary through
`mukaiCharge_of_isK3` (`DivisorialMukai.lean:124`).  Both proved.  The `SqrtTodd`
adapter it uses already exists at `DivisorialMukai.lean:69` with `sqrtTodd_eq_k3`
(`:86`); `toSqrtTodd_sqrtToddComp` identifies the two by `rfl`.  Note the
type-level limit: no equality of `ChargeFamily`s is statable (parameter spaces
`ℂ` against `StabilityParameters D`), so the comparison is pointwise on the
rank-one slice — intrinsic, not a weakness of the proof.  **Must be restated
with `R.realizePolarization P` (`DivisorialChargeNumerical.lean:106`); the
scratch file's `polDiv` is a duplicate of it.**  This replaces the old PR-13,
which called the same theorem "independent, low priority".

**PR-7 · the fourfold layer.  Unchanged in content, with one recorded gap.**
`Examples/Fourfold/ProjectiveSpaceWalls.lean` and `CalabiYauWalls.lean`;
`p4_degree_H_pow_four`, `p4Polarization`, `p4WallChargeFamily` all elaborate;
zero new charge polynomial.  Gap to record, not to hide: the n = 4 graded pairing
has **no** repository counterpart and no proved comparison (fu6), and no
fourfold consumer for it exists either (fu7).

**PR-8 · `Walls/Rotation.lean` and `Walls/Threefold/Tilt.lean` — the tilt node,
with its rotation.  Rewritten, and NO LONGER BLOCKED on PR-1..PR-5.**  Two
files, neither depending on the `Exp` kernel.
*`Walls/Rotation.lean`* (imports `Walls/ChargeFamily.lean` and
`Weak/Tilting/Semistable/TiltGeometry.lean`; **not** merged into
`Walls/ChargeFamily.lean`, which imports only Mathlib today and must stay
stability-neutral): `ChargeFamily.phaseRotate beta := smul (exp(-πβi))`, plus the
two bridges that stop it duplicating what exists — `phaseRotate_charge` (it **is**
`phaseTiltRotation`, `TiltGeometry.lean:42`, not `:43`) and
`phaseRotate_constFamily` (it agrees with `phaseTiltCharge`, `:53`, on the
constant family).  `phaseRotate_wall` is `wall_smul` (`ChargeFamily.lean:322`) at
`Complex.exp_ne_zero`; `phaseRotate_wallValue` is stronger — unit modulus fixes
the wall *expression*.  All proved.
*`Walls/Threefold/Tilt.lean`*: `threefoldTruncate : Threefold.NumClass →+ NumClass`
(the map that does not exist today — the four-to-three coordinate drop and
nothing more), `tiltFamily := (stChargeFamily.reindex Prod.swap).pullback
threefoldTruncate` — **the existing surface family, no new polynomial** — and
`rotatedTiltFamily := tiltFamily.phaseRotate (1/2)`, the charge BLMS actually
induce from.  `nu_eq_tilt_slope` and `chargeSlope_tilt` (ν = α · chargeSlope) tie
it to `Threefold.nu` (`Threefold/Basic.lean:208`); both proved.
`rotatedTiltFamily_wall_eq_preimage` makes every rotated ν-wall a `Prod.swap`
preimage of an `stChargeFamily` wall, which is what lets
`walls_nested_of_discr_nonneg` (`Nested.lean:179`), `wall_circle_eq`
(`Numerical/Basic.lean:183`) and `wall_eq_of_meet` (`:473`) apply to ν-walls.
The chart transposition lives in exactly this one `reindex Prod.swap`.  Two
negative results land with it and must be recorded, not dropped:
`tilt_wall_ne_threefold_wall` and `chargeSlope_rotated_ne`.  **Open obligation
carried into this slice:** whichever of PR-6 and PR-8 lands second must supply a
proved comparison among `tiltWallChargeFamily`, `Exp.tiltChargeFamily` and
`tiltFamily`, and must settle whether `Threefold.nu` or `BMT.nu` survives.

**PR-9 · `Walls/Spherical/Charge.lean` and `Walls/Mukai/ChargeFamily.lean`.
Unchanged.**  `pairingRe`/`pairingIm` as `.re`/`.im` under `hq`; `Spherical.wall`
as inclusion-plus-sign; reuse of `Mukai.im_expCharge_eq_apply_sub_smul` and
`two_mul_re_expCharge`.  Placement is load-bearing: under `Walls/`, never in
`LinearAlgebra/Lattice/Mukai/`.

**PR-10 · documentation only.  Amended.**  The corrected §2.2 spine block of this
document, N1–N14 plus N15, N16, N17 and N11b recorded under the "Negative
result" clause, the two Kuznetsov rules with their **corrected** justification
(signature additivity, not parity), and the instruction that a
`KuznetsovChargeData` carrier must not be introduced.  Independent; can land
first.

**PR-11 · cubic-threefold Ku(X), tilt route.  BLOCKED on an open obligation.**
It owns the BLMS statement that the rotated charge is a stability function on the
tilted heart, which fu8 explicitly does **not** prove and which is not a
wall-level fact: it needs `phaseTiltCharge_im_pos_of_phaseTors`
(`TiltGeometry.lean:278`) and the `WeakUpperClosed` machinery (`:68`).  Do not
land the thin `ChargeFamily.restrict` alias first (N12).

**PR-12a · cubic-fourfold Ku(X) charge on H̃_alg.  BLOCKED on the geometry
frontier F1, F3, F5.**  Plain `pairCharge`, no restriction; signature (2,ρ).

**PR-12b · cubic-fourfold Ku(X) period domain on A₂^⊥.  BLOCKED on the geometry
frontier F1–F4.**  `pairCharge.restrict` along the inclusion, with the proved
`HasSignatureTwo` witness from `QuadraticMap.sigPos_eq_add`
(`SignatureAdditive.lean:202`).  What was one PR is two, on two lattices that are
orthogonal complements for a very general X, so no comparison theorem between
them can exist (N-fu7-2).  Landing either requires de-privatising
`QuadraticMap.polar_restrict` (`SignatureAdditive.lean:62`) rather than copying
it.

**PR-13 · withdrawn.**  Absorbed into PR-6b.

**New slices from this remediation, in value order.**

- **PR-14 · `discr-01`.**  Generalise `Mukai.pairing`
  (`Lattice/Mukai/Basic.lean:56`) over the coefficient ring **in place**, make
  `Mukai.realPairing` an `abbrev` for it at R = ℝ, move
  `DivisorSpace.realDiscriminant` up to `RealForm.lean` (its current home imports
  two of the leaves it would parent), and land the eight projections and five
  bridges of §4.1.  No new declaration name.
- **PR-15 · the Fourier–Mukai compositor transport.**  `pullbackCompositorAt` in
  `CoherentPullbackCoherence.lean` and `pushforwardCompositorAt` in
  `CoherentPushforwardCoherence.lean`, with the guard as an explicit argument and
  the six constructor `def`s; plus FM-F1's `hasDerivedPushforwardOfCoherent`
  bridge as a `def` or scoped instance, never global.  Correct the
  `HasCommonPushforwardRoute` docstring in the same change.  Record FM-PSEUDO in
  `abstraction-tree.md` rather than building a pseudofunctor.
- **PR-16 · the pairing bridge as a standalone.**  If PR-3 stays blocked, the
  n = 2 comparison and the weighted rank-one bridge can still land beside
  `Mukai.realPairing` in `RealForm.lean` as theorems about the existing root,
  with N15/N16/N17 in the docstring.  This is the part of PR-3 that has two
  consumers today.
- **PR-17 · `ambientDatum` + the `relativePhase` move** (fu10-a1, fu10-a2).  One
  `ClassDatum` inhabitant in `HeartDatum.lean` and the six-lemma family stated
  once; then move `relativePhase` with its three theorems to
  `Analysis/SpecialFunctions/Complex/` and add
  `StabilityFunction.phase_eq_relativePhase`.  The move carries imports,
  umbrellas and audit records together.
- **PR-18 · the Serre bridge (W1) and the twist owner (W2)** from §4.2.  W1 is
  blocked until the bounded/unbounded question is settled and
  `ExtFiniteBounded` exists; W2 is one coherence lemma and is independent.
- **PR-19 · `Moduli/Semistability` `extends` restructure** (fu10-c), low value,
  self-contained, a move.
- **PR-20 · the site-generic isomorphism representation** (fu10-d).  **Blocked**
  on CI: the move into `CategoryTheory/` needs a second inhabitant or a
  `single_instantiation_baseline.txt` entry in the same change.

## 8. Still open

Each item names one agent-sized next step.

1. **`Exp.twist_twist` (`design-final.lean:161`, REAL).**  Prove the ℝ-side
   binomial/Vandermonde identity; `twist_add_beta`
   (`Numerical/Stability/TwistedChern.lean:110`) is ℚ-parameterised and not
   reusable (N6).
2. **`Exp.charge_twist` (`design-final.lean:168`, REAL).**  Prove the Cauchy
   product of two exponential coefficient sequences plus the double-sum reindex.
3. **The three-route tilt duplication.**  Prove `tiltWallChargeFamily`
   (`design-final.lean:567`) = `Exp.tiltChargeFamily` (`:197`) =
   `Tilt.tiltFamily` (`repair-fu8-rotation.lean:182`), or drop two of the three,
   before PR-6 and PR-8 both land.
4. **The `wallChargeFamily` name collision.**  State and prove the family-level
   comparison between the proposed `Polarised.wallChargeFamily` and the existing
   `Surface.wallChargeFamily` (`WallTransport.lean:156`), including the chart
   `reindex` (`ℝ × ℝ` against `ℂ`), or rename one of them.
5. **`polDiv`.**  Restate PR-6b's two theorems with
   `NumericalRealization.realizePolarization`
   (`DivisorialChargeNumerical.lean:106`) and delete the abbrev; while there,
   check `centralCharge_eq_ofNumericalDataB` (`:202`) for overlap with
   `expCharge_rankOne_eq_charge`.
6. **`Mukai.Graded.pairing`'s two consumers.**  Either name two independent
   n ≠ 2 consumers, or land only the n = 2 comparison (PR-16) and defer the
   graded definition.  `abstraction-tree.md:351-352` requires this before
   implementation.
7. **The n = 4 pairing gap.**  Record in PR-7's module docstring that the
   fourfold graded form has no repository counterpart and no consumer, or
   construct one.
8. **F1–F5, the cubic-fourfold geometry frontier.**  Construct or assume
   H̃(Ku X, ℤ); its signature (4,20); the distinguished positive-definite A₂ of
   rank 2; `IsCompl` with orthogonality; and the positive-pair property of
   (Re ℧, Im ℧).  Treat as `RankTwo.lean:13-17` treats its own obligation.
9. **The BLMS tilted-heart statement.**  Prove the rotated charge is a stability
   function on the tilted heart, via `phaseTiltCharge_im_pos_of_phaseTors`
   (`TiltGeometry.lean:278`); PR-11 owns it.
10. **`Threefold.nu` against `BMT.nu`.**  Grep `Stability/BMT.lean` around
    `:111`, confirm or refute the duplicate, and state `chargeSlope_tilt` for
    whichever survives.
11. **`discr-01`'s landing shape.**  Write the declaration list as "generalise
    `Mukai.pairing` in place"; do not land `mukaiSelfPairingOf` as a new `def`.
12. **`ChernCharacter.discriminant` and `ChargeCoordinates.discr` by
    elaboration.**  fu6 did not verify these two ends; fu4's `leaf4` and `leaf3`
    do, so cross-check the two statements agree before PR-4 lands.
13. **FM-D1.**  Construct the bifunctorial projection-formula iso at **both**
    consumption morphisms (`πYW` and `πXW`) and prove both currying instances, or
    close the candidate as a negative result.
14. **The FourierMukai inhabitation table.**  Re-run `scripts/EnumInhabitants`
    over the 24 classes to replace the spot-verified counts with gate-verified
    ones.
15. **`HasFlatBaseChange`.**  Decide whether to route it through Mathlib's
    `Adjunction/Mates.lean` mate calculus or leave it a chosen-iso leaf; record
    the answer either way.
16. **The Serre bounded/unbounded fault line.**  Either supply
    `Coh X ⥤ Dᵇ(Coh X)` or restate the Duality lane on
    `SchemeCoherentDerivedCategory X`; W1 cannot be written until one of the two
    happens.
17. **`ExtFiniteBounded` / `HomFiniteBounded` for `Dᵇ(Coh X)`.**  Both verified
    absent; supply the heart-level input via `HomFinite.lean:400`.
18. **W2, the coherence lemma.**  Prove `IsCoherent F → IsCoherent (L ⊗ F)` for
    invertible `L` beside `tensorLeftFunctor` (`Modules/Tensor/Invertible.lean:40`),
    then retire the two bare `Coh X → Coh X` twists.
19. **fu10-d's CI blocker.**  Find a second inhabitant of the diagonal
    representation, or add the baseline entry, before moving it into
    `CategoryTheory/`.
20. **The stack product.**  Until `F ×_G F` and the diagonal strong
    transformation exist, `HasRepresentableDiagonal = IsRepresentable Δ` cannot be
    stated; the groupoid comparison
    `Core (StructuredArrow …) ≌ Discrete (x|_T ≅ y|_T)` is the remaining step.
21. **The 75 uncovered directories.**  Two are now covered and three partly;
    `IntersectionTheory/`, `Morphisms/`, `Weak/Foundation/Slicing/`,
    `Algebra/Homology/SpectralSequence/` and
    `AlgebraicGeometry/ProjectiveSpectrum/Modules/` are the largest remaining, in
    that order of declaration density.
22. **Report §6.**  Replace the 83/31 headline with 75/27/41/7 and the per-lane
    table of §6 above, and state the 383-distinct-file coverage figure alongside
    the 997 examinations figure.
