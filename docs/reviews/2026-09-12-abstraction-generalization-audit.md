# Abstraction and generalization audit

Snapshot: 2026-09-12 EDT

Scope: `main` of `derived-alg-geo-lean` after the dg-category, dg-enhancement,
Bridgeland, numerical-geometry, wall, and Serre-functor merges.

## 1. Purpose and method

The audit looks for one disease: two or more declarations that are
specializations of a single parent that is missing, or that exists and is not
reached.  Twelve lanes partitioned the tree by subject — charges, numerical
n-fold, walls, weak/tilting, symmetry/metric, dg, triangulated structures,
geometry/derived, lattices/algebra, surfaces/varieties, sites/sheaves/cats, and
documentation drift — and together examined 997 files.  Each lane surveyed its
files for missing roots, dimension-specific structures that should be n-fold,
leaves copying a root's carrier or fields, and one equation appearing under two
names.  Every candidate finding was then attacked independently by three
adversarial lenses: a **mathematics** lens that recomputed the claimed shared
equation from the sources rather than from docstrings; a **repository** lens
that re-verified every `file:line`, checked Mathlib at the pin for an existing
root, and tested the proposal against `docs/architecture/placement.md`,
`layers.md`, `proposition-classes.md`, and `scripts/check_single_instantiation.py`;
and an **adoption-and-cost** lens that refused any finding whose root could not
be reached in Lean by two existing leaves without copying fields, whose root was
a record of its leaf's own fields, or whose migration cost exceeded the reuse it
bought.  A finding was killed only when at least two of the three lenses refuted
it; a single dissent is reported with the finding.  Every lens correction to a
root signature, a projection, or a placement is applied below, so the "proposed
root" and "projections" fields state the corrected version rather than the
surveyor's original.  The exemplar the owner named — the central charge — was
additionally put to a design panel: three independent designs (geometry-first,
lattice-first, categorical-first) were scored on mathematical coverage of
n = 2, 3, 4 and the Kuznetsov cases, on repository rules, on how many existing
leaves reach the root, and on migration cost, and the winning design was then
synthesized, amended from the losing designs' correct parts, and elaborated in
Lean.

## 2. The exemplar: the central-charge tree

### 2.1 Status of the Lean sketch

The synthesized design elaborates.  The scratch file is

```
/private/tmp/claude-501/-Users-chris-dare-Personal-SourceCode/c05f8e40-4e0b-4b29-8e2f-b2d8a4ed3897/scratchpad/design-final.lean
```

It is a scratch file and is **not committed**; it is cited only as evidence that
the design type-checks against the real declarations.  Re-verified for this
report:

```
$ LEAN_NUM_THREADS=2 lake env lean .../scratchpad/design-final.lean
design-final.lean:161:8: warning: declaration uses `sorry`
design-final.lean:168:8: warning: declaration uses `sorry`
design-final.lean:553:8: warning: declaration uses `sorry`
EXIT=0
```

665 lines, 61 declarations, no errors.  Three `sorry`s, each labelled in the
file:

| Line | Declaration | Class | Note |
|---|---|---|---|
| 161 | `Exp.twist_twist` | REAL | `ℝ`-side binomial/Vandermonde.  Not reusable from `twist_add_beta` (`AlgebraicGeometry/Numerical/Stability/TwistedChern.lean:110`), which is `ℚ`-parameterised while every wall child takes `β : ℝ`. |
| 168 | `Exp.charge_twist` | REAL | Cauchy product of two exponential coefficient sequences plus a double-sum reindex. |
| 553 | `Polarised.surface_toNumClass_eq` | ROUTINE | Three `Finset.range (k+1)` sums whose `κ j = 0` terms die, then `hDegrees_zero` (proved standalone) at `k = 0`. |

Proved with no `sorry`, and load-bearing for the design: `Lattice.pairCharge`
and its projections; `PeriodDomain.centralCharge_eq_pairCharge`;
`Mukai.expCharge_eq_pairCharge`; `Exp.ofMoments` and its additivity;
`stCharge_eq_exp`, `threefold_charge_eq_exp`, `stChargeFamily_eq`,
`threefold_chargeFamily_eq`; **`Divisorial.centralCharge_eq_ofMoments`** and
`Divisorial.moments_rankOne`; **`Mukai.Graded.exp_charge_eq_pairCharge`**;
`pairing_comm_parity`, `pairing_comm_even`, `pairing_self_eq_zero_odd`,
`dualClass_ne_self`, `dualClass_k3`; `discr_eq_pairing_self`,
`threefold_discr_eq_pairing_truncate`, `Exp.discr_twist`; `corrComp_add`,
`hDegreesHom`, `hDegrees_zero`, `tiltWallChargeFamily`; `p4Polarization` and
`p4WallChargeFamily`; and both Kuznetsov shapes as `example`s.

### 2.2 Design panel

| Angle | Mathematics (n = 2/3/4/Ku) | Repository rules | Existing leaves reaching the root | Migration cost | Total |
|---|---|---|---|---|---|
| A — geometry-first | 6 | 8 | 6 | 7 | 6.5 |
| B — lattice-first | 9 | 8 | 7 | 7 | 7.8 |
| **C — categorical-first** | **9** | **9** | **9** | **8** | **8.8 (winner)** |

Angle A's `(n, m)` decoupling and its ruling that the Todd correction stays on
the pullback are both correct, but it declared the multi-divisor divisorial
charge a non-child, and it asserted that `ℙ²` has no wall family — false:
`p2ProjectiveWallFamily` is at
`DerivedAlgGeo/AlgebraicGeometry/Numerical/Examples/Surface/ProjectivePlaneCharge.lean:475`,
so A's proposed new `p2WallChargeFamily` would have been a fresh instance of the
disease under audit.

Angle B produced the single strongest result of the panel, the parity theorem
`⟪v,w⟫ = (-1)ⁿ⟪w,v⟫`, which was re-derived independently and is correct; it
forces `pairing 3 v v = 0` and is the reason the cubic threefold must go by tilt
restriction while the cubic fourfold goes by the Mukai lattice.  It too benched
the multi-divisor charge.

Angle C wins because it adds no competing root: `Wall.ChargeFamily`
(`Walls/ChargeFamily.lean:49`) stays the root and the new kernel produces its
inhabitants.  Its decisive move is indexing the kernel by **moments** rather
than by compressed degrees, which is what lets the Picard-rank ≥ 2 divisorial
charge be a child rather than a sibling.

All three angles disagreed on whether the exponential lane and the period-domain
lane are siblings (A, C) or parent and child (B).  The disagreement was settled
in Lean: `exp_charge_eq_pairCharge` proves the scalar kernel **is**
`Lattice.pairCharge` against `exp(wH)` on the graded Mukai pairing.  They are one
root with two presentations.

### 2.3 The synthesized tree

```text
R0  Wall.ChargeFamily P N                                              EXISTS, unchanged
    Walls/ChargeFamily.lean:49
    reindex :67 (change of chart) · pullback :72 (change of class map)
    wall :129 · wallValue :118 · pullback_wall :338
    Every node below is an inhabitant, a reindex, or a pullback of R0.
│
├─ R0a  abstract charge on a triangulated category                     EXISTS
│   PreStabilityCondition.WithClassMap   Foundation/PreStabilityCondition.lean:42
│   StabilityCondition.WithClassMap      Foundation/StabilityCondition.lean:41
│   WithClassMap.preimage i h            Phase/Transfer/PreStability.lean:94
│                                        charge unchanged, class map v ∘ K₀.map i
│
├─ R1  Wall.Exp.ofMoments m μ = -∑_{j≤m} (-1)^j/j! · μ j               NEW, one definition
│   │  indexed by truncation degree m, never by ambient dimension n
│   ├─ R1a  scalar moments μ j = w^j · d_{m-j} on HDeg m = Fin (m+1) → ℝ
│   │   ├─ m = 1   slope        SlopeData.charge          Weak/…/Slope.lean:154
│   │   ├─ m = 2   surface      stChargeFamily            Numerical/ChargeFamily.lean:59
│   │   ├─ m = 3   threefold    Threefold.chargeFamily    Threefold/Basic.lean:174
│   │   ├─ m = 4   fourfold     free, no new polynomial                 NEW
│   │   └─ (n,m) = (3,2) tilt   the Ku(cubic threefold) ambient charge  NEW
│   └─ R1b  intersection-form moments μ0 = ch₂, μ1 = ⟨w,ch₁⟩, μ2 = ⟨w,w⟩·rk
│       ChernCharacter.centralCharge     Divisorial/Charge.lean:333     keystone
│       StabilityParameters / rankOne    Divisorial/Charge.lean:197,209
│       OrthogonalSlice.Point            Divisorial/Slice.lean:94
│       mukaiCharge / mukaiChargeFamily  Divisorial/Mukai.lean:173,224
│       smooth quadric, ℙ², blow-up of ℙ²                Picard rank ≥ 2 leaves
│
├─ R1↔R2 bridge  Mukai.Graded                                          NEW
│   exp_charge_eq_pairCharge, pairing_comm_parity, dualClass_ne_self
│   discr_eq_pairing_self, threefold_discr_eq_pairing_truncate
│
├─ R2  Lattice.pairCharge b x y v = ⟪x,v⟫ + i⟪y,v⟫                     NEW root
│   │  b is NOT assumed symmetric; that is what admits odd n
│   ├─ PeriodDomain.centralCharge        QuadraticForm/CentralCharge.lean:61
│   │  │  support property neg_of_centralCharge_eq_zero :109 stays here
│   │  ├─ Mukai.expCharge / expChargeHom  Lattice/Mukai/CentralCharge.lean:36,44
│   │  └─ Ku(cubic fourfold)              n even ⇒ symmetric ⇒ period domain applies
│   └─ packaged as R0 inhabitants under Walls/, never under LinearAlgebra/
│
├─ R3  geometric transport, one map for every (n, m, κ)                NEW
│   corrComp V κ E k = ∑_{j≤k} chComp E j · κ(k-j)       κ on the RIGHT slot
│   hDegrees V P κ m E k = ∫ H^(n-k) · (ch·κ)_k
│   wallChargeFamily := (Exp.chargeFamily m).pullback (hDegreesHom …)
│   ├─ Surface.toNumClass    WallTransport.lean:112             (n,m,κ) = (2,2,1)
│   ├─ Threefold.toNumClass  ThreefoldWallTransport.lean:146    (3,3,1)
│   ├─ degH                  Slope.lean:116                     k = 1, rfl
│   └─ grandchildren: K3, ℙ³, quintic (existing); ℙ⁴, sextic (new)
│
└─ R4  noncommutative varieties: no new root, no KuznetsovChargeData
     cubic threefold  n odd  ⇒ alternating ⇒ no period domain; tilt route forced
     cubic fourfold   n even ⇒ symmetric   ⇒ pairCharge.restrict on A₂^⊥
```

### 2.4 Amended `Canonical spine` text

The following is the exact block to add to
`docs/architecture/abstraction-tree.md`.  The `LinearAlgebra` fragment is
inserted as a third child of that node; the `Walls` fragment is inserted under
`Category ▸ Preadditive ▸ Triangulated category`; the `AlgebraicGeometry`
fragment replaces the two numerical K-theory lines and the final
stability-consuming line.

```text
LinearAlgebra
└─ bilinear form on a lattice
   └─ Lattice.pairCharge b x y v = ⟪x,v⟫ + i⟪y,v⟫   central-charge root; b not symmetric
      ├─ PeriodDomain.centralCharge                 quadratic-space presentation
      │  ├─ support property on HasSignatureTwo     ker Z = span(x,y)ᗮ negative definite
      │  ├─ Mukai.expCharge                         Bridgeland Z(β,ω), exponential plane
      │  └─ noncommutative: Ku(cubic fourfold)      A₂ ⊆ H̃(Ku X); NOT a child of expCharge
      └─ Mukai.Graded.pairing n                     ⟪v,w⟫ = (-1)ⁿ⟪w,v⟫; odd n alternating

Triangulated category
└─ Wall.ChargeFamily P N                       parameterized additive charges; wall loci
   ├─ reindex / pullback                       change of chart / change of class map
   ├─ Wall.Exp.ofMoments m                     -∑_{j≤m} (-1)^j/j! · μ j, one polynomial
   │  ├─ scalar moments on Fin (m+1) → ℝ       compressed H-degrees of a polarised n-fold
   │  │  ├─ m = 1 slope   m = 2 surface        SlopeData.charge / stChargeFamily
   │  │  ├─ m = 3 threefold                    Threefold.chargeFamily
   │  │  ├─ m = 4 fourfold                     no new polynomial
   │  │  └─ (n,m) = (3,2) tilt charge          ambient charge of Ku(cubic threefold)
   │  └─ intersection-form moments             Picard rank ≥ 2, no compression
   │     ├─ Divisorial.ChernCharacter.centralCharge   proved instance of the kernel
   │     ├─ StabilityParameters / rankOne      (B,ω) chart; w = β + iα fixed once here
   │     ├─ mukaiCharge / SqrtTodd             κ is a pullback, never a coefficient
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
│     └─ κ = 1 and κ = √td are two pullbacks   different walls; not one family
└─ stability-consuming children                DerivedCategory/Stability/, Moduli/,
                                               Numerical/, Stability/ — four, not one
```

The last line corrects a documented fact, not only a placement: the spine today
reads "`DerivedCategory/Stability/`, the one stability-consuming child", while
`scripts/check_layering.py:99-108` defines `STABILITY_CONSUMING_GEOMETRY` with
four entries and `docs/architecture/layers.md:67` names three.

### 2.5 Per-existing-leaf projections

No leaf is renamed, moved, or redefined.  Each gains a comparison theorem or an
`abbrev`.

**R0 and R0a — cited, not rebuilt.**
`Wall.ChargeFamily` (`Walls/ChargeFamily.lean:49`), `reindex` (:67), `pullback`
(:72), `wall` (:129), `wallValue` (:118), `pullback_wall` (:338);
`PreStabilityCondition.WithClassMap` (`Foundation/PreStabilityCondition.lean:42`),
`StabilityCondition.WithClassMap` (`Foundation/StabilityCondition.lean:41`),
`WithClassMap.preimage` (`Phase/Transfer/PreStability.lean:94`, which *is* the
Kuznetsov node at stability level), `K₀.map`
(`Triangulated/GrothendieckGroup/Functorial.lean:38`) — all unchanged.

**R1a — scalar leaves.**

| Leaf | Location | Projection |
|---|---|---|
| `Wall.NumClass` | `Walls/Numerical/Basic.lean:104` | carrier kept; `surfaceVec : NumClass ≃+ HDeg 2` |
| `Wall.reZ` / `imZ` | `:124` / `:128` | simp lemmas: `.re` / `.im` of `Exp.charge 2 (stChart (s,t))` |
| `Wall.stCharge` | `Numerical/ChargeFamily.lean:28` | theorem `stCharge_eq_exp` — **proved** |
| `Wall.stChargeFamily` | `:59` | theorem `stChargeFamily_eq` — **proved** |
| `Wall.NumClass.discr` | `Numerical/Discriminant.lean:70` | theorem `discr_eq_pairing_self` — **proved** |
| `Wall.Threefold.NumClass` | `Threefold/Basic.lean:64` | carrier kept; `threefoldVec : ≃+ HDeg 3` |
| `Threefold.betaTwist` | `:89` | theorem `= Exp.twist 3 b` |
| `Threefold.betaTwist_betaTwist` | `:113` | becomes `Exp.twist_twist`; hand `ring` proof deleted |
| `Threefold.reZ` / `imZ` | `:121` / `:131` | simp: `.re` / `.im` of `Exp.charge 3 (alphaBetaChart (α,β))` |
| `reZ_eq_betaTwist` / `imZ_eq_betaTwist` | `:137` / `:142` | instances of `Exp.charge_twist` |
| `Threefold.charge` | `:148` | theorem `threefold_charge_eq_exp` — **proved** |
| `Threefold.chargeFamily` | `:174` | theorem `threefold_chargeFamily_eq` — **proved** |
| `Threefold.discr` | `:204` | theorem `threefold_discr_eq_pairing_truncate` — **proved** |
| `Threefold.nu` | `:208` | theorem: `= α · chargeSlope (…)` on `0 < im`, re-rooting at `chargeSlope` (`Weak/…/WeakSlopeGeometry.lean:63`) |
| `Threefold.Q` | `:217` | **not** a child; stays dimension-specific (N1) |
| `SlopeData.charge` / `WeakSlopeData.charge` | `Slope.lean:154` / `WeakSlope.lean:138` | theorem `= Exp.charge 1 I` up to the `∫Hⁿ` rank weight; bridge lives in `Walls/Exp`, not `Slope.lean` (layers rule 4) |

**R1b — divisorial leaves.**
`DivisorSpace` (`Divisorial/Charge.lean:60`) unchanged; `ChernCharacter.centralCharge`
(`:333`) gains `centralCharge_eq_ofMoments` (**proved**) and keeps its status as
the Picard-rank ≥ 2 root; `centralCharge_rankOne_eq` (`:383`) is kept as the
R1b→R1a bridge and `moments_rankOne` (**proved**) is its moment-level form;
`ChernCharacter.twist` (`:121`) stays a **sibling** — it keeps `c₁ ∈ N¹(X)_ℝ`
and reaches `Exp.twist 2` only on the rank-one slice through `coordinatesAt`
(`:239`); `StabilityParameters` (`:197`) and `rankOne` (`:209`) are unchanged and
become the one place the `w = β + iα` chart order is fixed, retiring the
compensating swap at `Stability/DivisorialWallTransport.lean:55`;
`ChargeCoordinates` (`Coordinates.lean:44`) stays the derived rank-one view, with
`twistByScalar` (`:63`) `= Exp.twist 2 b` and `centralCharge_twistByScalar_apply`
(`:150`) an instance of `charge_twist`; `ChargeCoordinates.toNumClass` /
`toNumClassHom` / `stWallFamily` (`Divisorial/Circle.lean:79,93,126`) are the
third `n = 2` transport and are compared at the root so the surface does not keep
two; `ChargeCoordinates.discr` (`Divisorial/Discriminant.lean:288`) `= Exp.discr 2`;
`ChernCharacter.discriminant` (`:227`) stays the intrinsic sibling;
`mukaiVector` / `mukaiCharge` / `mukaiChargeFamily` (`Divisorial/Mukai.lean:112,173,224`)
are unchanged and already correct, and `dualClass_ne_self` proves that is the only
sound shape off K3; `centralCharge_eq_expChargeHom` (`Mukai.lean:155`) is the
existing R1b→R2 edge.

**R2 leaves.**
`PeriodDomain.centralCharge` (`QuadraticForm/CentralCharge.lean:61`) gains
`centralCharge_eq_pairCharge` (**proved**); `neg_of_centralCharge_eq_zero`
(`:109`) is unchanged and already lattice-generic, so the cubic-fourfold
Kuznetsov component inherits the support property with no new proof;
`Mukai.expCharge` / `expChargeHom` (`Lattice/Mukai/CentralCharge.lean:36,44`)
gain `expCharge_eq_pairCharge` (**proved**, needs symmetry `hb`);
`Wall.Spherical.chartRe` / `chartIm` (`Spherical/Basic.lean:153,158`) are
unchanged abbrevs of `Mukai.expRe` / `expIm`; `pairingRe` / `pairingIm`
(`:174` / `:181`) become `.re` / `.im` of the R2 charge under `hq`;
`Spherical.wall` (`:301`) becomes the R0 wall against the point class
intersected with the sign half (N7); `MukaiChargeData` (`Mukai/Charge.lean:101`)
and `ambientChargeHom` (`Mukai/Ambient.lean:51`) are unchanged and are the shape
a `KuznetsovChargeData` must not copy.

**R3 leaves.**
`Surface.toNumClass` / `toNumClassHom` (`WallTransport.lean:112,145`) become
`hDegrees V P (unitCorr) 2`, and `toNumClass_add` (`:129`) collapses into
`hDegreesHom`'s single additivity proof; `Surface.wallChargeFamily` (`:156`)
becomes the reindexed root family; `Threefold.toNumClass` / `toNumClassHom`
(`ThreefoldWallTransport.lean:146,175`) likewise at `m = 3`;
`betaTwist_toNumClass` (`:194`) becomes the n-fold `hDegrees_twist`, retiring the
hand-evaluated private `tc0..tc3` (`:65-77`); `degH` (`Slope.lean:116`) is
`hDegrees … 1` by **rfl** (which requires the root to be indexed by `ℕ`, not
`Fin`); `slopeH` (`Slope.lean:133`) gets the corrected theorem
`slopeH = ∫Hⁿ · (d₁/d₀)` (N4); `discrH` (`Slope.lean:174`) and `discDegH`
(`:143`) keep separate owners with the Hodge-index gap intact (N5);
`degH1Beta` / `degH2Beta` / `deg3Beta` (`BMT.lean:87,91,95`) become abbrevs of
`hDegrees ∘ twist` at `k = 1,2,3`; `discrHBeta` (`BMT.lean:103`) loses its inert
`β` argument; `k3WallChargeFamily` (`WallTransport.lean:303`),
`p3WallChargeFamily` (`Examples/Threefold/ProjectiveSpaceWalls.lean:153`) and
`quinticWallChargeFamily` (`Examples/Threefold/CalabiYauWalls.lean:153`) become
abbrevs; `p2ProjectiveWallFamily` (`ProjectivePlaneCharge.lean:475`) and
`SmoothQuadric.wallChargeFamily` (`SmoothQuadricCharge.lean:290`) are **already
correctly rooted and gain nothing**; `fourfoldChCoeff`
(`Examples/Fourfold/LinearSection.lean:56`), `p4NumericalVariety`
(`Examples/Fourfold/ProjectiveSpace.lean:64`) and `sexticNumericalVariety`
(`Examples/Fourfold/CalabiYau.lean:87`) are unchanged and gain the first
fourfold charge and wall family the repository has ever had.

### 2.6 Negative results

**N1 — the n-fold Mukai extension is not the parent of the n-fold charge, and
the reason is parity.**  `pairing_comm_parity` (proved) gives
`⟪v,w⟫ = (-1)ⁿ⟪w,v⟫`; `pairing_self_eq_zero_odd` (proved) gives
`pairing 3 v v = 0` identically.  There is therefore no threefold Mukai
quadratic form, no `HasSignatureTwo`, and no period domain in odd dimension.
`Mukai.RealExtension V = ℝ × V × ℝ` has no n-fold generalization.  The threefold
support quantity is BMT's `Q` (`Walls/Threefold/Basic.lean:217`), whose
nonnegativity is false in general.  The charge generalizes in the truncation
degree; the form does not generalize at all.

**N2 — the parity sign does not break the charge, and this constrains the root
signature.**  The charge uses only the left slot, so `v ↦ ⟪Ω,v⟫` is additive
whatever the symmetry; both the `n = 2` (symmetric) and `n = 3` (alternating)
leaf comparisons are proved with no sign correction.  Consequently
`Lattice.pairCharge` must be stated on a bilinear form that is **not** assumed
symmetric — a symmetric-form root would silently exclude every odd dimension.

**N3 — the multi-divisor divisorial charge is a child of the kernel.**
`centralCharge_eq_ofMoments` is proved.  What is true, and is what two of the
three design angles saw, is narrower: it does not factor through the compressed
carrier `HDeg 2`, because that collapses `c₁` to `∫H·c₁`.  The fix is to index
the kernel by moments, not by degrees.  Indexing by degrees would have left the
quadric, the blow-up of `ℙ²`, and every Picard-rank ≥ 2 surface permanently
outside the tree.

**N4 — `slopeH = d₁/d₀` is false, off by `∫Hⁿ`.**  `slopeH`
(`Stability/Slope.lean:133`) is `degH/rank`, while `hDegrees_zero` (proved) shows
slot 0 is `rank · ∫Hⁿ`.  The honest theorem is `slopeH = ∫Hⁿ · (d₁/d₀)`.

**N5 — the compressed `Δ_H` is not the ring-level `discDegH`.**
`discDegH E = ∫Δ(E)·H^(n-2)` (`Slope.lean:143`) and `d₁² − 2d₀d₂` differ by the
Hodge-index defect; `discrH_nonneg` (`Stability/BogomolovGieseker.lean:135`)
spends a full `HodgeIndexStatement` plus `nlinarith` to cross it.  Separately, a
root defining `Δ_H := pairing n v v` would be correct at `n = 2` and would
silently collapse to `0` for every odd `n` (N1); the honest n-general statement
is that `Δ_H` is the self-pairing of the codimension-2 truncation.

**N6 — `Exp.twist_twist` cannot reuse `TwistedChern.twist_add_beta`.**
`twistCoeff` (`Stability/TwistedChern.lean:70`) is `ℚ`-valued and
`twist_add_beta` (`:110`) is over a `ℚ`-algebra, while every wall child takes
`β : ℝ`.  The existing bridge `betaTwist_toNumClass`
(`ThreefoldWallTransport.lean:194`) is stated only for `β : ℚ` cast to `ℝ`.

**N7 — `Spherical.wall` must not be re-rooted at `ChargeFamily.wall` as an
equality.**  `ChargeFamily.wall` is a two-class proportionality locus;
`Spherical.wall` (`Spherical/Basic.lean:301`) is a one-class half-line condition.
The correct statement is the R0 wall against the point class intersected with the
sign half.  `finite_wallCandidates` (`Spherical/Finiteness.lean:233`) consumes the
inequality, not the equation.

**N8 — κ cannot be absorbed into the parameter.**  `dualClass_ne_self` (proved)
shows absorbing κ requires `κ^∨ = κ`, which fails as soon as κ has a nonzero odd
component; `dualClass_k3` (proved) shows K3's `√td = (1,0,1)` is the unique fixed
case.  `Walls/Divisorial/Mukai.lean:50-55` independently records that the Mukai
and ordinary charges "differ by a term that is real-linear in the class but is
not a scalar multiple of the charge, so `wall_smul` does not apply and the two
families have different walls in general".

**N9 — the halved Mukai form is the wrong normalization for the kernel's
discriminant.**  `Mukai.realForm` (`Lattice/Mukai/RealForm.lean:113`) is half the
self-pairing, while every wall child matches the unhalved
`DivisorSpace.realDiscriminant` (`Walls/Divisorial/Support.lean:92`).  Taking the
halved form scales every wall child by 2.

**N10 — truncation degree equal to dimension is false.**  The cubic-threefold
Kuznetsov charge is `(n,m) = (3,2)`, not the BMT `ch₃` charge `(3,3)`; the
Mumford slope is `(n,1)`.  An `n`-indexed root cannot state either.

**N11 — the cubic-fourfold Ku(X) charge is not a child of `Mukai.expCharge`.**
`H̃(Ku(X),ℤ)` is not a Mukai extension of a divisor space, and its charge pairs
against an arbitrary positive 2-plane, of which the exponential planes are a
proper slice.  The tree is
`pairCharge → centralCharge(2-plane) → {expCharge, Ku(X) fourfold}`; the last two
are siblings.

**N12 — landing `ChargeFamily.restrict Z i := Z.pullback (K₀.map i)` now is
refused.**  It is a thin alias with zero inhabitants: `grep -rn -i kuznetsov`
over `DerivedAlgGeo` returns exactly two disclaimers
(`LinearAlgebra/Lattice/Numerical/RankTwo.lean:11,13` and
`AlgebraicGeometry/Surface/Enriques/Residual.lean:20`).  It would also force
`GrothendieckGroup/Functorial` into `Walls/ChargeFamily.lean`, which today
imports only `Mathlib.Data.Complex.Basic` and `Mathlib.Tactic`.

**N13 — restriction of a stability condition along `K₀.map` is not automatic.**
Only the charge restricts freely.  The heart must be induced, and that datum has
a root: `Slicing.PreimageData` consumed by `WithClassMap.preimage`.

**N14 — the surface examples do not all live on one lattice.**  K3, abelian and
Enriques use `(r,c,s)` with `ch₂ = s`; `ℙ²` uses `(r,c,v)` with `ch₂ = c/2 + v`
(`Examples/Surface/ProjectivePlane.lean:43`); linear-section coordinates give a
third.  `HDeg 2` is what they agree on, not what they are built from.

### 2.7 Migration plan

**PR-1 · `Walls/Exp/Kernel.lean` — the root, landing with two inhabitants.**
`coeff`, `ofMoments`, `ofMoments_add`, `HDeg`, `moments`, `moments_add`,
`charge`, `chargeFamily`, `stChart`, `alphaBetaChart`, `surfaceVec`,
`threefoldVec`, and the four comparison theorems — all proved.  Imports only
`Walls/ChargeFamily.lean` and Mathlib, so the root imports no leaf.  Every new
declaration is a `def`/`abbrev`/`theorem`, so `check_single_instantiation.py`
does not scan it (verified: `scripts/check_single_instantiation.py:81` matches
`structure` heads only).  Leaf names all survive, so ~12 consumer files, 7 audit
scripts, and `exe/RestateHistoricalNames.lean` are untouched.

**PR-2 · `Walls/Exp/Divisorial.lean` — the keystone.**  `cPair`, `cSelf`,
`Divisorial.moments`, `centralCharge_eq_ofMoments`, `moments_rankOne` — both
theorems proved.  This is the PR that makes `Charge.lean:333` an instance rather
than a second charge formula, and the one to review hardest: it is the claim two
of three design angles got wrong.

**PR-3 · `LinearAlgebra/Lattice/Mukai/Graded.lean` and
`LinearAlgebra/BilinearForm/CentralCharge.lean` — the lattice root and the
bridge.**  `Lattice.pairCharge`; `centralCharge_eq_pairCharge` and
`expCharge_eq_pairCharge` (two inhabitants by construction);
`Graded.pairing` with the parity theorems; `dualClass_ne_self`, `dualClass_k3`;
and `exp_charge_eq_pairCharge`.  N1, N2, N8 go in the module docstring.  No
`CategoryTheory` and no `AlgebraicGeometry` import.

**PR-4 · `Walls/Exp/Discriminant.lean` and the inert-β fix.**  `discr`,
`discr_twist`, `discr_eq_pairing_self`, `threefold_discr_eq_pairing_truncate` —
all proved — plus **dropping the inert `β` argument from
`Threefold.discrHBeta` (`Stability/BMT.lean:103`)**.

**PR-5 · `Walls/Exp/Twist.lean`.**  `twist`, `twist_twist`, `charge_twist`, and
the two leaf comparisons.  Split from PR-4 because these are the two REAL
`sorry`s and `twist_add_beta` is not reusable over `ℝ` (N6).

**PR-6 · `AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean`.**
`corrComp`, `hDegrees` (ℕ-indexed so `degH` stays `rfl`), `hDegreesHom`,
`wallChargeFamily`, `hDegrees_zero` (proved), `tiltWallChargeFamily`, and the
`n = 2, 3` comparisons.  Retires `tc0..tc3` and gives `BMT.degH1Beta` and its
siblings one owner.

**PR-7 · the fourfold layer.**  `Examples/Fourfold/ProjectiveSpaceWalls.lean`
and `CalabiYauWalls.lean`.  `p4_degree_H_pow_four`, `p4Polarization`,
`p4WallChargeFamily` all elaborate.  Zero new charge polynomial; the entire
content is one `Polarization` per model.  This is the slice to point at when
asked what the root bought.

**PR-8 · `Walls/Exp/Truncate.lean` — the tilt node.**  `truncate`, `truncateHom`,
`tiltChargeFamily`, `nu_eq_chargeSlope`, and the `Threefold.NumClass →+ NumClass`
truncation map, which does not exist today — without it the nested-semicircle
theorems (`Walls/Numerical/Nested.lean:179`, `Basic.lean:183,473`) cannot be
applied to ν-walls at all.  Note the chart transposition: the pulled-back
ν-wall family needs an explicit `reindex Prod.swap`, and PR-1 puts that swap in
exactly one place.

**PR-9 · `Walls/Spherical/Charge.lean` and `Walls/Mukai/ChargeFamily.lean`.**
`pairingRe`/`pairingIm` as `.re`/`.im` under `hq`; `Spherical.wall` as
inclusion-plus-sign; reuse of `Mukai.im_expCharge_eq_apply_sub_smul` and
`two_mul_re_expCharge` in place of the second proofs.  Placement is load-bearing:
these go under `Walls/`, never in `LinearAlgebra/Lattice/Mukai/`, which would be
the first `CategoryTheory` import into `LinearAlgebra` in the tree.

**PR-10 · documentation only.**  The §2.4 block, plus N1–N14 recorded under the
"Negative result" clause, plus the two Kuznetsov rules with their parity
justification, plus the explicit instruction that a `KuznetsovChargeData` carrier
must not be introduced.  Independent; can land first.

**PR-11 and PR-12 · blocked on a real leaf.**  Cubic-threefold Ku(X) (tilt route)
and cubic-fourfold Ku(X) (Mukai-lattice route).  Do not land the thin
`ChargeFamily.restrict` alias or a speculative `A₂` Gram datum before these
(N12).

**PR-13 · independent, low priority.**  The K3 agreement theorem
`numericalCharge_eq_mukaiCharge` in `Stability/DivisorialMukai.lean`; two thirds
of it already exist (`DivisorialMukai.lean:115`,
`Examples/Surface/K3MukaiComparison.lean:97`).

## 3. Confirmed findings

83 findings survived the three-lens attack.  They are ranked high, then medium,
then low, and grouped by lane within each rank.  A finding is listed here if at
most one lens refuted it; that dissent is reported under **Verdicts**.  Every
root signature and projection below is the corrected version.

### 3.A High impact

#### charges-01 — No n-fold polarised charge root

**Kind** missing-root · **Impact** high · **Confidence** 0.97

**Declarations.**
`Wall.stCharge` (`Walls/Numerical/ChargeFamily.lean:28`),
`Wall.stChargeFamily` (`:59`),
`Wall.reZ` / `imZ` (`Walls/Numerical/Basic.lean:124`, `:128`),
`Wall.NumClass` (`:104`),
`Wall.Threefold.charge` (`Walls/Threefold/Basic.lean:148`),
`Wall.Threefold.chargeFamily` (`:174`),
`Wall.Threefold.reZ` / `imZ` (`:121`, `:131`),
`Wall.Threefold.NumClass` (`:64`),
`Divisorial.ChargeCoordinates.centralCharge` (`Walls/Divisorial/Coordinates.lean:108`),
`Surface.toNumClass` (`Numerical/Stability/WallTransport.lean:112`),
`Threefold.toNumClass` (`Numerical/Stability/ThreefoldWallTransport.lean:146`),
`k3WallChargeFamily` (`WallTransport.lean:303`),
`p3WallChargeFamily` (`Examples/Threefold/ProjectiveSpaceWalls.lean:153`),
`quinticWallChargeFamily` (`Examples/Threefold/CalabiYauWalls.lean:153`),
`fourfoldChCoeff` (`Examples/Fourfold/LinearSection.lean:56`, with no charge,
no transport, and no wall family in dimension 4).

**Parent equation.**  For a polarised n-fold with `B = βH`, `ω = αH`,
`w := β + iα`, and compressed H-degrees `d_k = ∫ H^(n-k) ch_k`, the
codimension-m truncation of `Z = -∫ exp(-wH) ch` is
`Z_m(w)(d) = -∑_{k=0}^{m} (-w)^(m-k)/(m-k)! · d_k`.  At `m = 2` its real and
imaginary parts are literally `Wall.reZ` / `imZ` at `s = β`, `t = α`; at `m = 3`
they are `Threefold.reZ` / `imZ`, which `Threefold/Basic.lean:27` states in prose
and then expands by hand.  `Threefold/Basic.lean:10-13` calls itself "the
threefold counterpart" of the surface model while importing only
`Walls.ChargeFamily`.

**Proposed root** (corrected: indexed by truncation degree `m`, not by `n`).
Module `Walls/Polarised/Basic.lean` and
`AlgebraicGeometry/Numerical/Stability/PolarisedWallTransport.lean`; namespace
`…Wall.Polarised`.

```lean
abbrev NumClass (m : ℕ) := Fin (m+1) → ℝ
noncomputable def charge (m : ℕ) (w : ℂ) : NumClass m →+ ℂ
noncomputable def chargeFamily (m : ℕ) : ChargeFamily ℂ (NumClass m)
abbrev stChart : ℝ × ℝ → ℂ := fun p => p.1 + p.2 * I
abbrev alphaBetaChart : ℝ × ℝ → ℂ := fun p => p.2 + p.1 * I
noncomputable def toNumClass (V : NumericalVarietyData n A N) (P : Polarization V.ring)
    (m : ℕ) : N →+ NumClass m
```

**Projections.**  `stChargeFamily = ((chargeFamily 2).reindex stChart).pullback surfaceEquiv`
and `Threefold.chargeFamily = ((chargeFamily 3).reindex alphaBetaChart).pullback threefoldEquiv`
— both compiled.  `reZ`/`imZ` and `Threefold.reZ`/`imZ` become `.re`/`.im` simp
lemmas.  `ChargeCoordinates.centralCharge a (twistByScalar b)` reaches the root
through the existing `stCharge_toNumClass` (`Divisorial/Circle.lean:114`).
`Surface.toNumClass` and `Threefold.toNumClass` become `toNumClass … 2` and
`… 3`.  `k3WallChargeFamily`, `p3WallChargeFamily`, `quinticWallChargeFamily`
become abbrevs.  `ℙ⁴` and the sextic become new grandchildren needing only a
`Polarization`.  `Divisorial.ChernCharacter.centralCharge` (`Charge.lean:333`)
is **not** a child of the compressed root; the existing
`wallChargeFamily_eq_rankOne_reindex` (`DivisorialWallTransport.lean:118`) is the
bridge from `m = 2` to the divisorial family.

**Future examples covered.**  `ℙ⁴` and the sextic Calabi–Yau fourfold; the
quadric threefold and Picard-rank-one Fano threefolds; the cubic-fourfold ambient
charge before restriction to Ku(X); the (α,β)-plane wall algebra for threefolds;
the threefold tilt charge `(n,m) = (3,2)`.

**Verdicts.**
- *Mathematics* — survives.  Both expansions recomputed by hand and matched
  character for character; `scratchpad/NFoldCharge.lean` recompiled, exit 0.
  Sign convention `exp(-wH)` with `Z = -∫` matches `Mukai.expCharge_apply`
  (`Lattice/Mukai/CentralCharge.lean:75`) so the divisorial bridge composes with
  no sign flip.  **Correction applied:** decouple the truncation degree `m` from
  the ambient dimension `n`; the root as originally proposed excluded the
  threefold tilt charge `(3,2)`, which the cubic-threefold Kuznetsov case needs.
- *Repository* — survives.  Every citation verified; the scratch file
  independently recompiled; no such root exists (`grep` for `Polarised|Polarized`
  hits only Gieseker's scheme-level `PolarizedVarietyData`; Mathlib has no
  `centralCharge`).  Placement under `Walls/` matches the precedent at
  `placement.md:100-112`; the root is `def`/`abbrev`, so
  `check_single_instantiation.py` cannot reject it.  **Correction applied:** the
  compressed H-discriminant `d₁² − 2d₀d₂` *does* generalize across `n` and
  belongs in the same root as `Polarised.discr`; only `Threefold.Q` and the
  Mukai signature-2 form stay dimension-specific.
- *Adoption and cost* — survives.  Both leaves reach by proved comparison, not by
  copying fields; `chComp_zero` (`Numerical/Core/Definitions.lean:125`) plus
  `degree_algebraMap_mul` reproduces both weighted rank slots; `Examples/Fourfold`
  confirmed to contain no charge, `Polarization`, or wall.  No baseline entry
  needed; none of `stCharge`/`Threefold.charge`/`reZ`/`betaTwist` appears in
  `exe/RestateHistoricalNames.lean`.  **Corrections applied:** add the `n = 1`
  slope child (`Slope.lean:154`, `WeakSlope.lean:138`), with the bridge in
  `Walls/Polarised` because layers rule 4 forbids `Weak` importing the Bridgeland
  tree; keep the leaf names and add comparison theorems rather than redefining
  them as abbrevs; cite `WallTransport.lean:30-40` and `Circle.lean:75-80` for the
  `∫Hⁿ` rank convention, not the surface docstring.

#### numerical-nfold-01 — Four dimension-specific K-trivial predicates are one

**Kind** dimension-specific-should-be-n-fold · **Impact** high · **Confidence** 0.9

**Declarations.**
`K3.IsK3` (`Numerical/RiemannRoch/K3.lean:52`) and `K3.chi_eq` (`:62`);
`Enriques.IsEnriques` (`RiemannRoch/Enriques.lean:39`) and `chi_eq` (`:50`);
`CalabiYauThreefold.IsCalabiYau` (`Specializations/Threefold.lean:85`) and
`chi_eq` (`:97`); `CalabiYauFourfold.IsCalabiYau`
(`Specializations/Fourfold.lean:94`) and `chi_eq` (`:107`);
`abelianToddComp_one` / `abelianChiStructureSheaf`
(`Examples/Surface/Abelian.lean:118`, whose docstring at `:120-123` says abelian
surfaces "have no class in this library to inhabit");
`Surface.chi₂_symm_of_toddComp_one_eq_zero` (`GrothendieckGroup/EulerPairing.lean:237`);
`K3.mukaiIntegral` (`Mukai/Pairing.lean:85`, docstring "Two dimensions only").

**Parent structure.**  All four assert the same two facts: `td_i(X) = 0` for
every odd `i < n`, and `∫td_n = χ(O_X)`.  `IsK3` is `(n,χ₀) = (2,2)`,
`IsEnriques` `(2,1)`, CY3 `(3,0)`, CY4 `(4,2)`.  The four `chi_eq` theorems are
one instance of `chi_eq_sum` (`RiemannRoch/General.lean:56`).

**Proposed root** (corrected on all three points below).  Module
`Numerical/RiemannRoch/CalabiYau.lean`; namespace
`AlgebraicGeometry.Numerical.NumericalVarietyData`.  Keep it a Prop
**structure** with an explicit bundle argument, never a class.

```lean
structure HasNumericallyTrivialCanonical (V : NumericalVarietyData n A N) : Prop where
  toddComp_odd : ∀ i, Odd i → i < n → V.toddComp i = 0
theorem chi_eq (hV : V.SatisfiesHRR) (h : V.HasNumericallyTrivialCanonical) (E : N) :
    (V.chi E : ℚ) = V.structureSheafEulerCharacteristic * V.rank E
      + ∑ i ∈ Finset.Icc 1 n, V.ring.degree (V.chComp E i * V.toddComp (n - i))
theorem chi₂_swap (h) (E F : N) :
    V.chi₂ E F - (-1 : ℚ) ^ n * V.chi₂ F E
      = (1 - (-1 : ℚ) ^ n) * V.structureSheafEulerCharacteristic * V.rank E * V.rank F
```

**Projections.**  Each of `IsK3`, `IsEnriques`, `CalabiYauThreefold.IsCalabiYau`
reaches the root by a `.toHasNumericallyTrivialCanonical` projection plus a
`.mk` converse — **not** by `abbrev`.  `CalabiYauFourfold.IsCalabiYau` keeps its
extra `toddComp_three = 0` field.  The abelian surface gains the class it
currently lacks, assembled from `abelianToddComp_one` and
`abelianChiStructureSheaf`.  `chi₂_symm_of_toddComp_one_eq_zero` and
`K3.chi₂_comm` become the `n = 2` instance of `chi₂_swap`.

**Future examples covered.**  Abelian surfaces; abelian and other CY threefolds;
CY fourfolds beyond the sextic; hyperkähler fourfolds as far as their Todd data
goes; CY n-folds for `n ≥ 5`; the Mukai pairing on CY threefolds that Bridgeland
stability on threefolds needs.

**Verdicts.**
- *Mathematics* — survives.  All ten citations verified; the parent re-derived
  independently, including the `chi₂_swap` coefficient `(-1)^i(1 - (-1)^k)`,
  nonzero only for odd `k`, leaving only `k = n`.  **Correction applied:**
  `(√td)^∨ = √td` is **false** in degree `n` for odd `n`; the correct n-general
  Mukai statement is `degree (mukaiDual E * mukaiClass F) = chi₂ E F - χ₀ · rank E · rank F`,
  which reduces to the sign-free identity for even `n` and for CY3 only because
  `χ₀ = 0`.
- *Repository* — survives.  All four field lists verified exactly; no such
  predicate exists in the tree or in Mathlib; `AlgebraicGeometry` is outside
  `GENERIC_SUBJECTS`, and the root is a Prop structure, not a class, so neither
  gate applies.  **Corrections applied:** do not name the root for one of its
  children (`IsNumericallyCalabiYau 1` would be the Enriques case); keep it a
  Prop structure with an explicit argument, since
  `Examples/Surface/Abelian.lean:111-115` is an explicit regression test against
  instance-selecting a numerical presentation.
- *Adoption and cost* — survives.  Four leaves, far past the two-leaf bar.
  **Corrections applied:** do not adopt by `abbrev` — roughly 25 consumer
  declarations across 8 files use the field names, and
  `scripts/AlgebraicGeometryAudit/Core.lean:998-1009` prints axioms of the field
  projections by name; drop `χ₀` from the root's signature, because
  `structureSheafEulerCharacteristic` (`RiemannRoch/General.lean:33`) already
  roots that half n-generally and a `χ₀`-parameterised root would *strengthen*
  the hypothesis of `chi₂_symm_of_toddComp_one_eq_zero`, which today needs only
  `toddComp 1 = 0`; fold in `abelianChi_eq_of_chComp_two_eq`
  (`Abelian.lean:134`), which calls itself "the two-dimensional shadow of
  `CalabiYauThreefold.chi_eq_of_chComp_eq`".

#### numerical-nfold-02 — The surface rank-one ring is the n = 2 case of the n-fold one

**Kind** leaf-copies-root · **Impact** high · **Confidence** 0.95

**Declarations.**
`SurfaceRing` (`Examples/Surface/RankOne.lean:48`) and
`surfacePB` / `H` / `surfaceW` / `surfaceDegree` / `surfaceNumericalRing` /
`SurfaceNum` / `surfaceCh` / `surfaceDegree_ch_mul_todd` (`:51`, `:131`, `:181`,
`:193`, `:197`, `:245`);
`RankOneRing n` (`Examples/RankOne.lean:79`) and its siblings (`:82`, `:171`,
`:219`, `:248`, `:259`, `:274`);
`rankOneNumericalVariety` (`:297`) and `_satisfiesHRR` (`:323`);
`k3NumericalVariety` (`Examples/Surface/K3.lean:75`),
`p2NumericalVariety` (`ProjectivePlane.lean:89`),
`abelianNumericalVariety` (`Abelian.lean:83`),
`enriquesNumericalVariety` (`Enriques.lean:102`) — all hand `where` blocks —
against `p3NumericalVariety` (`Examples/Threefold/ProjectiveSpace.lean:67`),
which correctly uses the n-fold constructor.

**Parent structure.**  For `Pic X = ℤ·H` the numerical ring of an n-fold is
`ℚ[t]/(t^{n+1})` with `∫Hⁿ = d`.  `Examples/RankOne.lean` builds exactly that for
every `n`, together with the model constructor and its HRR discharge, and its own
docstring (`:44-49`) says "`SurfaceRing` is the `n = 2` case of `RankOneRing` …
deliberate follow-up work".

**Proposed root.**  Existing: `rankOneNumericalVariety`.  The surface file
shrinks to abbrevs.

**Projections.**  `SurfaceRing`, `H`, `surfacePB`, `surfaceW`, `surfaceDegree`,
`surfaceNumericalRing`, `idx2` are all `rfl`-equal to their `n = 2` instances —
verified in Lean, including the whole `NumericalRingData` bundle, which is
stronger than the surveyor claimed.  The four surface models become
`rankOneNumericalVariety 2 …` with scalar Todd tables, and their HRR proofs
become `rankOneNumericalVariety_satisfiesHRR 2 …` plus one `push_cast; ring`,
exactly as `p3`/`quintic`/`p4`/`sextic` already do.

**Future examples covered.**  Every further Picard-rank-one surface; any n-fold
rank-one model through one constructor and one HRR lemma; surface wall and charge
files consuming `SurfaceRing` automatically agree with the threefold ones.

**Verdicts.**
- *Mathematics* — survives, strengthened: `surfaceNumericalRing h2 = rankOneNumericalRing 2 h2`
  is `rfl`, not only the ring and degree.  **Correction applied:** `surfaceCh` is
  **not** an `rfl`-abbrev of `rankOneCh 2` — `surfaceCh … 0` is
  `algebraMap (chCoeff E 0)` while `rankOneCh 2 … 0` is that times `H^0`, which
  differ by `mul_one`; the four models' `chComp_zero := fun _ => rfl` fields
  disappear into the constructor's own obligation.
- *Repository* — survives.  All ten citations exact; the definitional check
  re-run independently.  **Corrections applied:** the kind is equivalently
  existing-root-unused; the `SurfaceNum` bullet is a no-op, since
  `rankOneNumericalVariety` is already generic in `N`; the real cost is that
  `k3Todd`/`p2Todd`/`abelianTodd`/`enriquesTodd` are typed `ℕ → SurfaceRing`
  while the root wants `ℕ → ℚ`.
- *Adoption and cost* — survives, verified in Lean
  (`scratchpad/V02c.lean`, exit 0), including a rebuilt K3 model through the
  n-fold constructor with a scalar Todd table.  **Corrections applied:**
  `surfaceCh c = rankOneCh 2 c` **fails** as `rfl` (the surface version truncates
  by a `match` arm, the root relies on `H^i = 0`), so agreement is a ~10-line
  theorem and every downstream `rfl` through `surfaceCh` must be re-proved;
  `SurfaceRing` and `RankOneRing 2` are defeq only at *default* transparency, not
  at `instances` transparency, so the migration must go all the way through the
  abbrevs.  198 references across 13 files, most surviving unchanged.

#### numerical-nfold-03 — Linear-section coordinates are one Koszul table

**Kind** dimension-specific-should-be-n-fold · **Impact** high (repository and
adoption lenses both rate medium) · **Confidence** 0.8

**Declarations.**
`ThreefoldNum` / `threefoldChCoeff` / `threefoldRank` / `threefoldChi_sum`
(`Examples/Threefold/LinearSection.lean:61`, `:66`, `:84`, `:97`);
`FourfoldNum` / `fourfoldChCoeff` / `fourfoldRank` / `fourfoldChi_sum`
(`Examples/Fourfold/LinearSection.lean:50`, `:56`, `:76`, `:86`), whose docstring
at `:10` reads "The dimension-four counterpart of
`Examples/Threefold/LinearSection.lean`";
`SurfaceNum` (`Examples/Surface/RankOne.lean:193`);
`p3Todd` (`Examples/Threefold/ProjectiveSpace.lean:45`),
`p4Todd` (`Examples/Fourfold/ProjectiveSpace.lean:41`),
`p2Todd` (`Examples/Surface/ProjectivePlane.lean:59`).

**Parent structure.**  Both files record a class by its multiplicities against
`[O_X], [O_{X∩H}], …, [O_pt]` and expand `ch(O_{X∩H^k}) = (1 − e^{−H})^k`.  The
coefficients were recomputed independently: `k = 1` gives `(1, −1/2, 1/6, −1/24)`,
`k = 2` gives `(1, −1, 7/12)`, `k = 3` gives `(1, −3/2)` — including the `7/12`
and `−3/2` that the fourfold docstring singles out as what makes dimension four
"more than a longer version of dimension three".

**Proposed root** (corrected: keep the truncation in the geometric child, and
split the Todd half out).  Module `RingTheory/PowerSeries/KoszulChern.lean` for
`koszulChCoeff`, and `Numerical/Examples/LinearSection.lean` for the geometric
child.

```lean
noncomputable def koszulChCoeff (k i : ℕ) : ℚ   -- coefficient of x^i in (1 - e^{-x})^k
abbrev LinearSectionNum (n : ℕ) : Type := Fin (n + 1) → ℤ
noncomputable def linearSectionChCoeff (n : ℕ) (d : ℚ) (E : LinearSectionNum n) (i : ℕ) : ℚ :=
  if i ≤ n then (∑ k ∈ range n, (E k : ℚ) * koszulChCoeff k i)
                 + (if i = n then (E n : ℚ) / d else 0)
  else 0
```

**Projections.**  `ThreefoldNum`/`FourfoldNum` become `LinearSectionNum 3`/`4`;
`threefoldChCoeff`/`fourfoldChCoeff` become `fin_cases`/`norm_num` evaluations of
the table; `threefoldChi_sum`/`fourfoldChi_sum` become one lemma.  The `ℙⁿ` Todd
leg is **deferred to numerical-nfold-05**: `projectiveSpaceTodd n` needs the
power-series root, and `p2/p3/p4Chi_lineBundle` each carry per-dimension
integrality side conditions, so the general `χ(O(m)) = C(m+n,n)` is a new theorem,
not a projection.  The `ℙ²` coordinate-change leg is **dropped**: `ℙ²` uses
`(r,c,v)` with `ch₂ = c/2 + v`, K3/abelian/Enriques use `(r,c,s)`, and linear
sections give a third lattice, each chosen so `χ` lands in `ℤ`.

**Future examples covered.**  `ℙⁿ` for every `n`; Calabi–Yau hypersurfaces of any
degree in `ℙ^{n+1}`; linear-section coordinates on any Picard-rank-one n-fold,
including the Fano threefolds of the Kuznetsov lane.

**Verdicts.**
- *Mathematics* — survives.  Coefficients recomputed by hand and matched;
  the closed form `(−1)^{i+k} k! S(i,k)/i!` checked at `(2,4) = 7/12` and
  `(3,4) = −3/2`; the Todd truncations reproduced from `CharacteristicClasses`.
  **Correction applied:** state the finding as two halves — the linear-section
  half now, the `projectiveSpaceTodd` half conditional on numerical-nfold-05.
- *Repository* — survives at medium.  Every citation exact; nothing named
  `koszulChCoeff`, `LinearSectionNum`, or `projectiveSpaceTodd` exists.
  **Corrections applied:** `p2NumericalVariety` cannot be reached by `abbrev`;
  the closed form needs a binomial identity not in Mathlib as stated, so define
  it as `PowerSeries.coeff i ((1 - exp(-X))^k)`.
- *Adoption and cost* — survives at medium.  Tables recomputed with exact
  rationals, `p2Todd`/`p3Todd`/`p4Todd` all matched.  **Corrections applied:**
  split into three and keep one — the linear-section root; demote the `ℙⁿ`-model
  leg to a dependent of numerical-nfold-05; drop the `ℙ²` coordinate-change leg,
  which buys no reuse and would cost the `rfl` link numerical-nfold-02 depends
  on.  The `i > n → 0` truncation is the geometric fact `H^{n+1} = 0` and must
  stay in the geometric child, never in `koszulChCoeff`.

#### numerical-nfold-04 — `NumericalRingData` is a bounded Mathlib graded algebra

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.7

**Declarations.**
`NumericalRingData` (`Numerical/Core/Definitions.lean:63`) with its
`piece`/`isInternal`/`one_mem_piece_zero`/`mul_mem_piece` fields;
`chComp`/`toddComp` carried as data (`:121`, with the rationale at `:42-44`);
`NumericalRingDualData` (`GrothendieckGroup/Dual.lean:57`, whose docstring at
`:55` says it is "carried as data because `NumericalRingData` does not expose the
graded projections"); `chDual` (`:107`); `mukaiDual` (`Mukai/Pairing.lean:65`);
`mukaiComp` (`Mukai/VectorClass.lean:54`); `sqrtComp_convolution`
(`Mukai/SqrtTodd.lean:126`); `twist`/`chBComp` (`Stability/TwistedChern.lean:104`,
`:224`); `lineTauCandidate` and `chernCharacterComponent`
(`IntersectionTheory/ChernCharacter/Basic.lean:493`, `:280`);
`chi₂_eq_sum` (`GrothendieckGroup/EulerPairing.lean:104`).

**Parent structure.**  The fields of `NumericalRingData` are literally Mathlib's
`SetLike.GradedMonoid piece` plus a `DirectSum.Decomposition` obtainable from
`isInternal` by `IsInternal.chooseDecomposition`
(`Mathlib/Algebra/DirectSum/Decomposition.lean:80`), i.e. a `GradedAlgebra ℚ piece`
bounded above by `n` with a top-degree functional.  `GradedRing.proj i`
(`Mathlib/RingTheory/GradedAlgebra/Basic.lean:100`) is the projection every
consumer is denied.  The repository already consumes that API at
`AlgebraicGeometry/ProjectiveSpectrum/Modules/ChartGeneration.lean:68-77`.

**Proposed root.**  Module `Numerical/Core/Graded.lean`; namespace
`AlgebraicGeometry.Numerical.NumericalRingData`.  `gradedMonoid`,
`decomposition`, `gradedAlgebra` as plain **defs** used with `letI` (not global
instances), plus `proj`, `proj_mul`, `degree_mul_eq_sum`, and `dual`.

**Projections.**  `chComp`/`toddComp` stay as data and gain
`proj_ch : R.proj i (V.ch E) = V.chComp E i`.  `mukaiComp` becomes
`R.proj i (V.ch E * √td)` and `chBComp` becomes `R.proj i (exp(−B) * V.ch E)` —
**both verified in Lean** for `i ≤ n`, with `e^{−B}` an honest element of `A`.
`chi₂_eq_sum` and `degree_ch_mul_todd` become instances of `degree_mul_eq_sum`.
`NumericalRingDualData` becomes derivable and `dual (dual x) = x`, explicitly
deferred at `Dual.lean:38-42`, becomes provable.

**Future examples covered.**  Every class built from products —
`ch·√td` on threefolds, twisted Mukai vectors, the Todd correction in projective
families, `ch(E⊗F)`, λ-ring operations; Kuznetsov-component charges needing
`e^{−B}·ch·√td`; extension past codimension four.

**Verdicts.**
- *Mathematics* — survives.  All eleven citations verified, and the two design
  docstrings the finding leans on are real.  Nilpotency checks out, so
  `exp(-B)` is a finite honest element and `td` is a unit.  **Corrections
  applied:** the claim that one graded product rule is "re-proved seven times"
  is inaccurate — that equation is stated nowhere; the real and stronger defect
  is that no leaf is ever connected to a ring product at all (`grep` finds no
  theorem `mukaiClass E = ch E * sqrtTodd`, none for `chBComp`, none for
  `lineTauCandidate`), so the root's acceptance criterion is those comparison
  theorems; and "`(√td)² = td` with no `i ≤ 4`" is true only after
  numerical-nfold-05 replaces the construction.
- *Repository* — survives.  The strongest form of the disease in this lane: the
  leaf copies a Mathlib root's fields verbatim, and `GradedRing.proj` is already
  consumed elsewhere in this same repository.  **Corrections applied:** ship
  `gradedMonoid`/`decomposition`/`gradedAlgebra` as plain defs introduced by
  `letI`, because `Core/Definitions.lean:31-33` makes presentations explicit and
  `Examples/Surface/Abelian.lean:111-115` is a regression test against
  instance-selecting one; `Dual.lean:36-43` deliberately omits the dual laws, so
  reversing that is an owner decision, with the uniqueness theorem as the
  acceptance criterion.
- *Adoption and cost* — survives, and the root is cheaper than claimed:
  `scratchpad/V04b/V04c/V04d.lean` all compile; the instances come out of the
  existing fields in about 8 lines and `proj_mul` is two lines.  `Classical.choice`
  is allowed by `scripts/check_audit.py:69`.  **Corrections applied:** cut the
  leaf list by more than half — `twist`/`twist_add_beta`/`twistCoeff_add`,
  `sqrtComp`/`sqrtComp_convolution`, `expComponent`/`lineTauCandidate` are stated
  for *arbitrary* families with no grading hypothesis and would be **restricted**
  by routing through `proj_mul`, and `IntersectionTheory.chernCharacterComponent`
  is a triangular recursion, not a convolution.  Two bonuses: `NumericalRingDualData`
  has **zero** inhabitants anywhere in the repository, and the deferral is on the
  record in two places.

#### walls-01 — The ℝ³ surface model and the ℝ⁴ threefold model are one formula

**Kind** dimension-specific-should-be-n-fold · **Impact** high · **Confidence** 0.95

**Declarations.**  `Wall.NumClass` (`Walls/Numerical/Basic.lean:104`),
`reZ` (`:124`), `imZ` (`:128`), `stChargeFamily`
(`Walls/Numerical/ChargeFamily.lean:59`); `Wall.Threefold.NumClass`
(`Walls/Threefold/Basic.lean:64`), `reZ` (`:121`), `imZ` (`:131`),
`chargeFamily` (`:174`); `Wall.ChargeFamily` (`Walls/ChargeFamily.lean:49`);
`Divisorial.ChargeCoordinates.centralCharge` (`Coordinates.lean:108`).

**Parent equation.**  `Z_w(d) = -∑_{j=0}^{n} ((-w)^j / j!) · d_{n-j}` with
`d_k = ∫H^{n-k}·ch_k(E)`.  This is the same parent as charges-01 seen from the
wall lane; the two lanes found it independently.

**Proposed root.**  `Walls/HDegree/Basic.lean`, namespace `…Wall.HDegree`, with
`HDegree n := Fin (n+1) → ℝ`, `charge`, `chargeFamily`, and the two chart
theorems.

**Projections.**  `stChargeFamily` and `Threefold.chargeFamily` become
reindex-and-pullback theorems — both compiled in
`scratchpad/HDegreeProbe.lean`.  `ChargeCoordinates.centralCharge a` and
`(twistByScalar b).centralCharge a` become `charge 2 (b + a·I)` composed with
`toNumClassHom`.  `HDegree.chargeFamily 4` exists for free.  Grandchildren are
unchanged.

**Future examples covered.**  The fourfold central charge; the two-dimensional
tilt charge used as the tilt-slope charge on a threefold; any Picard-rank-one
n-fold example.

**Verdicts.**
- *Mathematics* — survives.  Both expansions redone from source, character for
  character, including the `1/2` and `1/6` factors and the outer `α` of
  `Threefold.imZ`.  **Corrections applied:** the Todd/√td branch is **not**
  covered by the root and must not become a coefficient —
  `Divisorial/Mukai.lean:50-56` states that the Mukai and ordinary charges have
  different walls; the fourfold is present-tense, not future, since
  `p4NumericalVariety` already exists with no wall family;
  `charge_truncate` is not a partial sum but the `(n−1)`-fold formula on the top
  `k+1` entries; `v ⟨n - j, _⟩` needs ℕ-subtraction discipline.
- *Repository* — survives.  All ten citations exact; the generating formula
  verified by hand at both `n`; no n-general carrier exists anywhere
  (`grep` for `Fin (n + 1)` finds only Čech files).  Placement under
  `Walls/HDegree/` is a sibling of the existing `Walls/Numerical/` and
  `Walls/Threefold/`, and an `abbrev` carrier does not touch the
  single-instantiation gate.  **Correction applied:** the surface charge is not
  unrooted intrinsically — besides `ChernCharacter.centralCharge` it also has
  `Mukai.expChargeHom`; the accurate statement is that the surface charge has two
  intrinsic roots and `n ≥ 3` has none.
- *Adoption and cost* — survives.  Both projections compiled against the real
  definitions; migration is additive, with no namespace cutover, and
  `check_single_instantiation.py` does not fire on an `abbrev`.  Reuse is
  concrete: `Examples/Fourfold/*` already carries `NumericalVarietyData 4` models
  with no charge.  **Corrections applied:** budget the two `AddEquiv`s
  (`NumClass ≃+ Fin 3 → ℝ` and `Threefold.NumClass ≃+ Fin 4 → ℝ`), which Mathlib
  does not supply for the nested-product spelling; budget the `Fin` literal
  normal-form rewrite at every comparison lemma.

#### walls-02 — Five copies of `Δ_H = d₁² − 2d₀d₂`

**Kind** same-equation-two-names · **Impact** high (adoption lens rates medium)
· **Confidence** 0.95

**Declarations.**
`Wall.NumClass.discr` (`Walls/Numerical/Discriminant.lean:70`),
`Wall.Threefold.discr` (`Walls/Threefold/Basic.lean:204`),
`Divisorial.ChargeCoordinates.discr` (`Walls/Divisorial/Discriminant.lean:288`),
`Surface.discrH` (`Numerical/Stability/Slope.lean:174`),
`Threefold.discrHBeta` (`Numerical/Stability/BMT.lean:103`),
`ChernCharacter.discriminant` (`Divisorial/Discriminant.lean:227`),
`barDiscriminant` (`:240`),
`NumericalVarietyData.discriminant` (`GrothendieckGroup/Discriminant.lean:31`).

**Parent structure.**  The quadratic form `Δ_H(d) = d₁² − 2·d₀·d₂` on the
H-degree vector, invariant under the `e^{−βH}` twist.  The β-invariance was
verified by hand: `(d₁−βd₀)² − 2d₀(d₂−βd₁+(β²/2)d₀) = d₁² − 2d₀d₂` exactly, for
every `n`, because `betaTwist` only mixes downward.

**Proposed root** (corrected: reuse the bundled quadratic form that already
exists).  `DivisorSpace.realDiscriminant` (`Walls/Divisorial/Support.lean:92`) is
already a `QuadraticForm ℝ (Mukai.RealExtension D)` evaluating to `c² − 2rs`.
Define `HDegree.discrForm n` as that at `V = ℝ`, composed with the projection to
the first three coordinates, and take the **unhalved** convention
(`Support.lean:87-91` documents the fork).

**Projections.**  `NumClass.discr` and `Threefold.discr` become theorems (both
compiled: `discr 2 v = NumClass.discr (v 0, v 1, v 2)` and the `n = 3` analogue
close by `simp`); `discr_scale` becomes `QuadraticMap.map_smul`;
`ChargeCoordinates.discr` becomes the root composed with `toNumClass`, turning
`Circle.lean:104` into the definition; `discrH` and `discrHBeta` become the root
composed with `hDegrees`, and `discrHBeta` loses its inert `β`.
`ChernCharacter.discriminant` and `NumericalVarietyData.discriminant` keep their
own owners with the Hodge-index gap recorded as a negative result.

**Future examples covered.**  Fourfold `Δ_H` with no new definition; the BMT-type
generalized inequalities `Q_k`, all of which contain `α²Δ_H` as leading term; the
`Δ̄^B_ω = α²Δ_H` identification on every rank-one slice in any dimension.

**Verdicts.**
- *Mathematics* — survives.  All five carriers verified to hold the identical
  polynomial; β-invariance re-derived by hand; the `discDegH` vs `discrH`
  Hodge-index separation confirmed as load-bearing and correctly preserved.
  **Corrections applied:** the bundled root the finding proposes to create
  **already exists** as `realDiscriminant`, so the kind is existing-root-unused
  and the count is seven copies, not five; take the **unhalved** form, since
  getting it backwards silently scales every wall child by 2;
  `discr_toNumClass` and `discr_betaTwist_toNumClass` become `push_cast; ring`,
  not `rfl`, because they cross a ℚ→ℝ cast; `discr` needs `2 ≤ n` discipline on
  the `Fin` literals.
- *Repository* — survives.  All eight citations real; β-invariance verified from
  the actual `betaTwist`, so `discrHBeta`'s `β` argument is provably inert; the
  false-unification guard is the repository's own recorded position
  (`Slope.lean:24-38`, `WallTransport.lean:43-50`).  **Correction applied:**
  split in two — at `n = 2` the root already exists
  (`Wall.NumClass.discr`) and `ChargeCoordinates.discr` copies its polynomial,
  reconciled only ex post by `Circle.lean:104`; that half is actionable today.
  The `QuadraticForm` bundling is optional, since `Support.IsCompatible` takes a
  bare `Q : V → R` and deliberately does not require bilinearity.
- *Adoption and cost* — survives at **medium**, not high.  Two leaves reach,
  verified in Lean; `Threefold.discr (betaTwist β v) = Threefold.discr v` is a
  two-line `ring`, and `discrHBeta` is provably independent of `β`.
  **Correction applied:** demote impact — the five leaves are already a connected
  graph of proved comparisons (`WallTransport.lean:180`,
  `ThreefoldWallTransport.lean:207`, `Circle.lean:104`,
  `Divisorial/Discriminant.lean:299`), so the root is consolidation, not a missing
  connection; split out the inert-β fix so it is not blocked on `Walls/HDegree/`.

#### weak-tilting-01 — Three abelian HN carriers and their whole calculus

**Kind** missing-root · **Impact** high · **Confidence** 0.92

**Declarations.**
`AbelianHNFiltration` (`Weak/Foundation/StabilityFunction/HarderNarasimhan.lean:28`),
`AbelianWeakHNFiltration` (`WeakHarderNarasimhan.lean:44`),
`WeakAbelianHNFiltration` (`Weak/HarderNarasimhan/Heart.lean:66`);
the three `HasHNProperty` (`HarderNarasimhan.lean:85`,
`WeakHarderNarasimhan.lean:167`, `Heart.lean:97`);
`phiPlus_eq` (`Uniqueness/Extrema.lean:135`) vs `μPlus_eq` (`WeakExtrema.lean:154`);
`phiPlus_le_of_mono` (`PhaseMonotone.lean:63`) vs `μPlus_le_of_mono` (`WeakExtrema.lean:287`);
`restrict` (`Truncation.lean:71` vs `WeakTruncation.lean:84`);
`tailAt` (`Uniqueness/Tail.lean:35` vs `WeakTail.lean:90`);
`exists_crossIndex` (`Splitting.lean:49` vs `WeakTruncation.lean:182`);
`AbelianHNFiltration.mass` (`HNPolygon.lean:563`);
slicing `HNFiltration` (`Weak/Foundation/Slicing.lean:37`);
`FiniteFiltration` (`CategoryTheory/FiniteFiltration.lean:66`).

**Parent structure.**  An object `E`, a linearly ordered label type `L`, a label
function `lab : A → L`, a semistability predicate `SS`, and a finite strict chain
whose successive quotients satisfy `SS` with strictly decreasing labels.  All
three carriers have field-for-field identical chain skeletons and differ only in
`(L, lab, SS)`.  `WeakExtrema.lean:14-24` states the diagnosis itself: "the strict
development never performs arithmetic on phases … all of which hold over
`WithTop ℝ` exactly as over `ℝ`".

**Proposed root** (corrected on all three points).  Module
`CategoryTheory/Abelian/HarderNarasimhan/Basic.lean`; **namespace kept as
`CategoryTheory.Triangulated`** so existing dot notation resolves.

```lean
structure LabelledHNFiltration {A} [Abelian A] {L} [LinearOrder L]
    (lab : A → L) (SS : ObjectProperty A) (E : A) extends FiniteFiltration A E where
  label : Fin length → L
  label_strictAnti : StrictAnti label
  factor_label : ∀ j, lab (graded j) = label j
  factor_semistable : ∀ j, SS (graded j)
class HNDatum (A) where
  L; lab; SS
  lab_eq_of_iso : ∀ {E F}, (E ≅ F) → lab E = lab F
  [SS.IsClosedUnderIsomorphisms]
  hom_eq_zero_of_semistable_label_gt
  seesaw
```

**Projections.**  The three carriers become `abbrev`s at their `(L, lab, SS)`,
with per-leaf `abbrev` projections for the field names (`F.phase := F.label`)
so no consumer changes; `AbelianHNFiltration Z E ≃ AbelianWeakHNFiltration Z.toWeak E`
via `mapLabel` along the order embedding; the slicing `HNFiltration` stays a
sibling; `mass` stays on the abelian chain only.

**Future examples covered.**  Gieseker/lexicographic-polynomial HN;
`ν_{α,β}`-tilt HN filtrations on `Coh^β` for BMT threefold stability; any future
weak stability function with values in an ordered abelian group.

**Verdicts.**
- *Mathematics* — survives.  All three carriers read field for field; the
  docstring quotes verified; strict-is-a-case-of-weak checked analytically
  (`chargeSlope z = -cot(arg z)` on `Im > 0`, `⊤` on the negative real axis).
  **Corrections applied:** the root must `extends FiniteFiltration`
  (`CategoryTheory/FiniteFiltration.lean:47,66`) rather than re-declare a chain
  carrier; `HNDatum` must also carry `lab_eq_of_iso` and closure under
  isomorphism, since `phiPlus_le_of_mono` uses them; mass is not label-generic
  and the two existing masses have different codomains (`ℝ` vs `ℝ≥0∞`); the
  Gieseker example holds only for the lex-ordered coefficient vector, not for the
  "eventually ≤" comparison, which is not antisymmetric.
- *Repository* — survives.  All 19 declarations read; no label-generic HN root
  exists in the tree, and Mathlib has no Harder–Narasimhan theory at this pin.
  **Corrections applied:** the duplicated surface is smaller than "the whole
  calculus" — the charge-free subobject-lattice primitives are already shared
  (`WeakExtrema.lean:26-31`); keep the path under `CategoryTheory/Abelian/` but
  the namespace `CategoryTheory.Triangulated`.  Supporting evidence the surveyor
  missed: `CutoffPhase.lean:51,57` and `WeakCutoffSlope.lean:149,155` prove the
  same see-saw statement twice by different methods.
- *Adoption and cost* — survives; the root was written and compiled
  (`scratchpad/LabelledHN.lean`, exit 0) with both leaves reaching it by an
  `Equiv` whose inverses are `rfl`, and generic `labPlus`/`labMinus` agreeing
  with `phiPlus`/`muPlus` by `rfl`.  The duplicated calculus is ~1000 lines per
  side.  **Corrections applied:** cost is understated — 43 files / 289 references
  mention the three carriers, and an `abbrev` preserves type names but not
  projection names, so ship per-leaf projection abbrevs;
  `WeakAbelianHNFiltration` is in `scripts/single_instantiation_baseline.txt:69`
  and must be edited in the same change; the Gieseker lane already *reuses* the
  abstract carrier (`Gieseker/HarderNarasimhan/Consequences.lean:52`), so the
  missing Gieseker case is only the polynomial label; the `classMass` projection
  is on the slicing carrier, not the abelian chain.

#### weak-tilting-02 — The HN-cutoff torsion pair, built twice

**Kind** duplicate-parent · **Impact** high (repository and adoption lenses rate
medium) · **Confidence** 0.9

**Declarations.**
`hnTors`/`hnFree` (`Weak/Foundation/StabilityFunction/Cutoff.lean:64`, `:69`)
against `WeakCutoff.lean:64`, `:69` — the same definitions at the same line
numbers with `phi` renamed to `μ`;
`hom_eq_zero_of_mem_hnTors_of_mem_hnFree` (`Cutoff.lean:137` vs
`WeakCutoff.lean:152`);
`exists_shortExact_hnTors_hnFree` (`Splitting.lean:119` vs `WeakSplitting.lean:76`);
`hnTorsionPair` (`Tilting/TorsionPair/StabilityFunction.lean:69` vs
`WeakStabilityFunction.lean:77`);
`slicingTorsionPair` (`TorsionPair/Slope.lean:94`);
`slopeTorsionPair` (`SourceSlope.lean:267`);
`hnHeartTorsionPair`/`hnTilt` (`HeartAdapter.lean:154` vs `WeakHnTilt.lean:70`);
`hnTilt_heart_iff` (`HnTiltHeart.lean:57` vs `WeakHnTilt.lean:95`).

**Parent structure.**  For an HN datum `(L, lab, SS)` with the HN property and a
cutoff `c`, `T_c = {E | c < lab⁻(E)}` and `F_c = {E | lab⁺(E) ≤ c}` form a
torsion pair.  `TorsionPair/StabilityFunction.lean:34` admits "Neither pair is
derived from the other here"; `WeakHnTilt.lean:16` says "Nothing here is new
mathematics.  Every declaration is one composition".

**Proposed root.**  `CategoryTheory/Abelian/HarderNarasimhan/Cutoff.lean`,
namespace `CategoryTheory.Abelian`: `HNDatum.hnTors`, `hnFree`,
`cutoffTorsionPair`, `cutoffTilt`.

**Projections.**  The two abelian `hnTors`/`hnFree` and both `hnTorsionPair`
become abbrevs at `phaseDatum`/`slopeDatum`; the strict-weak comparison
`hnTors Z β = hnTors Z.toWeak (slopeOfPhase β)` holds for `β ∈ (0,1)`;
`hnTilt` and `hnTilt_heart_iff` are proved once.

**Future examples covered.**  The second (ν-slope) tilt for threefolds;
Gieseker-cutoff torsion pairs on `Coh X`; cutoffs by any future ordered label.

**Verdicts.**
- *Mathematics* — survives.  The two files verified as character-for-character
  copies; the order-only argument confirmed against the two Hom-vanishing axioms
  (`PhaseGeometry.lean:271`, `WeakSlopeGeometry.lean:304`) and the see-saw.
  **Corrections applied:** the domain mismatch is worse than "degenerate" —
  `hnTors Z β` is defined for every `β : ℝ` and for `β ≤ 0` is all of `A`, while
  `WithTop ℝ` has no bottom element, so **no** `μ₀` reproduces it; record that as
  a small genuine non-unification.  The verified duplication is four copies, not
  five; the slicing-heart pair stays a sibling.
- *Repository* — survives at medium.  All 16 citations real, including the two
  docstring admissions.  **Corrections applied:** "five times" overstates —
  `slopeTorsionPair` is already a proved reparametrisation of `slicingTorsionPair`
  (`SourceSlope.lean:219,242`), and the two `hnTilt` pairs are two-line
  compositions over the already-shared `HeartTorsionPair.ofTorsionPair`; the real
  duplication is the abelian cutoff pair.  This finding's payload is entirely
  downstream of weak-tilting-01 and must land as one change.
- *Adoption and cost* — survives at medium.  Two leaves reach by abbrev given
  weak-tilting-01's root.  **Corrections applied:** the count is two, plus one
  derived reparametrisation and two correct leaves of an existing root; the
  slicing pair **cannot** be projected — `slicingTorsionPair` builds
  `exists_triangle` over ~30 lines of slicing-specific work in the ambient
  triangulated category and there is no `HeartTorsionPair → TorsionPair` bridge
  anywhere; merge this into weak-tilting-01 rather than scheduling it separately.

#### weak-tilting-03 — `charge`/`slope`/`IsSemistable` written twice at two class data

**Kind** leaf-copies-root · **Impact** high · **Confidence** 0.85

**Declarations.**
`ClassDatum` (`Weak/Charge.lean:91`);
`WeakStabilityFunction.slope` (`Weak/Basic/Definitions.lean:170`, a hand-written
`if/else`), `IsSemistable` (`:198`), `IsStable` (`:206`);
`chargeSlope` (`Weak/Foundation/StabilityFunction/WeakSlopeGeometry.lean:63`);
`WeakStabilityFunctionOn.charge` (`:184`), `slope` (`:210`), `IsSemistable` (`:233`);
`StabilityFunction.charge`/`phase`/`IsSemistable` (`Basic.lean:141`);
`heartSlope`/`HeartSemistable` (`Weak/HarderNarasimhan/Heart.lean:54`);
`heartDatum` (`HeartDatum.lean:57`);
`K₀Ab.toAmbient` (`Triangulated/GrothendieckGroup/HeartComparison.lean:81`).

**Parent structure.**  `ClassDatum` was introduced so that "the abelian and
ambient theories are one structure at two class data", yet every derived notion
is written twice.  `WeakStabilityFunction t` *is* `WeakStabilityFunctionOn (heartDatum t)`
(`Definitions.lean:93`), and its `slope` body is character-for-character
`chargeSlope` applied to `W.charge` — which `WeakSlopeGeometry.lean:210` defines
as exactly that.

**Proposed root.**  `ClassDatum.Hom` in `Weak/Charge.lean`, plus
`WeakStabilityFunctionOn.restrict`, `ClassDatum.charge`, `ClassDatum.slope`,
`ClassDatum.phase` in `Weak/Foundation/StabilityFunction/Basic.lean`.  The
`relevant` field of `Hom` is **one-directional**.

**Projections.**  `Definitions.slope` and `WeakSlopeGeometry.slope` both become
`ClassDatum.slope` — verified by `rfl` in both directions
(`scratchpad/ClassDatumHom.lean`, exit 0).  `heartSlope`/`HeartSemistable`
become `(W.restrict (toAmbientHom t)).slope` / `.IsSemistable`.
`StabilityFunction.phase` (`Basic.lean:123`) and `WeakSlopeData.phase`
(`WeakSlope.lean:187`) join the same root.  `toAmbientHom t` is built from
`K₀Ab.toAmbient_of` (`HeartComparison.lean:87`).

**Future examples covered.**  Kuznetsov components — `Ku(X) ⊂ D^b(X)` with the
class datum restricted along the inclusion is exactly a `ClassDatum.Hom`;
numerical class maps as `Hom`s rather than a new carrier each time; weak
stability functions on a tilted heart used as input to a second tilt.

**Verdicts.**
- *Mathematics* — survives, and the repository states the gap itself
  (`Mukai/Tilting.lean:24-26`: "Take the charge on `K₀ C` as the primitive and
  *define* the heart datum by composing with `K₀Ab.toAmbient` … Compatibility is
  then `rfl` rather than a field").  The two semistability shapes were checked to
  be equivalent on the closed half-plane, including the `⊤` branches.
  **Corrections applied:** the fix for the duplicated slope is a **move**, not an
  abbrev — `Definitions.lean` does not import `WeakSlopeGeometry.lean`, so
  `chargeSlope` must move up to `Weak/Charge.lean` first; the `relevant` field is
  not an identity, since the two `Relevant` predicates differ; the generic
  `IsSemistable` must be the SES form, with the `Subobject` form available only
  on the two half-planes, where both see-saw directions are proved.
- *Repository* — survives.  All 13 citations real; `slope`'s body is
  character-for-character `chargeSlope`; no morphism of class data exists
  anywhere.  **Corrections applied:** the concrete blocker is the import order —
  `chargeSlope` must move to `Weak/Charge.lean`; the composition site is
  `Mukai/Ambient.lean:41`, not only the docstring; `ClassDatum` was on the
  single-instantiation baseline until #784, so `ClassDatum.Hom` with one instance
  needs a second inhabitant in the same change or a baseline entry.
- *Adoption and cost* — survives; the cheap half is proved definitionally, with
  both leaves agreeing by `rfl`.  A second consumer of the same restriction
  pattern is already hand-written at `Mukai/Ambient.lean:40-41`.  **Corrections
  applied:** `Hom.relevant` must be one-directional; **split the finding** — the
  charge/slope/phase half is free and should land alone, while the `IsSemistable`
  half needs a third parameter (an `E`-side predicate) and the `Subobject` form
  becomes a theorem needing the half-plane see-saw, so it does not have two
  leaves reaching it without restating.

#### symmetry-metric-01 — Autoequivalence transport is the preimage transfer

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.9

**Declarations.**
`Slicing.mapEquiv` (`Symmetry/Autoequivalence/Slicing/Transport.lean:156`) vs
`Slicing.preimage` (`Phase/Transfer/Basic.lean:101`) and
`preimageData_equivalence` (`:196`);
`actStabAut` (`Symmetry/Autoequivalence/Stability/Transport.lean:238`) vs
`PreStabilityCondition.WithClassMap.preimage` (`Phase/Transfer/PreStability.lean:94`)
and `StabilityCondition.WithClassMap.preimage` (`Phase/Transfer/LocallyFinite.lean:259`);
and eight parallel theorem pairs — local finiteness
(`Stability/Transport.lean:177` vs `LocallyFinite.lean:232`), extreme phases
(`Metric/Isometry/Phase.lean:141` vs `Transfer/Phase.lean:118`), phase windows
(`Phase/Order/Equivariance.lean:35` vs `Transfer/Phase.lean:158`), order
equivariance (`Equivariance.lean:86` vs `Transfer/Phase.lean:218`), slicing
distance (`Isometry/Phase.lean:187` vs `Transfer/Phase.lean:273`), full distance
(`Isometry/Full.lean:128` vs `Transfer/Metric.lean:129`).

**Parent structure.**  For a triangulated functor `F` and a slicing `s`, the
transported slicing is `P_F(φ)(E) := s.P φ (F.obj E)`.  `mapEquiv s Φ` is
literally `P φ X := s.P φ (Φ.inverse.obj X)`, which is `preimage s Φ.inverse` on
the nose; `preimageData_equivalence`'s docstring says "Unlike `Slicing.mapEquiv`,
this theorem allows the source and target categories to differ", naming the
parent in prose without proving the equality.  `LocallyFinite.lean:44` says "The
proof follows `mapEquiv_isLocallyFinite`".

**Proposed root.**  `Slicing.mapEquiv_eq_preimage` in `Phase/Transfer/Basic.lean`
(which already imports the Symmetry module, so there is no cycle), plus
`WithClassMap.compClassMap` in `Phase/Transfer/Equivariance.lean` (which already
imports both lanes).

**Projections.**  `mapEquiv` = `preimage Φ.inverse` by `Slicing.ext C rfl` —
compiled.  `AutQuot`/`TriEquiv.act` reach the root through the same equation.
`actStabAut` becomes `(σ.preimage Φ.inverse _).compClassMap lam _`.
`mapEquiv_isLocallyFinite` becomes `PreimageData.isLocallyFinite`;
`mapEquiv_phiPlus`, `mapEquiv_ltProp_iff`, `precedes_act_iff` become instances of
the Transfer-side theorems; the two distance equalities become `le_antisymm` of
two applications of the preimage inequalities.

**Future examples covered.**  Any autoequivalence-transport theorem stated once
for `preimage`; Kuznetsov-component inclusion and projection functors, for which
transfer of stability conditions *is* `preimage`; the tensor-by-line-bundle twist
in the Bayer property.

**Verdicts.**
- *Mathematics* — survives; the identification is definitional and every
  instance hypothesis of `preimageData_equivalence` is among `mapEquiv`'s six.
  The charge half checks out arithmetically from `hlam` plus `K₀.map_of`.
  **Corrections applied:** the metric half needs one further lemma
  (`stabilityMass_compClassMap`), since `stabilityDist` is typed at a fixed class
  map; `Slicing.preimage_mapEquiv` (`Phase/Transfer/Equivariance.lean:69`)
  already relates the two constructions as a *commutation square*, not as the
  identification, and should be cited; `Equivalence.symm` is a plain def, so the
  six instances must be supplied by `letI`.
- *Repository* — survives.  All 18 citations real; `preimagePhase` and
  `mapEquiv`'s `P` are the same term at `F := Φ.inverse`; `Slicing.ext` needs
  only `P` equality; no cycle.  **Corrections applied:** the reverse inequality
  needs `Slicing.preimage_iso` (`:180`), because
  `(s.mapEquiv Φ).preimage Φ.functor` is only iso-equal to `s`;
  `Slicing.preimageOrderData` (`Transfer/Phase.lean:209`) is the better root for
  the four order theorems.
- *Adoption and cost* — survives; the projection was written and compiled
  (`scratchpad/SymBridge.lean`, exit 0), including
  `mapEquiv_eq_preimage := Slicing.ext C rfl` and two re-derived theorems.
  **Corrections applied:** the homes are `Transfer/Basic.lean` and
  `Transfer/Equivariance.lean`, both of which already import what is needed;
  `Transfer/LocallyFinite` does **not** import the Symmetry module (the grep hit
  is a docstring), so retiring the Symmetry-side duplicates adds imports to four
  files, none of them a forbidden or cyclic edge; the charge half is not free and
  needs `compClassMap` plus a mass-invariance lemma.

#### symmetry-metric-02 — Stability-space walls do not reach the wall root

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.85

**Declarations.**
`StabWall.stabWall` (`Chambers/Basic.lean:62`), `stabRegular` (`:72`),
`StabChamber` (`:187`), `IsAutStable` (`Chambers/Action.lean:48`);
`Wall.ChargeFamily` (`Walls/ChargeFamily.lean:49`), `wallValue` (`:118`),
`wall` (`:129`), `linearAct`/`wall_linearAct` (`:273`, `:294`);
`Wall.Spherical.wall` (`Walls/Spherical/Basic.lean:301`), `chamber` (`:310`);
`PeriodDomain.wall` (`LinearAlgebra/QuadraticForm/PeriodDomain.lean:118`);
`combinedCentralCharge_equivariant` (`Symmetry/Combined/PeriodMap.lean:126`).

**Parent structure.**  `Wall.ChargeFamily` is documented as "the dimension- and
geometry-independent root of the numerical wall hierarchy".  The stability space
is itself a parameter type for it: `⟨fun σ => σ.Z⟩` is a `ChargeFamily`, and that
is exactly the period map whose equivariance `PeriodMap.lean:111-126` already
proves.  `Chambers/Basic.lean:28-30` states the gap: "No map from the stability
space to any of those three parameter spaces is defined."

**Proposed root** (corrected).  `ChargeFamily.vanishingWall δ := {p | Z.charge p δ = 0}`
and `stabChargeFamily C v := ⟨fun σ => σ.Z⟩` in the Walls namespace; a set-level
`regular` taking the wall family as a parameter (it carries no charge content, so
it must not sit in the `ChargeFamily` namespace); a new
`vanishingWall_linearAct` needing only **injectivity**, not `realDet g ≠ 0`.
`halfWall` is **dropped** for now — `Spherical.wall` is its only inhabitant.

**Projections.**  `stabWall δ` becomes `vanishingWall δ` definitionally, so
`mem_stabWall_iff` stays `Iff.rfl`.  The period-domain wall reaches
`vanishingWall` through the **already-proved** comparison
`mem_wall_iff_centralCharge_eq_zero`, giving the root two genuine leaves.
`stabRegular`, `Spherical.chamber` and `periodDomain₀` are three leaves of
`regular`, and `stabRegular_eq_compl_iUnion` / `chamber_eq_compl_iUnion` are the
same two-line proof twice.  The `GLTilde` and `AutPairQuot` wall invariance come
from `linearAct` and `pullback` through the existing equivariance theorems.

**Future examples covered.**  Walls for stability conditions on Kuznetsov
components; threefold and fourfold BMT-type walls in `(α,β,s)` parameter spaces;
period-map preimages of wall complements in Bridgeland's `P⁺₀` construction.

**Verdicts.**
- *Mathematics* — survives.  `Z(pt) = -1` recomputed from `realPairing`, so
  `wallValue p δ pt = Im Z(δ)` and `Spherical.wall` is the root wall cut by the
  sign; the half-wall caveat confirmed load-bearing.  **Corrections applied:**
  `PeriodDomain.wall` is a set of *submodules*, so it reaches the root only
  through a chart — but the two chart theorems already exist
  (`Lattice/Mukai/CentralCharge.lean:110,120`); the charge hom need not be built,
  since `expChargeHom` already exists.
- *Repository* — survives.  All twelve citations real; `grep` over
  `abstraction-tree.md` for `Wall|Bridgeland|StabilityCondition|PeriodDomain|Chamber`
  returns **zero** hits.  **Corrections applied:** `Spherical` must be listed as a
  *sibling* of `ChargeFamily` under `Walls`, not a child — nothing under
  `Walls/Spherical/` mentions `ChargeFamily`; the stability-consuming children are
  four, not three (`check_layering.py:99-108`);
  `Wall.ChargeFamily` is the structure at `:49`, not `:47`.
- *Adoption and cost* — survives.  The projection compiled, and the decisive
  second leaf is the period-domain lane, which has **already proved** its wall is
  charge-vanishing.  **Corrections applied:** drop `halfWall` (one inhabitant);
  keep `regular` out of the `ChargeFamily` namespace; the `GLTilde` projection is
  wrong as written — `wall_linearAct` is about two-class walls and needs
  `realDet g ≠ 0`, whereas the existing stability-space invariance is proved from
  `actC_injective` alone, so `vanishingWall_linearAct` is a new lemma with
  strictly weaker hypotheses.

#### dg-01 — `Enhancement` has no exactness layer

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.85

**Declarations.**
`CategoryTheory.Enhancement` (`Triangulated/DGEnhancement/Basic.lean:105`);
the twelve consumer sites carrying `[e.equiv.functor.CommShift ℤ]` and
`[e.equiv.functor.IsTriangulated]` by hand — `H0/ConeFunctor.lean:181`, `:208`;
`FourierMukai/KernelCone.lean:42`, `:88`, `:143`, `:190`, `:205`, `:212`, `:219`,
`:226`; `FourierMukai/CounitKernel.lean:124`, `:153`;
`Cdg.enhancement` (`HomotopyCategory/DGEnhancement/Enhancement.lean:47`), the one
inhabitant, which discards `Cdg.seamCommShift` (`Agreement.lean:191`) and
`Cdg.seamIsTriangulated` (`:197`);
`TriEquiv` (`Symmetry/Autoequivalence/Slicing/Quotient.lean:59`), the same bundle
for the autoequivalence case.

**Parent structure.**  An enhancement is a pretriangulated dg category with an
**exact** equivalence `H⁰A ≃ T`.  `Basic.lean:33-37` says a statement quantifying
over enhancements "must quantify over exact comparisons — either by strengthening
this structure or by carrying the clause at the statement", and the repository
carries it at the statement, twelve times.

**Proposed root** (corrected: data, not a Prop class).  Extract `TriEquiv`'s
bundle to `CategoryTheory/Triangulated/Equivalence.lean`, namespace
`CategoryTheory.Triangulated`:

```lean
structure Triangulated.Equivalence (C D) [...] where
  e : C ≌ D
  [fAdd] [iAdd] [fCS : e.functor.CommShift ℤ] [iCS] [fTri] [iTri]
abbrev TriEquiv C := Triangulated.Equivalence C C
structure ExactEnhancement (T) extends Enhancement T where
  exact : Triangulated.Equivalence (H0 toEnhancement.dgCat) T
```

**Projections.**  `Cdg` reaches it by `⟨Cdg.seam⟩`, all six instance fields being
existing global instances.  `TriEquiv` becomes the `C = D` abbrev, keeping every
existing name.  The eight `_obj_distinguished` theorems take the bundle; the two
*definition* sites (`ConeFunctor.lean:177-183`, `KernelCone.lean:39-55`) keep
their bare `[CommShift]` hypothesis, since they are stated with only `[HasShift W ℤ]`
in scope.  `KernelAutoequivalence` and `KernelEquivalence` take the bundle as a
field.

**Future examples covered.**  Uniqueness of enhancements; enhancement of
`Dᵇ(Coh(X×Y))` kernel categories; Kuznetsov-component enhancements
`Ku(X) ⊂ Dᵇ(X)`; `K^dg(A)`.

**Verdicts.**
- *Mathematics* — survives.  Every citation verified, both design docstrings are
  real, and the Mathlib API is present at the pin.  **Corrections applied:** the
  Mathlib anchors are `Equivalence.CommShift` at
  `Mathlib/CategoryTheory/Shift/Adjunction.lean:526` and `Equivalence.IsTriangulated`
  at `Mathlib/CategoryTheory/Triangulated/Adjunction.lean:190`, not the cited
  `CommShift.lean:360`; the root **cannot** be a Prop class, because
  `Functor.CommShift` is data and both equivalence-level classes take the functor
  halves as instance arguments; `TriEquiv` also carries `fAdd`/`iAdd`.
- *Repository* — survives.  Every repository citation exact, and the identification
  is definitional.  **Corrections applied:** the proposed signature does not
  typecheck as a Prop class (same reason); the root must be extracted to a neutral
  `CategoryTheory/Triangulated/Equivalence.lean`, because `TriEquiv` currently
  lives under `StabilityCondition/Symmetry/`, which `DGEnhancement` must not
  import; `CategoryTheory.Enhancement` is already baselined
  (`single_instantiation_baseline.txt:4`) while `TriEquiv` is not, so re-rooting
  `TriEquiv` hands the new structure its inhabitants and the gate passes.
- *Adoption and cost* — survives.  **Corrections applied:** `Functor.CommShift`
  is data, `Equivalence.CommShift` presupposes the functor halves, and the two
  definition sites are stated without `Preadditive`/`Pretriangulated` in scope, so
  the root must be the data bundle and only the `_obj_distinguished` family
  collapses to it.  Migration: 4 files, no audit or umbrella churn, no baseline
  entry.

#### dg-02 — The cone of a natural transformation to the identity, three times

**Kind** missing-root · **Impact** high (adoption lens refuted) · **Confidence** 0.8

**Declarations.**
`DGAdjunction.CounitConeData` (`DGCategory/Pretriangulated/AdjunctionCone.lean:40`)
and `UnitConeData` (`:82`);
`EvaluationData.TwistConeData` (`DGCategory/Pretriangulated/ObjectTwist.lean:72`);
`CounitConeData.twistTriangleFunctor` and its seven companions
(`DGEnhancement/H0/AdjunctionCone.lean:70-127`);
`TwistConeData.twistTriangleFunctor` and its companions
(`DGEnhancement/H0/ObjectTwist.lean:81-152`);
`CounitKernelConeData` (`FourierMukai/CounitKernel.lean:59`), `twist` (`:115`),
`triangleInSource` (`:129`).

**Parent structure.**  For a closed degree-0 `ε : F ⟶ 𝟭` with chosen objectwise
cones, `T := Cone(ε)` is an endofunctor in the functorial distinguished triangle
`F ⟶ 𝟭 ⟶ T ⟶ F[1]` whose second arrow is the canonical inclusion.  Anno–Logvinenko's
twist, Seidel–Thomas's object twist and the Fourier–Mukai twist candidate are the
three specializations.

**Proposed root.**  `DGCategory/Pretriangulated/IdentityCone.lean` for the `G = 𝟭`
dg slice, and the H⁰ layer (`twistTriangleFunctor_obj_obj₂ = X`,
`_obj_mor₂ = h0 inclusion`, `twistH0CommShift`, `twistH0IsTriangulated`).

**Projections.**  `CounitConeData` and `TwistConeData` become
`IdentityConeData A.counit` / `V.evaluation`; the H⁰ suites become one; the
kernel twist reaches the triangulated-level shape only after transporting along
a triangle isomorphism.

**Future examples covered.**  Kuznetsov rotation functors and twists around an
exceptional object on `Ku(X)`; `Pⁿ`-twists and family twists; Fourier–Mukai
twists by a spherical kernel on K3 surfaces; dual cotwists.

**Verdicts.**
- *Mathematics* — survives.  All the cited sites read; the `G = 𝟭` slice is real,
  and `EnhancedFunctorH0.lean:16` admits "Every declaration is one composition".
  **Corrections applied:** `EnhancedFunctorH0.lean:84` and `:213` are **not** a
  third and fourth copy — they are one-line delegations; the kind is
  `missing-root` only for the thin `G = 𝟭` slice and for the triangulated-level
  statement, since the dg root `ConeData` exists and both leaves reach it by
  `abbrev`; the FM leaf's `obj₂` is **not** `X` on the nose, so it needs an
  explicit transport of a distinguished triangle along a triangle isomorphism.
- *Repository* — survives at medium.  Citations real, including the two docstring
  admissions.  **Corrections applied:** the count is "twice, plus three
  already-related presentations"; the real duplication is the H⁰ exactness half,
  where one `G = 𝟭` leaf has the suite and its sibling does not, so the consumer
  re-derives it; a fourth mirrored copy exists for `UnitConeData`
  (`H0/AdjunctionCone.lean:129-160`), so the parent should be stated for a
  transformation with the identity at either end; `Pretriangulated.ConeOfNatTransToId`
  would need two inhabitants in the same change or a baseline entry.
- *Adoption and cost* — **refuted** (single dissent).  The dg-level
  `twist`/`inclusion`/`inclusion_isClosed` are already generic `ConeData`
  projections, the H⁰ "copies" are one-line delegations and `rfl` lemmas, and at
  the triangulated level neither leaf can inhabit the proposed structure —
  `(DGFunctor.id C).h0` is only *isomorphic* to `𝟭 (H0 C)` (`H0.lean:373`), and
  the FM leaf's `obj₂` is a transform.  Recorded as the dissent; the surviving
  content is the H⁰ exactness asymmetry and the transport lemma.

#### triang-01 — Eight carriers of the graded self-Ext profile

**Kind** missing-root · **Impact** high · **Confidence** 0.9

**Declarations.**
`SerreFunctor.SphericalExtProfile` (`SerreFunctor/Transport.lean:37`);
`SphericalTwist.IsSphericalObject` (`SphericalTwist/Basic.lean:60`);
`SerreFunctor.PseudoprojectiveExtProfile` (`Transport.lean:47`);
`SerreFunctor.IsSphericalObject` / `IsPseudoprojectiveObject`
(`SerreFunctor/Objects.lean:39`, `:50`);
`Triangulated.IsExceptional` (`SemiorthogonalDecomposition/Exceptional.lean:104`);
`AdjacentExtProfile` (`SemiorthogonalDecomposition/AdjacentExt.lean:38`);
`IsGradedOrthogonal` (`SerreFunctor/Classification.lean:78`);
`ExceptionalCollection.hom_shift_eq_zero` (`Collection.lean:137`) and `IsStrong` (`:149`);
`K3Surface.SphericalExtProfile` (`Surface/Spherical.lean:143`) and its bridge
(`Surface/SphericalCategorical.lean:48`).

**Parent structure.**  `dim_k Hom(E, F⟦i⟧) = [i ∈ S]`, specialized by the support
set `S` and by whether `E = F`: spherical `S = {0,n}`, pseudoprojective
`S = [0,n]`, exceptional `S = {0}`, adjacent `S = {0,1}`, graded-orthogonal
`S = ∅`, strong `S ⊆ {0}`, K3 `S = {0,2}`.  The generic lemmas `not_isZero`
(five copies), `of_iso` (four copies), and transport along a fully faithful
`k`-linear `CommShift` functor (three copies) are each proved per carrier.

**Proposed root.**  `CategoryTheory/Linear/ExtProfile.lean`, namespace
`CategoryTheory.Linear`: `ExtSupportIn (S : Set ℤ) (E F : C)` and
`HasExtProfile (S) (E F)`, with `of_iso_left/right`, `map`, `finrank_eq_ite`,
`not_isZero`, and `chiHom_eq` proved once.

**Projections.**  Each leaf reaches the root by a **proved iff**, not by
`abbrev` — the degree-0 clause is stated on the unshifted `End E` while the root
lands on `E ⟶ E⟦0⟧`, and the repository already needs that bridge
(`SphericalTwist/Basic.lean:97`).  `IsExceptional` reaches it only as a bridge
theorem, keeping its `algebraMap`-bijectivity API.  `AdjacentExtProfile` is
one-way (root ⇒ leaf) because its `other_zero` is a `finrank = 0` clause.
`IsGradedOrthogonal` is a genuine `abbrev` of `ExtSupportIn ∅`.

**Future examples covered.**  `ℙⁿ`-objects (`S = {0,2,…,2n}`); 3-spherical objects
on CY threefolds and in `Ku(cubic threefold)`; 2-spherical objects in
`Ku(cubic fourfold)`; exceptional pairs on `ℙⁿ` and quadrics; spherical objects on
Enriques surfaces and their residual categories.

**Verdicts.**
- *Mathematics* — survives.  All carriers read field for field; the
  `IsExceptional` iff holds over a field; the Euler shadow confirmed.
  **Corrections applied:** none of the spherical/pseudoprojective/K3 leaves can be
  an `abbrev` (unshifted `End`); the `AdjacentExtProfile` projection is one-way,
  since `finrank = 0` is junk-true on an infinite-dimensional Hom; the
  `not_isZero` count is five, not four.
- *Repository* — survives.  All twelve citations exact, and the duplicated-lemma
  counts verified; no root of this shape exists in the tree or in Mathlib;
  placement under `CategoryTheory/Linear/` is Tier-2 correct and the root would
  have many producers.  **Corrections applied:** the `AdjacentExtProfile`
  projection is one-way; the label "bridge to the wrong sibling" on
  `SphericalCategorical.lean:48` is wrong — it bridges to the correct abstract
  sibling; the root also needs `[HasShift C ℤ]`, whose Mathlib site is
  `CategoryTheory/Shift/`, so the author must state which carrier decides
  placement, and must drop three now-dead baseline rows.
- *Adoption and cost* — survives.  Three carriers are field-identical and the
  repository already writes three hand-rolled field-copy adapters between them
  (`Transport.lean:207-210`, `SphericalTwist/Basic.lean:196-200`,
  `SphericalCategorical.lean:48-52`, the last of which says "Field for field").
  Only 6 files touch the fields at all.  **Corrections applied:** the projections
  are proved comparisons, not `rfl`; **drop** `IsExceptional` (its whole API is
  algebra-theoretic) and `AdjacentExtProfile` (no consumer anywhere) from the leaf
  list; `of_serreFunctor` does exist, which strengthens rather than weakens the
  finding — the unbridged pair is `SerreFunctor.SphericalExtProfile` against
  `SphericalTwist.IsSphericalObject`.

#### triang-02 — `twistK₀` and `Mukai.reflect` are `Module.preReflection`

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.9

**Declarations.**
`SphericalTwist.twistK₀` (`SphericalTwist/GrothendieckGroup.lean:95`),
`twistK₀Equiv` (`:151`), `chiK₀_twistK₀_twistK₀` (`:208`);
`Mukai.reflect` (`LinearAlgebra/Lattice/Mukai/Reflection.lean:73`), `reflectHom`
(`:104`), `reflectEquiv` (`:147`), `reflectIsometry` (`:213`);
`MukaiRealization.map_twistK₀` (`SphericalTwist/Mukai.lean:141`);
Mathlib `Module.preReflection` (`Mathlib/LinearAlgebra/Reflection.lean:71`),
`Module.reflection` (`:101`), `preReflection_preReflection` (`:88`).

**Parent structure.**  `preReflection x f = id − f.smulRight x`, involutive when
`f x = 2`.  `twistK₀ E x = x − χ(E,x)•[E]` is `preReflection [E] (χ(E,−))` with
`f x = 2 ⇔ χ(E,E) = 2`; `reflect b s v = v + ⟪v,s⟫•s` is
`preReflection s (−⟪−,s⟫)` with `f s = 2 ⇔ ⟪s,s⟫ = −2`, i.e. exactly
`IsSpherical`.  `grep` for `preReflection|Module.reflection` over `DerivedAlgGeo`
returns **zero** hits.  `GrothendieckGroup.lean:29-30` states that "the split
mirrors `Reflection.lean` term for term".

**Proposed root.**  Mathlib's, plus one owed generic lemma
`preReflection_isometry` in `DerivedAlgGeo/LinearAlgebra/Reflection.lean`
(Tier-1: the Mathlib path).

**Projections.**  `twistK₀` becomes `preReflection` routed through
`AddMonoidHom.toIntLinearMap`; `twistK₀_twistK₀` becomes
`involutive_preReflection`; `twistK₀Equiv` becomes `Module.reflection`;
`twistK₀_self` becomes `preReflection_apply_self`; `reflect`, `reflect_reflect`,
`reflectEquiv`, `reflect_self`, `reflect_of_pairing_eq_zero` likewise;
`chiK₀_twistK₀_twistK₀` and `pairing_reflect_reflect` become the one isometry
lemma; `map_twistK₀` becomes a generic naturality lemma.

**Future examples covered.**  The A₂ Weyl/braid action on the Mukai lattice of a
cubic fourfold's `Ku(X)`; reflections in (−2)-classes of Enriques and K3 lattices;
twists by 3-spherical objects on CY threefolds (where `χ(E,E) = 0`, so the root
correctly refuses `reflection`); root-system reflections for exceptional-collection
mutations.

**Verdicts.**
- *Mathematics* — survives.  Both identifications checked arithmetically,
  including the `.flip` and the sign that makes `f s = 2` exactly `IsSpherical`.
  **Corrections applied:** "Mathlib has no reflection-is-isometry lemma" is
  **false** — `LinearMap.IsReflective.isOrthogonal_reflection` exists at
  `Mathlib/LinearAlgebra/RootSystem/OfBilinear.lean:83`, and both leaves satisfy
  `IsReflective` over `ℤ`, so the owed lemma is a wrapper, not a new theorem; the
  braid projection is weaker than claimed and should be demoted to "related via
  `preReflection_preReflection` plus an extra identification".
- *Repository* — survives, with the strongest evidence of the set: the Mathlib
  citations are exact, the repository grep returns zero, and the arithmetic checks
  both ways.  **Correction applied:** type-coercion friction —
  `preReflection` is an `End R M` while `twistK₀` is an `AddMonoidHom`, so the
  round trip through `toIntLinearMap` means `twistK₀_apply` becomes
  `preReflection_apply` rather than `rfl`, and downstream `@[simp]` normal forms
  need re-checking.  `Mukai.reflectHom` is already `→ₗ[ℤ]` and takes the root
  cleanly.
- *Adoption and cost* — survives.  Both leaves reach in Lean with no field
  copying; roughly 60 lines across two files plus the braid relation are retired;
  the leaf names stay, so there is no review-payload exposure.  **Corrections
  applied:** place the owed lemma at `LinearAlgebra/Reflection.lean` (Tier 1, not
  under a `BiadditiveForm` subdirectory); the isometry lemma genuinely is absent
  from `Mathlib/LinearAlgebra/Reflection.lean`, which is what makes the root
  non-thin; keep the functional `f` explicit, since `twistK₀` weights by `χ(E,−)`
  and `reflect` by `⟪−,s⟫`.

#### triang-03 — `K₀.map` and `K₀Ab.map` and the descent law

**Kind** existing-root-unused · **Impact** high (adoption lens refuted) ·
**Confidence** 0.8

**Declarations.**
`GrothendieckPresentation.map` (`CategoryTheory/GrothendieckGroup/Presentation.lean:123`),
`map_id`/`map_comp` (`:148`, `:156`), `IsAdditive.of_relationMap` (`:136`);
`K₀.map` (`Triangulated/GrothendieckGroup/Functorial.lean:38`) with `map_id`
(`:47`), `map_comp` (`:52`), `map_congr` (`:63`);
`K₀Ab.map` (`CategoryTheory/GrothendieckGroup/Functorial.lean:47`) with the same
three;
`K₀Ab.toAmbient` (`Triangulated/GrothendieckGroup/HeartComparison.lean:81`), the
only descent written the intended way;
`K₀.Realization.Descends` (`Triangulated/GrothendieckGroup/Realization.lean:44`);
`CompatibleClassMaps` (`Triangulated/Families/BaseChange.lean:162`);
`pullK₀` (`:92`).

**Parent structure.**  A map of presentations induces `P.Group →+ Q.Group` with
`map_id` and `map_comp` proved once; and the descent law `R' ∘ m = f ∘ R` is one
equation.

**Proposed root** (corrected).  Add `GrothendieckPresentation.map_congr` to
`Presentation.lean`; keep `K₀.Realization.Descends` (`Realization.lean:44`) as the
descent root rather than inventing a presentation-level `Descends`.

**Projections.**  `K₀.map` and `K₀Ab.map` are already *definitionally* the root's
term (`K₀.lift` is `(triangulatedPresentation C).lift`), so what is duplicated is
`map_of`/`map_id`/`map_comp`/`map_congr`.  `CompatibleClassMaps.pull_compatible`
becomes `Descends (classMap t) (classMap s) (F.pull f) (AddMonoidHom.id V)`, and
`class_pull` becomes `Descends.apply_of`.  `AutPair.compat`
(`Symmetry/Autoequivalence/Stability/ClassMap.lean:94`) is a second leaf of the
same equation.  The heart-charge descent
`Descends R_heart R_C (K₀Ab.toAmbient t) id` is the genuinely missing statement.

**Future examples covered.**  Pushforward on `K₀` along a proper morphism;
`K₀` of a tilted heart; base-change functors of Kuznetsov components in families;
`N(X) = K₀/ker χ` as a `Descends` witness.

**Verdicts.**
- *Mathematics* — survives.  The definitional identity confirmed, and the two
  descent spellings verified to be the same equation.  **Corrections applied:**
  "re-derive the root" overstates it — they *are* the root's term, unnamed, so
  the defect is the un-named root plus four re-proved lemmas; `map_congr` genuinely
  does not exist at the root; the `[F.Additive]` risk is weaker than stated;
  `CompatibleClassMaps` needs no new presentation-level `Descends`; and the
  finding under-counts the leaves — `AutPair.compat` and `TwistShaped.compat`
  (`SphericalTwist/StabilityAction.lean:107`) are two more.
- *Repository* — survives at medium.  All nine citations exact, and the descent
  half is airtight; collapsing `CompatibleClassMaps` removes a baseline row.
  **Corrections applied:** downgrade the functoriality half — `K₀.map F` is
  *already* definitionally `(triangulatedPresentation C).map F.obj _`; do not
  invent `GrothendieckPresentation.Descends`, since `K₀.Realization.Descends`
  already serves both consumers and `BaseChange.lean` already imports it; promote
  the missing `toAmbient` descent, which `HeartComparison.lean:26-29` says is the
  whole purpose of `toAmbient`.
- *Adoption and cost* — **refuted** (single dissent).  The `map` half is
  definitionally identical, so what is duplicated is three two-line `ext; simp`
  proofs per leaf — proof duplication, which the brief excludes — and `map_congr`
  would have to be donated *upward*, not received.  The salvageable core is the
  `Descends` half, which has two leaves (`CompatibleClassMaps` and
  `AutPair.compat`) and is refiled at medium.

#### geometry-derived-01 — Coherent pullback and pushforward are one exact lift

**Kind** same-equation-two-names · **Impact** high · **Confidence** 0.92

**Declarations.**
`HasCoherentPullback` (`DerivedCategory/Families/BoundedGeometry.lean:81`, four
core fields at `:84-90`, plus five derived data fields at `:92-106`) and
`ofExactSheafPullback` (`:117`);
`HasCoherentPushforward` (`Families/CoherentPushforward.lean:100`, the identical
four fields at `:102-109`) and `coherentDerivedPushforward` (`:131`);
`sheafPullbackId`/`sheafPullbackComp` (`CoherentPullbackCoherence.lean:71`, `:82`)
against `sheafPushforwardId`/`sheafPushforwardComp`
(`CoherentPushforwardCoherence.lean:68`, `:80`);
`Coh.pullback` (`Modules/Coherent/Pullback.lean:130`) and `Coh.pushforward`
(`Modules/Coherent/Pushforward/Finite.lean:163`), both
`(Scheme.coherent _).lift (ι ⋙ G)`;
`cohPushforward` (`Cohomology/ClosedImmersion.lean:78`).

**Parent structure.**  One statement about a functor `G : X.Modules ⥤ Y.Modules`:
`G` preserves coherence, its restriction is exact, and
`Coh.ι ⋙ G ≅ (restriction) ⋙ Coh.ι`.  The two contracts are the same record at
`G = modulePullback f` and `G = modulePushforward f`; the pushforward docstring
calls itself the "mirror" of the pullback contract, and the id/comp laws are the
same `fullyFaithfulCancelRight` term with the module-level id/comp swapped.

**Proposed root.**  `Modules/Coherent/ExactLift.lean`, namespace
`AlgebraicGeometry.Coh`.  `Coh.ExactLift G` must be a **class**, with the
coherence-preservation hypothesis an argument of `ofLift` rather than a field —
it is free on the pullback side and needs `IsFinite` on the pushforward side.

**Projections.**  `HasCoherentPullback f := Coh.ExactLift (modulePullback f)` and
`HasCoherentPushforward f := Coh.ExactLift (modulePushforward f)`, with per-field
aliases so the ~101 uses of `sheafPullback`/`sheafPushforward` do not change;
`sheafPullbackId/Comp` and `sheafPushforwardId/Comp` become `idIso`/`compIso`;
the derived data fields of the pullback contract are dropped in favour of
`ExactLift.derived`/`bounded`, exactly as the pushforward side already does;
`cohPushforward g F` becomes an explicit `rfl` lemma against `(Coh.pushforward g).obj F`.

**Future examples covered.**  Affine-morphism coherent pushforward; tensor with a
line bundle on `Coh` and `Dᵇ(Coh)`; Fourier–Mukai transforms with kernel finite
over both factors; closed-immersion pushforward used by Serre-functor and
Kuznetsov computations; any future `HasCoherentX` contract.

**Verdicts.**
- *Mathematics* — survives.  Both contracts read field for field and are the same
  record at two `G`; the id/comp laws are the same term; `cohPushforward` is
  `(Coh.pushforward g).obj F` by `rfl`.  **Corrections applied:** `ExactLift` must
  be a `class`, or `[HasCoherentPullback f]` binders stop resolving; `ofLift`
  cannot derive coherence-preservation, which is hypothesis-free on the pullback
  side but needs `IsFinite` on the pushforward side; state in the migration that
  `derivedFactors` pins the functor through the localization `Q`.
- *Repository* — survives.  Every cited declaration real; the id/comp proofs read
  side by side and are the same term; no root of this shape exists in the tree,
  and Mathlib owns only the raw `ObjectProperty.lift`.  Placement is legal and
  `AlgebraicGeometry` is outside `GENERIC_SUBJECTS`.  **Corrections applied:**
  make it a class; `cohPushforward` is definitional but under stronger hypotheses,
  which `ClosedImmersion.lean:78` already discharges; keep the coherence
  hypothesis in `ofLift`.
- *Adoption and cost* — survives.  Two leaves, the same record, and the gates are
  clear: `AlgebraicGeometry` is excluded from `check_single_instantiation.py`, and
  `exe/RestateHistoricalNames.lean` names none of these.  **Corrections applied:**
  ship per-field aliases or the cutover touches 14 files and ~101 occurrences; the
  `cohPushforward` projection is overstated and should be an explicit `rfl` lemma;
  the root belongs under `AlgebraicGeometry/Modules/Coherent/`, not under
  `CategoryTheory/`.

#### geometry-derived-02 — Five finite-Ext realizations and three Euler characteristics

**Kind** missing-root · **Impact** high (mathematics and adoption lenses rate
medium) · **Confidence** 0.8

**Declarations.**
`LinearCohomology` (`Cohomology/Finiteness/FiniteDimensional.lean:54`),
`FiniteDimensionalCohomology` (`:67`);
`FiniteCohomology` (`Cohomology/EulerCharacteristic/Basic.lean:53`) and
`eulerCharacteristic` (`:79`);
`grothendieckEulerHom` (`Cohomology/EulerCharacteristic/Additivity.lean:296`);
`Duality.Serre.Data` (`Duality/Serre/Cohomology.lean:114`);
`Duality.Serre.BilinearData` (`Duality/Serre/Bilinear.lean:104`) and `eulerChar` (`:164`);
`ExtFiniteBounded` (`Algebra/Homology/DerivedCategory/HomFinite.lean:75`);
`HomFiniteBounded` (`Triangulated/GrothendieckGroup/EulerForm.lean:128`),
`chiHom` (`:141`), `K₀.EulerForm.ofLinear` (`:274`);
`Scheme.Modules.extUnitAddEquivDerivedH` (`Cohomology/Derived/UnitExt.lean:67`).

**Parent structure.**  A `k`-linear, degreewise finite-dimensional realization of
`Ext^•(E,F)` on a `k`-linear abelian category, and its alternating sum.
`Bilinear.lean:18` says the two-variable realization "specialises at `E = 𝒪` to
the above", and `Bilinear.lean:101` says "The fields mirror `Serre.Data`", yet no
projection exists (`grep` for `toData`/`ofBilinear` in `Bilinear.lean` returns
nothing).

**Proposed root** (heavily corrected).  Keep only the `Coh X` realization root,
and place it under `AlgebraicGeometry/Duality/Serre/` or
`AlgebraicGeometry/Cohomology/` — **not** under `Algebra/`, which is a
`GENERIC_SUBJECT` where a two-inhabitant root needs a baseline entry.

```lean
structure LinearExtRealization (k) (A) [HasExt A] where
  extSpace : A → A → ℕ → ModuleCat k
  comparison : ∀ E F n, (forget₂ _ AddCommGrpCat).obj (extSpace E F n)
                          ≅ AddCommGrpCat.of (Abelian.Ext E F n)
  finite : ∀ E F n, Module.Finite k (extSpace E F n)
```

**Projections.**  `BilinearData` reaches it by `extends`; `Data` carries it as a
field with `extSpace F j := R.extSpace F K.canonicalCohObject j`.  The
`FiniteCohomology` family and the Euler/K₀ half are **dropped** (see the verdicts).

**Future examples covered.**  The Mukai pairing on K3 consumed by Bridgeland
Lemma 5.1; Hilbert polynomials for Gieseker stability; Hirzebruch–Riemann–Roch;
Euler forms on Kuznetsov components; the numerical Grothendieck quotient.

**Verdicts.**
- *Mathematics* — survives at medium.  Every cited bridge verified; the signs of
  the three Euler characteristics agree; the Coh-vs-`X.Modules` obstruction is
  real and correctly named (`CoherentExtComparison` is inhabited only for affine
  noetherian schemes).  **Corrections applied:** `Linear k (Coh Y)` is already an
  instance and Mathlib's `Abelian.Ext` is already a `k`-module, so for the two
  `Coh X` leaves the honest root is the existing `ExtFiniteBounded k (Coh X)` plus
  the duality datum; only the `Sheaf.H` side needs a realization layer;
  `BilinearData.canonicalTwist` is unconstrained, so `toData` needs an added
  hypothesis; `Serre.Data` additionally carries `derived`, so it is not a pure
  projection.
- *Repository* — survives at medium.  All citations real and the missing
  projection confirmed by grep.  **Corrections applied:** the root as sketched
  cannot produce `FiniteCohomology`, because `LinearCohomology.moduleH` is a
  *functor* with a natural comparison while the sketch is a bare function; split
  the claim — the Ext-realization root is genuinely missing, but the
  alternating-sum half is existing-root-unused, with `chiHom` and
  `K₀.EulerForm.ofLinear` as the canonical owners and
  `Surface/SphericalCategorical.lean:58` as the bridge idiom; `Algebra` is a
  `GENERIC_SUBJECT`, so a zero-producer root needs a baseline line.
- *Adoption and cost* — survives at medium, narrowly.  Exactly two declarations
  in the tree carry a linear Ext realization, with identical three-field shapes
  under the same local `HasExt` instance, and the promised projection is
  genuinely absent.  **Corrections applied:** four claims refuted — the
  `FiniteCohomology` family cannot reach the root (`moduleH` is a functor compared
  against `Sheaf.H` in `X.Modules`, and `extUnitAddEquivDerivedH` does not bridge
  Coh-Ext to `Sheaf.H`); `extFiniteBounded` cannot be written, because the two
  `k`-actions are unrelated across a comparison in `AddCommGrpCat`;
  `grothendieckEulerHom` is at `:296` and lives on `K₀Ab (Coh X)`, so the K₀ half
  is a theorem chain, not a projection; and `BilinearData.toData` is still not
  writable from the root.  Keep only the `Coh X` root; drop `bound`/`vanishesAbove`
  and the naturality field.

#### geometry-derived-03 — Left-derived pullback interfaces are scheme-decorated

**Kind** dimension-specific-should-be-n-fold · **Impact** high (adoption lens
refuted) · **Confidence** 0.85

**Declarations.**
`SchemeBaseChange.LeftDerivedPullback` (`Families/LeftDerivedPullback.lean:54`);
`PullbackAcyclicResolution` (`Families/PullbackAcyclicResolution.lean:48`),
`isLeftDerived` (`:346`), `toLeftDerivedPullback` (`:360`);
`derivedPullback` (`Families/ExactPullback.lean:107`);
`kProjectiveDerivedFunctor` (`Algebra/Homology/DerivedCategory/KProjective.lean:99`);
`boundedAboveProjectiveDerivedFunctor` (`BoundedAboveProjective.lean:156`);
`affineKProjectiveDerivedPullback` (`DerivedCategory/Dqc/AffineKProjectivePullback.lean:48`);
`RelativePerfectPullback` (`Moduli/PerfectComplex/Pullback.lean:70`).

**Parent structure.**  Mathlib's universal property `Functor.IsLeftDerivedFunctor`
plus the standard functorial-acyclic-resolution constructor.
`LeftDerivedPullback` and `PullbackAcyclicResolution` have exactly those fields at
`F := modulePullback f`, and no proof in the resolution file uses a scheme fact —
`isLeftDerived`'s `CostructuredArrow` terminal-object argument included.
Independently, `kProjectiveDerivedFunctor` is a second construction that is never
shown to satisfy the universal property: repository-wide,
`IsLeftDerivedFunctor` occurs only in the two scheme files.

**Proposed root.**  `Algebra/Homology/DerivedCategory/LeftDerived/AcyclicResolution.lean`,
namespace `CategoryTheory.Functor`: `LeftDerivedData` and `AcyclicResolutionData`,
with the scheme structures as abbrevs and a bridge theorem for the K-projective
construction on its locus.

**Projections.**  Both scheme structures become abbrevs at
`F := modulePullback f`; `FlatPullbackResolution.ofFlat` becomes
`AcyclicResolutionData.ofExact`; `affineKProjectiveDerivedPullback` gets the
missing bridge; `RelativePerfectPullback` is unchanged.

**Future examples covered.**  K-flat resolutions for non-flat pullback; the
derived tensor product; right-derived pushforward by K-injective resolutions;
derived Hom into `ω_X`; derived functors of extension of scalars.

**Verdicts.**
- *Mathematics* — survives.  Every field checked; the whole resolution file
  grepped for scheme-specific content, which occurs only in variable binders;
  `IsLeftDerivedFunctor` confirmed to occur in exactly the two scheme files.
  **Corrections applied:** the genericity claim must read "no scheme-theoretic
  *fact* is used", not "no scheme tokens occur"; the K-projective bridge cannot be
  an equality even on `ModuleCat`, because its source is an essential-image
  subcategory, so the bridge theorem must first prove that image is everything.
- *Repository* — survives at medium.  All citations exact; the proposed root is
  `def`-level and the leaves have ≥ 2 producers each.  **Corrections applied:**
  the proposed root is partly pre-empted by Mathlib — `IsLeftDerivabilityStructure`
  and its functorial-resolution constructor exist at the pin — so the repo-owned
  structure should be a thin adapter onto that API, or the leaves should consume it
  directly; the K-projective bridge must be stated on the locus and for
  `A = ModuleCat R`, since `X.Modules` has no projectives.
- *Adoption and cost* — **refuted** (single dissent).  `LeftDerivedPullback.isLeftDerived`
  *is* Mathlib's `IsLeftDerivedFunctor`, so the root is already reached as a field
  and generalizing the bundle is a sigma type; `kProjectiveDerivedFunctor` has a
  different source and reaches neither root; both proposed roots would ship with
  one inhabitant family under `Algebra/`, a `GENERIC_SUBJECT`, requiring a baseline
  entry.  Recorded as the dissent; what survives is a placement issue and a
  missing bridge theorem, both out of the brief's scope.

#### geometry-derived-06 — Geometric Serre duality never reaches `SerreFunctorData`

**Kind** existing-root-unused · **Impact** high (adoption lens refuted) ·
**Confidence** 0.8

**Declarations.**
`SerreFunctorData` (`Triangulated/SerreFunctor/Basic.lean:72`), `SerreCategoryData` (`:102`);
`Duality.Serre.BilinearData` (`Duality/Serre/Bilinear.lean:104`), whose `duality`
field is `Dual (Ext^i(E,F)) ≃ₗ Ext^{n−i}(F, canonicalTwist E)`;
`Duality.Serre.Data` (`Duality/Serre/Cohomology.lean:114`), the `E = 𝒪_X` case;
`DerivedStatement` (`:61`); `LocallyFreeSpecialization` (`:189`).

**Parent structure.**  `SerreFunctorData.eta : Dual (A ⟶ B) ≃ₗ[k] (B ⟶ S A)`.
On `Dᵇ(Coh X)` with `S = (−⊗ω_X)[n]`, evaluating at `A := E`, `B := F[i]` gives
the bilinear statement verbatim.  `grep` for `SerreFunctorData|SerreCategoryData`
under `AlgebraicGeometry/Duality/` returns **nothing**, and nothing constructs a
`SerreCategoryData` for `Dᵇ(Coh X)`.

**Proposed root** (corrected: pointwise, with the twist as data).
`AlgebraicGeometry/Duality/Serre/SerreFunctor.lean`:

```lean
structure GeometricSerreFunctor (K) where
  serre : SerreCategoryData k (SchemeBoundedCoherentDerivedCategory X)
  twist : Coh X → Coh X
  twistIso : ∀ E, serre.serre.S.obj ((single _ 0).obj E)
                    ≅ ((single _ 0).obj (twist E))⟦(n : ℤ)⟧
```

**Projections.**  `BilinearData` is the one projection (eta at single objects and
shifts, under `[HomFiniteBounded k Dᵇ(Coh X)]`).  `Serre.Data` and
`DerivedStatement` are **blocked negative results**, on `CoherentExtComparison`
and on the absent coherent `RHom` respectively.

**Future examples covered.**  K3 `S ≅ [2]`; Enriques `S² ≅ [4]`;
`Ku(cubic fourfold)` `S ≅ [2]` and `Ku(cubic threefold)` `S³ ≅ [5]`; Bridgeland
Lemma 5.1; Riemann–Roch symmetry.

**Verdicts.**
- *Mathematics* — survives.  The specialization checked exactly, including the
  `n − i` degree arithmetic and the `E = 𝒪` case; the non-connection verified by
  grep (the single `SerreCategoryData` use under `AlgebraicGeometry/` is on an
  Enriques residual category, never on `Dᵇ(Coh X)`).  **Correction applied:**
  `serreIso` as sketched has no referent — there is no `−⊗ω_X` functor on `Coh X`,
  which is exactly why `BilinearData` carries `canonicalTwist` as a bare function
  — so state the root with objectwise isos on heart objects, which are writable now.
- *Repository* — survives.  All citations verified; the structure is expressible
  today (`Linear k (Coh Y)` and `Linear k (DerivedCategory (Coh Y))` both exist,
  and `chiHom` already typechecks on the bounded coherent category); placement is
  correct and the bridge gives the already-baselined `SerreFunctorData` a second
  inhabitant.  **Corrections applied:** name the two prerequisites the tree itself
  records as open — `HomFiniteBounded` for `Dᵇ(Coh X)` and `CoherentExtComparison`;
  only root ⇒ leaf is a projection.
- *Adoption and cost* — **refuted** (single dissent).  The root as sketched is
  unwritable (no tensor endofunctor on `Coh X` anywhere), and only one leaf
  reaches even a repaired version: `Serre.Data`'s `duality` is stated against
  `moduleH` in `X.Modules`, and `DerivedStatement` is built from a supplied bare
  `rHomDualizing`.  Recorded as the dissent; its salvage — the pointwise root with
  one projection and two recorded negatives — is what is written above.

#### lattices-01 — The Mukai extension and pairing, duplicated over ℤ and ℝ

**Kind** missing-root · **Impact** high · **Confidence** 0.9

**Declarations.**
`Mukai.MukaiLattice` (`LinearAlgebra/Lattice/Mukai/Basic.lean:51`), `pairing` (`:56`),
`selfPairing` (`:143`), `pairingBilin` (`:263`);
`Mukai.RealExtension` (`Mukai/RealForm.lean:82`), `realPairing` (`:87`),
`realPairing_comm` (`:94`), `realBilin` (`:100`);
`Wall.Spherical.pairing` (`Walls/Spherical/Basic.lean:117`), `selfPairing` (`:125`);
`Mukai.extendMap` (`Mukai/IntegralBridge.lean:116`), `extendMapHom` (`:131`),
`realPairing_extendMap` (`:136`);
`Wall.Spherical.IntegralComparison` (`Spherical/Basic.lean:367`), `.map` (`:376`),
`pairing_map` (`:387`).

**Parent structure.**  The Mukai extension of a bilinear module over a commutative
ring: `Ext R N := R × N × R` with `⟪(r,c,s),(r',c',s')⟫ = b c c' − r s' − r' s`.
`Mukai.pairing` and `Mukai.realPairing` are the same expression
`b v.2.1 w.2.1 - v.1 * w.2.2 - w.1 * v.2.2` typed twice; the ℤ→ℝ comparison is
also built twice, both `(r,c,s) ↦ ((r:ℝ), f c, (s:ℝ))`.
`Walls/Spherical/Basic.lean:67` states "Generalising `Mukai/Basic.lean` over a
base ring would be the tidier fix and is deliberately not done here", and
`RealForm.lean:76-81` records that a third copy (`RealMukai`) was already deleted.

**Proposed root.**  `LinearAlgebra/Lattice/Mukai/Basic.lean`, namespace `Mukai`:
`Extension R N := R × N × R`, `pairing`, `pairingBilin`, `selfPairing`, and
`map (σ : R →+* S) (f) (compat)` with `pairing_map`.

**Projections.**  `MukaiLattice N := Extension ℤ N` and
`RealExtension V := Extension ℝ V` — both `rfl`, verified; `realPairing`,
`realBilin`, `selfPairing` likewise `rfl`; `extendMap f u = Extension.map (Int.castRingHom ℝ) f u`
is `rfl`; one ring-generic `pairing_map` subsumes both `realPairing_extendMap` and
`Spherical.pairing_map`; `realForm` (half the self-pairing) and `expRe`/`expIm`
stay ℝ-children, since the exponential chart is not ring-generic.

**Future examples covered.**  Mukai lattices over `ℤ`, `ℚ` (the repository already
has a third ring at `Numerical/GrothendieckGroup/EulerPairing.lean:255`), `ℝ` and
`ℂ`; the cubic-fourfold Kuznetsov Mukai lattice; the Enriques `U ⊕ E₈(−1)` real
extension.

**Verdicts.**
- *Mathematics* — survives.  The expression is identical character for character
  and is polynomial in the coordinates, hence ring-generic verbatim; both bridges
  have identical `simp; push_cast; ring` proofs.  **Corrections applied:**
  "no proof change" is false for `not_isSpherical_and_isIsotropic`
  (`Basic.lean:207`), whose statement is **false** over a ring with `2 = 0`, so the
  root must carry `(2 : R) ≠ 0` for that lemma or leave it in the ℤ child;
  `extendMap` takes `→ₗ[ℤ]` while `IntegralComparison.toFun` is `→+`, so those
  projections are "equal by construction", not `rfl`.
- *Repository* — survives.  All 16 citations real; the two `map` constructions are
  the same term; the docstring quote is verbatim; no ring-generic Mukai extension
  exists in the tree or in Mathlib (`QuadraticMap.prod` is a different carrier);
  placement is Tier-1 correct and `Extension` is an `abbrev`, so the gate does not
  apply.  A fourth ring is already present at `EulerPairing.lean:255`.
  **Correction applied:** the two leaves disagree on the middle map's type, so
  state the root's `map` on the weaker `N →+ V` plus the compatibility hypothesis.
- *Adoption and cost* — survives, and is the strongest of the lattice findings:
  every projection compiled, including `rfl` for all four carrier and pairing
  identifications and for `extendMap`; three rings, not two.  **Corrections
  applied:** the cheapest root takes the middle map as a bare function plus the
  compatibility hypothesis; `IntegralComparison` must **not** be dissolved — it is
  supplied geometric data — only its `.map` and `pairing_map` become projections;
  the root must export the **unhalved** `selfPairing`.

#### lattices-02 — The Bogomolov discriminant is `Mukai.selfPairing`

**Kind** existing-root-unused · **Impact** high · **Confidence** 0.85

**Declarations.**
`Mukai.selfPairing_mk` (`Lattice/Mukai/Basic.lean:150`), `realForm_mk`
(`Mukai/RealForm.lean:120`), `Wall.Spherical.selfPairing_mk`
(`Walls/Spherical/Basic.lean:132`);
`Wall.NumClass.discr` (`Walls/Numerical/Discriminant.lean:70`) and `discr_scale` (`:93`);
`Wall.Threefold.discr` (`Walls/Threefold/Basic.lean:204`);
`ChernCharacter.discriminant` (`Walls/Divisorial/Discriminant.lean:227`),
`ChargeCoordinates.discr` (`:288`);
`NumericalVarietyData.discriminant` (`Numerical/GrothendieckGroup/Discriminant.lean:31`);
`Surface.discrH` (`Numerical/Stability/Slope.lean:174`), `discrHBeta` (`BMT.lean:103`);
`K3.mukaiSelfPairing` (`Numerical/RiemannRoch/K3.lean:88`), `mukaiSelfPairing_eq` (`:100`);
`K3.mukaiPairing` (`GrothendieckGroup/EulerPairing.lean:255`).

**Parent structure.**  `q_b(r, c, s) = b(c,c) − 2rs`, which is exactly
`Mukai.selfPairing_mk`.  Every discriminant in the tree is that form pulled back
along a Chern triple.  `K3.mukaiSelfPairing_eq` already proves the identification
for one leaf and does not lift it; `discr_scale`'s docstring ("the discriminant is
a quadratic form") re-proves `Mukai.selfPairing_smul`.

**Proposed root** (corrected: the root exists).  `Mukai.realPairing`/`selfPairing`
is the parent for every ℝ-valued leaf; the only new declaration needed is
`discriminantOf b (ch : M →+ Extension R N)` for the pullback presentation, on an
`AddMonoidHom`, because in `NumericalVarietyData` the class group is only an
`AddCommGroup` and `chComp` is a bare function.

**Projections.**  Compiled: `Wall.NumClass.discr v = Mukai.realPairing (mul) v v`;
`Wall.Threefold.discr` likewise on the first three coordinates;
`ChernCharacter.discriminant S E = Mukai.realPairing S.intersection (ch.toRealExtension E) (…)`,
which reaches the root in one line because `ChernCharacter.toRealExtension`
already exists (`Walls/Divisorial/Charge.lean:108`).  `discr_scale` becomes
`selfPairing_smul`.  `ChargeCoordinates.discr`, `discrH`, `discrHBeta` are
pointwise identities.  `K3.mukaiSelfPairing` is the same form after the shear
`s ↦ s + r`, and `mukaiSelfPairing_eq` becomes that shear identity.
`NumericalVarietyData.discriminant` reaches the root only through lattices-01's
ring-generic version.

**Future examples covered.**  Quintic and `ℙ³` BMT walls; the cubic threefold's
`Ku(X)` via tilt restriction; the fourfold `Δ_H`; the cubic-fourfold Mukai
self-pairing on `A₂^⊥`; generalized Bogomolov–Gieseker inequalities stated once.

**Verdicts.**
- *Mathematics* — survives.  Each of the five carriers checked to hold
  `d₁² − 2d₀d₂`; the K3 shear arithmetic re-derived; the `discDegH` separation
  confirmed and preserved.  **Correction applied:** `discriminantOf` as sketched
  requires the class group to be a module over the coefficient ring, which holds
  only for the two wall carriers and fails for every geometric leaf, so state the
  projection pointwise or supply an `AddMonoidHom`-valued variant.
- *Repository* — survives.  All 16 citations real and the arithmetic checked, with
  the `algebraMap ℚ A` rank slot noted.  **Corrections applied:** state the
  `NumericalVarietyData` Chern triple explicitly or the `rfl` will not close; note
  that the full pairing is also duplicated at `ℚ` (`EulerPairing.lean:255`), so the
  discriminant root and lattices-01 should land in the same change.
- *Adoption and cost* — survives, and is the cheapest-to-adopt finding relative to
  what it buys.  Three projections compiled, including the divisorial one through
  the existing `toRealExtension`; purely additive, ~6 comparison theorems in 6
  files.  **Corrections applied:** the root already exists, so no new
  `QuadraticForm` is needed; the declaration is `Wall.Threefold.discr`, not
  `Threefold.NumClass.discr`; the K3 *pairing* half is already correctly rooted
  (`GrothendieckGroup/MukaiVector.lean:201`) and should be cited as the pattern the
  discriminant leaves have not adopted, not as a further duplicate.

#### lattices-03 — Threefold and fourfold linear-section lattices are one Koszul table

**Kind** dimension-specific-should-be-n-fold · **Impact** high (adoption lens
rates medium) · **Confidence** 0.85

**Declarations.**
`ThreefoldNum`/`threefoldChCoeff` (`Examples/Threefold/LinearSection.lean:61`, `:66`);
`FourfoldNum`/`fourfoldChCoeff` (`Examples/Fourfold/LinearSection.lean:50`, `:56`);
`SurfaceNum` (`Examples/Surface/RankOne.lean:193`);
`k3ChCoeff` (`Examples/Surface/K3.lean:38`), `p2ChCoeff` (`ProjectivePlane.lean:43`);
Mathlib `PowerSeries.exp` (`Mathlib/RingTheory/PowerSeries/Exp.lean:48`).

**Parent structure.**  The same Koszul table as numerical-nfold-03, found
independently from the lattice side: the coefficient of `H^i` in `(1 − e^{−H})^k`.
The two lanes agree on the coefficients, on the `7/12` and `−3/2` entries, and on
the fact that `_ + 4 => 0` / `_ + 5 => 0` is the `i > n` truncation.

**Proposed root.**  `RingTheory/PowerSeries/KoszulChern.lean` (Tier-1: Mathlib's
`PowerSeries` site), plus the geometric child.  Define the table finitely or
recursively; the `PowerSeries` identification is an optional later theorem.

**Projections.**  `ThreefoldNum`/`FourfoldNum` become `LinearSectionNum 3`/`4`;
the two tables become evaluations; `threefoldChi_sum`/`fourfoldChi_sum` become one
lemma.  The surface leaves do **not** reach it: `k3ChCoeff` is the identity table
and `p2ChCoeff` has `+E₁/2` at `i = 2`, the opposite sign to the Koszul `−1/2`, so
`n = 2` is a lattice equivalence, not an instance.

**Future examples covered.**  Fivefolds and higher; Calabi–Yau hypersurfaces of any
degree in `ℙ^{n+1}`; linear-section coordinates on any Picard-rank-one n-fold,
including the cubic threefold and cubic fourfold.

**Verdicts.**
- *Mathematics* — survives.  Coefficients recomputed; the closed form evaluated at
  every entry of both tables and matched; the `ℙ²` coordinate change checked on
  both coordinates and on `χ`.  **Correction applied:** split the root — the
  linear-section half is verified and cheap; `projectiveSpaceTodd` cannot be
  written without the power-series carrier or a Bernoulli closed form.
- *Repository* — survives.  Citations exact; coefficients recomputed
  independently; the Mathlib API real at the pin; nothing named `koszulChCoeff`,
  `LinearSectionNum`, or `projectiveSpaceTodd` exists.  **Corrections applied:**
  placement must be `RingTheory/PowerSeries/`, not `Algebra/PowerSeries/`;
  Mathlib's Stirling numbers are `Nat.stirlingSecond`; the `i = 0` coefficient is
  `0`.
- *Adoption and cost* — survives at medium; the unification verified in Lean with
  one universal table reproducing both leaf tables by `match i; simp; ring`.
  **Corrections applied:** the truncation **must** be in the geometric child —
  `threefoldChCoeff d E 4 = 0` while the untruncated table gives
  `−E₁/24 + 7E₂/12`, so a root folding the truncation into `koszulChCoeff` is
  false; Mathlib at this pin has no `Nat.stirling2` and `PowerSeries.exp` has a
  different signature, so define the root as a finite table or a recursion.

#### surf-01 — Harder–Narasimhan existence is a generic abelian theorem on a leaf

**Kind** dimension-specific-should-be-n-fold · **Impact** high · **Confidence** 0.92

**Declarations.**
`PolarizedVarietyData.hasHNProperty` (`Stability/Gieseker/HarderNarasimhan/Existence.lean:146`);
`MuHNInput` (`HarderNarasimhan/MaximalDestabilizing.lean:63`), `exists_slopeMax` (`:128`),
`IsMaximalDestabilizing` (`:215`), `multiplicity_le_of_mono` (`:96`);
`topSlope_le_of_shortExact` (`HarderNarasimhan/Seesaw.lean:66`);
`splice` (`HarderNarasimhan/Splice.lean:236`);
`IsPure` (`Gieseker/Basic.lean:236`);
`MuPositivityData` (`Gieseker/MuStability.lean:66`);
`WeakSlopeData` (`Weak/Foundation/StabilityFunction/WeakSlope.lean:84`);
`HasHNProperty`/`AbelianWeakHNFiltration` (`WeakHarderNarasimhan.lean:167`, `:44`).

**Parent structure.**  Rudakov's theorem for an abelian category with a
`WeakSlopeData`: Noetherian objects plus slopes bounded above give the HN
property.  Every `Coh X` fact consumed is a field of `WeakSlopeData`;
`MuPositivityData` literally restates the two positivity fields in Coh-X spelling;
`Splice.lean:24-25` says "Nothing here mentions a polarization";
`Existence.lean:11-12` records that `HasHNProperty` "appears only as an assumption
in the abstract theory".

**Proposed root** (corrected: the degree must be integral).  Module
`Weak/Foundation/StabilityFunction/WeakHNExistence.lean`, namespace
`CategoryTheory.Triangulated`:

```lean
theorem WeakSlopeData.hasHNProperty {A} [Abelian A] (D : WeakSlopeData A)
    (f : K₀Ab A →+ ℤ) (hf : D.degreeHom = (Int.castAddHom ℝ).comp f)
    (hnoeth : ∀ E : A, IsNoetherianObject E)
    (hbdd : ∀ E : A, ∃ μ₀ : ℝ, ∀ B : Subobject E, ¬IsZero (B : A) →
      0 < D.rank (B : A) → D.degree (B : A) / (D.rank (B : A) : ℝ) ≤ μ₀) :
    D.toWeakStabilityFunction.HasHNProperty
```

**Projections.**  `Gieseker.hasHNProperty` becomes one line at
`D := P.weakSlopeData h`, discharging `hf` by `⟨P.degreeHom, rfl⟩`;
`MuHNInput` becomes the two root hypotheses; `IsPure`, `IsMaximalDestabilizing`,
`exists_slopeMax`, `topSlope_le_of_shortExact` and `splice` become root theorems
instantiated at that datum; `HeartTransport.heart_hasHNProperty` stays a consumer.

**Future examples covered.**  μ-slope HN on `Coh` of any Noetherian scheme with an
integral degree; weak `(ω,B)`-slope HN on `Coh^β(X)` where the degree is integral;
HN for quiver representations and finite-dimensional algebras; HN on the heart of a
stability condition on a Kuznetsov component with an integral rank component.

**Verdicts.**
- *Mathematics* — survives.  Every citation verified and each proof in the chain
  read.  **Correction applied — the root as first stated is FALSE.**
  `exists_slopeMax` puts every slope over a common integer denominator and applies
  `Int.exists_greatest_of_bdd`, which needs the **degree** to be ℤ-valued, not only
  the rank; with a real degree the maximum need not be attained (an object with
  infinitely many rank-1 subobjects of degrees `1 − 1/n`).  The root must add the
  integrality hypothesis, which the Coh-X leaf already satisfies.
- *Repository* — survives.  All twelve citations exact; no generic root exists —
  the only other `HasHNProperty` proof is HN transport across a phase tilt, not an
  existence theorem; `MuPositivityData` has exactly the two `WeakSlopeData` fields.
  **Corrections applied:** the same integrality correction; the listed future
  example "weak `(ω,B)`-slope on `Coh^β(X)`" has a real degree and is **not**
  covered as stated; the namespaces are `CategoryTheory.Triangulated.WeakSlopeData`
  and `…WeakStabilityFunctionOn.HasHNProperty`; the kind is missing-root, not
  dimension-specific.
- *Adoption and cost* — survives.  The scheme-freeness confirmed where testable,
  and `Splice.lean` says so itself.  **Corrections applied:** the same integrality
  fix, with the leaf discharging it verbatim; adoption today is thinner than
  claimed — `P.slopeData` is definitionally the same object and `heartWeakSlopeData`
  is its congr-transport, so the real reuse is discharging the `hHN` hypothesis
  threaded through 26 sites in the Mukai lane; about 980 of the 1395 lines under
  `Stability/Gieseker/HarderNarasimhan/` relocate, with `SlopeBoundedness.lean`
  staying geometric; no review-payload cutover.

#### surf-02 — The surface HRR assembly is a hand-restated `d = 2` copy

**Kind** duplicate-parent · **Impact** high · **Confidence** 0.95

**Declarations.**
`Surface.GeometricData` (`RiemannRoch/Surface/NumericalVariety.lean:71`),
`SatisfiesSheafHRR` (`:83`), `riemannRochHom` (`:106`), `hirzebruch_riemannRoch`
(`:147`), `toNumericalVariety` (`:165`), `toIsK3` (`:236`);
`Assembly.sheaf_hirzebruch_riemannRoch` (`RiemannRoch/Surface/Assembly.lean:124`),
`toNumericalVariety` (`:189`);
`HigherDimension.sheaf_hirzebruch_riemannRoch` (`RiemannRoch/HigherDimension/Hirzebruch.lean:181`),
`riemannRochHom` (`:209`), `hirzebruch_riemannRoch` (`:251`),
`toNumericalVariety` (`:271`).

**Parent structure.**  One assembly: from a pairing context, reconstruction data,
a reconstruction system, and a graded Todd family, build `riemannRochHom` and the
`NumericalVarietyData`, and descend HRR through `K₀Ab`.  The surface file is that
with `Finset.range 3`; the `HigherDimension` file is that with `Finset.range (d+1)`
and a fixed reconstructed Todd family.  The two files do not import each other and
declare the same eleven names with identical bodies;
`NumericalVariety.lean:59` records that `ReconstructionSystem` was already
de-duplicated in exactly this way.

**Proposed root.**  `AlgebraicGeometry/RiemannRoch/Assembly.lean`, namespace
`AlgebraicGeometry.RiemannRoch`, beside the existing `Reconstruction.lean`:
`GeometricData` (Todd family as data), `SatisfiesSheafHRR`, `toNumericalVariety`,
`toNumericalVariety_satisfiesHRR`, and the four `*_class` lemmas.

**Projections.**  `Surface.GeometricData` becomes the root at `d = 2`;
`HigherDimension.toNumericalVariety` becomes
`(reconstructed RO).toNumericalVariety`, with `toNumericalVariety_eq := rfl`
(both sides are the same reducible structure literal);
`Assembly.toGeometricData` stays a `def` and is unchanged, since it already
routes through `Surface.GeometricData`; `Assembly.sheaf_hirzebruch_riemannRoch`
stays a second `SatisfiesSheafHRR` witness with a genuinely different proof.

**Future examples covered.**  A geometric quintic threefold and `ℙ³`
`NumericalVarietyData 3`; a geometric cubic fourfold `NumericalVarietyData 4` and
its Mukai-lattice input for `Ku(X)`; any future geometric Todd construction.

**Verdicts.**
- *Mathematics* — survives.  Both files read side by side; identical field for
  field except the Todd family; the `1 ≤ d ≤ 4` bound lives only on the
  reconstructed witness, as claimed.  **Corrections applied:** `Assembly.lean:124`
  and `:189` are not independent copies — `Assembly` already consumes
  `Surface.GeometricData` — so the duplication is exactly the two files; the root's
  `SatisfiesSheafHRR` must keep `Finset.range (d+1)` on both factors.
- *Repository* — survives.  All twelve citations real and the duplication literal,
  including the four `*_class` lemmas with identical `change`/`exact` proofs; no
  parent exists.  **Correction applied:** the finding under-counts the siblings —
  `AlgebraicGeometry.Variety.NumericalData` (`Variety/Numerical.lean:58`) is a
  third child with the same field list and the same projection names, so the parent
  must have three children and the Todd family is what separates them.
- *Adoption and cost* — survives.  The two files declare the same twelve
  declarations with token-identical bodies; three leaves reach the root, and the
  `HigherDimension` projection is genuinely `rfl`.  The repository has already run
  this exact de-duplication one layer down and recorded it
  (`RiemannRoch/Reconstruction.lean:22-30`).  Cost is 3 files plus 2 umbrella lines
  plus one audit slice; `check_single_instantiation.py` does not apply.
  **Correction applied:** the `toIsK3` bullet is premature and is only true after
  surf-08 lands.

#### surf-03 — `IsK3Surface` and `IsEnriquesSurface` are siblings of a missing parent

**Kind** missing-root · **Impact** high (adoption lens rates medium) ·
**Confidence** 0.88

**Declarations.**
`SmoothProperVariety.IsK3Surface` (`Surface/K3.lean:130`),
`antiCanonicalClass_eq_one` (`:156`), `canonicalClass_eq_one_iff` (`:108`);
`IsEnriquesSurface` (`Surface/Enriques/Basic.lean:106`),
`antiCanonicalClass_eq_canonicalClass` (`:166`), `not_isK3Surface` (`:176`);
`CanonicalSheafData` (`Duality/Canonical/Basic.lean:48`).

**Parent structure.**  Both classes carry `{projective, a torsion equation on
C.canonicalClass, h1_vanishing}` over `CanonicalSheafData k X 2`.  The parent is
`κ^m = 1` plus `H^i(X,O_X) = 0` for `0 < i < n`: K3 is `(n,m) = (2,1)`, Enriques
`(2,2)` plus `κ ≠ 1`, and the strict Calabi–Yau `n`-folds the target tree wants are
`m = 1`.  `canonicalClass_eq_one_iff` is already stated for arbitrary `n`, with the
docstring "nothing about surfaces enters" — the layer is demonstrably n-agnostic.

**Proposed root** (corrected: split the vanishing clause out, and place it with
the carrier).  Module `Duality/Canonical/TorsionCanonical.lean`, namespace
`AlgebraicGeometry.SmoothProperVariety`:
`IsTorsionCanonicalVariety k X C m` carrying only `C.canonicalClass ^ m = 1`,
with projectivity and the middle-degree vanishing as separate mixins — because
abelian surfaces have `κ = 1` with `h¹(O) = 2` and are already a third sibling on
the numerical side.

**Projections.**  `IsK3Surface` and `IsEnriquesSurface` `extends` the parent at
`m = 1` and `m = 2`; K3's `canonicalClass_eq_one` becomes a one-line theorem
(`pow_one` is not defeq in a monoid) and Enriques's `canonicalClass_sq_eq_one`
matches on the nose; `antiCanonicalClass_eq_one` and
`antiCanonicalClass_eq_canonicalClass` become one theorem
`κ⁻¹ = κ^(m−1)` under `1 ≤ m`; `not_isK3Surface` stays the leaf comparison.

**Future examples covered.**  Quintic and other strict CY threefolds; the
cubic-fourfold `Ku(X)` route, which needs the K3 field list only through this
parent; abelian surfaces and bielliptic surfaces as further torsion children once
the vanishing clause is a separate mixin.

**Verdicts.**
- *Mathematics* — survives.  Field lists verified literally; the `(n,m)` reading
  checked at each leaf; the only Enriques consumer that touches the class beyond an
  instance parameter uses `h1_vanishing` alone.  **Correction applied:**
  `antiCanonicalClass_eq_pow` needs `1 ≤ m` — at `m = 0` the hypothesis is vacuous
  for every `κ` while the conclusion asserts `κ⁻¹ = 1`.
- *Repository* — survives.  Both classes verified; `CanonicalSheafData` is
  n-parametric; no geometric strict-CY class exists anywhere; the class passes
  `proposition-classes.md` rules 1 and 2.  **Corrections applied:** placement is
  `Duality/Canonical/`, not `Variety/`, since the whole signature is
  `(C : CanonicalSheafData k X n)`; `middle_vanishing` must not sit in a class named
  for the torsion of the canonical class.
- *Adoption and cost* — survives at medium.  Two leaves reachable by `extends`,
  and consumer cost is near zero because Lean resolves inherited parent fields, so
  the 3 K3-side and 10 Enriques-side files keep working.  **Corrections applied:**
  the `pow_one` non-defeq; the vanishing/projectivity split; and the honest
  observation that the `n` index has **no** inhabitant other than `2` today — what
  the two leaves exercise is the `m` index, so report it that way rather than as an
  n-fold root with no witness.

#### sites-01 — Leray-acyclic cover defined twice, on sites and on spaces

**Kind** duplicate-parent · **Impact** high (adoption lens rates medium) ·
**Confidence** 0.92

**Declarations.**
`Sheaf.IsCechAcyclicFor` (`Sites/SheafCohomology/Cech/Comparison.lean:486`),
`IsCechAcyclicCover` (`:576`);
`Sheaf.IntersectionAcyclic` (`Topology/Sheaves/Cech/Boundedness.lean:54`),
`HPrime_subsingleton_opensUnion_of_intersectionAcyclic` (`:68`);
`Scheme.modules_intersectionAcyclic_of_forall_isAffineOpen`
(`AlgebraicGeometry/Cohomology/Finiteness/Boundedness.lean:209`);
`polynomialVariable_isCechAcyclicFor_of_isQuasicoherent`
(`Finiteness/ProjectiveSpace.lean:71`);
`isCechAcyclicCover_cechComputesDerivedCohomology`
(`Topology/Sheaves/Cech/GlobalComparison.lean:859`).

**Parent structure.**  "`F` has no positive derived cohomology on any nonempty
finite intersection of members of `U`".  The tuple form quantifies over
`Fin (n+1) → ι`; the list form recurses over sublists, and the enumeration was
checked by hand to give exactly the same set of sub-infima.  Both sides use the
same `Sheaf.H'`, so there is no normalization mismatch.  The Leray comparison
consumes the tuple form; the Mayer–Vietoris bound consumes the list form; the
geometric lane proves each separately from one fact.

**Proposed root.**  Keep `IsCechAcyclicFor` as the root; add the bridge
`intersectionAcyclic_of_isCechAcyclicFor` in `Topology/Sheaves/Cech/Boundedness.lean`,
and restate the Mayer–Vietoris bound on the root.

**Projections.**  The list form becomes a bridge theorem rather than an `abbrev`
(it is an inductive that `Boundedness.lean:68` inducts over, so the bound must be
re-run on `Fin`-tuples); the two geometric suppliers stay two suppliers of one
predicate.

**Future examples covered.**  Leray and Mayer–Vietoris bounds on any site (étale,
fppf); Čech-to-derived comparison and cohomological-dimension bounds for schemes
over a base; affine-cover acyclicity supplied once and consumed by both lanes.

**Verdicts.**
- *Mathematics* — survives.  Both definitions verified; the enumeration checked by
  hand on a three-element example; both sides confirmed to use the same cohomology
  functor.  **Corrections applied:** the bridge is
  `∏ᶜ (U ∘ x) = (Finset.univ.image x).inf U`, since the list form enumerates infima
  of *sets* while the tuple form quantifies over tuples with repetition — the
  existing inline proof supplies only the first half; the proposed unified affine
  supplier **strengthens** the `Proj` leaf's hypotheses, which today needs no
  separatedness.
- *Repository* — survives.  All seven citations exact; the two predicates really
  are one; both `HasExt` witnesses are handled explicitly on both sides, so the
  bridge has somewhere to put the universe parameter; no layering edge is crossed.
  **Correction applied:** the kind is existing-root-unused — the root exists and is
  already consumed by `GlobalComparison.lean:859`; the deliverable is the bridge
  plus the restated bound, and the claim that both geometric suppliers become one
  theorem is over-claimed for the reason above.
- *Adoption and cost* — survives at medium.  **Corrections applied:** the
  surveyor's `abbrev` is **ill-typed** — `Fin L.length` is `Type` while `ι : Type a`
  is `Type u` on `Opens X` (reproduced: "Application type mismatch"); the `ULift`
  form elaborates.  Keep `IntersectionAcyclic` as an inductive induction device and
  ship one bridge theorem; the `Boundedness.lean:68` proof runs under
  `maxHeartbeats 1600000` and an abbrev would force it to be rewritten on `ULift`
  tuples, and `scripts/StabilityConditionAudit/Cech.lean:63-67` prints its
  recursors.

#### sites-02 — Čech-nerve localization to one member, written three times

**Kind** missing-root · **Impact** high · **Confidence** 0.9

**Declarations.**
`cechComplex_exactAt_succ_of_isTerminal` (`Sites/SheafCohomology/Cech/Contractible.lean:31`);
`freeCechStalkData` (`Topology/Sheaves/Cech/InjectiveAcyclic.lean:193`);
`affineCechLocalizationData` (`AlgebraicGeometry/Cohomology/Cech/Affine.lean:358`);
the duplicated `Set.Iic` finite-product instances
(`InjectiveAcyclic.lean:38` vs `Affine.lean:192`) and slice inclusions
(`InjectiveAcyclic.lean:165` vs `Affine.lean:292`).

**Parent structure.**  For a family `U` and a member `j`, the restricted family
lives in the slice over `U j`, where `U j` is terminal and the diagonal supplies
the extra-degeneracy datum, so Mathlib's `extraDegeneracyCech` applies; pushing
along the slice-forgetful functor and comparing to the global nerve gives
positive-degree exactness for any `G`.  The two leaf blocks are byte-identical up
to a bound-variable name, including the `zToV` naturality proof.

**Proposed root.**  `CategoryTheory/Limits/FormalCoproducts/Localize.lean`
(Tier-1: the Mathlib site of `FormalCoproduct`, `.cech`, `extraDegeneracyCech`),
namespace `CategoryTheory.Limits.FormalCoproduct`.  State it at the level of the
augmented simplicial object with its extra degeneracy and the comparison map,
**before** any whiskering, so both variances follow.  Keep `Set.Iic` rather than
`Over`, and put the three finite-product instances in
`Topology/Category/TopCat/Opens/Limits.lean`, which exists for exactly this
purpose.

**Projections.**  `Contractible.lean:31` stays as it is — it assumes a map from a
terminal object of `C` itself, with no slice and no `⊓`.  The two private data
become instantiations of the root at `C := Opens X` and
`C := Opens (PrimeSpectrum R)`, whiskered with their own `G`.  The duplicated
local instances collapse to one.

**Future examples covered.**  Čech acyclicity on the étale or fppf site;
affine-cover acyclicity for quasi-coherent modules on any ringed site; any future
Leray-type vanishing proved by contracting the nerve.

**Verdicts.**
- *Mathematics* — survives.  The two blocks read line by line and found identical
  in the same order with the same local names; the opposite-variance concern is
  real and correctly resolved by cutting before the whiskering.  **Correction
  applied:** the root signature is insufficient — binary products in `Over B` are
  pullbacks in `C`, so the root needs `[HasPullbacks C]`, not `[HasFiniteProducts C]`;
  both leaves satisfy this.  Extract `FormalCoproduct.mapFunctor` first and
  separately; it is duplicated privately in both files and is independently
  actionable.
- *Repository* — survives.  The duplication is near-verbatim, including the same
  `zToV` and the same two-case naturality proof; the construction is not in
  Mathlib.  **Corrections applied:** the module path must be
  `CategoryTheory/Limits/FormalCoproducts/`, per Tier 1 and the finding's own
  namespace; the root must also absorb the private `mapFunctor` duplicate, which
  Mathlib lacks; keep `Set.Iic` rather than `Over`, and put the instances in the
  file that already owns Opens-lattice limits, whose docstring records that it
  "replaces two independent workarounds for the same gap";
  `Contractible.lean:31` should stay as it is.
- *Adoption and cost* — survives.  Both blocks read and confirmed
  character-for-character in the `zToV` body; two leaves, both private, so no
  public-name cutover and no `RestateHistoricalNames` entry; the precedent for the
  cheap fix exists in-tree.  **Corrections applied:** the largest verbatim
  duplicate is `FormalCoproduct.mapFunctor` (byte-identical private defs, absent
  from Mathlib) and should be the first thing the new file owns; do not root on
  `Over (U j)`, since both leaves use `Set.Iic`.

#### docs-01 — The Canonical spine has no node for charges, walls, or stability

**Kind** missing-root · **Impact** high · **Confidence** 0.95

**Declarations.**
`abstraction-tree.md:45` (the `Category` root, with no `StabilityCondition` child),
`:236` (numerical K-theory, with no Stability/Mukai/Examples children),
`:247` ("the one stability-consuming child");
`layers.md:140` (the StabilityCondition subtree, listing no `Mukai`, no
`Chambers`, and no children of `Walls`), `:67`;
against `Wall.ChargeFamily` (`Walls/ChargeFamily.lean:49`), `stChargeFamily`
(`Walls/Numerical/ChargeFamily.lean:59`), `Threefold.chargeFamily`
(`Walls/Threefold/Basic.lean:174`), `ChernCharacter.centralCharge`
(`Walls/Divisorial/Charge.lean:333`), `ChargeCoordinates.centralCharge`
(`Coordinates.lean:108`), `MukaiChargeData` (`Mukai/Charge.lean:101`),
`stabWall` (`Chambers/Basic.lean:62`), `StabChamber` (`:187`),
`numericalCharge` (`Numerical/GrothendieckGroup/CentralCharge.lean:63`), and the
two `Numerical/` consumers importing the Walls tree
(`ThreefoldWallTransport.lean:6`, `SurfaceChargeNumerical.lean:5`).

**Parent structure.**  A documented tree with no charge node is how the surface
and threefold duplication went unnoticed.  The code already has a five-level
chain — `PeriodDomain.centralCharge → Mukai.expCharge → ChernCharacter.centralCharge
→ ChargeCoordinates / stChargeFamily / Threefold.chargeFamily / MukaiChargeData /
numericalCharge` — and the spine records none of it.

**Proposed amendment.**  The §2.4 text block, plus the corrected
stability-consuming line.

**Projections.**  Each edge of the chain is an existing definitional identity or
proved theorem, listed in §2.5.

**Future examples covered.**  Any new surface, threefold or fourfold charge is
placed by reading one tree; Kuznetsov-component charges get a named planned node
instead of a sibling root; the stability-consuming AG subtrees stop being
described as nonexistent.

**Verdicts.**
- *Mathematics* — survives.  Every docs fact verified independently;
  `StabilityCondition/` is 296 files with `Chambers/`, `Mukai/` and five `Walls/`
  children; 23 files import `Walls.Divisorial`; "central charge" appears once in
  all of `docs/`.  The five-level chain re-derived by hand, including confirming
  that `expCharge` *is* Bridgeland's pairing.  **Correction applied:** the prose
  claim "every concrete charge is `⟪x,−⟫ + i⟪y,−⟫` for a positive pair" is false
  for the threefold charge, whose associated form is the BMT quantity and whose
  positivity is false in general; the amended spine must say so beside the
  exponential node, or it recreates the disease at `n = 3`.
- *Repository* — survives, with the strongest form of the evidence: `grep` for
  `Wall|Bridgeland|StabilityCondition|PeriodDomain|Chamber` over
  `abstraction-tree.md` returns **zero** hits, and `charge` appears nowhere in
  `abstraction-tree.md` or `layers.md`.  All ten code citations resolve.
  **Corrections applied:** `Spherical` is a sibling of `ChargeFamily`, not a child
  (zero `ChargeFamily` hits under `Walls/Spherical/`); the stability-consuming
  children are **four**, since `check_layering.py:99-108` includes
  `AlgebraicGeometry.Stability`; `Wall.ChargeFamily` is at `:49`, not `:47`.
- *Adoption and cost* — survives; the cheapest finding in the lane (two markdown
  files, no code, no audit churn, no namespace cutover), and every projection it
  records is an existing compiled theorem.  **Corrections applied:** strip the
  `[PROPOSED]` and `[PLANNED — no code]` blocks out of the spine —
  `abstraction-tree.md:344-346` forbids a node for code that does not exist, and
  their home is `cutover-ledger.md`'s "Confirmed next lanes"; the count is 296
  files, and 24 modules mention `Walls.Divisorial`; `ChargeFamily.pullback` is at
  `:72`; add that the Mukai charge lane is pinned at `NumericalVarietyData 2`.

#### docs-02 — The threefold and surface charges are one truncated formula

**Kind** dimension-specific-should-be-n-fold · **Impact** high · **Confidence** 0.92

**Declarations.**
`cutover-ledger.md:124` ("a future threefold or BMT charge family"),
`placement.md:106` (naming Divisorial's siblings without the threefold);
`Wall.Threefold.NumClass` (`Walls/Threefold/Basic.lean:64`), `reZ` (`:121`),
`imZ` (`:131`), `charge` (`:148`), `betaTwist` (`:89`);
`Wall.NumClass` (`Walls/Numerical/Basic.lean:104`), `reZ` (`:124`), `imZ` (`:128`),
`stCharge` (`Numerical/ChargeFamily.lean:28`);
`ChargeCoordinates.twistByScalar` (`Divisorial/Coordinates.lean:63`);
`Surface.toNumClassHom` (`WallTransport.lean:145`),
`Threefold.toNumClassHom` (`ThreefoldWallTransport.lean:175`);
`twist` (`Stability/TwistedChern.lean:104`).

**Parent structure.**  Identical to charges-01 and walls-01, found a third time
from the documentation side.  This entry is the documentation half: the ledger
records the threefold family as future work, `placement.md` does not know it
exists, and the fourfold examples have no charge because nothing
dimension-general exists to instantiate.

**Proposed amendment.**  The §2.4 block; plus amending `cutover-ledger.md:115-126`,
whose predicted relationship did not happen — `Walls/Threefold` consumes
`ChargeFamily`, not the divisorial layer the ledger says a future threefold family
would consume.

**Projections.**  As in charges-01/walls-01, with the one addition that the root
must also own `discr` (see the verdict).

**Future examples covered.**  Fourfold charge on `ℙ⁴` and the sextic; the quadric
threefold and Picard-rank-one Fano threefolds; any Picard-rank-one n-fold tilt
charge `Z_{α,β}`; hyperkähler fourfolds once a model exists.

**Verdicts.**
- *Mathematics* — survives.  Both expansions verified by hand, term for term,
  including the rank-slot weighting, which is imposed by the transports
  (`WallTransport.lean:112-118`, `ThreefoldWallTransport.lean:153-161`).
  **Corrections applied:** the twist law has a **sign error** — `betaTwist b` is
  `ch ↦ e^{−bH}ch`, so `Z_w(twist_b v) = Z_{w+b}(v)`, matching the repository's own
  `reZ_eq_betaTwist`, not `w − b`; and the root is under-scoped, since
  `Δ = d₁² − 2d₀d₂` is declared three separate times and is twist-invariant by the
  same one-line identity in each, so the root must also own `discr` with one
  invariance lemma.
- *Repository* — survives.  The unification re-derived independently at both `n`;
  the threefold file's own docstring derives its polynomials from the same
  exponential and calls itself "the threefold counterpart"; `TwistedChern.twist` is
  already dimension-general and geometry-free; the fourfold examples have zero
  `charge` hits; no such root exists in `DerivedAlgGeo` or Mathlib.  **Correction
  applied:** the expected gate objection does **not** land — the root is `def`s and
  an `abbrev`, which `EnumInhabitants` never sees, so no baseline entry is needed;
  and the ledger entry needs amending as well as the spine.
- *Adoption and cost* — survives, confirmed by compilation: both leaf comparisons
  proved with `reZ`/`imZ` left untouched, so this is a proved comparison, not a
  redefinition, and the ledger's own ruling is respected.  The geometric side needs
  no new carrier, and the `k = 0` slot reconciles with the existing weighted rank
  slot through `chComp_zero` plus `degree_algebraMap_mul`.  **Correction applied:**
  one real cost is unpriced — the n-general twist law needs the truncated-exponential
  convolution identity, which lives under `AlgebraicGeometry/` and is therefore
  blocked by the geometry firewall, so land the charge half first and carry the
  twist unification as a second lane.

### 3.B Medium impact

#### charges-02 — The compressed β-twist, written by hand at n = 2 and n = 3

**Kind** dimension-specific-should-be-n-fold · **Impact** medium · **Confidence** 0.95

**Declarations.**  `ChargeCoordinates.twistByScalar` (`Walls/Divisorial/Coordinates.lean:63`);
`Threefold.betaTwist` (`Walls/Threefold/Basic.lean:89`) and `betaTwist_betaTwist`
(`:113`); `ChernCharacter.twist` (`Walls/Divisorial/Charge.lean:121`);
`twistCoeff`/`twist`/`twist_add_beta` (`Numerical/Stability/TwistedChern.lean:70`,
`:104`, `:110`) — the existing n-fold root on the ℚ-ring side;
`betaTwist_toNumClass` (`ThreefoldWallTransport.lean:194`).

**Parent equation.**  On compressed degrees the twist is the convolution
`(twist β d) k = ∑_{j ≤ k} (-β)^j/j! · d (k-j)`.  `twistByScalar` is that at
`m = 2` with the `∫H²` rank weight; `betaTwist` is it at `m = 3` with the
coefficients `1, −β, β²/2, −β³/6` typed by hand and `betaTwist_betaTwist`
re-proving the group law by `ring`.  The real-side n-fold twist does not exist, so
each dimension transcribes the coefficients and re-proves the law; a fourfold
would transcribe five.

**Proposed root.**  `Walls/Polarised/Basic.lean`, namespace `…Wall.Polarised`:
`twist (m : ℕ) (β : ℝ) : NumClass m →+ NumClass m`, `twist_add`, `charge_twist`,
`toNumClass_twist`.

**Projections.**  `twistByScalar b` and `betaTwist β` become `twist 2 b` and
`twist 3 β` — both verified in Lean by `fin_cases; simp; ring`;
`betaTwist_betaTwist` becomes `twist_add`; `reZ_eq_betaTwist`/`imZ_eq_betaTwist`
become `charge_twist`; `ChernCharacter.twist` stays a sibling (it keeps
`c₁ ∈ N¹(X)_ℝ`) and reaches the root only on the rank-one slice;
`betaTwist_toNumClass` becomes the n-fold `toNumClass_twist`.

**Future examples covered.**  The fourfold β-twist with its five coefficients and
group law for free; any `(α,β)`-wall statement in dimension ≠ 2, 3.

**Verdicts.**
- *Mathematics* — survives.  Both leaves checked coordinate by coordinate against
  the convolution; the companion identity `reZ_eq_betaTwist` is the `w`-shifted
  form of `charge_twist` and holds for every truncation; no sign or normalization
  issue.  **Correction applied:** index by truncation degree `m`, per charges-01.
- *Repository* — survives.  All citations verified, including the two hand-written
  coefficient bodies; `grep` finds no real-side n-fold twist under `Walls/`, and
  the ℚ-ring `twist` cannot serve the wall lane directly because `Walls/` is under
  `CategoryTheory/` and may not import `AlgebraicGeometry/` (geometry firewall).
- *Adoption and cost* — survives.  Both leaves reach by proved comparison
  (`scratchpad/NFoldTwistVerify.lean`, exit 0); the content is real, since
  `betaTwist_betaTwist` and `reZ_eq_betaTwist`/`imZ_eq_betaTwist` are n-specific
  re-proofs of statements true for every `m`.  **Correction applied:** "one proof,
  from `twistCoeff_add`" does not transfer — `twistCoeff` is ℚ-valued while the
  root's `β` is real, so budget a fresh `ℝ` proof (see N6).

#### charges-03 — Kuznetsov-component charges have no node

**Kind** existing-root-unused · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.85

**Declarations.**  `NumLattice` (`LinearAlgebra/Lattice/Numerical/RankTwo.lean:13`,
a disclaimer) and `ResidualCategory` (`Surface/Enriques/Residual.lean:20`, another)
— the repository's entire current Kuznetsov surface area;
`ChargeFamily.pullback` (`Walls/ChargeFamily.lean:72`), `pullback_wall` (`:338`);
`K₀.map` (`Triangulated/GrothendieckGroup/Functorial.lean:38`);
`PeriodDomain.centralCharge` (`QuadraticForm/CentralCharge.lean:61`) and
`neg_of_centralCharge_eq_zero` (`:109`);
`MukaiChargeData` (`Mukai/Charge.lean:101`) — the shape a future Ku(X) file would
be tempted to copy;
`StabilityCondition.WithClassMap` (`Foundation/StabilityCondition.lean:41`).

**Parent structure.**  Both required shapes are existing roots.  (a) Tilt
restriction: the Ku-charge is `Z ∘ K₀.map i`, i.e. `ChargeFamily.pullback`, and its
walls are `pullback_wall`.  (b) Mukai-lattice pairing: `H̃(Ku(X),ℤ)` is an even
lattice of signature `(2,·)` containing `A₂`, and the charge is
`PeriodDomain.centralCharge Q x y v` verbatim, with the support property already
lattice-generic.  `Mukai.expCharge` is the special case where the plane is
exponential; the Ku(X) case is the same root at a different lattice, not a child of
`expCharge`.

**Proposed root.**  Documentation only, for now: a "noncommutative charges" node
in `abstraction-tree.md` stating that a Ku(X) charge is
`ChargeFamily.pullback (cl.comp (K₀.map i))` and a Ku(X) lattice charge is
`PeriodDomain.centralCharge`, and that a `KuznetsovChargeData` with its own
`charge`/`map_zero`/`additive` fields must not be introduced.

**Projections.**  Cubic-threefold Ku(X): the `(n,m) = (3,2)` tilt family,
post-composed with the `−i` rotation (`phaseTiltRotation (1/2)`,
`Weak/Tilting/Semistable/TiltGeometry.lean:43`), then `.pullback (K₀.map i)`, with
the stability-level datum `WithClassMap.preimage i h`
(`Phase/Transfer/PreStability.lean:94`) supplying the induced heart.
Cubic-fourfold Ku(X): `PeriodDomain.centralCharge` at the Mukai form of `H̃(Ku(X))`
with `neg_of_centralCharge_eq_zero` as the support property.

**Future examples covered.**  Ku(X) of cubic threefolds and fourfolds;
Gushel–Mukai and Enriques residual categories once `ResidualCategory` gets a class
map; any admissible-subcategory stability lane.

**Verdicts.**
- *Mathematics* — survives.  Both shapes confirmed to reach existing roots, and
  the false-unification warning (`H̃(Ku(X))` is not an `ℝ × V × ℝ` extension, so it
  must not go through `expRe`/`expIm`) is correct.  **Correction applied — the
  threefold projection restricts the wrong ambient charge:** Bayer–Lahoz–Macrì–Stellari
  induce stability on `Ku(cubic threefold)` from the **tilt** charge rotated by
  `1/i = −i`, not from the Bayer–Macrì–Toda charge with `ch₃`; the repository holds
  the tilt charge only as its slope (`Threefold.nu`, `BMT.nu`), and the rotation
  exists as `phaseTiltRotation (1/2)`.  Walls are unchanged by the rotation.
- *Repository* — survives.  All citations verified and the Kuznetsov grep confirmed
  to return only the two disclaimers.  **Corrections applied:** the finding
  under-reports the existing roots — the stability-level restriction it calls "not
  automatic" already has a root, `WithClassMap.preimage` with
  `Slicing.PreimageData` as the induced-heart witness; and the proposed `abbrev`
  must **not** go into `Walls/ChargeFamily.lean`, which imports only
  `Mathlib.Data.Complex.Basic` and `Mathlib.Tactic`, so importing
  `GrothendieckGroup/Functorial` there violates the weakest-vocabulary tie-breaker.
- *Adoption and cost* — **refuted** (single dissent).  Zero existing leaves: no
  Kuznetsov charge, class map, or admissible inclusion exists anywhere, so
  `ChargeFamily.restrict` would be a zero-adoption thin alias of `pullback`, which
  is the shape `check_single_instantiation.py`'s docstring names as the disease.
  The mathematical guidance is correct but is a documentation obligation, which is
  why the proposed root above is docs-only.

#### charges-04 — The spherical (℧, δ) pairing is Re/Im of `Mukai.expCharge`

**Kind** same-equation-two-names · **Impact** medium · **Confidence** 0.96

**Declarations.**  `Spherical.pairingRe` (`Walls/Spherical/Basic.lean:174`),
`pairingIm` (`:181`), `chartRe`/`chartIm` (`:153`, `:158`), `wall` (`:301`),
`pairingIm_eq_of_symm` (`:199`), `two_mul_rk_mul_pairingRe` (`:214`);
`mem_periodDomainWall_iff_mem_wall` (`Spherical/WallComparison.lean:94`);
`DivisorSpace.expPairMap` (`Divisorial/Region.lean:74`);
`Mukai.expCharge` (`Lattice/Mukai/CentralCharge.lean:36`) and
`mem_wall_iff_expCharge_eq_zero` (`:108`);
`Mukai.im_expCharge` / `two_mul_re_expCharge` (`Lattice/Mukai/ChargePositivity.lean:110`, `:165`).

**Parent equation.**  `pairingRe q β ω δ = (Mukai.expCharge q β ω δ).re` and
likewise for `Im`, by `polar_realForm` under symmetry of `q`.  `grep` shows
neither `expCharge` nor `centralCharge` appears anywhere under `Walls/Spherical/`,
although `chartRe`/`chartIm` are already abbrevs of `Mukai.expRe`/`expIm`.  The
consequence is that `Spherical/Basic.lean:44-46` describes its wall as "a different
structure" from the tilt walls, when both are conditions on one charge, and the
`ChargePositivity` lane proves the same Re/Im identities that
`Spherical/Basic.lean:199,214` prove again on the other name.

**Proposed root.**  Existing: `Mukai.expCharge`.  Add
`pairingRe_eq_re_expCharge`, `pairingIm_eq_im_expCharge` and
`mem_wall_iff_expCharge` in a new `Walls/Spherical/Charge.lean`, so that
`Basic.lean`'s audit prose is amended rather than contradicted.

**Projections.**  The two pairing functions become `.re`/`.im` of the charge —
compiled; `Spherical.wall` becomes the charge-language statement
`Im = 0 ∧ Re ≤ 0`; `pairingIm_eq_of_symm` and `two_mul_rk_mul_pairingRe` reuse
`Mukai.im_expCharge_eq_apply_sub_smul` and `two_mul_re_expCharge`;
`mem_periodDomainWall_iff_mem_wall` is restated as the containment between
`expCharge δ = 0` and `expCharge δ ∈ ℝ_{≤0}`.

**Future examples covered.**  Spherical walls for any Mukai-type lattice (abelian
surfaces, Enriques via its K3 cover) stated once in charge language; Bridgeland's
finiteness read as "finitely many δ with `Z(δ)` real non-positive on a region",
reusable by the fourfold Ku(X) lane.

**Verdicts.**
- *Mathematics* — survives, confirmed by compilation: the two identities and the
  wall restatement all close by `rw [expCharge, centralCharge_re/im, polar_realForm]; rfl`.
  Signs checked term for term against `expCharge_apply`.  The honest distinction
  (half-line vs vanishing) is preserved and made clearer.
- *Repository* — survives.  All citations verified; the `Walls/Spherical/` grep is
  empty and `Basic.lean`'s imports stop at `Mukai/RealForm`; the file's own
  docstrings record two earlier de-duplications of exactly this kind and give no
  reason for stopping short of the charge; the import direction is permitted.
- *Adoption and cost* — survives.  Recompiled independently; the duplicate proofs
  are real (modulo `hq` and `selfPairing = 2·realForm`); adding the import creates
  no cycle; 3 theorems plus 1 import, 1 audit slice, no renames.  **Correction
  applied:** tighten the claim — the shared root is the charge `Mukai.expCharge`,
  **not** `Wall.ChargeFamily`, so `Spherical.wall` must not be re-rooted at
  `ChargeFamily.wall`; prefer a new file over editing `Basic.lean`.

#### numerical-nfold-05 — Four truncated power-series operations, hand-expanded

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.65

**Declarations.**  `sqrtComp` (`Numerical/Mukai/SqrtTodd.lean:70`) with
`sqrtComp_eq_zero_of_four_lt` (`:88`); `twistCoeff` (`Stability/TwistedChern.lean:70`);
`expComponent` (`IntersectionTheory/ChernCharacter/Basic.lean:489`);
`ChernClassData.chernCharacterComponent` (`Numerical/Core/CharacteristicClasses.lean:64`)
and `toddComponent` (`:109`);
`IntersectionTheory.ChernCharacter.chernCharacterComponent` (`Basic.lean:280`);
`toChernClassData` (`:637`);
`reconstructedToddComponent` (`RiemannRoch/HigherDimension/Hirzebruch.lean:132`).

**Parent structure.**  All are coefficients of universal power series —
`√(1+x)`, `e^x`, `x/(1−e^{−x})`, the Chern character via Newton, and the
multiplicative inverse — evaluated on a graded family.  Mathlib at the pin has the
carrier and the operations.  The `| _ + 5 => 0` ceilings are the truncation.

**Proposed root** (corrected placement, split in two).  The universal series
belong at `RingTheory/PowerSeries/<Name>.lean` (Tier 1: Mathlib's definition site,
and they must not import `AlgebraicGeometry`); only `evalGraded`, which mentions
`NumericalRingData`, belongs at `Numerical/Core/UniversalSeries.lean`.

**Projections.**  `sqrtComp` becomes `evalGraded sqrtOneAdd` and
`sqrtComp_eq_zero_of_four_lt` disappears; `twistCoeff` and `expComponent` become
`coeff (exp)` rescaled, with `twist_add_beta` becoming `exp_mul_exp_eq_exp_add`;
`ChernClassData.toddComponent` stays hand-written (the splitting principle is not
in Mathlib); `toChernClassData` keeps its definition and gains the round-trip
theorem, which is provable **today** by `ring` with no power-series carrier and
should be split out and landed independently; the `hd4 : d ≤ 4` on
`sheaf_hirzebruch_riemannRoch` drops once the `τ/td` inversion is unbounded.

**Future examples covered.**  Dimensions ≥ 5; `√td` on a fourfold and `td₄`-corrected
charges for cubic fourfolds; any further characteristic class (`Â`, `L`, the
Γ-class) as one more universal series.

**Verdicts.**
- *Mathematics* — survives.  All citations verified; `sqrtComp`'s five entries
  re-expanded and matched; `twistCoeff` and `expComponent` confirmed to be the same
  exponential series under two names; the missing round trip verified to be exactly
  true and provable by `ring`.  **Corrections applied:** the proposed `toddSeries`
  is **wrong as written** — `1 − exp(−X)` has zero constant coefficient and is not
  a unit, so invert `(1−e^{−X})/X` instead; `sqrtOneAdd` needs a scalar rescaling
  spelled properly; split out the `toChernClassData` round trip.
- *Repository* — survives.  Every repository and Mathlib line verified;
  `toChernClassData` is referenced by nothing else, so the round trip asserted in
  its docstring is nowhere proved.  **Corrections applied:** the placement split
  above; `chernCharacterComponent` is at `CharacteristicClasses.lean:64` while
  `toddComponent` is at `:109`; severity stays medium because the
  Chern-class → Todd half needs a splitting principle Mathlib lacks.
- *Adoption and cost* — survives, and the Mathlib side is stronger than the
  surveyor knew: `PowerSeries.binomialSeries` **is** `(1+X)^r`, i.e. `sqrtOneAdd`
  at `r = 1/2` with computable coefficients; `exp_mul_exp_eq_exp_add` is precisely
  the identity `twistCoeff_add` re-proves by hand over ~20 lines; and
  `PowerSeries.subst`/`coeff_subst'` **is** `evalGraded`.  **Corrections applied:**
  keep `ChernClassData.toddComponent` out of the adoption count; state the payoff
  as removing the `i ≤ 4` ceiling on `sqrtComp`, which is what blocks `√td` on a
  fourfold and hence the cubic-fourfold Kuznetsov charge; no gate fires; cost is
  the largest in the lane (~6–8 files).

#### numerical-nfold-06 — The H-degree compression, defined per dimension

**Kind** dimension-specific-should-be-n-fold · **Impact** medium · **Confidence** 0.7

**Declarations.**  `Surface.toNumClass` (`Stability/WallTransport.lean:112`);
`Threefold.toNumClass` (`Stability/ThreefoldWallTransport.lean:146`);
`degH` (`Stability/Slope.lean:116`), already n-general at slot 1;
`degH1Beta`/`degH2Beta`/`deg3Beta` (`Stability/BMT.lean:87`);
`Wall.NumClass` (`Walls/Numerical/Basic.lean:104`),
`Wall.Threefold.NumClass` (`Walls/Threefold/Basic.lean:64`);
`Polarization` (`Stability/Slope.lean:88`), already n-general.

**Parent structure.**  Both transports compute `k ↦ ∫_X H^{n−k}·ch_k(E)`, with
slot 0 equal to `∫Hⁿ · rank E` because `ch₀ = rank`; the twisted BMT degrees are
the same vector applied to `ch^β`.

**Proposed root** (corrected: indexed by `ℕ`, not `Fin`).
`Stability/Slope.lean`, beside `Polarization` and `degH`:

```lean
noncomputable def hDegreesOf (R : NumericalRingData n A) (P : Polarization R)
    (c : ℕ → A) : ℕ → ℚ := fun i => R.degree (c i * P.cls ^ (n - i))
```

with `hDegreesB` in `TwistedChern.lean` (which imports `Slope.lean`, so `chBComp`
is unavailable in the other direction), and a `Fin`-indexed view supplied only
where a fixed-arity Walls carrier is being fed.

**Projections.**  All verified in Lean (`scratchpad/V06.lean`, exit 0):
`degH V P E = hDegreesOf … 1` by **rfl**; `Surface.toNumClass` and
`Threefold.toNumClass` as the `m = 2`, `m = 3` tuples; `degH1Beta` by `rfl` and
`degH2Beta` by `pow_one`.  The slot-0 weighting that both `WallTransport`
docstrings present as a per-dimension discovery falls out of the uniform formula
at `i = 0` — proved, not asserted.

**Future examples covered.**  Fourfold charges for the cubic fourfold and `ℙ⁴`,
which today would need a third `toNumClass`; twisted compressions on surfaces
without a second BMT-style triple; any polarised n-fold wall transport.

**Verdicts.**
- *Mathematics* — survives.  Both transports verified to be the uniform formula,
  including the weighted rank slot via `degree_algebraMap_mul`.  **Correction
  applied:** a `Fin`-indexed signature **breaks** the two `rfl` projections, since
  `((1 : Fin (n+1)) : ℕ)` is `1 % (n+1)` — not `rfl` for symbolic `n`, and false at
  `n = 0`; index by `ℕ`.
- *Repository* — survives at medium.  All seven citations exact and the arithmetic
  checked slot by slot; nothing named `hDegrees` exists.  **Corrections applied:**
  `hDegreesB` cannot live in `Slope.lean` (import direction); five of the seven
  declarations sit outside this lane's scope, so check against the charges/walls
  lanes before ranking — this is the same parent charges-01 and walls-06 found.
- *Adoption and cost* — survives, verified in Lean.  **Correction applied:**
  whether `Wall.NumClass`/`Wall.Threefold.NumClass` become `Fin (n+1) → ℝ` is the
  charges lane's call and must not be bundled into this finding's cost; every leaf
  reaches through the existing ℚ→ℝ cast.  Cost is small: one def plus one
  `AddMonoidHom` in `Slope.lean`, two comparison theorems, one audit file.

#### numerical-nfold-07 — Three hand-built surface intersection rings

**Kind** missing-root · **Impact** medium · **Confidence** 0.7

**Declarations.**  `SurfaceRing` (`Examples/Surface/RankOne.lean:48`);
`SmoothQuadric.Ring` (`Examples/Surface/SmoothQuadric.lean:40`) and `numericalRing`
(`:216`), `numericalRealization` (`:522`);
`BlowUpPlane.Ring` (`Examples/Surface/BlowUpPlane.lean:85`) with its `Mul` instance
(`:109`), `numericalRing` (`:357`), `numericalRealization` (`:597`);
`surfaceRealization` (`Examples/Surface/RankOneRealization.lean:188`);
`Surface.NumericalRealization` (`Stability/DivisorialChargeNumerical.lean:52`);
`Mukai.MukaiLattice` (`LinearAlgebra/Lattice/Mukai/Basic.lean:51`).

**Parent structure.**  The numerical intersection ring of a smooth projective
surface is determined by `(N¹(X)_ℚ, b)`: `A = ℚ ⊕ Λ ⊕ ℚ` with
`(a,v,s)(a',v',s') = (aa', av'+a'v, as'+a's+b(v,v'))`.  `BlowUpPlane.lean:38-48`
**writes that general formula** and then says the dual-number trick "does not
extend"; the quadric realizes the hyperbolic case through nested dual numbers; the
rank-one ring is `Λ = ℚ`.

**Proposed root** (corrected: symmetry is required, and placement splits).
`LinearAlgebra/BilinearForm/LatticeRing.lean` for `LatticeRing Λ b` with its
`CommRing`/`Algebra` instances — which need `b` **symmetric**, since
commutativity of the stated product *is* symmetry of `b` — and
`Examples/Surface/LatticeRing.lean` for `numericalRing`, `realization` and the
three comparison isomorphisms.

**Projections.**  `BlowUpPlane.Ring` reaches it by an `abbrev`/definitional
restructure (verified in Lean); `SmoothQuadric.Ring` and `SurfaceRing` reach it
only by explicitly constructed algebra isomorphisms; the Mukai identity
`⟨v,w⟩ = −degree (dual v * w)` was checked by hand and holds.

**Future examples covered.**  The Enriques rank-ten lattice `U ⊕ E₈(−1)`; K3
surfaces of Picard rank ≥ 2, which the Bridgeland K3 wall theory actually needs;
cubic surfaces and del Pezzos, Hirzebruch surfaces, abelian surfaces with `ρ > 1`;
every `DivisorSpace`/`NumericalRealization` pair produced once from `(Λ, b)`.

**Verdicts.**
- *Mathematics* — survives.  All three identifications verified by computing the
  degree-2 coefficient in each carrier; the `DivisorSpace` requirement (a symmetric
  real form with no definiteness) confirmed, so "one realization for every Λ" is
  sound.  **Corrections applied:** `instance : CommRing (LatticeRing Λ b)` is
  **false** for a general bilinear form — commutativity is exactly symmetry — so
  the carrier must take symmetry as data; associativity needs no further
  hypothesis; `BlowUpPlane.numericalRealization` is at `:597`, not `:357`.
- *Repository* — survives.  Citations exact, and the decisive evidence is the
  repository's own prose at `BlowUpPlane.lean:41-49`; three carriers for one
  construction; no such generic ring exists in the tree or in Mathlib
  (`TrivSqZeroExt` is the square-zero case).  **Corrections applied:** make the
  placement split primary, since a `LatticeRing` under `LinearAlgebra/` may not
  mention `NumericalRingData`; that move puts the structure inside a
  `GENERIC_SUBJECT`, so the change must ship at least two element-producing defs or
  a baseline entry; keep the `SurfaceRing` link an `AlgEquiv`, never a redefinition,
  or numerical-nfold-02's `rfl` chain is lost.
- *Adoption and cost* — survives.  The root was built and compiled
  (`scratchpad/V07.lean`), with `blowUpEquiv` proved.  **Corrections applied:** the
  signature bug above (symmetry); **adoption is one leaf, not three** — the quadric
  and the rank-one ring reach only by explicit algebra isomorphisms, and there is
  **no** `NumericalRingData`-transport-along-a-ring-equivalence lemma anywhere, so
  that transport must be budgeted as part of the change; and the
  `GENERIC_SUBJECTS` exposure must be priced.

#### numerical-nfold-08 — The general "only total codimension n survives" lemma is private in a leaf

**Kind** leaf-copies-root · **Impact** medium · **Confidence** 0.85

**Declarations.**  `degree_sum_mul_sum_eq_antidiagonal`
(`RiemannRoch/HigherDimension/Hirzebruch.lean:150`, `private`, fully general);
`NumericalVarietyData.degree_ch_mul_todd` (`Numerical/RiemannRoch/General.lean:40`,
the root-file version, specialised, identical proof);
`degree_surface_total` (`RiemannRoch/Surface/Assembly.lean:82`, `private`, `n = 2`);
`rankOneDegree_sum_mul_sum` (`Examples/RankOne.lean:219`);
`surfaceDegree_ch_mul_todd` (`Examples/Surface/RankOne.lean:245`);
`chi₂_eq_sum` (`GrothendieckGroup/EulerPairing.lean:104`);
`K3.mukaiIntegral_eq` (`Mukai/Pairing.lean:103`).

**Parent equation.**  `∫(∑ x_i)(∑ y_j) = ∑_{i≤n} ∫ x_i·y_{n−i}`, because every
mixed term of total codimension ≠ n dies under `degree_eq_zero_of_mem`.  The
general statement is `private` in a leaf while the root file states only its
`chComp`/`toddComp` specialisation with the same
`Finset.sum_mul_sum / sum_eq_single (n - i)` proof.  This is the dependency
direction rule inverted.

**Proposed root.**  `NumericalRingData.degree_sum_mul_sum` (and the triple
version) on **bare families**, in `Numerical/Core/Definitions.lean` — above every
current copy.  It must be on `NumericalRingData`, not `NumericalVarietyData`,
because `Hirzebruch.lean` applies it to reconstructed families that are not any
variety's `chComp`.

**Projections.**  The `private` copy is deleted and the root called with `P.ring`;
`degree_ch_mul_todd` becomes `R.degree_sum_mul_sum _ _ (V.chComp_mem E) V.toddComp_mem`
after `simp only [ch, todd]`; `degree_surface_total` becomes the root at `n = 2`
plus `Finset.sum_range_succ` **and** `degree_algebraMap_mul` (it also performs the
rank extraction); `rankOneDegree_sum_mul_sum`/`surfaceDegree_ch_mul_todd` become
the root applied to `algebraMap (c i) * H^i`; `chi₂_eq_sum` becomes the triple
version; `mukaiIntegral_eq` becomes the root with `x = (−1)^i • mukaiComp E i`.

**Future examples covered.**  Every future Riemann–Roch-type integral — the Mukai
pairing in dimension `n`, twisted charges, Euler pairings on threefolds and
fourfolds; the reconstruction lane in dimension > 4 without another private copy.

**Verdicts.**
- *Mathematics* — survives, with no amendment needed to the substance: both
  statements read, the proof scripts are identical, and the hypotheses the root
  needs (membership for all `i`) hold at every proposed call site.  **Correction
  applied:** `degree_ch_mul_todd` is stated on the named total classes, so the
  projection needs `simp only [ch, todd]` first.
- *Repository* — survives; the cleanest finding in its lane, and the inversion is
  literal.  **Correction applied:** `degree_surface_total` also takes
  `hc0`/`ht0` and concludes in a rank-extracted form, so its projection is the root
  plus `sum_range_succ` plus `degree_algebraMap_mul`.
- *Adoption and cost* — survives; the cheapest finding in its lane, with no new
  structure, no baseline, no namespace cutover, and no review-payload exposure.
  **Correction applied:** sequence numerical-nfold-04 first, or this theorem gets
  written twice — under that root it is `degree` composed with `proj_mul`.

#### walls-03 — Four implementations of the β-twist

**Kind** missing-root (reclassified from leaf-copies-root) · **Impact** medium ·
**Confidence** 0.9

**Declarations.**  `twist`/`twist_add_beta` (`Stability/TwistedChern.lean:104`, `:110`);
`Threefold.betaTwist` (`Walls/Threefold/Basic.lean:89`) and `betaTwist_betaTwist` (`:113`);
`ChargeCoordinates.twistByScalar` (`Walls/Divisorial/Coordinates.lean:63`);
`ChernCharacter.twist` (`Walls/Divisorial/Charge.lean:121`);
`Wall.NumClass.shift` (`Walls/Numerical/Basic.lean:213`) — a different operation,
correctly excluded.

**Parent structure.**  The action of `ℝ` on H-degree vectors by convolution with
the exponential coefficients.  The surface `NumClass` model has no twist at all
and treats `s` as a coordinate, so `Threefold/Basic.lean:134-145` must prove
`reZ_eq_betaTwist` to reconcile the two, and no surface analogue exists on that
carrier.

**Proposed root** (corrected: a **new** ℝ-coefficient root, not the ℚ ring twist).
`Walls/HDegree/Twist.lean`, namespace `…Wall.HDegree`: `betaTwist`, `betaTwist_add`,
`charge_betaTwist`.

**Projections.**  `Threefold.betaTwist` and `ChargeCoordinates.twistByScalar`
reproduce the root coordinatewise — both compiled
(`scratchpad/Probe2.lean`, `Probe6.lean`).  `ChernCharacter.twist` stays the
intrinsic owner.  `NumClass.shift` is untouched.

**Future examples covered.**  The fourfold β-twist with no new expansion; the
surface second-tilt and threefold third-tilt hearts, which need `e^{−βH}` at every
codimension simultaneously.

**Verdicts.**
- *Mathematics* — survives.  The n-general root's relation to the ring-level twist
  verified by integrating against `H^{n−k}`; `twistByScalar` checked coordinate by
  coordinate against `betaTwist` on `(H²·rank, degree, chTwo)` with an exact match;
  `NumClass.shift` confirmed to be `w + k•v`.  **Corrections applied:** "no surface
  analogue exists" is overstated — `stCharge_toNumClass` (`Divisorial/Circle.lean:113`)
  *is* the `n = 2` "β is a twist" statement, but on the `ChargeCoordinates` carrier,
  so the symptom is a carrier split, not absence; the third sketch theorem is
  malformed; `twist_add_beta` cannot be reused by `rfl` over `ℝ`.
- *Repository* — survives.  Every citation checks out, including the two
  hand-written coefficient bodies and the `tc0..tc3` bridging lemmas.
  **Corrections applied:** `TwistedChern.twist` convolves Chern *components* in the
  graded ring and carries `H^(i-j)` factors, so its relation to an H-degree twist
  is a theorem, not an identity; the numerical layer is **already** fully rooted
  (`chBComp` and `chBetaComp` both go through `twist`, and `chBComp_along` proves
  they agree), so the duplication is confined to the two wall-layer twists.
- *Adoption and cost* — headline **refuted**, residual survives.  `twist` takes
  `β : ℚ` on a graded ring while `betaTwist` takes `β : ℝ` on `ℝ⁴`, so no
  instance/abbrev/extends can connect them and the existing bridge is stated only
  for rational `β`; `betaTwist_betaTwist` is not a re-proof of `twist_add_beta`.
  **Corrections applied:** reclassify as `missing-root`; drop `TwistedChern.twist`
  as the parent; budget the ℝ group law as new work; the two
  `ofNumericalDataB_along_*` lemmas are **not** instances of one theorem with
  `betaTwist_toNumClass`.

#### walls-04 — The threefold tilt slope is the surface charge's slope

**Kind** existing-root-unused · **Impact** medium (adoption lens rates high) ·
**Confidence** 0.9

**Declarations.**  `chargeSlope` (`Weak/Foundation/StabilityFunction/WeakSlopeGeometry.lean:63`);
`Wall.Threefold.nu` (`Walls/Threefold/Basic.lean:208`);
`Threefold.nu` (`Stability/BMT.lean:111`);
`slopeH` (`Stability/Slope.lean:133`);
`Wall.stCharge` (`Walls/Numerical/ChargeFamily.lean:28`).

**Parent structure.**  Every slope in the lane is `chargeSlope z = −Re z / Im z`
of a truncated H-degree charge.  Verified by hand and by compilation:
`Threefold.nu α β v = α · (−reZ β α (trunc v) / imZ β α (trunc v))` — the
threefold's first tilt slope is the **surface** charge polynomial on the
threefold's first three H-degrees, up to the factor `α`.  `BMT.nu` is the same
ratio in ℚ, already identified by `nu_toNumClass`.  So there are three slope
definitions and one root that none of them uses.

**Proposed root.**  `Walls/HDegree/Slope.lean`: `tiltSlope k w v := chargeSlope (charge k w (truncate k v))`,
plus the `Threefold.NumClass →+ NumClass` truncation map, which does not exist today.

**Projections.**  `Threefold.nu` becomes `α · tiltSlope 2 (β + αI)` on `Im ≠ 0`;
`BMT.nu` follows through `nu_toNumClass`; `slopeH` becomes the `k = 1` case
**with the `∫Hⁿ` factor** (see the correction); and the surface tilt walls of a
threefold become `(chargeFamily 2).pullback (truncate 2)`, so `wall_circle_eq`,
`wall_eq_of_meet` and `walls_nested_of_discr_nonneg` apply to threefold ν-walls by
`pullback_wall` with no new theorem.

**Future examples covered.**  ν-walls on `ℙ³` and the quintic as nested
semicircles; the `k = 3` slope for a fourfold; the Mumford slope on any n-fold as
the `k = 1` case.

**Verdicts.**
- *Mathematics* — survives.  The central identity recomputed from source rather
  than taken on trust, numerator and denominator separately.  **Corrections
  applied:** `tiltSlope_one v = v 1 / v 0` is **FALSE** — the correct statement is
  `((v 1 − β · v 0)/(α · v 0))`, the β-twisted slope divided by α, equal to the
  Mumford slope only at `w = i`; the `slopeH` projection is off by `∫Hⁿ`, not
  merely by a cast; `truncate_charge` is not a partial sum.
- *Repository* — survives.  Kind confirmed as existing-root-unused: `chargeSlope`
  occurs only inside the Weak tree and none of the three slopes reaches it; the
  central identity verified by hand; no layering violation, since `Walls` importing
  the Weak tree is already exercised.  **Corrections applied:** `SlopeData.slope`
  is **not** an alternative root for `slopeH` (it is parameterised by an abelian
  category), so `chargeSlope` is the only reachable root; the type mismatch
  (`WithTop ℝ` vs junk-valued ℝ/ℚ) is load-bearing and the comparison must be
  conditional.
- *Adoption and cost* — survives and rates **high**: both identities compiled, the
  missing `truncHom` was built and compiled, and the reuse is the largest in the
  lane — an entire nested-semicircle theory transported for one `→+` and two
  lemmas.  Cost is the smallest in the lane.  **Corrections applied:** the
  identification holds on `0 < α ∧ 0 < (e^{−βH}d)₁`, so the unconditional sketch is
  not provable; the α factor is not removable; and the two families are indexed in
  **opposite** coordinate orders, so the pulled-back ν-wall family needs an explicit
  `reindex Prod.swap`.

#### walls-05 — The (s,t) and (α,β) half-planes are one chart with opposite order

**Kind** dimension-specific-should-be-n-fold · **Impact** medium (adoption lens
refuted) · **Confidence** 0.9

**Declarations.**  `Divisorial.StabilityParameters` (`Walls/Divisorial/Charge.lean:197`),
`rankOne` (`:209`); `OrthogonalSlice.Point` (`Walls/Divisorial/Slice.lean:94`);
`Wall.stChargeFamily` (`Walls/Numerical/ChargeFamily.lean:59`);
`Wall.Threefold.chargeFamily` (`Walls/Threefold/Basic.lean:174`);
`NumericalRealization.rankOneParameters` (`Stability/DivisorialWallTransport.lean:55`).

**Parent structure.**  The pair `(B, ω) ∈ D × D` with the rank-one chart
`(β,α) ↦ (βH, αH)`.  The surface child takes `p = (s,t) = (β,α)`; the threefold
child takes `p = (α,β)`.  The same `ℝ × ℝ` means two different points in the two
files, and `rankOneParameters p := rankOne H p.2 p.1` swaps to compensate.  Worse,
the threefold has **no** `DivisorSpace`/`ChernCharacter`/`StabilityParameters`
layer at all, so `wallChargeFamily_eq_rankOne_reindex` — the theorem that made the
surface `(s,t)` plane a slice rather than a second owner — has no threefold
counterpart and cannot have one today.

**Proposed root** (corrected: no `abbrev` for ℂ).  Fix one documented order at the
threefold child (one `reindex Prod.swap`, one file), and record in
`Threefold/Basic.lean` that the `(α,β)` plane is the rank-one chart of an unbuilt
intrinsic family — per the "Negative result" clause.

**Projections.**  `stChargeFamily` and `Threefold.chargeFamily` become reindexings
of one chart; `StabilityParameters.rankOne H α β` is unchanged and becomes the one
place the order is fixed; a threefold `DivisorSpace`/`ChernCharacter` layer is the
missing intrinsic parent, recorded rather than built.

**Future examples covered.**  Fourfold `(α,β)` plane with the same chart;
Picard-rank > 1 threefolds, where BMT fails and `B ∉ ℝH` is needed; Kuznetsov
stability on the cubic threefold, whose parameters are the same chart restricted
to a region.

**Verdicts.**
- *Mathematics* — survives.  Every factual claim checked: the two children
  genuinely disagree about what `ℝ × ℝ` means, the compensating swap is real, and
  the threefold has no intrinsic layer (`ChargeCoordinates` carries only three
  Chern slots).  **Corrections applied:** do **not** write `abbrev RankOneChart := ℂ`
  — an abbrev inherits ℂ's `Field`/`Algebra` instances and lets typeclass search
  unify a wall parameter with a scalar; and state the severity as *latent*, since
  the two planes never meet today.
- *Repository* — survives.  All declarations real at the cited lines and the swap
  is literal; the structural half is also true.  **Corrections applied:** reclassify
  the `n = 2` half — `StabilityParameters` **is** the parameter-space root and the
  surface already reaches it by proved reindexing, so the surface is not a second
  owner; drop the ℂ abbrev; the genuinely missing object is the threefold intrinsic
  layer, and that note is the deliverable.
- *Adoption and cost* — **refuted** (single dissent).  The proposed root is a thin
  abstraction whose entire content is `ChargeFamily.reindex`, which already exists;
  one leaf reaches the genuine existing root (`StabilityParameters`, already bridged
  by `wallChargeFamily_eq_rankOne_reindex`); and the second leaf **cannot be
  written**, since nothing under `Walls/Threefold/` mentions `DivisorSpace`.  The
  correct outputs are the one-file coordinate fix and the recorded negative result,
  which is what is proposed above.

#### walls-06 — Wall transport is two copies of one construction

**Kind** duplicate-parent · **Impact** medium · **Confidence** 0.9

**Declarations.**  `Surface.toNumClass`/`toNumClassHom`/`wallChargeFamily`
(`Stability/WallTransport.lean:112`, `:145`, `:156`);
`Threefold.toNumClass`/`toNumClassHom`/`wallChargeFamily`
(`Stability/ThreefoldWallTransport.lean:146`, `:175`, `:183`);
`degH` (`Stability/Slope.lean:116`);
`ChargeFamily.pullback` (`Walls/ChargeFamily.lean:72`).

**Parent structure.**  Both transports are `E ↦ (∫H^{n−k}·ch_k(E))_k` cast to ℝ,
followed by `ChargeFamily.pullback`; each proves additivity coordinate by
coordinate, bundles it, and defines `wallChargeFamily := child.pullback`.  The
`k = 1` coordinate already has an n-general owner.  Every downstream identity is
`pullback_wallValue` specialised.

**Proposed root.**  `Stability/HDegreeTransport.lean`, namespace
`AlgebraicGeometry.Numerical`: `hDegree`, `hDegreesHom`, `wallChargeFamily`,
`hDegrees_betaTwist`.

**Projections.**  The two `toNumClassHom` become `hDegreesHom` composed with the
carrier equivalence; `betaTwist_toNumClass` becomes `hDegrees_betaTwist`;
`degH` is `hDegree 1` by `rfl`; `BMT.degH1Beta` and siblings become abbrevs of one
`hDegreeBeta k`; the grandchildren need no change beyond the root's index type.

**Future examples covered.**  Fourfold transport for `ℙ⁴` and the sextic with zero
new proofs; any future polarised n-fold example.

**Verdicts.**
- *Mathematics* — survives.  Both transports verified end to end, including the
  slot-0 identity through `chComp_zero` and `degree_algebraMap_mul`, so no leaf
  needs a mathematical change.  **Correction applied:** there are **three** `n = 2`
  transports, not two — `ChargeCoordinates.toNumClass` (`Divisorial/Circle.lean:79`)
  is an independent third copy, bridged by a hand-proved theorem
  (`DivisorialWallCircle.lean:36`), which is precisely why that module exists; the
  root must absorb it, or two copies survive the refactor.  Also, an `abbrev`
  carrier loses the named `deg0..deg3` accessors that downstream `simp only` lists
  name, so matching accessor abbrevs are needed.
- *Repository* — survives at medium.  All eight citations real; the two transports
  are the same map at two arities; the layering caveat is correct and
  self-consistent with `WallTransport.lean:55-60`.  **Correction applied:** the
  same third-copy amendment, plus noting that `BMT.degH1Beta`/`degH2Beta`/`deg3Beta`
  are three more hand-written `hDegree k` instances.
- *Adoption and cost* — survives at medium.  The duplication verified by reading
  both files side by side; leaf names survive, so the per-example lemmas need no
  edit; the placement constraint (carrier under `Walls/`, map under
  `AlgebraicGeometry/`) is the load-bearing one.  **Corrections applied:** this is
  **not** an independent finding — its carrier is walls-01's, and adopting it alone
  would produce an n-general map into two hand-expanded tuple children, so land
  them as one change or they double-count; `discr_toNumClass` does **not** become
  `rfl` under the root, since it is stated against `Surface.discrH` in ℚ.

#### walls-07 — The spherical half-wall is a `ChargeFamily` wall cut by a sign

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.85

**Declarations.**  `Wall.Spherical.wall` (`Walls/Spherical/Basic.lean:301`),
`pairingRe` (`:174`), `pairingIm` (`:181`), `chamber` (`:310`);
`Mukai.expChargeHom` (`Lattice/Mukai/CentralCharge.lean:44`);
`ChernCharacter.mukaiChargeFamily` (`Walls/Divisorial/Mukai.lean:224`);
`Wall.ChargeFamily.wall` (`Walls/ChargeFamily.lean:129`).

**Parent structure.**  For the point class `pt = (0,0,1)` one has `Z(pt) = −1`
(recomputed by hand), so `wallValue p δ pt = Im Z(δ)` and the numerical wall
`F.wall δ pt` is exactly `{pairingIm = 0}`; Bridgeland's `H(δ)` is that wall
intersected with the half where `Z(δ)` points the same way as `Z(O_x)`.  Meanwhile
the divisorial branch already has this very charge as a `ChargeFamily`.

**Proposed root** (corrected placement).  `Mukai.expChargeFamily` must live
**under `Walls/`**, not in `LinearAlgebra/Lattice/Mukai/CentralCharge.lean` — a
`Wall.ChargeFamily`-valued definition there would be the first
`LinearAlgebra → CategoryTheory` import in the tree (`grep` returns zero today).
Every theorem must carry symmetry of `q`.

**Projections.**  `Spherical.wall q δ` becomes
`(expChargeFamily q).wall δ pointClass ∩ {Re ≤ 0}` — compiled, with `hq`;
`chamber` becomes the complement of a union of root walls with the sign condition;
`mukaiChargeFamily t` becomes a reindex-and-pullback of the root, which finally
relates the K3 spherical walls to the divisorial Mukai charge;
`PeriodDomain.wall` is recorded as the degenerate `Z(δ) = 0` point of the root.

**Future examples covered.**  Spherical and (−2)-class walls on any surface with a
Mukai lattice; the cubic-fourfold Ku(X) charge as a pullback child rather than a
new root; comparison of Bridgeland's chamber with the divisorial nested-wall
chambers on the same `(B,ω)` parameters.

**Verdicts.**
- *Mathematics* — survives.  `Z(pt) = −1` and `wallValue p δ pt = pairingIm`
  recomputed from the definitions; the half-wall caveat verified to be load-bearing.
  **Corrections applied:** symmetry `hq` is a **hypothesis**, since
  `polar (realForm q)` is the symmetrisation; the cubic-fourfold claim in the
  future-examples list is **wrong** — that charge pairs against an arbitrary
  positive 2-plane, so `expChargeFamily` cannot be its parent and it must reach
  `QuadraticForm.centralCharge` directly (this is exactly N11); and the placement
  correction above.
- *Repository* — survives.  All citations real; the point-class computation checked
  from `realPairing`, `expRe`, `expIm`; the import claim verified (no
  `Walls.ChargeFamily` anywhere under `Walls/Spherical/`); the `mukaiChargeFamily`
  projection is `rfl`.  **Corrections applied:** the placement fix; the symmetry
  hypothesis; and a factual trim — `DivisorialRegion.lean` and `WallComparison.lean`
  do import other modules, so the accurate claim is that no Spherical module *names*
  `Wall.ChargeFamily`.
- *Adoption and cost* — survives; every step compiled
  (`scratchpad/Probe5.lean`), including `Z(pointClass) = −1`, the `wallValue`
  identity, and the headline wall equation; the second leaf is an honest `rfl`; a
  third comes free through `centralCharge_eq_expChargeHom`.  **Corrections
  applied:** symmetry is required; do not place the family in `LinearAlgebra`; keep
  the inclusion-plus-sign statement, since `finite_wallCandidates` consumes the
  inequality.

#### weak-tilting-04 — Three carriers differing only in the positivity set P

**Kind** existing-root-unused · **Impact** medium (repository and adoption lenses
rate low) · **Confidence** 0.8

**Declarations.**  `IsPositive` (`Weak/Charge.lean:101`);
`StabilityFunctionOn` / `WeakStabilityFunctionOn`
(`Weak/Foundation/StabilityFunction/Basic.lean:35`, `:42`) and `toWeak` (`:49`);
`SlopeData` (`Slope.lean:84`), `toWeakSlopeData` (`:143`);
`WeakSlopeData` (`WeakSlope.lean:84`), `toWeakStabilityFunction` (`:165`);
`SkewedStabilityFunction` (`Foundation/Deformation/SkewedStability.lean:32`).

**Parent structure.**  All are "`Z : G →+ ℂ` with `Z(cl E) ∈ P` for every relevant
`E`" at different `(D, P)`.  `IsPositive D P Z` is the P-parametrised root, and
`IsStabilityCharge`/`IsWeakStabilityCharge` are its two abbrevs — but no *carrier*
is parametrised by `P`, so `StabilityFunctionOn` and `WeakStabilityFunctionOn` are
two structures with identical fields and the monotonicity is written by hand as
`toWeak`.

**Proposed root** (corrected: keep the field name, and drop the slope half).
`PositiveCharge (D : ClassDatum O G) (P : Set ℂ)` with field `nonzero_mem`, in
`Weak/Charge.lean`, plus `PositiveCharge.mono`.

**Projections.**  `StabilityFunctionOn D` and `WeakStabilityFunctionOn D` become
abbrevs at the two half-planes — verified in Lean, with `Equiv`s `rfl` both ways,
so all 36 `.nonzero_mem` projections and every anonymous constructor survive;
`toWeak` becomes `PositiveCharge.mono` — also proved by `rfl`.

**Future examples covered.**  Charges valued in the open upper half-plane for
σ-stability on Kuznetsov components after tilting; any future "stability function
with prescribed positivity cone P".

**Verdicts.**
- *Mathematics* — survives.  The positivity equation checks out exactly:
  `semiClosedUpperHalfPlane` instantiates to `SlopeData`'s two fields and
  `closedUpperHalfPlane` to `WeakSlopeData`'s, and `SkewedStabilityFunction` is
  `IsPositive` at `P = {z ≠ 0}` for the interval-factor datum.  **Corrections
  applied:** **drop** the second future-example — the ν-slope charge on a tilted
  heart is **not** an `IntegralRankCharge`, since its imaginary slot
  `H·ch₁^β = H·ch₁ − β·H²·ch₀` is real-valued for irrational β, so "integral after
  scaling" is false; `im_eq` needs the ℤ→ℝ cast; `rank_nonneg` is quantified over
  all objects while `IsPositive` constrains only relevant ones.
- *Repository* — survives at **low**.  The `IsPositive` half stands.  **Correction
  applied:** the `SlopeData`/`WeakSlopeData` half is **refuted** —
  `Slope.lean:61-67` states that `toWeakSlopeData` *is* the forgetful map and that
  everything carrying a positive-rank hypothesis "is proved once on `WeakSlopeData`
  and inherited here", and `toWeakStabilityFunction` already discharges both fields
  into `IsWeakStabilityCharge`; so narrow the finding to the carrier
  parametrisation, and severity drops because the saving is ~8 lines plus one
  lemma and the argument is the future `P`, not present duplication.
- *Adoption and cost* — survives at low, verified by compilation: keeping the field
  name `nonzero_mem` makes the root field-for-field both carriers, so there is no
  cutover and the `RestateHistoricalNames` concern does not bite.  **Corrections
  applied:** the `SlopeData` half is largely refuted (the residual duplication is
  ~35 lines of mirrored formal theorems against 28 files / 279 references —
  net negative, do not adopt); `SkewedStabilityFunction` does **not** reach, since
  its `nonzero` field quantifies over `(E, φ)` pairs and its phase is
  branch-centred; three of the four names are in the baseline and must be edited in
  the same change.

#### weak-tilting-05 — Support-property binding structures copied three times

**Kind** duplicate-parent · **Impact** medium · **Confidence** 0.88

**Declarations.**  The correctly shared generic roots
`Support.HasSupportProperty` (`Weak/Support/Predicate/Basic.lean:58`),
`HasQuadraticSupportProperty` (`Predicate/Quadratic.lean:59`),
`HasUniformQuadraticSupportProperty` (`Predicate/Uniform.lean:30`);
against the duplicated binding layer —
`WeakStabilityFunction.semistableClasses`/`HasSupportProperty`/`QuadraticSupportData`/
`UniformQuadraticSupportData`/`QuotientUniformQuadraticSupportData`
(`Weak/Support/Basic.lean:43`, `:49`; `Weak/Support/Quadratic.lean:55`, `:87`, `:125`)
and `PreStabilityCondition.WithClassMap.semistableClasses`/`HasSupportProperty`/
`QuadraticSupportData`/`UniformQuadraticSupportData`
(`Support/Semistable.lean:38`, `:61`, `:68`, `:88`);
`WeakQuotientQuadraticSupportData` (`Weak/Families/Weak.lean:135`).

**Parent structure.**  "A real-linear charge `Zlin` realising the additive charge
on classes, together with (uniform) quadratic support on the selected semistable
locus" — the same two-field Prop structure and the same three lemmas
(`fiber`, `reindex`, `constant`) written twice, differing only in the locus and in
whether the class map `v` is inserted.

**Proposed root.**  `Weak/Support/Predicate/Package.lean`, namespace
`…WeakStabilityCondition.Support`: `NumericalLocus (Λ V)` and
`QuadraticSupportPackage`/`UniformQuadraticSupportPackage`, with `fiber`,
`reindex`, `constant` proved once.

**Projections.**  Both `QuadraticSupportData`s become packages at their locus —
verified in Lean, constructor to constructor, with the ordinary case at
`v := AddMonoidHom.id V`; `WeakQuotientQuadraticSupportData` becomes
`QuotientUniformQuadraticSupportData` at a one-point index, or is deleted in favour
of `.fiber`; `Support/Transfer.lean`'s preimage theorems become locus monotonicity.

**Future examples covered.**  Support property for stability conditions on
Kuznetsov components with the Mukai/`A₂` lattice as `V`; Gieseker and tilt-stability
boundedness statements; Bridgeland stability on Ku(X) via restriction.

**Verdicts.**
- *Mathematics* — survives.  Both records read field for field and the three
  lemmas are one-for-one two-field anonymous constructors;
  `WeakQuotientQuadraticSupportData` is verbatim the conclusion type of
  `QuotientUniformQuadraticSupportData.fiber`; the generic predicates are already
  correctly parametrised by the locus, so nothing is at stake in the equation.
  **Corrections applied:** the `abbrev` for the quotient wrapper is an **iff**, not
  a definitional equality (it goes through `hasUniformQuadraticSupportProperty_iff_union`
  at a singleton index); the `false_unification_risk` overstates the danger, since
  the locus is a parameter of the root.
- *Repository* — survives.  All 13 citations real, and the duplication is verbatim
  down to identical proof terms for `fiber`/`reindex`/`constant`; no contract is
  violated, since these are Prop structures used as explicit hypotheses, and the
  layering direction is already established.  **Correction applied:** keep the
  ordinary case's `charge_compatible` stated directly on `V`, since existing simp
  normal forms depend on that shape.
- *Adoption and cost* — survives; the projection compiled with both bindings
  reaching the root by anonymous constructors.  **Corrections applied:** the risk
  that a `v = id` coercion breaks simp normal forms does **not** materialise; note
  that the two `charge_compatible`s are genuinely different strength (the weak one
  only on the image of `v`), which the root accommodates by varying `Λ`; three
  baseline names must be updated in the same change.

#### weak-tilting-06 — The strict theory is not registered as a specialisation

**Kind** same-equation-two-names · **Impact** medium · **Confidence** 0.8

**Declarations.**  `StabilityFunctionOn.toWeak`
(`Weak/Foundation/StabilityFunction/Basic.lean:49`);
`slopeOfPhase` (`Foundation/StabilityFunction/SlopeThreshold.lean:64`);
`weakPhaseOfSlope` (`Weak/Heart/EquivalenceReverse.lean:45`) and
`weakPhaseOfSlope_strictMono` (`:83`);
`slopeCutPhase` (`Tilting/TorsionPair/SourceSlope.lean:178`);
`StabilityFunction.IsSemistable` (`Basic.lean:141`) vs
`WeakStabilityFunctionOn.IsSemistable` (`WeakSlopeGeometry.lean:233`);
`WeakSlopeData.phase` (`WeakSlope.lean:187`).

**Parent structure.**  On the semi-closed upper half-plane, phase and slope are
related by the strictly monotone bijection `φ ↦ −cot(πφ)`, whose two directions
already exist.  Hence `Z.IsSemistable E ↔ Z.toWeak.IsSemistable E`, HN filtrations
correspond bijectively, and `hnTors Z β = hnTors Z.toWeak (slopeOfPhase β)` — none
of which is stated, so roughly 1000 lines of strict development are a parallel
theory rather than a corollary.

**Proposed root.**  `Weak/Foundation/StabilityFunction/PhaseSlope.lean`:
`phaseSlopeOrderIso : WithTop ℝ ≃o Set.Ioc (0:ℝ) 1` built from `weakPhaseOfSlope`,
with `slopeOfPhase` recovered as its inverse on the interior, plus the transport
theorems.

**Projections.**  The strict `Uniqueness`, `PhaseMonotone`, `Cutoff`, `Splitting`,
`Truncation` and `Tail` files become corollaries through the equivalence — or,
with weak-tilting-01, both become instances of the labelled root, in which case
this finding dissolves into `mapLabel`.

**Future examples covered.**  Any strict stability function on a curve or a tilted
heart inheriting the weak HN and tilting toolkit without re-proving it;
normalised phase for weak conditions.

**Verdicts.**
- *Mathematics* — survives.  The bijection verified in both presentations by
  composing the two formulas, and `phase = weakPhaseOfSlope ∘ chargeSlope` confirmed
  on the semi-closed half-plane; no bridge exists anywhere.  **Corrections
  applied:** no new analysis is needed —
  `complex_eq_pos_mul_exp_weakPhaseOfSlope` (`Weak/Basic/ChargeRay.lean:38`) already
  gives the identity in two lines; `slopeOfPhase` **cannot** be an abbrev for the
  order iso (it is ℝ-valued and returns junk at the endpoints), so the iso is
  `weakPhaseOfSlope`'s inverse; `weakPhaseOfSlope` must move down from
  `Weak/Heart/` into `Foundation/`, which is free since it has no categorical
  dependencies.
- *Repository* — survives.  All 8 citations real, and the decisive check confirms
  the claim: `StabilityFunction A` is an abbrev of `StabilityFunctionOn (abelianDatum A)`,
  so every comparison is directly statable, yet `.toWeak` has exactly three
  occurrences repo-wide — the definition, its `rfl` lemma, and one wrapper.
  **Correction applied:** narrow "none of these is stated" — partial bridges exist
  at the slope-data level and in the cutoff direction; what is absent is any
  statement relating a charge to its own `toWeak`.  This finding and weak-tilting-01
  are two routes to the same fix and must not be scheduled separately.
- *Adoption and cost* — survives.  `toWeak` has essentially no consumer;
  `slopeOfPhase` is consumed only for `SlopeData` at positive rank;
  `weakPhaseOfSlope` only on the heart/slicing side; the two are mutually inverse
  and this is nowhere recorded.  **Corrections applied:** "three names" is two —
  `slopeCutPhase` is literally `weakPhaseOfSlope` applied to a coercion;
  `WeakSlopeData.phase` belongs with weak-tilting-03's `ClassDatum.phase`; add the
  contrast that makes this a defect rather than a preference — at the *slicing*
  level the repository already expresses the same strict/weak relation as
  inheritance (`PreStabilityCondition.WithClassMap extends WeakPreStabilityCondition`
  with `ofStrict`), so the abelian/charge level is the one place it is left as an
  unused `def`; sequence after weak-tilting-01.

#### symmetry-metric-03 — Four copies of the uniform-quadratic family package

**Kind** duplicate-parent · **Impact** medium · **Confidence** 0.85

**Declarations.**  `WeakStabilityFunction.UniformQuadraticSupportData`
(`Weak/Support/Quadratic.lean:87`) and `QuotientUniformQuadraticSupportData` (`:125`);
`PreStabilityCondition.WithClassMap.UniformQuadraticSupportData`
(`Support/Semistable.lean:88`);
`OrdinaryFiberUniformQuadraticSupportData` (`Families/FiberwiseSupport.lean:74`);
`OrdinaryFiberStabilityInFamiliesData.charge_compatible`/`uniformSupport`
(`Families/FiberwiseOrdinary.lean:65`);
`FiberPreStabilityBaseChangeData.charge_compatible`
(`Families/PreStabilityBaseChange.lean:45`);
`CategoricalOrdinaryFiberStabilityInFamiliesData` (`Families/CategoricalOrdinary.lean:49`);
`Support.HasUniformQuadraticSupportProperty` (`Predicate/Uniform.lean:30`) and
`…Modulo` (`Predicate/Quotient.lean:56`).

**Parent structure.**  One `Zlin` with `∀ i, Zlin ∘ cl = Z_i` and uniform quadratic
support on `S`.  The fixed-category ordinary structure **is** the fiberwise one at a
constant family — `ordinaryFiberSemistableClasses σ i` is *definitionally*
`(σ i).semistableClasses` — and `WithClassMap.UniformQuadraticSupportData` has no
consumer outside its own file.

**Proposed root.**  `Weak/Support/Predicate/Uniform.lean`, namespace
`…WeakStabilityCondition.Support`: `UniformChargedLoci cl Zi S Zlin`, with
`fiber`/`reindex`/`constant` proved once and a `Modulo` abbrev at the quotient.

**Projections.**  The four structures become abbrevs at
`cl := v` or `cl := AddMonoidHom.id V`; the consumer-less fixed-category copy can
simply be deleted in favour of the fiberwise one at a constant family;
`ordinaryFiberUniformQuadraticSupportData_constant` becomes `ChargedLocus.constant`.

**Future examples covered.**  Uniform support for stability conditions on the
fibers of a family of Kuznetsov components; threefold and fourfold tilt-stability
families in one numerical space; any future ordinary/weak/quotient support package.

**Verdicts.**
- *Mathematics* — survives.  All three field lists read and found identical, with
  `ordinaryFiberSemistableClasses` definitionally the constant case; the `cl`
  parameter recovers both spellings with no hypothesis weakened; the `Modulo` form
  is literally the plain predicate at the quotient; the base-change redundancy is
  real.  **Corrections applied:** do not carry `[FiniteDimensional ℝ V]` in the
  root (every `.fiber`/`.reindex`/`.constant` `omit`s it); keep `Zi` additive and
  `Zlin` linear as distinct carriers; the base-change field is redundant only
  *inside* the combined package.
- *Repository* — survives.  Every citation real, and the claim is stronger than
  stated: the fixed-category and fiberwise predicates are field-for-field the same
  and **neither** has a consumer outside its own file — precisely the failure mode
  `check_single_instantiation.py` documents.  Placement beside the generic
  predicate respects layers rule 4, and the `.fiber`/`.reindex`/`.constant` theorems
  are themselves inhabitants.  **Corrections applied:**
  `FiberPreStabilityBaseChangeData.charge_compatible` must **not** be deleted — it
  has standalone consumers in three geometric files; and
  `OrdinaryFiberStabilityInFamiliesData` already reaches the five-clause root, so
  only the `(charge_compatible, uniformSupport)` pair is unrooted.
- *Adoption and cost* — survives, verified in Lean with both directions
  round-tripped by anonymous constructors.  **Corrections applied:** the quadratic
  half is **already** rooted and already reused — every leaf proof delegates to
  `HasUniformQuadraticSupportProperty.fiber`/`reindex`/`constant` — so the reuse
  ceiling is "9 theorems → 3, 4 structures → 2", not a new mathematical layer; and
  the base-change sub-claim is wrong for the same standalone-consumer reason.

#### symmetry-metric-04 — A second `MulAction` on `Slicing C` with no group hom

**Kind** duplicate-parent · **Impact** medium (adoption lens rates low) ·
**Confidence** 0.9

**Declarations.**  `StrictAut` (`Symmetry/Autoequivalence/Slicing/Strict.lean:60`),
`actSlicing` (`:120`), `mulActionSlicing` (`:153`);
`TriEquiv` (`Slicing/Quotient.lean:59`), `TriEquiv.act` (`:108`),
`AutQuot` (`:158`), `AutQuot.mulActionSlicing` (`:183`).

**Parent structure.**  One action, `g • s := s.mapEquiv Φ_g`.  A strict action
determines `g ↦ ⟦⟨ρ.equiv g, …⟩⟧ : G →* AutQuot C`, and the strict `MulAction`
should be `MulAction.compHom` along it.  Instead `Strict.lean` rebuilds
`one_smul`/`mul_smul` by hand, its docstring points at `AutQuot` as the "honest"
version, `StrictAut` appears nowhere else in the repository, and nothing proves
`ρ.actSlicing g s = ρ.toAutQuot g • s`.

**Proposed root.**  Existing: `AutQuot` plus Mathlib's `MulAction.compHom`.  Add
`StrictAut.toTriEquiv`, `toAutQuot : G →* AutQuot C`, and `actSlicing_eq` in
`Strict.lean` (adding one import).

**Projections.**  `mulActionSlicing` becomes `MulAction.compHom … ρ.toAutQuot` and
inherits both laws; `actSlicing` becomes `actSlicing_eq`, which is `rfl`; if no
consumer materialises, delete `StrictAut` and record it as a negative result — the
strict framework is subsumed.

**Future examples covered.**  Strict actions by finite groups of automorphisms of a
variety (the Enriques involution, K3 symplectic automorphisms) acting on Stab
through the one `AutQuot` action; strict ℤ-actions.

**Verdicts.**
- *Mathematics* — survives.  The two formulas are the same, the multiplication
  orders were checked rather than assumed and **agree**, and `actSlicing_eq` is
  `rfl` because `AutQuot.mk_smul_P` reduces definitionally.  The consumer claim is
  confirmed: outside its own file `StrictAut` appears only in a docstring, an audit
  `#print axioms`, and **`single_instantiation_baseline.txt:63`** — the repository's
  own gate has already recorded it as a generic structure with no inhabitant.
  **Corrections applied:** drop the opposite-group hedge (the variance already
  matches); the dependency remark is wrong — neither file imports the other, so no
  move is needed; given the baseline entry, deletion is the default.
- *Repository* — survives.  All citations verified, `StrictAut` has no consumer
  anywhere, and the variance works out with no opposite group; the tree already
  contains the precedent (`gltildeSlicingMulAction` is `MulAction.compHom` along a
  group hom).  **Corrections applied:** the kind is existing-root-unused;
  the dependency claim is wrong; the deletion option carries two chores — the
  baseline line and the umbrella import.
- *Adoption and cost* — survives at **low**.  The facts are confirmed and the fix
  was compiled (`scratchpad/StrictHom.lean`, exit 0), including
  `actSlicing_eq := rfl`.  Impact is low because the reuse gained today is zero:
  with no consumer this is a ~20-line hom that makes a dead framework honest, or an
  argument for deleting the file.  **Corrections applied:** no dependency reversal
  to undo; no multiplicative opposite needed.

#### symmetry-metric-05 — Equivariance, continuity and orbit spaces stated per group

**Kind** missing-root · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.65

**Declarations.**  `GLTilde.chargeAddEquiv` (`Symmetry/Combined/PeriodMap.lean:38`),
`AutPair.chargeAddEquiv` (`:62`), `AutPairQuot.chargeAddEquiv` (`:82`),
`combinedChargeAddEquiv` (`:96`), and the three equivariance theorems (`:111`,
`:117`, `:126`);
`GLTilde.stabilityHomeomorph` (`Symmetry/GLTilde/Action/Continuous.lean:308`),
`combinedStabilityHomeomorph` (`:313`), `AutPairQuot.homeomorph`
(`Combined/Topology.lean:147`);
the three orbit spaces and three orbit maps (`Combined/OrbitSpace.lean:91`, `:107`);
`componentSmul` (`Combined/Components.lean:40`), already generic.

**Parent structure.**  A group `G` acting on `Stab` with a homomorphism
`ρ : G → AddAut (Λ →+ ℂ)` such that `(g • σ).Z = ρ g σ.Z`.  `Components.lean:40`
already states component transport for an arbitrary `G`, but the charge action is
written four times and the equivariance three times, the three "named
homeomorphisms" are each literally `Homeomorph.smul`, and three orbit spaces and
maps differ only in the acting group while `ComponentOrbitSpace` in the same file
is already generic.

**Proposed root** (corrected: Mathlib's, not a new Prop class).  `MulActionHom`
and `MulActionSemiHomClass` already own φ-equivariance; the right shape is
`ρ : G →* AddAut (Λ →+ ℂ)`, the induced action by `MulAction.compHom`, and the
period map as `periodMap : Stab →ₑ[ρ] (Λ →+ ℂ)`.  The three orbit maps become one
generic `Quotient.mk`.

**Projections.**  `GLTilde`, `AutPairQuot` and the product become three
`MulActionHom`s; `combinedCentralCharge_equivariant` becomes `map_smulₛₗ`; the
three homeomorphism aliases are deleted in favour of `Homeomorph.smul`; the orbit
spaces become `OrbitSpace G`.

**Future examples covered.**  The ℂ-subgroup acting by isometries, a fourth group
that would otherwise need a fifth set of copies; autoequivalence groups of
Kuznetsov components acting on `Stab(Ku(X))` and their period maps to the
`A₂`/Mukai lattice.

**Verdicts.**
- *Mathematics* — survives.  The duplication is real and the file demonstrates the
  generic form is available and then declines to use it three times; the three
  homeomorphisms are literally `Homeomorph.smul`; both charge actions are genuinely
  `AddAut (Λ →+ ℂ)`.  **Corrections applied:** the product instance is **not**
  `ρ.prod τ` (wrong target) — it is the product in `AddAut`, so use
  `MonoidHom.noncommCoprod` or an explicit hom; and the variance hedge is **wrong**
  and should be deleted — neither hom lands in the opposite, since for
  `AutPairQuot` the two contravariances cancel and for `GLTilde` `actC_mul` gives
  the same.
- *Repository* — survives at **low**.  All citations real.  **Corrections applied:**
  most of the claimed duplication is already rooted — the three orbit spaces are
  already abbrevs of `MulAction.orbitRel.Quotient`, the openness theorems are
  one-line applications, the three homeomorphisms are thin aliases, and the
  combined equivariance is *derived* from the other two; what survives is three
  literal copies of one `Quotient.mk` and the absence of any packaging of the
  period map as an equivariant map; and a bespoke Prop class over a data parameter
  is hard to justify under `proposition-classes.md` rule 3.
- *Adoption and cost* — **refuted** (single dissent).  No consumer exists
  (`centralCharge_equivariant` has exactly three occurrences, all inside its own
  file); the named homeomorphs are dead code already reaching the Mathlib root by
  definition; the orbit spaces are already abbrevs; the two `chargeAddEquiv`s are
  post- and pre-composition and share only a codomain type; and the proposed class
  fails `proposition-classes.md` rules 2 and 3 outright.  The salvageable sliver —
  making `orbitMap` generic as `ComponentOrbitSpace` already is, and deleting the
  three unused aliases — is recorded above.

#### dg-03 — Two owners of "functorial dg cone ⇒ functor to distinguished triangles"

**Kind** duplicate-parent (corrected to missing-link) · **Impact** medium
(adoption lens refuted) · **Confidence** 0.75

**Declarations.**  `ConeData.coneMorphism`
(`DGEnhancement/H0/NaturalTransformationCone.lean:103`),
`ConeData.triangleFunctor` (`:151`), `triangleNatTrans`/`compareIso` (`:312`);
`DGCategory.ConePresentation` (`DGCategory/Pretriangulated/ConeCategory.lean:38`)
and `ConePresentation.Hom` (`:57`);
`H0.coneTriangleFunctor` (`DGEnhancement/H0/ConeFunctor.lean:121`);
`Enhancement.coneTriangleFunctor` (`:187`);
`Correspondence.kernelConeTransformTriangleFunctor` (`FourierMukai/KernelCone.lean:49`);
`CounitKernelConeData.presentation` (`FourierMukai/CounitKernel.lean:90`);
`Z0.toH0` (`DGCategory/H0.lean:348`).

**Parent structure.**  Both are "chosen cone presentation ↦ cone triangle,
`IsConeOf.Morphism` ↦ triangle morphism".  `ConeData.coneMorphism` is literally a
`ConePresentation.Hom` between the objectwise presentations, and both routes bottom
out in the same `toTriangleMorphism`.  The Fourier–Mukai lane can only be fed
`ConePresentation`s; the spherical lane can only be fed nat-trans-shaped data.

**Proposed root** (corrected: a factorisation theorem, not a re-definition).
`ConeData.presentationFunctor : Z0 C ⥤ ConePresentation D` plus
`Z0.toH0 C ⋙ K.triangleFunctor hα = K.presentationFunctor hα ⋙ H0.coneTriangleFunctor D`,
in `H0/NaturalTransformationCone.lean` (adding the `H0/ConeFunctor` import).

**Projections.**  `triangleFunctor` keeps its definition and gains the
factorisation; `triangleNatTrans`/`compareIso` become whiskerings;
`CounitKernelConeData.presentation` is unchanged, being the object-level case.

**Future examples covered.**  Cones of kernel morphisms natural in a parameter
(families of Fourier–Mukai twists over a base); functorial cones of `ε : F ⟶ 𝟭`
read in an enhanced category rather than in `H0 D`.

**Verdicts.**
- *Mathematics* — survives.  Verified that both routes end in the same
  `toTriangleMorphism`, whose three components are exactly what `triangleFunctor`
  writes into `Triangle.homMk`, so the factorisation is true and closes by
  `Triangle.hom_ext`; the descent caveat (no functor out of `H0 C`, because a
  `ConePresentation.Hom` carries a cocycle and a homotopy) is correctly recorded.
  **Correction applied:** `presentationFunctor`'s laws need `ConePresentation.Hom.ext`,
  which also demands equality of the chosen homotopy — available here because
  `coneMorphism` has `homotopy = 0`.
- *Repository* — survives.  Every citation real; the consumer split is verified,
  and no functor into `ConePresentation` exists anywhere.  **Correction applied:**
  the kind is **missing-link**, not duplicate-parent — `H0.coneTriangleFunctor`
  *is* the root and `ConeData.triangleFunctor` is its descent along `Z0.toH0`, so
  the deliverable is `presentationFunctor` plus the factorisation.
- *Adoption and cost* — **refuted** (single dissent).  The shared root already
  exists and both sides already use it — `H0.coneTriangle` plus
  `toTriangleMorphism` with its `_id`/`_comp` laws — so the only duplicated content
  is `map_id`/`map_comp`, six lines; and `presentationFunctor` has exactly one
  adopter, since `CounitKernelConeData.presentation` is an object, not a family.
  The surviving deliverable is the factorisation lemma, which is what is proposed.

#### dg-04 — `FamilyCommShift` stores by hand what the pointwise shift packages

**Kind** existing-root-unused · **Impact** medium (repository lens rates high) ·
**Confidence** 0.8

**Declarations.**  `functorCategoryHasShift` (`CategoryTheory/Shift/FunctorCategory.lean:90`),
`evaluationCommShift` (`:131`), `evaluationCommShift_iso_hom_app` (`:161`);
`Functor.FamilyCommShift` (`Triangulated/ExactFunctorFamily.lean:57`) with its
per-object `commShift` and separate `commShift_naturality`;
`Functor.ExactFamily` (`:127`), `ExactFamily.evaluationCommShift` (`:139`);
`Functor.ExactBifunctor` (`:220`);
`Correspondence.KernelEvaluationExact` (`FourierMukai/KernelCone.lean:103`).

**Parent structure.**  With the pointwise shift on `X ⥤ Y`, a family commuting
with shifts is **one** isomorphism with Mathlib's zero and add laws, whose
components at `E` are automatically natural, and evaluation commutes with the shift
on the nose.  `FamilyCommShift` instead stores the evaluated instances one per `E`
plus an extra naturality axiom **and no zero or add law**, and `postShift` is
character-for-character `functorCategoryShiftMkCore.F`.  The root file's own
docstring says ExactFunctorFamily "stores that datum by hand" and "is what such a
family should be built on instead", and that "the rewiring is not done here".

**Proposed root.**  Existing: `F.CommShift ℤ` for `functorCategoryHasShift`, plus
`FamilyCommShift.ofCommShift`/`toCommShift` in `ExactFunctorFamily.lean`.

**Projections.**  `commShift E` becomes `inferInstance` — **verified by
compilation**; `commShift_naturality` becomes naturality of the single iso's
components; `ExactFamily` extends `F.CommShift ℤ` plus fiberwise triangulatedness;
`evaluationCommShift_iso_hom_app` supplies the `rfl` comparison consumers need.

**Future examples covered.**  Kernel evaluation of geometric correspondences;
monoidal and tensor bifunctors; families of twists over a parameter category.

**Verdicts.**
- *Mathematics* — survives.  Both directions verified: `F.CommShift ℤ` plus
  `evaluationCommShift` plus Mathlib's composition gives the per-`E` field, and the
  per-`E` zero/add laws transfer back because a natural iso in `X ⥤ Y` is determined
  by its components; `postShift` confirmed definitionally equal to the shift
  functor, so `shiftIso` *is* the missing `commShiftIso` minus its two laws.
  **Corrections applied:** `ExactFamily.evaluationCommShift` is a parallel name, not
  a clash; the ⇒ direction needs a short joint-faithfulness argument, so the abbrev
  is a re-rooting with one proof obligation; `ExactFunctorFamily.lean` currently
  imports only Mathlib, so the rewiring adds its first repository import.
- *Repository* — rates **high** and survives.  Every citation exact, and the
  strongest datum is one the surveyor did not report: `grep -rl 'Shift.FunctorCategory'`
  returns a single file, the umbrella — the root has **zero** real consumers, so
  this is an existing root built and never imported, while the thing it was written
  for reimplements it two directories away.  **Correction applied:** none to the
  substance; note only that the rewiring adds the first intra-repository import to
  `ExactFunctorFamily.lean`, crossing no layering edge and creating no cycle.
- *Adoption and cost* — survives, with the repository's own documentation as the
  finding.  **Corrections applied:** `FamilyCommShift` is strictly **weaker** than
  `F.CommShift ℤ` (no zero/add law), so every inhabitant acquires two new coherence
  obligations — the right direction, but work, not an abbrev swap;
  `ExactFamily.evaluationCommShift` is not a name clash; migration is 5 files plus
  the `mapTriangle` comparison lemma the docstring names as the blocker.

#### dg-05 — Three unlinked shift packagings for the shift of a dg functor

**Kind** duplicate-parent · **Impact** medium · **Confidence** 0.7

**Declarations.**  `DGFunctor.z0HasShift`
(`DGCategory/Pretriangulated/FunctorCategoryShift.lean:345`, with no consumer
outside its own file);
`DGFunctor.shiftedFunctor` (`Pretriangulated/FunctorCategory.lean:158`) and
`shiftedFunctorWitness` (`:251`);
`isPretriangulated_dgFunctor` (`:774`);
`H0.hasShift` (`DGEnhancement/H0/Shift.lean:325`) and `H0.shiftObj` (`:73`,
`Classical.choice`);
`functorCategoryHasShift` (`CategoryTheory/Shift/FunctorCategory.lean:90`);
`DGFunctor.h0Comparison` (`DGCategory/FunctorCategoryH0.lean:92`);
`Z0.toH0` (`DGCategory/H0.lean:348`);
`shiftedFunctor_h0_obj`/`_map` (`H0/ShiftedFunctor.lean:63`, `:72`);
`Cdg.toH0CommShift` (`HomotopyCategory/DGEnhancement/CommShift.lean:186`).

**Parent structure.**  One shift, `F ↦ F[n]` with the Koszul sign, packaged three
times — on `Z⁰(DGFunctor C D)`, on `H⁰(DGFunctor C D)` through the generic
`H0.hasShift` whose `shiftObj` is `Classical.choice`, and pointwise on
`H⁰C ⥤ H⁰D` — with none of them linked by Mathlib's root for such comparisons,
`Functor.CommShift`.  `ShiftedFunctor.lean:63,72` proves by hand exactly the object
and morphism components of the missing `CommShift`.

**Proposed root.**  `H0.commShiftOfWitnesses` (generic, in `H0/Shift.lean`) plus
the two instances in `H0/ShiftedFunctor.lean`.

**Projections.**  `Cdg.toH0CommShift` becomes `commShiftOfWitnesses` applied to
the three model lemmas it already consumes; `shiftedFunctor_h0_obj`/`_map` become
`rfl`-components of the strict `CommShift`; `z0HasShift` gains its first consumer.

**Future examples covered.**  Any further dg model with its own shift (`K^dg(A)`,
`Perf(k)`, the opposite dg category) needing a `CommShift` into `H0`; the cotwist
as a shifted dg functor; uniqueness-of-enhancement statements comparing shifts
across a quasi-equivalence.

**Verdicts.**
- *Mathematics* — survives.  Every citation verified, including that `H0.shiftObj`
  is `(exists_shift X n).choose` and therefore only propositionally the model
  shift; the strictness of the `(a)→(c)` comparison confirmed; the proposed generic
  lemma's three hypotheses are exactly the three model lemmas `Cdg.toH0CommShift`
  already consumes.  **Corrections applied:** the `EnhancedFunctorH0` line numbers
  are `:131`/`:191` and are proved by `rfl`; the `(a)→(b)` comparison is **not**
  simply the `Cdg` argument re-run, because the `Z⁰` side is built from bespoke
  `shiftedFunctorZero`/`Add` isos rather than the `IsShiftBy` calculus, so it must
  first be re-expressed through `IsShiftBy.compare_unique` — an extra step the
  finding does not budget.
- *Repository* — survives.  All eleven citations exact; `grep` confirms
  `z0HasShift` has zero consumers.  **Corrections applied:** packaging (b) is
  weaker than presented — nothing in the tree *mentions*
  `HasShift (H0 (DGFunctor C D)) ℤ`, it is only synthesisable, so keep it as the
  recorded hazard and make the actionable claim the strict `(a)→(c)` link;
  the instance needs imports that do not exist today, so it is not an in-place edit;
  `H0.commShiftOfWitnesses` is a `def`, so the single-instantiation gate does not
  see it.
- *Adoption and cost* — survives.  The second leaf exists and was found:
  `DGFunctor.shiftedFunctorWitness` is the exact analogue of `Cdg.isShiftBy`, and
  both categories' `exists_shift` field is `⟨model, ⟨that witness⟩⟩`; `z0HasShift`
  confirmed to have zero consumers, so packaging (a) is dead weight that would gain
  its first consumer.  **Corrections applied:** `shiftedFunctor_h0_obj`/`_map`
  compare (a) with the **pointwise** shift, not with (b), and they are not yet a
  `CommShift` — the missing content is `commShiftIso_zero`/`_add` against three
  different packagings, which is the actual cost; the file states outright that it
  deliberately proves no equality of functors, which is compatible but must be
  phrased as "the iso is identity-componented".

#### triang-04 — Four spellings of "φ intertwines two biadditive forms"

**Kind** same-equation-two-names · **Impact** medium (adoption lens rates low) ·
**Confidence** 0.7

**Declarations.**  `K₀.EulerForm.Preserves`
(`Triangulated/GrothendieckGroup/EulerForm.lean:93`);
`Numerical.PreservesEuler` (`Numerical/GrothendieckGroup/Realization.lean:127`);
`Numerical.IsRiemannRoch` (`Numerical/GrothendieckGroup/EulerTransfer.lean:106`);
`MukaiRealization.chi_eq_neg_pairing` (`SphericalTwist/Mukai.lean:112`);
`preservesEuler_of_descends` (`EulerTransfer.lean:116`);
Mathlib `LinearMap.BilinForm.Isometry`
(`Mathlib/LinearAlgebra/BilinearForm/Isometry.lean:42`).

**Parent equation.**  `E' (φ x) (φ y) = ι (E x y)` for a group map `φ` and a
scalar map `ι`.  The four instances are `ι = id`, `ι = id`, `ι = Int.castAddHom ℚ`,
and `ι = −id`.  `preservesEuler_of_descends` is the composition law for such
morphisms along a commuting square, proved for one instantiation.

**Proposed root** (corrected placement and value ring).
`LinearAlgebra/BilinearForm/Hom.lean`, namespace `LinearMap.BilinForm` — Mathlib's
definition site for a form-preserving map, which the repository already extends at
`Numerical/GrothendieckGroup/Realization.lean:218`.  `IsBiformHom E E' φ ι`, with
`comp` and `of_surjective_square`.

**Projections.**  `Preserves` and `PreservesEuler` at `ι = id`;
`IsRiemannRoch` at `ι = Int.castAddHom ℚ` (value ring `ℚ`, since `chi₂` is
ℚ-valued); `chi_eq_neg_pairing` as a field at `ι = −id`;
`preservesEuler_of_descends` as `of_surjective_square`.

**Future examples covered.**  Mukai-lattice isometries induced by Fourier–Mukai
equivalences of K3s; χ-preservation for the tilt-restriction functor into
`Ku(cubic threefold)` and for the `A₂`-lattice embedding into the Mukai lattice of
`Ku(cubic fourfold)`; the numerical quotient `N(X) = K₀/χ-radical`; Euler-form
preservation by autoequivalences acting on Stab.

**Verdicts.**
- *Mathematics* — survives.  All four spellings verified to be the one equation at
  four `(φ, ι)`, and the `−id` slot confirmed load-bearing.  **Corrections
  applied:** `V.chi₂` is a **bare function**, not a bundled biadditive map, so the
  two `PreservesEuler`/`IsRiemannRoch` leaves cannot be `abbrev`s until `chi₂` is
  proved biadditive — or the root must be typed on bare functions; and
  `IsRiemannRoch` is written in the opposite orientation, so a literal `abbrev`
  fails.
- *Repository* — survives at medium.  All six citations verified, including the
  ℤ-vs-ℚ codomain mismatch that forces the `ι` slot, and the fact that one leaf
  already reaches Mathlib's `Isometry`.  **Corrections applied:** the placement
  above (namespace `LinearMap.BilinForm`, not `AddMonoidHom` under `Algebra/Group/`);
  `PreservesEuler` cannot be an `abbrev` for the bare-function reason; the kind is
  part existing-root-unused (Mathlib's `Isometry` covers `ι = id`) and part
  genuinely missing ι-twisted generalization.
- *Adoption and cost* — survives at **low**.  The blocker the surveyor named is
  already solved in-tree: `chi₂` is bundled as `eulerPairing`
  (`GrothendieckGroup/Lattice.lean:48`), so four leaves reach the root and the leaf
  names survive as abbrevs.  **Corrections applied:** the sketch's value ring is
  wrong (ℚ, not `A`); the honest reuse is one shared proof
  (`preservesEuler_of_descends`, five lines) plus four renamings, which clears the
  thin-abstraction bar only because the four leaves spell the same equation with
  four names and three sign conventions; **drop** the Mathlib `Isometry`
  re-rooting, which is the `ι = id` single-ring linear case and is already used
  where it applies.

#### triang-05 — `HomFiniteBounded` restates `HomFinite`

**Kind** leaf-copies-root · **Impact** medium · **Confidence** 0.85

**Declarations.**  `SerreFunctor.HomFinite` (`Triangulated/SerreFunctor/Basic.lean:62`);
`Triangulated.HomFiniteBounded` (`Triangulated/GrothendieckGroup/EulerForm.lean:128`);
`instHomFiniteBoundedBounded` (`GrothendieckGroup/HomFiniteWitness.lean:161`);
`Duality.Serre.BilinearData.extFinite` (`Duality/Serre/Bilinear.lean:112`).

**Parent structure.**  `HomFinite` is `∀ A B, Module.Finite k (A ⟶ B)`;
`HomFiniteBounded.finite` is `∀ X Y i, Module.Finite k (X ⟶ Y⟦i⟧)` — the same
proposition, since `Y⟦i⟧` is an object — plus the finite-Ext-amplitude clause.
`EulerForm.lean` does not import `SerreFunctor/Basic` and there is no instance in
either direction, so a category with `[HomFiniteBounded k C]` cannot use
`SerreFunctorData.finrank_hom_eq` or `no_exceptional_of_serre_iso_shift`, which is
exactly the combination the spherical and Enriques lanes need.

**Proposed root** (corrected: relocate, and drop one leaf).
`CategoryTheory/Linear/HomFinite.lean` at `[DivisionRing k]`, with
`HomFiniteBounded extends HomFinite`.

**Projections.**  `HomFiniteBounded` gains the parent and its `finite` field
becomes inherited; `instHomFiniteBoundedBounded` also yields `HomFinite k (Kᵇ C)`
for free; `finrank_hom_eq` and `no_exceptional_of_serre_iso_shift` become
dischargeable from `[HomFiniteBounded k C]`.

**Future examples covered.**  Proper dg and triangulated categories — Kuznetsov
components are proper, and "smooth and proper" is the standing hypothesis for Serre
functors and Bridgeland stability on `Ku(X)`; `Dᵇ(Coh X)` for proper `X` of any
dimension, with `D(Qcoh X)` as the counterexample; Ext-finite hearts of bounded
t-structures.

**Verdicts.**
- *Mathematics* — survives.  Both directions verified (root ⇒ leaf by
  `B := Y⟦i⟧`; leaf ⇒ root at `i = 0` through `Linear.homCongr` and
  `shiftFunctorZero`), so `extends` loses nothing.  **Corrections applied:**
  `BilinearData.extFinite` is **not** an instance of the root and cannot be made
  one at the pin — `extSpace` is client-supplied data whose only link to the derived
  category is an isomorphism with Mathlib's `Abelian.Ext` in `AddCommGrpCat`;
  and the `Field`/`DivisionRing` mismatch means the root must sit at `DivisionRing`
  and the relocation is part of the fix.
- *Repository* — survives.  Verified in full, including that
  `instHomFiniteBoundedBounded`'s own hypothesis is the *unbundled* `HomFinite`
  written out because the bundled class is not in scope.  **Correction applied:**
  the move renames `CategoryTheory.SerreFunctor.HomFinite`, and
  `single_instantiation_baseline.txt` carries the **old** name, so the baseline row
  must be edited in the same change or the gate fires on the new name.
- *Adoption and cost* — survives; `extends` is the honest shape and is one line.
  **Corrections applied:** drop `extFinite` for the reason above; the `Field` in
  `SerreFunctor/Basic.lean` is needed for `Module.Dual` in `SerreFunctorData` and
  must stay there, so moving the class is a genuine one-declaration rename and
  should be scheduled with the `RestateHistoricalNames` bridge.

#### triang-06 — The Serre-shift clause `S^m ≅ [n]` has no root

**Kind** missing-root · **Impact** medium · **Confidence** 0.75

**Declarations.**  `SerreFunctor.IsSphericalObject.serre_shift`
(`SerreFunctor/Objects.lean:47`) and `IsPseudoprojectiveObject.serre_shift` (`:56`);
`EnriquesCategoryData.squareShift` (`SerreFunctor/Enriques.lean:41`);
`no_exceptional_of_serre_iso_shift` (`Enriques.lean:79`, hypothesis at `:81`);
`SerreCompatibleEquivalence.mapSpherical`/`mapPseudoprojective`
(`SerreFunctor/Transport.lean:201`, `:218`).

**Parent structure.**  `S^m ≅ [n]` — fractional Calabi–Yau of dimension `n/m` —
and its objectwise shadow `S(E) ≅ E⟦n⟧`.  The categorical form is stated twice with
different `m` (as a structure field at `m = 2`, as a theorem hypothesis at `m = 1`),
the objectwise form twice as identical fields, and transported twice with the
**byte-identical** three-iso composite.

**Proposed root.**  `SerreFunctor/CalabiYau.lean`: `IsFractionalCalabiYau D m n` and
`IsCalabiYauObject D n E`, with `IsCalabiYauObject.map` proved once.

**Projections.**  The two `serre_shift` fields become fields of type
`IsCalabiYauObject D n E`; `squareShift` becomes `IsFractionalCalabiYau serre 2 _`;
`no_exceptional_of_serre_iso_shift`'s hypothesis becomes `IsFractionalCalabiYau D 1 n`;
`mapSpherical`/`mapPseudoprojective` both call one `IsCalabiYauObject.map`;
`Surface/Spherical.lean`'s omitted clause becomes a theorem rather than an omission.

**Future examples covered.**  `Ku(cubic fourfold)` `S ≅ [2]`;
`Ku(cubic threefold)` `S³ ≅ [5]`; CY threefolds and fourfolds; Enriques categories
`S² ≅ [4]`; CY objects in categories that are not CY.

**Verdicts.**
- *Mathematics* — survives.  All sites verified, the transport composite confirmed
  byte-identical, and the parent's `m = 1` consequence checked.  **Corrections
  applied:** `quartic double solid` is mislabelled in the future-examples list — its
  Kuznetsov component is fractional CY of dimension `5/3`, i.e. `S³ ≅ [5]`, not
  `S² ≅ [4]` (which is the Enriques case the tree already has); `iterate` as sketched
  does not give `S ⋙ S` syntactically, so the Enriques edge needs an explicit `Iso`
  bridge, not `rfl`.
- *Repository* — survives.  All six citations real, including the two identical
  `serre_shift` fields and the verbatim transport; no such root exists, and Mathlib
  has no Serre functor at all at this pin.  **Corrections applied:** the surveyor's
  own risk note is load-bearing and must be honoured — `SerreFunctorData` is a
  **right** Serre functor only, so `IsFractionalCalabiYau` silently upgrades it to
  an equivalence, and the predicate should be stated against `SerreCategoryData` or
  the upgrade recorded explicitly; the `iterate` mismatch above.
- *Adoption and cost* — survives on the objectwise half, where the two leaves are:
  the field is identical twice and the transport proof is character-for-character
  the same.  **Corrections applied:** `IsFractionalCalabiYau` has only **one**
  declaration-level leaf (`squareShift`), the `m = 1` occurrence being a theorem
  hypothesis, so it is justified by the linking theorem and the named future
  inhabitants rather than by deduplication — say so, or a reviewer will read the
  finding as claiming two; do not promise `rfl` for the Enriques leaf.

#### triang-07 — Objectwise cone of an adjunction counit, at three levels

**Kind** missing-root · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.6

**Declarations.**  `ObjectProperty.RightProjectionData.CounitTriangle`
(`SemiorthogonalDecomposition/Mutation.lean:59`) and `counitTriangle` (`:79`);
`DGAdjunction.CounitConeData` (`DGCategory/Pretriangulated/AdjunctionCone.lean:40`);
`EnhancedAdjunctionCones.twist` (`SphericalTwist/EnhancedFunctor.lean:48`) and
`twistTriangleFunctor` (`EnhancedFunctorH0.lean:84`);
`FourierMukai.CounitKernelConeData` (`FourierMukai/CounitKernel.lean:59`).

**Parent structure.**  For `L ⊣ R` in a pretriangulated category, the distinguished
triangle `L R X ⟶ X ⟶ C X ⟶ (L R X)⟦1⟧` whose first map is `counit.app X`.  The
SOD mutation triangle is that triangle; the dg twist is its functorial dg
refinement whose `H⁰` values are such triangles; `CounitKernelConeData` is the same
cone when the adjunction is kernel-presented.  At the triangulated level there is
no `Adjunction.CounitTriangle`, and the SOD copy records `mutation_mem` as a
**field** although `counitTriangle` proves it.

**Proposed root.**  `CategoryTheory/Triangulated/Adjunction/CounitTriangle.lean`:
`Adjunction.CounitTriangle` plus `chosenCounitTriangle`.

**Projections.**  The SOD carrier becomes a subtype with `mutation_mem` as the
refinement; the dg twist's values become `CounitTriangle` of the `H⁰` adjunction;
`CounitKernelConeData.triangleInSource` likewise; the dual `UnitTriangle` covers the
cotwist and right mutation.

**Future examples covered.**  Spherical twists by objects of `Ku(cubic fourfold)`
and their action on Stab; left and right mutations through exceptional objects;
Fourier–Mukai twists for kernel-presented adjunctions; Kuznetsov's Serre-functor
formula, which needs the triangle at the triangulated level.

**Verdicts.**
- *Mathematics* — survives.  The declarations and the mathematics check out, and
  `Q.projectObj X` is `P.ι.obj (Q.project X)`, i.e. exactly `L.obj (R.obj X)`, so
  the SOD leaf fits the root as a subtype with no comparison iso.  **Corrections
  applied:** the `CounitKernelConeData` projection is a **theorem**, not a
  restatement — its `arrow` lives between enhancement lifts and its identification
  with the counit holds only modulo three isomorphisms; and the impact is generous,
  since `distinguished_cocone_triangle` already produces the chosen triangle in one
  line, so the root buys a shared name and shared lemmas.
- *Repository* — survives.  Five of six citations exact; the SOD structure does
  hard-code the adjunction shape and discharge `mutation_mem` at `:102`; nothing in
  `DerivedAlgGeo` or Mathlib provides a chosen distinguished triangle on
  `adj.counit.app X`.  **Corrections applied:** `EnhancedAdjunctionCones.twist` is
  at `EnhancedFunctor.lean:48`, not `:50`; `CounitConeData` is an `abbrev` of
  `ConeData`, so calling it "the dg root" overstates it; and the new structure would
  have one producer, since the SOD leaf becomes a `Subtype` whose head is not
  `CounitTriangle`, so the change needs a second producer or a baseline entry.
- *Adoption and cost* — **refuted** (single dissent).  The root is a four-field
  record of `distinguished_cocone_triangle`; `CounitConeData` is a dg functor whose
  only bridge is one-way and needs `[IsPretriangulated B]`; and
  `CounitKernelConeData` contains no counit map at all, only an `arrow` between
  enhancement lifts with `transform_arrow` as the identification.  The dissent
  points instead at a **real** duplicate in the same lane, recorded in §5:
  `counitTriangle` and `IsRightAdmissible.exists_distTriang_mem_rightOrthogonal`
  construct the same triangle by the same proof, once in chosen-data form and once
  in ∃-form, with the dual repeating it a third time.

#### geometry-derived-04 — Six one-field wrappers around `Slicing.PreimageData`

**Kind** leaf-copies-root · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.7

**Declarations.**  `DerivedPullbackPreimageData` and `DerivedPullbackInducingData`
(`DerivedCategory/Stability/DerivedPullback.lean:46`, `:120`);
`BoundedCoherentPullbackPreimageData`/`InducingData`
(`Stability/BoundedCoherentBaseChange.lean:58`, `:154`);
`BoundedCoherentPushforwardPreimageData`/`InducingData`
(`Stability/BoundedCoherentPullback.lean:102`, `:193`);
`Slicing.PreimageData` (`Phase/Transfer/Basic.lean:84`);
`SchemeTriangulatedFiberFamily` (`DerivedCategory/Families/Scheme.lean:31`);
`BoundedCoherentDerivedRealization` (`BoundedCoherentBaseChange.lean:193`).

**Parent structure.**  Each of the six has exactly one field —
`preimageData : s.PreimageData Φ` or `inducedTStructures : s.InducedTStructures Φ` —
at one of three functors, and every companion (`preimage`, `identity`, `comp`,
`preimage_identity`, `preimage_comp`, `toPreimageData`) is re-proved per functor
from that functor's unit and compositor.  The pushforward docstring confirms the
copy is deliberate.

**Proposed root** (corrected: use the existing family-level root).
`FiberPreStabilityBaseChangeData` (`Families/PreStabilityBaseChange.lean:36`)
already carries `preimageData : ∀ {s t} (f : s ⟶ t), (sigma s).slicing.PreimageData (F.pull f)`,
with `preimageData_comp` (`:77`), `preimageData_pullComp` (`:89`),
`preimage_pullComp` (`:93`) and `constant` (`:155`).  The deliverable is to delete
the six wrappers and let the leaves use `Slicing.PreimageData` directly, obtaining
identity and composition from `preimageData_pullComp`.

**Projections.**  The three `PreimageData` wrappers and three `InducingData`
wrappers disappear; the four pullback-of-stability definitions in
`BoundedCoherentPushforward.lean` and `BoundedCoherentPullback.lean` are unchanged
consumers, now of one structure.

**Future examples covered.**  Fourier–Mukai action on stability conditions as
preimage data along `Φ_K`; perfect-fiber and residue-fiber pullback preimage data;
pullback of stability along Kuznetsov-component inclusions.

**Verdicts.**
- *Mathematics* — survives.  All six are single-field wrappers and the companions
  are re-derived per functor from the same two generic moves.  **Correction
  applied:** the variance risk the finding raises is an artifact of its own
  packaging — `Slicing.PreimageData` is already stated for an arbitrary functor, so
  the covariant pushforward case is inside its scope and no opposite-category trick
  is needed; the exact-pullback leaf, however, lives over the wide subcategory of
  morphisms with exact pullback, which `TriangulatedFiberFamily` cannot express.
- *Repository* — survives.  The six wrappers and the docstring admission verified.
  **Correction applied:** the proposed root **already exists** in
  `PreStabilityBaseChange.lean`, and the geometric side is already wired to it
  through `GeometricPreStabilityBaseChangeData`; do not create a new file under
  `Triangulated/Families/`, which `layers.md:135,144` orders *before*
  `StabilityCondition`, so a `Slicing`-valued structure there inverts the direction.
- *Adoption and cost* — **refuted** (single dissent).  The leaves do not copy the
  root — each holds `s.PreimageData Φ` as its single field and never restates
  `hom_vanishing`/`hn_exists` — and the generic laws are already generic and already
  consumed; the proposed root is itself a one-field wrapper; and **zero** existing
  leaves could reach it, since the only inhabitant of `TriangulatedFiberFamily`
  anywhere is `constant`, and the exact-pullback family cannot exist over all of
  `Over S`.  The surviving deliverable is the two generic transport lemmas above.

#### lattices-04 — The Gram determinant of a pair, defined three times

**Kind** missing-root · **Impact** medium · **Confidence** 0.8

**Declarations.**  `Mukai.gram` (`Lattice/Mukai/RankTwo.lean:43`), `gram_lincomb`
(`:86`), `IsHyperbolicPair` (`:100`), `pairSpan` (`:197`);
`PeriodDomain.pairSpan` (`QuadraticForm/Orientation.lean:61`), `pairingDet` (`:71`),
`pairingDet_ne_zero` (`:136`);
`pairingDet_ref_comb` (`QuadraticForm/OrientationCocycle.lean:74`),
`pairingDet_self` (`:81`);
`isPositivePair_iff` (`QuadraticForm/PositivePairOpen.lean:46`).

**Parent structure.**  `det₂ B (x₀,y₀) (x,y) = B x₀ x · B y₀ y − B x₀ y · B y₀ x`
over any commutative ring, with `gram B v w := det₂ B (v,w) (v,w)`.  `Mukai.gram`
is `gram (pairingBilin b)`; `pairingDet` is `det₂ Q.polarBilin` verbatim;
`pairingDet_self = 4 Q x Q y − polar²` is `gram (polar Q)` since `polar x x = 2 Q x`;
`isPositivePair_iff` is `0 < B x x ∧ 0 < gram`, and `IsHyperbolicPair` is
`gram < 0` — the two signs of one discriminant.  The transformation law is proved
twice, the two-slot version following from the one-slot version applied twice.

**Proposed root.**  `LinearAlgebra/BilinearForm/GramDet.lean`, namespace
`LinearMap.BilinForm`: `det₂`, `gram`, `det₂_comb_left`/`_right`, `gram_comb`,
`det₂_swap`, plus the ordered-field `isPositivePair_iff`.

**Projections.**  `pairingDet Q = det₂ Q.polarBilin` — **`rfl`**;
`Mukai.gram b = gram (pairingBilin b)` by `simp; ring` under the symmetry every
call site already carries; `gram_lincomb := gram_comb`;
`pairingDet_ref_comb := det₂_comb_left`; `pairingDet_self := gram` plus
`polar_self = 2·Q`.

**Future examples covered.**  Hyperbolic rank-two sublattices in the cubic-fourfold
Mukai lattice for the Bayer–Macrì wall classification; orientation of positive
pairs in any period domain (Enriques, abelian surfaces) without re-deriving the
cocycle lemmas.

**Verdicts.**
- *Mathematics* — survives.  All five shapes confirmed, and the transformation law
  verified to be one lemma: `det₂` is bilinear and alternating in the first pair and
  symmetric between the pairs, so the one-slot law applied twice gives the squared
  factor.  **Correction applied:** the projection `Mukai.gram b = gram (pairingBilin b)`
  is **not** `rfl` — `Mukai.gram` squares `pairing v w` while `det₂` produces
  `pairing v w * pairing w v` — so it is a theorem needing `hb`; conversely
  `gram_comb` needs **no** symmetry, so state it unconditionally.
- *Repository* — survives.  All ten citations real; no Gram-determinant-of-a-pair
  root exists in Mathlib or in the tree; placement matches Tier 1.  **Correction
  applied:** the `pairSpan` unification is a **migration**, not a projection —
  `Mukai.pairSpan` is a `Set` of ℤ-combinations while `PeriodDomain.pairSpan` is a
  `Submodule ℝ`, so replacing the first changes its type and every
  `mem_pairSpan_*` consumer.
- *Adoption and cost* — survives.  Both projections compiled, the ℝ leaf by `rfl`;
  cost is 4 files plus one new module, no rename, no baseline entry.  **Correction
  applied:** do **not** bundle the `pairSpan` merge into this change — the ℤ side is
  consumed through explicit coefficient witnesses that `Submodule.mem_span_pair`
  would turn into rewrites; and the root must not name either sign.

#### lattices-05 — "Self-pairing = c" bound to specific carriers four times

**Kind** same-equation-two-names · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.8

**Declarations.**  `Mukai.IsSpherical` (`Lattice/Mukai/Basic.lean:188`),
`IsIsotropic` (`:191`);
`Wall.Spherical.IsSpherical` (`Walls/Spherical/Basic.lean:259`),
`isSpherical_map_iff` (`:398`);
`PeriodDomain.IsSphericalClass` (`QuadraticForm/PeriodDomain.lean:109`),
`isSphericalClass_iff_apply` (`:169`);
`IntegralLattice.IsIsotropicSequence` (`Lattice/IsotropicSequence.lean:76`);
`Mukai.isSphericalClass_extendMap` (`Mukai/IntegralBridge.lean:147`).

**Parent structure.**  `B v v = c`.  Sphericity is defined on three carriers, with
two comparison theorems whose only content is transport along a form-preserving
map, and `IsotropicSequence.lean`'s docstring says explicitly that "Neither
existing isotropy notion is reusable here, which is why a new predicate appears at
all".

**Proposed root** (corrected).  Not a predicate but the **transport lemma**:
`HasSquare.map_ringHom` — a map respecting the forms carries square `c` to square
`σ(c)` — stated on the bilinear form, never on the quadratic form.

**Projections.**  `isSpherical_map_iff` and `isSphericalClass_extendMap` become
instances; the three sphericity predicates collapse to two (ℤ-pairing and
ℝ-polar) once lattices-01 lands.

**Future examples covered.**  Spherical and (−2)-classes in the Enriques lattice,
in `NS(X)` (Picard–Lefschetz), and in the cubic-fourfold Mukai lattice; roots of
ADE lattices (square 2) and exceptional classes (square −1) as the same predicate
at a different `c`.

**Verdicts.**
- *Mathematics* — survives.  The four sites verified as one predicate on three
  carriers, and the factor-of-two analysis confirmed load-bearing: the predicate
  must be stated on the bilinear form, since `realForm` is half the self-pairing.
  **Correction applied:** the isotropy leg is **wrong at this pin** —
  `LinearMap.BilinForm.IsOrtho` is marked `@[deprecated "Use `B x y = 0`."]`, so do
  not root isotropy on it; use the bare equation, as Mathlib instructs.
- *Repository* — survives.  All nine citations real, and the `IsotropicSequence`
  docstring says what the finding claims; the factor-of-two warning is the
  repository's own documented trap; `HasSquare` is a `def ... : Prop`, so
  `proposition-classes.md` does not bite.  **Corrections applied:** the deprecated
  `IsOrtho` again; and the load-bearing content is the transport lemmas, since the
  bare alias adds no mathematics.
- *Adoption and cost* — **refuted** (single dissent).  Both leaf projections are
  `Iff.rfl`, but the root is a record of the leaf's equation and upstream Mathlib
  has already adjudicated this question the other way by deprecating `IsOrtho` in
  favour of the bare equation; and the only non-thin content — the transport lemma —
  is entirely absorbed by lattices-01, since once the carriers are one the two
  predicates are one predicate.  Recorded as the dissent; the finding is folded into
  lattices-01 with one lemma kept.

#### lattices-06 — The hyperbolic plane and every Gram-matrix lattice, hand-built

**Kind** existing-root-unused · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.7

**Declarations.**  `IntegralLattice.hyperbolicPairing` (`Lattice/IsotropicSequence.lean:211`);
`Mukai.rankUnit`/`corankUnit` (`Lattice/Mukai/Basic.lean:233`, `:236`),
`pairing_outer` (`:241`), `pairing_rankUnit_corankUnit` (`:253`);
`Mukai.hyperbolicIncl` (`Mukai/RealFormSignature.lean:87`), `hyperbolic` (`:109`);
`SmoothQuadric.intersectionForm` (`Examples/Surface/SmoothQuadric.lean:434`);
`BlowUpPlaneWalls.intForm` (`Examples/Surface/BlowUpPlaneWalls.lean:204`);
`IntegralLattice.NumLattice` (`Lattice/Numerical/RankTwo.lean:27`);
Mathlib `Matrix.toBilin'` (`Mathlib/LinearAlgebra/Matrix/BilinearForm.lean:98`).

**Parent structure.**  A free lattice `Fin n → R` with the bilinear form of a Gram
matrix, which Mathlib already provides.  `U = !![0,1;1,0]` appears as
`hyperbolicPairing`, as the outer plane of every Mukai extension (`U(−1)`), and as
the quadric's `NS`; `diag(1,−1,−1)` is a fifth hand `mk₂`; the cubic-fourfold
`A₂ = !![2,−1;−1,2]` the mission asks a home for does not exist and would be a
sixth.

**Proposed root.**  Mathlib's `Matrix.toBilin'`, used directly.

**Projections.**  `hyperbolicPairing` and `BlowUpPlane.intForm` reach it —
both compiled; `rankUnit`/`corankUnit` become `outerIncl` images with
`pairing_outerIncl` carrying the `U(−1)` sign; `hyperbolicIncl` reaches it after a
carrier equivalence; `SmoothQuadric.intersectionForm` likewise.

**Future examples covered.**  `A₂ ⊂ H̃(Ku(X),ℤ)` for cubic fourfolds and its
orthogonal complement — the lane brief's explicit ask; `E₈(−1)`, `U ⊕ E₈(−1)`,
`U³ ⊕ E₈(−1)²` via `Matrix.fromBlocks`; any Picard lattice given by an intersection
matrix.

**Verdicts.**
- *Mathematics* — survives.  Five hand-built forms confirmed, `Matrix.toBilin'`
  verified **not** deprecated at the pin and stated over `CommSemiring`, and the
  `U(−1)` vs `U` sign confirmed: the Mukai outer plane is isometric to `U` via
  `(r,s) ↦ (r,−s)` but not equal, so the projection carries a minus sign.  `NumLattice`
  really does carry no form while its docstring names `K_num(Ku(X))`.
  **Correction applied:** do not restate `ofGram_apply`; it is Mathlib's
  `Matrix.toBilin'_apply` verbatim, so make `ofGram` a plain abbrev and re-export.
- *Repository* — survives.  All eleven citations verified and `Matrix.toBilin'`
  applies over ℤ, ℝ, `Fin 2`, `Fin 3`; placement under `LinearAlgebra/Lattice/` is
  Tier-1 correct.  **Correction applied:** split the file —
  `outerIncl`/`pairing_outerIncl` must live in `Lattice/Mukai/Basic.lean`, not in
  the generic Gram module, or the root would import a consumer.
- *Adoption and cost* — **refuted** (single dissent).  `ofGram` is a rename of a
  Mathlib definition; only two of the five leaves live on `Fin n → R` and can reach
  it at all; the Mukai outer plane is `U(−1)`, not `U`; no theorem transfers, since
  the only two facts anyone proves about the plane are on different sides; and
  `Matrix.toBilin'_apply` normalises to a double `Finset.sum`, heavier in every
  existing `simp` set than the current `mk₂` lambdas.  The narrow survivor — write
  the `A₂` lattice with `Matrix.toBilin'` plus `BilinForm.orthogonal` **when** the
  Kuznetsov lane needs it, with no alias and no retrofit — is recorded above.

#### lattices-07 — Signature is stated only at p = 2

**Kind** dimension-specific-should-be-n-fold · **Impact** medium · **Confidence** 0.75

**Declarations.**  `PeriodDomain.HasSignatureTwo` (`QuadraticForm/PeriodDomain.lean:100`);
`Mukai.hasSignatureTwo_realForm` (`Mukai/RealFormSignature.lean:241`, with the two
loose hypotheses at `:242-243`);
`QuadraticMap.sigPos_eq_add` (`QuadraticForm/SignatureAdditive.lean:202`);
`DivisorSpace.HodgeDefinite` (`Walls/Divisorial/Discriminant.lean:119`),
`HodgeIndex` (`:86`);
`sigPos_sigNeg_of_hodgeDefinite` (`Walls/Divisorial/Signature.lean:190`),
`hasSignatureTwo_of_hodgeDefinite` (`:263`).

**Parent structure.**  `sigPos Q = p ∧ sigNeg Q + p = finrank`.  `HasSignatureTwo`
is its `p = 2` instance; the `p = 1` instance — the Hodge index theorem on
`NS ⊗ ℝ` — is never named, and travels as two loose real equations across a
directory boundary.

**Proposed root** (corrected namespace and instances).
`QuadraticMap.HasSignature Q p` in `QuadraticForm/SignatureAdditive.lean` (or a new
`QuadraticForm/Signature.lean`), carrying `[FiniteDimensional ℝ M]`, with
`HasSignature.add` and `of_posDef_line_negDef_compl`.

**Projections.**  `HasSignatureTwo Q := HasSignature Q 2` — field-for-field, so
existing anonymous constructors and projections survive;
`hasSignatureTwo_realForm` restated as `HasSignature _ 1 → HasSignature _ 2`;
`sigPos_sigNeg_of_hodgeDefinite` becomes the named `p = 1` certificate;
`HodgeDefinite` stays a child with a forgetful theorem (it names a class `H`), and
`HodgeIndex` stays the strictly weaker inequality — a negative result
`Walls/Divisorial/Signature.lean` already records.

**Future examples covered.**  Cubic-fourfold `Ku(X)`, where the Mukai lattice has
signature `(2, 22)` and the algebraic part `(2, ρ)` is derived from `(1, ρ−1)` by
`HasSignature.add`; abelian surfaces, Enriques, and any `NS ⊗ ℝ`; higher-signature
period domains (hyperkähler `(3, b₂−3)`).

**Verdicts.**
- *Mathematics* — survives.  The `p = 1` pattern appears literally twice in the
  exact two-clause shape of the `p = 2` structure, and `HasSignature.add` needs no
  missing theorem: nondegeneracy of each summand follows from its own signature by
  the radical count.  **Corrections applied:** the root must carry
  `[FiniteDimensional ℝ M]`, or the clause degenerates; state `add` with the
  summands' signatures as the only hypotheses, since deriving nondegeneracy is part
  of the root's value.
- *Repository* — survives.  All seven citations real; `sigPos`/`sigNeg` are
  Mathlib's; the gate is satisfied because `HasSignatureTwo` is absent from the
  baseline, so it already has ≥ 2 inhabitants and `HasSignature` inherits them.
  **Correction applied:** the namespace must be `QuadraticMap`, not `QuadraticForm`
  — `QuadraticForm R M` is an abbreviation for `QuadraticMap R M R`, so the head
  symbol is `QuadraticMap` and the repository's own signature extensions already
  live there.
- *Adoption and cost* — survives.  Both leaves compiled, the `p = 2` one
  field-for-field; the gate passes with two producers on day one.  **Corrections
  applied:** `HasSignature.add` is thin, since `sigPos_eq_add` already returns both
  splits and is already called twice — scope the proposal to the structure plus the
  Hodge certificate; keep `HodgeDefinite` and `HodgeIndex` as children, never
  abbrevs.

#### lattices-08 — Saturation defined a second time beside the `Algebra` root

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.85

**Declarations.**  `ZeroChargeLattice.IsSaturated`
(`Weak/Support/Predicate/ZeroChargeLattice.lean:37`), `saturatedClosure` (`:41`),
`Quotient` (`:81`), `quotientCharge` (`:145`);
`AddSubgroup.saturation` (`Algebra/SaturatedQuotient.lean:23`),
`SaturatedQuotient` (`:69`), `saturatedQuotientLift` (`:101`);
`RelativeNumerical.Group` (`Algebra/RelativeNumerical/Basic.lean:56`), the
correctly rooted consumer;
Mathlib `AddSubmonoid.NSMulSaturated` (`Mathlib/GroupTheory/Subgroup/Saturated.lean:31`).

**Parent structure.**  The saturation of an additive subgroup and the torsion-free
quotient by it.  `ZeroChargeLattice.IsSaturated` is character-for-character
Mathlib's `NSMulSaturated`, including the strict-implicit binders;
`saturatedClosure S` equals `(AddSubgroup.closure S).saturation`; and the four
downstream declarations re-derive the `Algebra` root's four.  Decisively,
`ZeroChargeLattice.lean`'s import block is Mathlib-only — it does not import
`Algebra/SaturatedQuotient.lean` at all, so this is a second independent
construction, not an alias.

**Proposed root.**  Existing: `AddSubgroup.saturation` and `SaturatedQuotient`,
plus one theorem `saturation_closure_eq_sInf`.

**Projections.**  `IsSaturated = NSMulSaturated` — `Iff.rfl`, verified;
`saturatedClosure S = (closure S).saturation` — a six-line theorem from the four
lemmas the root already exports; `Quotient`, `quotient_isAddTorsionFree`,
`quotientClass`, `quotientCharge` become `SaturatedQuotient`,
`saturatedQuotient_isAddTorsionFree`, `saturatedQuotientMk`, `saturatedQuotientLift`.

**Future examples covered.**  Numerical Grothendieck groups
`K_num = K₀/(Euler radical)^sat` for every variety and for Kuznetsov components;
Néron–Severi as the saturated quotient of `Pic`; any "lattice = free quotient"
construction.

**Verdicts.**
- *Mathematics* — survives.  The predicate is character-for-character Mathlib's;
  the closure identity was proved by hand from lemmas the root already has; the
  contrast case verified (`RelativeNumerical.Group` reaches the root).
  **Correction applied:** the Mathlib predicate is on `AddSubmonoid`, so the
  projection is `H.toAddSubmonoid.NSMulSaturated` (membership coercion is `rfl`);
  do **not** route through `AddSubgroup.Saturated`, deprecated at this pin.
- *Repository* — survives.  All nine citations real and the duplication is
  character-for-character; the Mathlib-only import block is the decisive evidence;
  no layering problem, since the fix imports downward exactly as
  `RelativeNumerical` already does.  **Correction applied:** dot notation already
  resolves through the coercion in this tree, so the projection is `H.NSMulSaturated`.
- *Adoption and cost* — survives; the cleanest adoption of its lane, with the
  predicate `Iff.rfl` and the closure identity proved in six lines.  Cost is the
  smallest: 4 files plus one audit slice, zero `RestateHistoricalNames` hits, five
  declarations deleted outright.  **Correction applied:** keep the surveyor's own
  cost note — `sInf` and the explicit carrier are propositionally but not
  definitionally equal, so `Quotient S` becomes a different type and the two
  consumer files need reproving, not a drop-in `abbrev`.

#### surf-04 — `K3Surface.SphericalExtProfile` copies the categorical root

**Kind** leaf-copies-root · **Impact** medium (adoption lens rates medium with a
refuted Euler half) · **Confidence** 0.95

**Declarations.**  `K3Surface.SphericalExtProfile` (`Surface/Spherical.lean:143`),
`not_isZero` (`:167`), `finrank_end` (`:174`), `finrank_hom_eq_zero` (`:211`),
`selfEuler` (`:225`);
`K3Surface.euler` (`Surface/SphericalMukai.lean:74`);
`SphericalExtProfile.isSphericalObject` (`Surface/SphericalCategorical.lean:48`);
`SphericalTwist.IsSphericalObject` (`SphericalTwist/Basic.lean:60`);
`SerreFunctor.SphericalExtProfile` (`SerreFunctor/Transport.lean:37`);
`SerreFunctor.IsSphericalObject` (`SerreFunctor/Objects.lean:39`);
`chiHom` (`GrothendieckGroup/EulerForm.lean:141`).

**Parent structure.**  One predicate, declared four times.  The geometric leaf is
field-for-field `SphericalTwist.IsSphericalObject k 2 E`, its own docstring says
"This is the `n = 2` case of `CategoryTheory.SerreFunctor.SphericalExtProfile`,
restated", and it re-proves `not_isZero`, `finrank_end` and `finrank_hom_eq_zero`
verbatim from `SphericalTwist/Basic.lean:77-89`.

**Proposed root.**  Existing: `SphericalTwist.IsSphericalObject`, which is
ℤ-indexed and therefore needs no cast.  `SerreFunctor.SphericalExtProfile` becomes
an abbrev of it; the K3 leaf becomes an abbrev at `(2 : ℤ)`.

**Projections.**  `K3Surface.SphericalExtProfile → IsSphericalObject k 2` —
compiled in both directions, so the `((2:ℕ):ℤ)` cast concern does not materialise;
`SphericalCategorical.isSphericalObject` becomes `id`; the three duplicated
consequence proofs are deleted.

**Future examples covered.**  `n`-spherical objects on CY `n`-folds with no new
geometric predicate; spherical objects in `Ku(cubic fourfold)`; the Enriques
3-spherical candidates, which already use the `SerreFunctor` spelling.

**Verdicts.**
- *Mathematics* — survives.  Both declarations read and found identical at `n = 2`;
  the generic structure takes no Serre functor, so the leaf's stated reason ("no
  Serre functor is available") is not an obstruction.  **Correction applied:** the
  finding names the **wrong parent** — there is a third declaration,
  `SphericalTwist.IsSphericalObject`, which is ℤ-indexed, so the abbrev drop-in the
  finding worried about **does** typecheck against it and the theorem fallback is
  unnecessary; the corrected tree is
  `SphericalTwist.IsSphericalObject ← SerreFunctor.SphericalExtProfile ← K3`.
  Also duplicated: the three consequence proofs, not only the structure.
- *Repository* — survives.  All citations real and the docstring says so.
  **Corrections applied:** the same third declaration, and the fact that the K3 leaf
  **already** reaches it field-for-field through
  `SphericalCategorical.lean:48-52`, so under contract option 5 the geometric leaf
  is already compliant and `leaf-copies-root` overstates it; what survives is a
  duplicate-parent between the two generic roots, with a missing three-line bridge;
  and projection 3 would **break CI**, since an `abbrev` type synonym is not counted
  as an inhabitant, so baseline line 18 must stay.
- *Adoption and cost* — survives.  The finding's own stated risk is **refuted by
  compilation** — both directions typecheck, so the cast is not an obstruction —
  and the "no Serre functor" excuse is contradicted by the tree itself, where the
  generic ℕ-indexed profile already has geometric consumers at `n = 3` on an
  Enriques residual category.  **Corrections applied:** the root is mis-identified
  (see above); cost includes 8 audit lines in
  `AlgebraicGeometryAudit/Core.lean:2236-2243`, which lose the field projections if
  the leaf becomes an abbrev.

#### surf-05 — Serre-duality Euler symmetry hardcoded at n = 2

**Kind** dimension-specific-should-be-n-fold · **Impact** medium (adoption lens
refuted) · **Confidence** 0.93

**Declarations.**  `Duality.Serre.Data.SurfacePicardSymmetry`
(`Duality/Serre/Cohomology.lean:310`);
`SurfaceLineBundleFamily` (`:319`) with its field `dimension_eq_two : n = 2` (`:324`);
`surface_eulerCharacteristic_symmetry` (`:298`);
`eulerCharacteristic_symmetry` (`:266`), the n-fold theorem;
`RiemannRoch.Surface.eulerPic_eq` (`RiemannRoch/Surface/Divisor.lean:100`).

**Parent equation.**  `χ(L) = (−1)ⁿ · χ(ω_X ⊗ L⁻¹)`.  `eulerCharacteristic_symmetry`
proves it for every `n`, three declarations earlier, by a `Fin.revPerm` reindexing
with no dimension hypothesis; the Picard-level packaging then fixes
`IntersectionContext D C 2` and states symmetry **without the sign**, and
`SurfaceLineBundleFamily` carries `dimension_eq_two` as a field only to invoke the
`n = 2` restatement.  `IntersectionContext` is itself `d`-parametric.

**Proposed root** (corrected: the minimal fix).  Delete the `dimension_eq_two`
field and have `toSurfacePicardSymmetry` call the already-n-general
`eulerCharacteristic_symmetry` directly, deleting
`surface_eulerCharacteristic_symmetry`.  Generalizing the *structure* to
`PicardSymmetry I K p` should wait for the first `n ≠ 2` leaf.

**Projections.**  With the minimal fix, all nine consumer positions in
`RiemannRoch/Surface/Divisor.lean` are untouched, because at `n = 2` the sign is
still absent.  Under the full generalization, `SurfacePicardSymmetry` becomes an
abbrev plus a restated `symmetry` lemma.

**Future examples covered.**  Threefold divisor Riemann–Roch (sign −1) for `ℙ³` and
the quintic; fourfold Picard Euler symmetry (sign +1) for the cubic fourfold; curve
Riemann–Roch as the `n = 1` case.

**Verdicts.**
- *Mathematics* — survives.  The n-fold theorem verified to carry no dimension
  hypothesis and the `n = 2` restatement to be `subst; simpa` from it; the sign
  values at `n = 1, 3, 4` confirmed.  **Correction applied:** the abbrev does not
  give back the current field syntactically, so ship a simp lemma
  (`neg_one_sq`/`Even.neg_one_pow`) or `Divisor.lean:100` stops firing; and the root
  must take **one** `n` shared by the intersection context and the specialization.
- *Repository* — survives.  Every citation exact; the `dimension_eq_two` field's
  only use is feeding the `n = 2` restatement; `IntersectionContext` is
  `d`-parametric; the root stays in the same file and namespace, so no placement or
  gate question arises.  **Correction applied:** the consumers are **not**
  unchanged — the root's field carries the sign, so `P.symmetry L` needs a one-line
  rewrite at each call site.
- *Adoption and cost* — **refuted** (single dissent).  `SurfacePicardSymmetry` has
  exactly one producer and nine hypothesis positions in one file; no threefold or
  fourfold Picard-symmetry declaration exists anywhere, so the generalized structure
  would ship with a single inhabitant and every named future example is unwritten —
  the shape `check_single_instantiation.py`'s docstring calls out.  The salvage is
  the minimal fix above, which is what is proposed.

#### surf-06 — Exceptionality of line bundles hardcodes n = 2 and an Enriques instance

**Kind** dimension-specific-should-be-n-fold · **Impact** medium (adoption lens
refuted) · **Confidence** 0.9

**Declarations.**  `EnriquesSurface.ExtComparison` (`Surface/Enriques/Exceptional.lean:73`),
`isExceptional_of_extComparison` (`:97`),
`IsotropicCollection.ExceptionalityData` (`:130`);
`SmoothProperVariety.IsEnriquesSurface` (`Surface/Enriques/Basic.lean:106`).

**Parent structure.**  For a line bundle `L` on a `d`-dimensional `X`,
`Ext^i(L,L) ≅ H^i(X,O_X)` for all `i` and `Ext^i = 0` outside `[0,d]`, so `L` is
exceptional iff `H^i(O_X) = 0` for `0 < i ≤ d`.  Nothing about Enriques surfaces,
2-torsion, or projectivity enters: the proof body touches the instance in exactly
one place, `hEnriques.h1_vanishing`, and takes `H²(O_Y) = 0` as a separate
hypothesis; the `2` in `outside_surface_range` is the dimension.

**Proposed root** (corrected: a one-line hypothesis change, not a new structure).
Replace the `[IsEnriquesSurface k Y C]` instance parameter of
`isExceptional_of_extComparison` by an explicit
`(hOne : IsZero ((Cohomology.coherentH Y 1).obj (Scheme.structureSheafCoh Y)))`
alongside the `hTwo` it already takes.  The theorem then mentions no Enriques
surface, and `ExceptionalityData.bundle_isExceptional` supplies `hOne` from the
instance it already has in scope.

**Projections.**  `ExtComparison` generalizes to `(d : ℕ)` for free, since the
`include` of the Enriques instance is on the theorem, not the structure;
`ExceptionalityData` keeps its Enriques-specific `h_two_vanishing`; once surf-03's
`middle_vanishing` exists, `hOne` comes from that field and only `H^n(O) = 0`
remains supplied.

**Future examples covered.**  `O, O(1), O(2)` exceptional on `ℙ²`, quadrics and del
Pezzos; `O..O(2)` on the cubic threefold and cubic fourfold — the exceptional parts
whose orthogonal complement is `Ku(X)`; line bundles on any Fano or rational
variety.

**Verdicts.**
- *Mathematics* — survives.  The proof body read and confirmed to touch the
  instance in exactly one place; the generalization is standard and the field set
  covers every degree.  **Correction applied:** ordering — once surf-03 lands,
  `hOne` is discharged from `middle_vanishing`, so surf-03 should land first or the
  two together.
- *Repository* — survives.  Verified in full, including that
  `isExceptional_of_extComparison` uses `hEnriques.h1_vanishing` alone and that
  `IsExceptional` (the generic root) is at
  `SemiorthogonalDecomposition/Exceptional.lean:104`; the proposed placement is
  legal.  **Correction applied:** `ExtComparison` itself does **not** mention the
  Enriques instance — the `include` at `:95` puts it on the theorem only — so the
  structure already generalizes and the Enriques-ectomy applies to the theorem;
  keep the `endomorphisms` field, which is the degree-zero half of `IsExceptional`
  and not part of the Ext comparison.
- *Adoption and cost* — **refuted** (single dissent).  One leaf:
  `ExtComparison` is the only Ext-comparison structure in the repository, and
  `IsExceptional` is produced geometrically at two sites; and the proposed
  `SelfExtComparison`'s fields are all supplied Prop data identical to the leaf's,
  which the surveyor concedes ("no more provable than the leaf").  The salvage is
  the one-line hypothesis change above, which is what is proposed.

#### surf-07 — Three numerical K-trivial surface models are one constructor

**Kind** missing-root · **Impact** medium · **Confidence** 0.93

**Declarations.**  `k3Todd` (`Examples/Surface/K3.lean:52`), `k3NumericalVariety` (`:75`);
`enriquesTodd` (`Examples/Surface/Enriques.lean:77`), `enriquesNumericalVariety` (`:102`);
`abelianTodd` (`Examples/Surface/Abelian.lean:63`), `abelianNumericalVariety` (`:83`);
`p2Todd`/`p2NumericalVariety` (`Examples/Surface/ProjectivePlane.lean:59`);
`surfaceNumericalRing` (`Examples/Surface/RankOne.lean:181`), `surfaceCh` (`:197`).

**Parent structure.**  All three K-trivial models are the same
`NumericalVarietyData 2` with the same ring, rank and `chComp` (the Enriques and
abelian files literally reuse the K3-named coefficient function), differing only in
the top Todd scalar and `χ`: one equation `td₂ = (χ(O)/(2d))·H²`,
`χ(E) = χ(O)·r + 2d·s` with `χ(O) ∈ {2, 1, 0}`.  The HRR proofs are the same
`field_simp/ring` computation three times.  `ℙ²` shares the Todd constructor with a
nonzero linear term but not the `ch` coordinates.

**Proposed root.**  `Examples/Surface/RankOne.lean`: `kTrivialSurfaceTodd (h2 χ₀)`
with a literal `| 1 => 0` branch, and `kTrivialSurfaceVariety d χ₀`, with the HRR
hypothesis `d ≠ 0 ∨ χ₀ = 0`.

**Projections.**  `k3NumericalVariety d := kTrivialSurfaceVariety d 2`,
`enriquesNumericalVariety d := … 1`, `abelianNumericalVariety d := … 0`; `ℙ²`
reaches the separate general `rankOneSurfaceTodd`, keeping its own `ch` coefficients.

**Future examples covered.**  Bielliptic surfaces (`χ(O) = 0`); Enriques with any
polarization degree and K3 of any degree, already parameters; general-type or del
Pezzo rank-one surfaces via the general Todd constructor.

**Verdicts.**
- *Mathematics* — survives.  All constants recomputed: `2/(2d) = 1/d`, `1/(2d)`,
  `0/(2d) = 0` all check, and `χ = r·∫td₂ + ∫ch₂` gives the three `χ` homs; `ℙ²` is
  a child of the Todd constructor only, since its nonzero `td₁` adds a cross term.
  **Corrections applied:** the projections cannot be `rfl`-abbrevs, since `1/d` and
  `χ₀/(2d)` are propositionally but not syntactically equal, so several current
  `rfl` proofs must be re-closed by `field_simp`; the HRR hypothesis is
  `d ≠ 0 ∨ χ₀ = 0`, not a blanket `d ≠ 0`, or the abelian model loses an
  unconditional theorem.
- *Repository* — survives.  All nine citations real and the unifying formula
  reproduces all three models.  **Correction applied:** re-kind to
  existing-root-unused — the parent already exists **one level up** and is n-general
  (`Examples/RankOne.lean`, whose own docstring says `SurfaceRing` is the `n = 2`
  case and records the migration as deliberate unfinished work), so give the three
  models `rankOneNumericalVariety 2 (2*d) …` with one Todd-coefficient family rather
  than adding a fourth layer beside it; the `…Presentations` defs are documented
  regression tests, not artefacts.
- *Adoption and cost* — survives.  The three models verified field-for-field
  identical except `toddComp` and `chi`, the unifying equation checked numerically,
  and the `d = 0` question resolved in the root's favour.  **Corrections applied:**
  keep a literal `| 1 => 0` branch or several `rfl`s are lost
  (`abelianToddComp_one`, the three `toddComp_zero`, and `k3_isK3`'s first
  component); the `…Presentations` characterisation is wrong — they are regression
  tests and should be kept.

#### surf-08 — Four numerical K-trivial predicates are one

**Kind** same-equation-two-names · **Impact** medium · **Confidence** 0.9

**Declarations.**  `K3.IsK3` (`Numerical/RiemannRoch/K3.lean:52`) and `chi_eq` (`:62`);
`Enriques.IsEnriques` (`RiemannRoch/Enriques.lean:39`);
`CalabiYauThreefold.IsCalabiYau` (`Specializations/Threefold.lean:85`);
`CalabiYauFourfold.IsCalabiYau` (`Specializations/Fourfold.lean:94`);
`RiemannRoch.Surface.GeometricData.toIsK3` (`RiemannRoch/Surface/NumericalVariety.lean:236`).

**Parent structure.**  The numerical shadow of surf-03, and the same parent as
numerical-nfold-01 seen from the surfaces lane: `{td₁ = 0, ∫td_n = χ(O)}` at
`(n, χ₀) = (2,2), (2,1), (3,0), (4,2)`.  The geometric bridge `toIsK3` exists only
for K3; `grep` over `RiemannRoch/` finds no `toIsCalabiYau`, so the threefold and
fourfold children cannot be reached from geometry at all.

**Proposed root** (corrected).  `IsNumericallyCalabiYau` with its second field
stated as `V.structureSheafEulerCharacteristic = χ₀`, which is the existing
n-general owner (`RiemannRoch/General.lean:33`, already aliased as
`chiStructureSheaf` at three dimensions), and the leaves reaching it by `extends`,
not `abbrev`.

**Projections.**  The four predicates `extends` the root at their `χ₀`, with a
one-line compatibility theorem for the old field name; the fourfold keeps its extra
`toddComp_three`; `toIsK3` and its two siblings become instances of one
`toIsNumericallyCalabiYau` on the surf-02 assembly, giving the missing CY3 and CY4
geometric bridges for free.

**Future examples covered.**  Numerical hyperkähler fourfolds (`χ(O) = 3`) and
bielliptic surfaces; the cubic fourfold's `Ku(X)` as a numerical K3 category, whose
Mukai-lattice consumer needs only the root at `n = 2`; quintic and other CY3
examples reaching the same predicate the K3 examples use.

**Verdicts.**
- *Mathematics* — survives.  All four field lists verified; the parent's
  odd-`i < n` quantification confirmed to match each leaf (in particular CY3 states
  `∫td₃ = 0`, a degree equation, which the parent's top-degree field matches);
  the `chi_eq` index set re-derived and checked at `n = 2, 3, 4`.
  **Corrections applied:** the sketched `chi_eq` is **wrong** — `Finset.Icc 2 n`
  drops the `i = 1` term `ch₁·td_{n−1}`, which does not vanish at `n = 3`; the
  correct range is `Finset.range (n+1) \ {0, n−1}`.
- *Repository* — survives.  All citations real and the geometric asymmetry
  confirmed by grep.  **Corrections applied:** the threefold and fourfold predicates
  are `CalabiYauThreefold.IsCalabiYau` and `CalabiYauFourfold.IsCalabiYau`, not
  `Threefold.`/`Fourfold.`; half the parent already exists as
  `structureSheafEulerCharacteristic`, whose docstring already says the
  per-dimension names are "only compatibility aliases", so the root's second field
  must reuse it; the `chi_eq` range correction; and `IsNumericallyCalabiYau 1` for an
  Enriques surface is a misnomer.
- *Adoption and cost* — survives.  Four leaves with literally the same field names
  at `n = 2`, and three `toIsK3` bridges against zero `toIsCalabiYau`.
  **Corrections applied:** the `chi_eq` range; reuse
  `structureSheafEulerCharacteristic`; and use `extends`, **not** `abbrev` —
  `K3.IsK3` appears in roughly sixty hypothesis and dot-notation positions across
  ten files, and an abbrev changes the head symbol so every `hK3.degree_toddComp_two`
  loses resolution.

#### sites-03 — Two copies of one colimit-preservation transfer

**Kind** same-equation-two-names · **Impact** medium (repository and adoption
lenses rate low) · **Confidence** 0.9

**Declarations.**  `Limits.preservesColimit_comp_left`
(`CategoryTheory/Limits/Preserves/Composition.lean:23`);
`Adjunction.preservesColimitsOfShape_of_comp_left`
(`Limits/Preserves/Reflective.lean:32`);
`Limits.preservesCoproductsOfShape_of_essSurj`
(`Limits/Preserves/Shapes/Products.lean:37`).

**Parent structure.**  "`F` preserves `K`-colimits if `L` and `L ⋙ F` do and every
`K`-diagram in `D` is isomorphic to an `L`-image."  The reflective case takes
`d' := d ⋙ G`; the discrete case takes `d' := Discrete.functor (L.objPreimage ∘ Y)`,
and its body **re-inlines** `Composition.lean:23` verbatim instead of calling it.

**Proposed root.**  State the hypothesis as the lifting property
`(h : ∀ d, ∃ d', Nonempty (d' ⋙ L ≅ d))` rather than as an `EssSurj` instance on a
whiskering functor, in `Limits/Preserves/Composition.lean`.

**Projections.**  Both leaves derive from the root with no restated proof —
compiled.  Independently of any root, the one-line fix is to make `Products.lean`
import `Composition.lean` and call `preservesColimit_comp_left`.

**Future examples covered.**  Homology functors on Verdier quotients preserving
arbitrary shaped colimits computed upstairs; transport across localizations with a
fully faithful right adjoint (sheafification, `Dqc ⊂ D`); filtered-colimit
preservation along essentially surjective quotient functors.

**Verdicts.**
- *Mathematics* — survives.  All three files read in full; the re-inlining
  confirmed; and the key mathematical point is correct — `EssSurj` of `L` alone does
  **not** give a natural iso for general `K` (only objectwise isos), which is why
  the discrete case works and the general one does not, and why the hypothesis must
  be on the whiskered functor.  **Correction applied:** the discrete supplier is a
  two-step composite, since an arbitrary `Discrete ι ⥤ D` must first be replaced by
  `Discrete.functor` via `Discrete.natIsoFunctor`.
- *Repository* — survives at **low**.  All three citations exact and the
  re-inlining verified.  **Corrections applied:** recast as existing-root-unused —
  the shared root already exists and the whole defect is that `Products.lean` does
  not call it; and the further proposed root's two advertised suppliers cannot be
  instances, since the adjunction is explicit data, so with two call sites the extra
  layer buys little.
- *Adoption and cost* — survives at low, verified by compilation: both leaves
  derived from the root with no restated proof, and `Products.lean`'s import list is
  Mathlib-only, so it *cannot* call `Composition.lean:23` today.  Migration is
  ~free.  **Correction applied:** state the lifting property rather than an
  `EssSurj` instance on a whiskering functor, which would add a fragile global
  instance for no content.

#### sites-04 — Chain-condition transfer proved four times

**Kind** leaf-copies-root · **Impact** medium (repository and adoption lenses rate
low) · **Confidence** 0.85

**Declarations.**  `isStrictArtinianObject`/`isStrictNoetherianObject`
(`CategoryTheory/Abelian/QuasiAbelian.lean:526`, `:538`);
`subobjectImageOfFullFaithful` (`:621`);
`isArtinianObject_of_fullFaithful_preservesMono` (`:672`),
`isNoetherianObject_of_fullFaithful_preservesMono` (`:696`);
`strictSubobjectImageOfFullFaithful` (`:723`);
`isStrictArtinianObject_of_fullFaithful_map_strictMono` (`:782`),
`isStrictNoetherianObject_of_fullFaithful_map_strictMono` (`:818`);
`isNoetherianObject_of_reflectsIsomorphisms`
(`CategoryTheory/Subobject/NoetherianObject.lean:91`).

**Parent structure.**  Well-foundedness pulled back along a monotone injective map
of subobject sub-posets.  The four transfer theorems each re-run the chain-condition
unfolding, differing only in which image map is fed in; and `:696` is additionally
the fully-faithful special case of `NoetherianObject.lean:91`.

**Proposed root** (corrected: Mathlib's, with no new wrapper).
`Monotone.strictMono_of_injective` (`Mathlib/Order/Monotone/Defs.lean:232`) composed
with `StrictMono.wellFoundedLT` (`Mathlib/Order/Monotone/Basic.lean:222`, which
carries `@[to_dual]`, so the `GT` dual is free).

**Projections.**  All four become one-liners over Mathlib — verified by
compilation; `:696` is replaced outright by
`isNoetherianObject_of_reflectsIsomorphisms F`, since Mathlib registers
`reflectsIsomorphisms_of_full_and_faithful`.

**Future examples covered.**  Strict finite length transferred along interval
inclusions of slicings; Artinian/Noetherian objects of `Coh` transferred along
restriction to charts; any future sub-poset of subobjects with its own chain
condition.

**Verdicts.**
- *Mathematics* — survives.  All four leaves read and confirmed to run the same
  script, and the hypotheses the root needs hold at every proposed call site.
  **Correction applied:** the `degree_ch_mul_todd`-style spelling note — the root
  must go on the bare sub-poset, and the Mathlib lemma names are as corrected above.
- *Repository* — survives at **low**.  All nine citations real and the inversion is
  literal.  **Correction applied:** the proposed root **already exists in Mathlib**,
  so no new `DerivedAlgGeo` declaration should be added; each of the four collapses
  to `ObjectProperty.is_of_prop _ ((mono.strictMono_of_injective inj).wellFoundedLT)`;
  and two further copies of the same pattern (`isStrictArtinianObject_of_isArtinianObject`
  at `:550` and its Noetherian twin at `:558`) hand-roll `InvImage.wf` along
  `Subtype.val`.
- *Adoption and cost* — survives at low, with every projection compiled.
  **Corrections applied:** reclassify as existing-root-unused and do **not** add a
  `Subobject.wellFoundedLT_of_monotone_injective` wrapper — with four call sites and
  no content beyond composing two Mathlib lemmas, that is the thin abstraction this
  lens rejects; call Mathlib directly and replace `:696` by the repository's own
  `isNoetherianObject_of_reflectsIsomorphisms`.

#### sites-05 — "Extension-closed plus zero ⇒ binary products", three times

**Kind** leaf-copies-root · **Impact** medium · **Confidence** 0.88

**Declarations.**  `ObjectProperty.serreIsClosedUnderBinaryProducts`
(`CategoryTheory/Abelian/SerreClass/FullSubcategory.lean:57`) and
`serreIsClosedUnderFiniteProducts` (`:67`);
`Scheme.coherent_isClosedUnderBinaryProducts`
(`AlgebraicGeometry/Modules/Coherent/Abelian/Basic.lean:40`);
`coherent_isClosedUnderExtensions` (`Coherent/Abelian/Extensions.lean:30`);
`heart_biprod`/`heart_closedUnderBinaryProducts`
(`Triangulated/TStructure/HeartBridge.lean:125`, `:131`).

**Parent structure.**  In a preadditive category with a zero object and binary
biproducts, an extension-closed `P` is closed under binary products, because
`X ⊞ Y` is a split extension — Mathlib's `prop_biprod`, whose only hypotheses are
`Preadditive`, `HasZeroObject` and `IsClosedUnderExtensions`.  The Serre version
proves it under the stronger `IsSerreClass`, and its docstring says the body is
copied from the coherent one.

**Proposed root** (corrected signature).
`isClosedUnderBinaryProducts_of_isClosedUnderExtensions` in
`CategoryTheory/ObjectProperty/Extensions.lean` (the Mathlib mirror path), with
`[P.ContainsZero] [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]` —
the last is required, because the body calls `prop_of_iso`, and Mathlib's
triangulated analogue carries it explicitly.  `ContainsZero` is needed only for the
finite-products corollary, so state the two instances with different hypotheses.

**Projections.**  The Serre version is deleted and reached by instance search;
the coherent version likewise — and the import-order risk the finding names is
**false**, since `Coherent/Abelian/Basic.lean:5` already imports
`Coherent/Abelian/Extensions.lean`.  The heart version is **dropped**: its ambient
category is only pretriangulated, so supplying `IsClosedUnderExtensions` there
would need the splitting plus the very triangle argument `heart_biprod` already
runs.

**Future examples covered.**  Quasi-coherent sheaves on any scheme; perfect
complexes, torsion classes and any future extension-closed subcategory; Serre
subcategories of `Coh` becoming abelian by instance search alone.

**Verdicts.**
- *Mathematics* — survives.  The two bodies confirmed character-for-character
  identical; `IsSerreClass` verified to extend `IsClosedUnderExtensions`, so the
  Serre leaf is pure instance search; `heart_biprod` is the third copy through a
  different route.  **Corrections applied:** the import-direction risk is **false in
  the safe direction**, so the coherent leaf can be deleted as soon as the root
  exists; the heart leaf costs more than admitted, since `heart_biprod` becomes the
  *input* to the extension instance rather than being replaced by it.
- *Repository* — survives.  The two bodies are byte-identical, the docstring says
  so, and Mathlib has the exact analogous instance on the triangulated side
  (`Mathlib/CategoryTheory/Triangulated/Subcategory.lean:660-667`), which both
  confirms the root is missing on the abelian side and fixes its mirror path.
  **Corrections applied:** the `IsClosedUnderIsomorphisms` hypothesis; `ContainsZero`
  is not needed for the binary-product instance; and the import risk is false.
- *Adoption and cost* — survives, verified by compilation: the root elaborates and
  both leaves reach it by explicit application.  **Corrections applied:** the
  missing `IsClosedUnderIsomorphisms` (reproduced as a synthesis failure); the false
  import risk; and **drop** the heart projection for the pretriangulated-ambient
  reason above.

#### sites-06 — `FamilyCommShift` at the site level

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.8

**Declarations.**  `functorCategoryHasShift` (`CategoryTheory/Shift/FunctorCategory.lean:90`),
`evaluationCommShift` (`:131`);
`Functor.FamilyCommShift` (`Triangulated/ExactFunctorFamily.lean:57`),
`Functor.ExactFamily` (`:127`).

This is the same defect as dg-04, reported independently by the sites lane; the
declarations, parent structure and proposed root are identical and are not repeated
here.  The sites lane adds two facts.

**Verdicts.**
- *Mathematics* — survives, with the same corrections as dg-04.
- *Repository* — survives, and adds the decisive datum: `postShift`
  (`ExactFunctorFamily.lean:76`) is `(whiskeringRight X Y Y).obj (shiftFunctor Y n)`,
  which is **character-for-character** the `F` field of `functorCategoryShiftMkCore`
  (`Shift/FunctorCategory.lean:69`) — the leaf re-defines the root's carrier rather
  than reaching it.
- *Adoption and cost* — survives, and adds the second: `functorCategoryHasShift`
  and `evaluationCommShift` have **zero** consumers — `grep -rl` returns only the
  `CategoryTheory/Shift.lean` umbrella and the audit slice — so this is a root built
  and never adopted, and adopting it retires a single-use module rather than adding
  one.  Verified: `example (F) [F.CommShift ℤ] (E : X) : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := inferInstance`
  compiles.  **Correction applied:** `commShift_naturality` was **not** verified —
  three attempts left a residual goal about
  `(shiftFunctor K n ⋙ F).obj A` versus `F.obj ((shiftFunctor K n).obj A)`, so budget
  a `show`-fixing proof rather than assuming a one-liner.

#### sites-07 — `QuasicoherentData` has no per-chart transport

**Kind** missing-root (corrected from existing-root-unused) · **Impact** medium ·
**Confidence** 0.88

**Declarations.**  `SheafOfModules.LocalGeneratorsData.transport`
(`Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean:59`) and
`isLocallyFreeData_transport` (`:74`);
`Scheme.Modules.pullbackLocalGeneratorsData` (`Modules/Pullback/LocallyFree.lean:48`);
`pullbackPresentationOver` (`Modules/Coherent/Pullback.lean:78`),
`isFinitePresentation_pullback` (`:97`);
`SheafOfModules.Presentation.isFinite_map` (`Sheaf/Presentation/Transport.lean:59`).

**Parent structure.**  Both Mathlib structures are cover-indexed local data with
the same three shared fields, differing only in the per-chart payload
(`GeneratingSections` vs `Presentation`).  Transport along per-chart
colimit-preserving slice functors is one operation, and the generators side states
it once while the presentation side rebuilds it field by field inside
`isFinitePresentation_pullback`.

**Proposed root.**  `QuasicoherentData.transport` in
`Sheaf/Presentation/Transport.lean`, beside the existing `QuasicoherentData.ofIso`
and `.over`, with explicit universe annotations and the finiteness instance proved
from index types.

**Projections.**  `isFinitePresentation_pullback` becomes one `transport` call with
the same five inputs `pullbackLocalGeneratorsData` already uses;
`pullbackPresentationOver` becomes the per-chart component, or is deleted.

**Future examples covered.**  Pullback of finite presentation along morphisms of
ringed sites (étale, fppf) without a scheme; transport of coherence along an
equivalence of sites or a base change; any new cover-indexed local datum.

**Verdicts.**
- *Mathematics* — survives.  The five inputs verified identical in the same
  orientation, including the `.inv`/`.symm` bookkeeping.  **Correction applied:**
  the per-chart combinators are **not** the same operation — the generators side
  uses `GeneratingSections.ofEpi` and the presentation side needs
  `Presentation.ofIsIso` — so a single `CoverIndexed.transport` would have to take
  the per-chart carrier together with its `map` and its `ofEpi`/`ofIsIso` as
  parameters; and the universe caveat is confirmed by the code, which writes the
  annotations explicitly.
- *Repository* — survives.  All six citations verified and the leaf does build the
  data field by field; Mathlib has no such transport (`QuasicoherentData.pushforward`
  is tied to a continuous-and-cocontinuous functor with its own heavy hypothesis
  block); the repository already owns the sibling operations `ofIso` and `over`, so
  the placement matches convention.  **Correction applied:** the kind is
  missing-root, since `LocalGeneratorsData.transport` is a sibling on a different
  carrier, not a root the presentation side could reach.
- *Adoption and cost* — survives, with one live cost objection quoted from the leaf
  itself: naming the transported data globally "makes Lean re-check instance
  arguments of the presentation type at whnf and does not terminate in the default
  heartbeat budget", and anonymous constructors elaborate the finiteness classes at
  universe 0.  Four hand-built `QuasicoherentData where` sites exist, not two.
  **Corrections applied:** write the root with explicit universe annotations and
  prove finiteness from index types, never by anonymous constructor; prototype it as
  a `#check`-only scratch file first — if the whnf non-termination reproduces, the
  finding downgrades to a negative result.

#### docs-03 — The K3 spherical profile is undocumented and unbridged

**Kind** leaf-copies-root · **Impact** medium · **Confidence** 0.9

**Declarations.**  `single_instantiation_baseline.txt:18`
(`CategoryTheory.SerreFunctor.SphericalExtProfile`);
`SerreFunctor.SphericalExtProfile` (`SerreFunctor/Transport.lean:37`);
`K3Surface.SphericalExtProfile` (`Surface/Spherical.lean:143`) with its docstring at
`:19`; the imports of `Surface/Spherical.lean` (`:5`, containing no `SerreFunctor`);
`abstraction-tree.md:63` (`IsSphericalObject  two-degree self-Hom profile`, with no
geometric leaf listed).

**Parent structure.**  The documentation half of surf-04: one Prop, restated at
`n = 2` on `Dᵇ(Coh X)`, with the docstring naming the parent and no declaration
connecting them, while the baseline records the generic root as single-inhabitant.

**Proposed amendment.**  Record in the spine that the profile has **two** generic
roots and one geometric copy; add the missing three-line bridge; keep the baseline
row.

**Projections.**  `K3Surface.SphericalExtProfile → SphericalTwist.IsSphericalObject k (2:ℤ)`
by `abbrev` (compiled); `SerreFunctor.SphericalExtProfile → SphericalTwist.IsSphericalObject k (n:ℤ)`
likewise.

**Future examples covered.**  Spherical objects on abelian and Enriques surfaces
and on CY threefolds without a third copy; pseudoprojective profiles on surfaces
reusing `PseudoprojectiveExtProfile` the same way.

**Verdicts.**
- *Mathematics* — survives.  Both declarations read and confirmed identical at
  `n = 2`; the "no Serre functor available" excuse is not an obstruction, since the
  generic structure takes none; the baseline row verified.  **Correction applied:**
  the finding names the wrong parent — `SphericalTwist.IsSphericalObject` is
  ℤ-indexed, so it is the better root and the cast concern evaporates; and the
  duplicated consequence proofs (`not_isZero`, `finrank_end`, `finrank_hom_eq_zero`)
  should be listed as deletions.
- *Repository* — survives.  All citations real and the docs gap confirmed
  (`layers.md:131` lists `SphericalTwist` as a bare name).  **Corrections applied:**
  the third declaration again, and the fact that the K3 leaf already reaches it
  field-for-field, so what remains is a duplicate-parent between the two generic
  roots plus a three-line missing bridge; projection 3 is wrong — an `abbrev` adds
  no counted inhabitant, so baseline line 18 must stay.
- *Adoption and cost* — survives.  The stated cast risk is **refuted by
  compilation**, and the "no Serre functor" excuse is contradicted by the tree,
  where the generic profile already has geometric consumers at `n = 3` on an
  Enriques residual category.  **Corrections applied:** the root is mis-identified;
  cost includes audit lines that lose the field projections under an abbrev.

#### docs-04 — `BoundedRegion` and `PlaneRegion` are one structure in two charts

**Kind** duplicate-parent · **Impact** medium (mathematics lens refuted) ·
**Confidence** 0.8

**Declarations.**  `single_instantiation_baseline.txt:64`
(`…Wall.Spherical.BoundedRegion`);
`Wall.Spherical.BoundedRegion` (`Walls/Spherical/Finiteness.lean:76`) and
`BoundedRegion.ofDivisorSpace` (`Spherical/DivisorialRegion.lean:68`);
`PeriodDomain.PlaneRegion` (`QuadraticForm/WallRegion.lean:138`) with its docstring
at `:21` ("exactly as `Walls/Spherical/Finiteness.lean` does for `BoundedRegion` in
the other chart") and `PlaneRegion.ofCompactPairs` (`:185`);
`DivisorSpace.expPlaneRegion` (`Walls/Divisorial/Region.lean:220`);
`DivisorSpace.expPairMap` (`Region.lean:74`).

**Parent structure.**  A set of positive planes with a uniform coercivity constant,
whose consequence is "finitely many spherical classes have a wall meeting the
region".  Both are inhabited from **one** certificate — `HodgeDefinite` on a compact
`K` — and each carries its own finiteness theorem.

**Proposed root** (corrected: a strengthening, not a forgetful projection).
`PeriodDomain.PlaneRegion`, with `BoundedRegion.toPlaneRegion` supplying the
constant from `R.coercivity`, `R.ampleLower` and the carrier bound.  The direction
is one-way: a `PlaneRegion` carrier forgets `(β,ω)`.

**Projections.**  `BoundedRegion → PlaneRegion` by `toPlaneRegion`; the
plane-level comparison **already exists and is `rfl`**
(`expPlane_eq_chartPlane`, `Spherical/DivisorialRegion.lean`, under the heading
"The two charts are one"), so only the constant transfer is open;
`ofDivisorSpace` and `expPlaneRegion` become one construction.

**Future examples covered.**  Region-wise wall finiteness for any future chart —
a `(B,ω)` chart on a threefold divisor space, or a Kuznetsov-component chart —
reaching one `PlaneRegion` root instead of a third region structure.

**Verdicts.**
- *Mathematics* — **refuted** (single dissent).  `WallComparison.lean` exists
  precisely to relate the two lanes and establishes that the two **loci** are not
  the same: `Spherical.wall` is an inequality and `PeriodDomain.wall` a vanishing
  condition, with a one-way inclusion, and the file states that the two finiteness
  theorems "are not restatements of each other".  So the proposed
  `wallCandidates_eq` is false and the two finiteness engines do not merge; the two
  proofs are genuinely different (one bounds `‖δ‖` from `Q δ = −2` exactly, the
  other from an inequality, which is why `BoundedRegion` needs the extra
  `ampleLower` field).  Recorded as the dissent.
- *Repository* — survives.  Both structures real and duplicated as described, both
  inhabited from the same certificate, both deriving a finiteness theorem by the
  same `ZSpan` argument, and no declaration relating them.  **Corrections applied:**
  `BoundedRegion` is **not** single-inhabitant today — `boxRegion` appears twice in
  `Examples/Surface/`, so baseline line 64 is **stale**; `Mukai.realForm b` is
  already a `QuadraticForm`, so the sketch's `.toQuadraticForm` is wrong; and the
  projection is cheaper than assumed, since the plane-level comparison is already
  `rfl` and only the constant transfer is open.
- *Adoption and cost* — survives.  The two inhabitants take the same three inputs,
  and the direction is a **strengthening**, not a forgetful projection —
  `PlaneRegion.uniform` controls all of `W^⊥` while `BoundedRegion.neg_definite`
  controls only `ω^⊥`, which is visible downstream: `PlaneRegion` bounds `‖δ‖`
  straight off the constant while `BoundedRegion` must reconstruct `δ` using
  integrality of the rank.  **Corrections applied:** the payoff is therefore
  **larger** than claimed — roughly 110 lines and the whole integrality detour are
  retired, not merely "one finiteness engine"; 19 immutable `#print axioms` lines
  and the baseline row are the cost; and the finding's own fallback (require
  `IsCompact`, which the sole inhabitant already has) should be promoted.

#### docs-05 — The quadratic-support binding layer, declared twice

**Kind** same-equation-two-names · **Impact** medium (adoption lens refuted) ·
**Confidence** 0.85

**Declarations.**  `single_instantiation_baseline.txt:74`;
`WeakStabilityFunction.QuadraticSupportData` (`Weak/Support/Quadratic.lean:55`) and
`UniformQuadraticSupportData` (`:87`);
`PreStabilityCondition.WithClassMap.QuadraticSupportData`
(`Support/Semistable.lean:68`) and `UniformQuadraticSupportData` (`:88`);
`layers.md:41` (rule 4: the ordinary theory `extends` the weak one "rather than
copying its fields");
`abstraction-tree.md:12` ("A leaf must not copy the carrier or fields of its root");
`PreStabilityCondition.WithClassMap` (`Foundation/PreStabilityCondition.lean:43`).

**Parent structure.**  The same two-field Prop with `Z`, `Zlin` and a semistable
locus, at two `(Z, v, S)`.  The repository decided this exact shape for the
`PreStabilityCondition` pair; the baseline names only the weak copy, so the gate
sees one single-inhabitant abstraction and cannot see its twin three directories
away.

**Proposed amendment** (corrected: documentation, not a structure).  Record the
family beside layers rule 4: name its shared root `Support.HasQuadraticSupportProperty`,
name all seven members, and record why the parallelism is deliberate — per
`abstraction-tree.md`'s "Negative result" clause.

**Projections.**  If a structure were shipped, both leaves would be abbrevs at
`(W.Z, v, W.semistableClasses v)` and `(σ.Z, id, σ.semistableClasses)`.

**Future examples covered.**  Quadratic support for stability conditions in
families and for the Mukai tilted-heart function without a third copy; support data
for a Kuznetsov-component charge on the same root.

**Verdicts.**
- *Mathematics* — survives.  Both records read field for field and the same three
  lemmas are re-proved; the proposed `(Z, v, S)` parametrisation specializes exactly,
  and the differing semistable sets are a parameter, not an obstruction.
  **Correction applied:** `layers.md:41` is a rule about the `PreStabilityCondition`
  pair specifically, so the binding contract line is `abstraction-tree.md:12`, with
  rule 4 as precedent.
- *Repository* — survives.  Every declaration and downstream lemma verified as
  duplicated one-for-one, down to identical proof terms.  **Corrections applied:**
  lower the impact — the mathematical engine is **already** shared, so what is
  duplicated is a two-field wrapper plus three one-line lemmas; and a new structure
  whose only leaves are `abbrev`s would have **zero** counted inhabitants and fail
  the gate, so either state the producer lemmas at the root's own spelling or ship a
  baseline entry with a reason.
- *Adoption and cost* — **refuted** (single dissent).  The shared content is already
  rooted; the claim that the gate "cannot see the twin" is false, since the ordinary
  structure has three inhabitant-producing declarations and correctly does not fire;
  the two `charge_compatible` fields are not the same statement (the ordinary one
  quantifies over all of `V` and is strictly stronger); and ~15 immutable audit
  payload lines would lose declarations.  The dissent's own salvage — the docs entry
  above, naming all seven members and their four axes — is what is proposed.

#### docs-06 — The LinearAlgebra node omits the quadratic-space subtree

**Kind** existing-root-unused · **Impact** medium · **Confidence** 0.95

**Declarations.**  `abstraction-tree.md:178` (the `LinearAlgebra` node, with only
"finite free integral lattices" and "weighted-basis graded pieces");
`layers.md:80` ("Where each theory lives", with **no** `LinearAlgebra` entry at all);
`PeriodDomain.centralCharge` (`QuadraticForm/CentralCharge.lean:61`);
`Mukai.expCharge` (`Lattice/Mukai/CentralCharge.lean:36`);
`PeriodDomain.IsPositivePlane` (`QuadraticForm/PeriodDomain.lean:91`);
`PeriodDomain.PlaneRegion` (`QuadraticForm/WallRegion.lean:138`);
`centralCharge_eq_expChargeHom` (`Walls/Divisorial/Mukai.lean:155`);
`numericalCharge_add` (`Numerical/GrothendieckGroup/CentralCharge.lean:77`);
`MukaiChargeData.chargeHom` (`Mukai/Charge.lean:111`).

**Parent structure.**  `Z_{x,y}(v) = ⟪x,v⟫ + i⟪y,v⟫` on a real quadratic space of
signature `(2, n−2)`, with the support property.  Bridgeland's `Z(β,ω)` is that
root at the exponential pair — **definitionally**; the divisorial charge is proved
equal to it; the geometric K3 charge is it composed with the Mukai vector; the
categorical charge is it composed with a class map.  `LinearAlgebra/QuadraticForm/`
(9 files) and `Lattice/Mukai/` are therefore the root of the whole exponential-plane
charge lane, and neither document has a node for them.

**Proposed amendment.**  The `LinearAlgebra` fragment of §2.4, plus a
`LinearAlgebra` block in `layers.md`'s "Where each theory lives" and two import-guide
rows.

**Projections.**  Each edge already exists as a definitional identity or a proved
theorem.

**Future examples covered.**  The cubic-fourfold `Ku(X)` charge as a direct
instance on the `A₂`-extended Mukai lattice; hyperkähler and abelian-surface charges
at a different quadratic space.

**Verdicts.**
- *Mathematics* — survives.  Every projection verified in code and the docs gap
  confirmed: `grep -n LinearAlgebra layers.md` returns **nothing**.  **Corrections
  applied:** narrow the scope sentence — `QuadraticForm/` and `Lattice/Mukai/` root
  the **exponential-plane** charges, not "the whole charge/wall lane", since
  `Wall.ChargeFamily` and its two concrete children do not factor through them and
  the `n = 3` charge has no positive-plane presentation the repository owns; file
  counts are 9 and 9.
- *Repository* — survives.  All citations real, the definitional chain confirmed,
  and the kind is right: the root exists and is used in code, unused in the
  documented tree.  **Corrections applied:** the omission is larger than stated —
  `ExteriorPower/`, `Matrix/`, `FiniteDimensional/`, `Lattice/{Arithmetic,Mukai,Numerical}/`
  and `QuadraticForm/` are **all** unrecorded, so the amended node should cover the
  subject; keep the `ChargeFamily`-is-a-sibling paragraph verbatim in the committed
  text.
- *Adoption and cost* — survives; every link verified as already compiled, so there
  is nothing to adopt, only to document, at essentially zero cost.  **Corrections
  applied:** say that the numerical-lane realization is dimension-pinned at
  `NumericalVarietyData 2`, or the amended spine implies an n-general Mukai charge
  lane that does not exist; and name `WallFiniteness.lean`/`WallRegion.lean` as the
  finiteness engine, since that is what docs-04's adoption turns on.

### 3.C Low impact

Seven findings survived all three lenses but were rated low by at least two of
them.  They are recorded in full because the report is read by machine as well as
by hand; each is a one-file change or a documentation line.

#### charges-05 — `chargeSlope` and `slopeH` are one quotient

**Kind** same-equation-two-names · **Impact** low · **Confidence** 0.7

**Declarations.**  `Wall.chargeSlope` (`Walls/ChargeFamily.lean:118`);
`DivisorSpace.slopeH` (`Walls/Divisorial/Slope.lean:64`);
`Numerical.slope` (`Walls/Numerical/Slope.lean:41`);
`WeakStabilityFunction.slope` (`Weak/Function/Slope.lean:52`).

**Parent equation.**  `μ(v) = re/im` — a partial quotient of two additive
functionals, undefined where the denominator vanishes, with the same three lemmas
(`slope_smul`, `slope_eq_iff`, `slope_lt_iff`) proved at each site.  Negative
result N4 records that `slopeH = ∫Hⁿ·(d₁/d₀)` is the *same* quotient at a
different pair of functionals, not a different notion of slope.

**Proposed root.**  `Order/Slope.lean` (or beside `ChargeFamily`):
`slopeOf (num den : N →+ ℝ) (v : N) : ℝ := num v / den v`, with the three lemmas
stated once under `den v ≠ 0`.

**Projections.**  All four are `rfl` after unfolding the two functionals; the
`Numerical` and `Weak` leaves additionally keep their `im < 0` orientation lemma,
which is about the sign convention and not about the quotient.

**Future examples covered.**  Threefold tilt slope `ν_{β,ω}`; any Kuznetsov-component
slope; twisted slopes for a B-field.

**Verdicts.**
- *Mathematics* — survives at low.  The four quotients verified identical; the
  three lemmas are genuinely one proof each.  **Correction applied:** two of the
  four leaves orient the denominator downward (`im < 0`), so the root's `slope_lt_iff`
  must be stated with an explicit sign hypothesis rather than assuming positivity.
- *Repository* — survives at low.  All four citations exact; no Mathlib root exists
  (`Slope` in Mathlib is the divided-difference of a function, a different notion).
  **Correction applied:** do not name it `slope` at root level — the name collides
  with `Mathlib/Analysis/Calculus/Slope.lean` in the root namespace.
- *Adoption and cost* — survives at low.  Four `rfl` projections, one new small
  module, no gate impact (`def`s are not counted).  The content saved is nine
  one-line lemmas, so this is worth doing only when one of the four files is already
  being touched.

#### charges-06 — Two spellings of "the charge of a shifted object"

**Kind** same-equation-two-names · **Impact** low · **Confidence** 0.65

**Declarations.**  `ChargeFamily.charge_neg` (`Walls/ChargeFamily.lean:96`);
`PreStabilityCondition.central_shift` (`Foundation/PreStabilityCondition.lean:121`);
`WeakStabilityFunction.Z_shift` (`Weak/Function/Basic.lean:88`).

**Parent equation.**  `Z(E[1]) = −Z(E)`, which on the Grothendieck group is
`Z(−v) = −Z v` — the `map_neg` of an `AddMonoidHom`.  All three sites restate
Mathlib's `map_neg` under a local name.

**Proposed root.**  None new: delete the three restatements and call `map_neg`,
or keep one `@[simp]` alias per namespace with a docstring saying it is `map_neg`.

**Projections.**  All three are `map_neg _ _` verbatim.

**Future examples covered.**  Every future charge on an additive carrier, including
the abstract root of §2.

**Verdicts.**
- *Mathematics* — survives at low; it is literally `map_neg`.
- *Repository* — survives at low.  All three citations exact.  **Correction
  applied:** the three aliases are `@[simp]`-tagged and the bare `map_neg` is not
  in the relevant simp sets at two of the three sites, so deleting them changes
  automation — keep the aliases and document them rather than deleting.
- *Adoption and cost* — survives at low, with the same caveat: the only defensible
  change is a one-line docstring at each site.  Recorded so that the abstract root
  of §2 does not acquire a fourth copy.

#### weak-tilting-07 — `HeartBoundedness` restated for the tilted heart

**Kind** leaf-copies-root · **Impact** low · **Confidence** 0.7

**Declarations.**  `TStructure.HeartBoundedness` (`Triangulated/TStructure/Bounded.lean:44`);
`Tilt.HeartBoundedness` (`StabilityCondition/Weak/Tilt/Heart.lean:96`);
`tilt_heartBoundedness` (`Tilt/Heart.lean:131`).

**Parent structure.**  The two-field boundedness record on a heart.  The tilt
version restates both fields on the tilted t-structure instead of taking the
generic record at `t.tilt`.

**Proposed root.**  Existing: `TStructure.HeartBoundedness`, applied at the tilted
t-structure.

**Projections.**  `Tilt.HeartBoundedness t s := TStructure.HeartBoundedness (t.tilt s)`
— an `abbrev`; `tilt_heartBoundedness` becomes the constructor for that.

**Future examples covered.**  Double tilts (the threefold tilt-stability
construction needs two), and boundedness of any future heart obtained by tilting.

**Verdicts.**
- *Mathematics* — survives at low.  The fields are the generic ones at `t.tilt s`.
- *Repository* — survives at low.  Both citations exact.  **Correction applied:**
  `Tilt.HeartBoundedness` is a `structure`, so it is counted by
  `check_single_instantiation.py`; replacing it by an `abbrev` removes a counted
  inhabitant of nothing (it has no baseline row) but does change the audit payload.
- *Adoption and cost* — survives at low.  One file, one `abbrev`, two audit lines.
  Worth doing when the double-tilt lane lands, and not before.

#### dg-06 — Two names for the shifted Hom-complex degree convention

**Kind** same-equation-two-names · **Impact** low · **Confidence** 0.6

**Declarations.**  `HomComplex.shiftIso` consumers in
`Algebra/Homology/DGCategory/Shift.lean:73`;
`DGEnhancement.shiftDegree` (`Triangulated/DGEnhancement/Shift.lean:58`).

**Parent equation.**  `Hom(X, Y[n])_m ≅ Hom(X,Y)_{m+n}`, Mathlib's `HomComplex`
shift isomorphism.  The enhancement side names the index shift separately and
proves the two cocycle compatibilities Mathlib already has.

**Proposed root.**  Existing: Mathlib's `HomComplex.shiftIso` and its `Cochain`
degree lemmas, called directly.

**Projections.**  Both compatibilities are `simp [HomComplex.shiftIso]` from
Mathlib — verified at one of the two sites; the second was not attempted.

**Future examples covered.**  Any dg enhancement of a triangulated category with a
shift, including the Kuznetsov-component enhancements.

**Verdicts.**
- *Mathematics* — survives at low, with the caveat that only one of the two
  compatibilities was checked.
- *Repository* — survives at low.  Both citations exact.  **Correction applied:**
  `shiftDegree` is a `def` with a `Nat`/`Int` coercion the Mathlib lemma does not
  carry, so the projection needs an explicit cast lemma, not a bare `simp`.
- *Adoption and cost* — survives at low.  One file; the saving is two short proofs.
  Recorded rather than scheduled.

#### sites-08 — `ContainsZero` re-derived for coherent sheaves

**Kind** existing-root-unused · **Impact** low · **Confidence** 0.8

**Declarations.**  `Scheme.coherent_containsZero`
(`AlgebraicGeometry/Modules/Coherent/Abelian/Basic.lean:31`);
Mathlib `ObjectProperty.ContainsZero` and its `prop_of_isZero` route.

**Parent structure.**  "`P` holds at a zero object", which Mathlib derives from
`IsClosedUnderIsomorphisms` plus one witness.  The coherent version rebuilds the
witness from a presentation.

**Proposed root.**  Existing: `ObjectProperty.ContainsZero`, with the coherent
instance supplied by `prop_of_isZero` and the zero-module presentation.

**Projections.**  One instance, compiled.

**Future examples covered.**  Quasi-coherent, perfect, and torsion subcategories
getting `ContainsZero` by the same three-line route.

**Verdicts.**
- *Mathematics* — survives at low.
- *Repository* — survives at low; the citation is exact and the Mathlib route
  exists.  **Correction applied:** the existing proof is already only four lines,
  so the saving is one line, not a construction.
- *Adoption and cost* — survives at low.  Bundle with sites-05, which touches the
  same file; do not ship alone.

#### docs-07 — `abstraction-tree.md` says "the one stability-consuming child"

**Kind** existing-root-unused (documentation) · **Impact** low · **Confidence** 0.95

**Declarations.**  `docs/architecture/abstraction-tree.md` (the
`AlgebraicGeometry` node's stability line);
`scripts/check_layering.py:99-108`, whose `STABILITY_CONSUMING_GEOMETRY` set has
**four** entries: `Moduli`, `Numerical`, `DerivedCategory.Stability`, and
`AlgebraicGeometry.Stability`;
`CLAUDE.md`'s "Stability-neutral geometry" bullet, which names **three**.

**Parent structure.**  The documented tree and the enforced gate disagree about
the arity of one node.  This is the documentation shadow of the charge lane: the
`Numerical/` subtree is a stability consumer in the gate and is invisible in the
spine, which is exactly why the n-fold charge root has no documented home.

**Proposed amendment.**  Replace the singular phrase by the enumerated four, with
the gate line as the citation, and reconcile `CLAUDE.md`'s three-name list in the
same change.

**Projections.**  Documentation only.

**Future examples covered.**  The `Stability/Kuznetsov/` subtree proposed in §2.7,
which would be a fifth entry and currently has nowhere to be recorded.

**Verdicts.**
- *Mathematics* — survives at low; nothing mathematical is at stake.
- *Repository* — survives at low and is unambiguous: the gate set and the prose
  disagree, verified by reading both.  **Correction applied:** `CLAUDE.md` names
  three, not four, so two documents need the same edit; `CLAUDE.md` is outside this
  audit's authorized write scope and is recorded as a follow-up.
- *Adoption and cost* — survives at low.  Two lines in one authorized file plus one
  follow-up line elsewhere.

#### docs-08 — Five baseline rows with no recorded reason

**Kind** existing-root-unused (documentation) · **Impact** low · **Confidence** 0.9

**Declarations.**  `scripts/single_instantiation_baseline.txt` lines 18, 42, 50,
64, 74 — `SerreFunctor.SphericalExtProfile`, `SlopeData`, `WeakSlopeData`,
`Wall.Spherical.BoundedRegion`, `WeakStabilityFunction.QuadraticSupportData`.

**Parent structure.**  The baseline file records single-inhabitant abstractions
that are grandfathered.  Four of these five are the subjects of confirmed findings
in this report (docs-03, docs-04, docs-05, and the slope pair under charges-05),
and the file records no reason for any of them, so a reader cannot tell a
deliberate negative result from an unfinished unification.

**Proposed amendment.**  Add a one-line reason to each row, citing either the
finding that would retire it or the negative result that keeps it; and mark
line 64 **stale** — `BoundedRegion` has two inhabitants today (`boxRegion` appears
twice in `Examples/Surface/`), so the row no longer describes reality.

**Projections.**  Documentation only; the stale row can be deleted once verified
by a gate run.

**Future examples covered.**  Any future grandfathered row, which should carry its
reason from the day it is added.

**Verdicts.**
- *Mathematics* — survives at low.
- *Repository* — survives at low.  All five line numbers verified against the file.
  **Correction applied:** line 64 is stale, as recorded in docs-04; deleting it is
  a gate-visible change and must be done in the same PR as a gate run, not in a
  docs-only slice.
- *Adoption and cost* — survives at low.  The baseline file is outside this audit's
  authorized write scope; recorded as a follow-up PR.

## 4. Refuted findings

Six of the 89 reported findings were killed by the majority rule — at least two of
the three lenses refused them.  They are recorded with their ids because a
falsified unification is itself an architecture result, and because a later pass
that re-proposes one of them should find the refutation rather than repeat the
work.  The last column says whether the refutation is worth writing into
`docs/architecture/abstraction-tree.md` as a standing negative result.

#### walls-08 — "Every wall is the zero locus of a quadratic form"

**Kind proposed** missing-root · **Verdict** refuted 3–0 · **Record as negative
result** yes, as N15.

**Claim.**  `Wall.Spherical.wall` (`Walls/Spherical/Basic.lean:212`),
`PeriodDomain.wall` (`QuadraticForm/WallLocus.lean:88`),
`DivisorSpace.numericalWall` (`Walls/Divisorial/Wall.lean:141`) and
`Numerical.wall` (`Walls/Numerical/Wall.lean:57`) were proposed as four
specializations of one root "the locus where a quadratic form in the parameters
vanishes".

**Winning refutation** (all three lenses).  They are not the same kind of locus.
`PeriodDomain.wall` is a **vanishing** condition — `Im(Z(δ)) = 0` and
`Re(Z(δ)) = 0` on a class with `Q δ = −2` — while `Spherical.wall` is an
**inequality** region and `numericalWall` an equality between two *slopes*, which
is a vanishing condition only after clearing a denominator that is allowed to be
zero.  `WallComparison.lean` already exists to relate the first two and proves only
a one-way inclusion, stating explicitly that the two finiteness theorems are not
restatements of each other.  The repository lens added that the proposed root's
signature would have to take the quadratic form, the class, and a side condition
naming which of the three shapes is meant — at which point it is a disjunction, not
a parent.  The adoption lens added that no leaf could be an `abbrev` and every
downstream lemma would need re-proving through the disjunction.

**What survives.**  Nothing at the wall level; the plane-level comparison
`expPlane_eq_chartPlane` already exists and is `rfl`, and docs-04 is the part of
this territory that did survive.

#### weak-tilting-08 — "The HN filtration is a filtration in the `Order` sense"

**Kind proposed** existing-root-unused · **Verdict** refuted 2–1 · **Record as
negative result** yes, as N16.

**Claim.**  `WeakStabilityCondition.HNFiltration`
(`Weak/HarderNarasimhan/Basic.lean:64`) and `PreStabilityCondition.HNFiltration`
(`HarderNarasimhan/Basic.lean:58`) were proposed to reach Mathlib's
`RelSeries`/`CompositionSeries` machinery, so that uniqueness and refinement would
come from order theory.

**Winning refutation** (mathematics and adoption).  An HN filtration is not a chain
in a poset: its data are *triangles*, not subobjects, and the ambient category is
triangulated, not abelian, so there is no lattice of subobjects to take a series
in.  Mathlib's `RelSeries` requires a relation on a type; the triangles here have
distinguished-triangle content that a relation cannot carry, and the strict slope
decrease is a property of the factors, not of a relation between consecutive terms.
The adoption lens added that the two existing uniqueness proofs argue by
`Hom`-vanishing between semistable factors, which is exactly the content `RelSeries`
does not supply — so nothing would be saved.  The repository lens dissented,
pointing out that `RelSeries` is used elsewhere in the tree for the t-structure
slicing; that use is on an honest poset of degrees and does not generalize here.

**What survives.**  The genuine shared root between the two HN filtrations is
already recorded as weak-tilting-01; this finding proposed a *third*, upstream root
and that is what failed.

#### symmetry-metric-06 — "The three metric-like distances share a root"

**Kind proposed** missing-root · **Verdict** refuted 2–1 · **Record as negative
result** yes, as N17.

**Claim.**  The slicing distance in `StabilityCondition/Metric.lean`, the
`Wall` chamber distance, and the parameter-space Euclidean norm were proposed as
three instances of one `PseudoMetricSpace`-valued root parametrized by a supremum
over classes.

**Winning refutation** (mathematics and adoption).  The first is a `sSup` over
objects of a difference of phases and is only a **pseudo**metric with an `⊤`-valued
branch on the empty category; the second is not a distance at all but a membership
predicate for a chamber; and the third is Mathlib's norm, already rooted.  The
proposed root would be `sSup`-valued into `ℝ≥0∞` and would need a separate
finiteness hypothesis at each site — different at each site.  The adoption lens
added that `Metric.lean` already carries a `PseudoMetricSpace` instance obtained
from Mathlib, so the "missing root" is present for the only leaf that is a metric.

**What survives.**  The observation that the chamber predicate should be stated as
a `Set` membership and not as a distance — a style point, out of scope here.

#### dg-07 — "`HomComplex` and `DGCategory` Hom-objects are one carrier"

**Kind proposed** leaf-copies-root · **Verdict** refuted 2–1 · **Record as
negative result** no; `docs/adr/ADR-0010` already records this decision and its
reasons.

**Claim.**  `DGCategory.Hom` was proposed to be an `abbrev` for Mathlib's
`HomComplex`, removing the bespoke carrier.

**Winning refutation** (repository and adoption).  ADR-0010 and ADR-0011 already
adjudicated this: `DGCategory` is deliberately *built on* `HomComplex` rather than
identified with it, because the composition and the shift need a `CochainComplex`
indexed the other way, and because the enriched encoding (Option A′) was explicitly
deferred.  Re-proposing the identification without addressing the ADR is the
failure mode the ADR exists to prevent.  The adoption lens added that
`CLAUDE.md` states the subtree moves under `CategoryTheory/Enriched/` *in the same
change* if Option A′ ever lands, so this is a planned migration with a named
trigger, not a missing abstraction.  The mathematics lens dissented on the ground
that the two carriers are definitionally equal in the cases the repository uses;
that is true and is not the question the ADR asked.

**What survives.**  Nothing new; dg-01 through dg-06 are the parts of this lane
that survived.

#### triang-08 — "Semiorthogonal decompositions and t-structures share a root"

**Kind proposed** missing-root · **Verdict** refuted 3–0 · **Record as negative
result** yes, as N18.

**Claim.**  `TStructure` and `SemiorthogonalDecomposition` were proposed as the
`n = 2` and general cases of one "orthogonal filtration of a triangulated
category" root, since both give every object a functorial triangle with factors in
prescribed subcategories.

**Winning refutation** (all three lenses).  The orthogonality conditions point in
opposite directions and are not the same axiom at different arities: a t-structure
requires `Hom(D^{≤0}, D^{≥1}) = 0` **and** closure under the shift in one
direction, which a semiorthogonal decomposition's admissible pieces do not satisfy —
the pieces of an SOD are shift-stable in *both* directions.  A t-structure is
therefore not a two-piece SOD, and the standard relation runs the other way (an SOD
plus a t-structure on each piece glues to a t-structure).  The repository lens added
that `Triangulated/TStructure/` and `Triangulated/SemiorthogonalDecomposition/` are
built on disjoint APIs with no shared lemma today, and the adoption lens that the
gluing theorem — the real shared content — is a theorem to prove, not a root to
factor out, and is out of scope for an abstraction audit.

**What survives.**  The gluing theorem is worth an issue; it is a missing theorem,
which this audit does not report.

#### geometry-derived-05 — "`Coh` and `Dqc` membership predicates share a root"

**Kind proposed** duplicate-parent · **Verdict** refuted 2–1 · **Record as
negative result** no; it restates the `Dqc/Comparison.lean` ledger already in
`docs/architecture/placement.md`.

**Claim.**  The coherence predicate on `X.Modules` and the quasicoherent-cohomology
locus predicate on `D(X.Modules)` were proposed as one "locally finitely presented
cohomology" root.

**Winning refutation** (repository and adoption).  One is a property of a sheaf and
the other a property of a complex, related only by the explicit propositions
`Dᵇ(Coh X) ≃ Dᵇ_coh(Dqc X)`, which `CLAUDE.md` says must **remain** explicit
propositions and not become instances before the geometric theorem is proved.  A
shared root would have to be stated on the complex and would therefore prejudge
exactly that theorem.  The adoption lens added that `Dqc/Comparison.lean` already
consumes supplied evidence for precisely this comparison, so the mechanism exists
and the finding proposes to bypass it.  The mathematics lens dissented that the
predicates are both "degreewise finite presentation"; that is the statement of the
theorem, not a definitional identity.

**What survives.**  geometry-derived-01, -02, -03 and -06 carry the surviving
content of this lane.

## 5. Verifier "missed" notes

Each of the three lenses was asked, after judging the surveyed findings, what the
survey had missed in its lane.  The 117 notes below are their answers.  They are
**candidate** findings only: none has been through the three-lens refutation, none
has had its citations fully verified, and several will not survive.  They are
recorded with ids so a second pass can pick them up by name.  The lens that raised
each note is given in italics.

### 5.A charges (11)

- **miss-charges-01** (*mathematics*) — `ChargeFamily.charge` and the abstract
  root of §2 both quantify over a single class; no lane looked at charges valued in
  a *family* of complex lines (a `ℂ`-torsor), which is what a twisted charge on a
  gerbe needs.  Candidate missing-root above `expCharge`.
- **miss-charges-02** (*mathematics*) — the `B`-field twist appears as
  `expCharge` precomposition on the lattice side and as a `DivisorSpace`
  translation on the divisorial side; only the ℚ-coefficient law was surveyed
  (negative result N6), and the ℝ law's own shape was not examined for a shared
  root with the ℚ one at the level of the *group action*, which is where the two
  might still meet.
- **miss-charges-03** (*repository*) — `Walls/Numerical/Basic.lean` defines
  `NumClass` as a bare `abbrev` for `ℝ × ℝ × ℝ` with hand-written `.deg0/.deg1/.deg2`
  projections; the threefold file defines its own on `ℝ⁴`.  The survey treated the
  charges but not the **carriers**; a `Fin (n+1) → ℝ` root with named projections is
  a separate candidate.
- **miss-charges-04** (*repository*) — no finding covered
  `Numerical/GrothendieckGroup/CentralCharge.lean`'s `numericalCharge` against
  `MukaiChargeData.chargeHom`; they are cited in docs-06 as links in a chain but
  never compared to each other as siblings.
- **miss-charges-05** (*adoption*) — the migration plan in §2.7 does not say what
  happens to the ~40 `@[simp]` lemmas attached to the existing concrete charges when
  they become projections of the root; a slice-0 inventory of those simp sets is a
  prerequisite the plan is missing.
- **miss-charges-06** (*adoption*) — `#print axioms` payload lines naming the
  concrete charge definitions were not counted; if any are in an immutable review
  payload, the rename half of slice 3 is blocked and needs the
  `RestateHistoricalNames` bridge.
- **miss-charges-07** (*mathematics*) — the Todd correction is carried as an
  optional multiplicative factor in the §2 root; nobody checked whether the
  *square-root* Todd used for the K3 Mukai vector and the full Todd used for the
  numerical lane can be the same parameter, or whether the root needs two slots.
- **miss-charges-08** (*mathematics*) — charges on a **relative** base (a family
  of varieties over `S`) were not examined at all; `Moduli/` has the family
  machinery and no charge lane reaches it.
- **miss-charges-09** (*repository*) — `Walls/ChargeFamily.lean` has no umbrella
  entry check in this audit; whether `Walls.lean` re-exports every child was not
  verified, and the migration adds two modules.
- **miss-charges-10** (*adoption*) — the parity theorem `⟪v,w⟫ = (-1)ⁿ⟪w,v⟫` is
  proved in the scratch file but no existing repository lemma was located that it
  would replace; if none exists, the root ships a theorem with no consumer.
- **miss-charges-11** (*adoption*) — the cost of `moments` indexing was estimated
  against the surface leaf only; the threefold leaf's four-component carrier has a
  different projection pattern and was not costed.

### 5.B walls (10)

- **miss-walls-01** (*mathematics*) — the numerical wall and the tilt wall in
  `Weak/Tilt/` were never compared; both are "slope equality after a tilt" and the
  survey covered only the untilted pair.
- **miss-walls-02** (*mathematics*) — wall **crossing** (the change of the
  semistable locus across a wall) has no root anywhere and was not surveyed; every
  existing statement is per-example.
- **miss-walls-03** (*repository*) — `Walls/Spherical/DivisorialRegion.lean`'s
  heading "The two charts are one" suggests further `rfl` comparisons beyond
  `expPlane_eq_chartPlane`; the file was read only at the two cited lines.
- **miss-walls-04** (*repository*) — the `boxRegion` inhabitants that make
  baseline line 64 stale were found by grep in `Examples/Surface/` but their
  definitions were not read; if they are both in one file they may themselves be a
  copy.
- **miss-walls-05** (*adoption*) — docs-04's projection needs the constant
  transfer from `BoundedRegion` to `PlaneRegion`; nobody attempted it in Lean, so
  the "only the constant transfer is open" claim is unverified.
- **miss-walls-06** (*mathematics*) — the finiteness engines in
  `WallFiniteness.lean` and `Spherical/Finiteness.lean` both run a `ZSpan`
  argument; whether the `ZSpan` step itself is a shared lemma was not checked.
- **miss-walls-07** (*mathematics*) — `Walls/Divisorial/Discriminant.lean`'s
  `HodgeDefinite` is used as a certificate in two lanes; whether it should be a
  class rather than a structure was not considered.
- **miss-walls-08** (*repository*) — the `Examples/Surface/` wall families
  (`p2ProjectiveWallFamily` and its siblings) were cited but not compared to each
  other; four examples with the same shape is the pattern this audit hunts.
- **miss-walls-09** (*adoption*) — the 19 immutable `#print axioms` lines named in
  docs-04 were counted but not read; whether they name `BoundedRegion` fields or
  only the structure was not established.
- **miss-walls-10** (*adoption*) — no estimate exists for how much of
  `Spherical/Finiteness.lean` survives if docs-04 lands; "roughly 110 lines" is the
  adoption lens's own figure and was not independently checked.

### 5.C numerical-nfold (10)

- **miss-numerical-nfold-01** (*mathematics*) — the Hirzebruch–Riemann–Roch
  statement is instantiated at `n = 2, 3, 4`; the `n`-general statement exists but
  nobody checked whether its proof is by induction on `n` or by a closed formula,
  which decides whether a fifth dimension is free.
- **miss-numerical-nfold-02** (*mathematics*) — `chComp` and `toddComp` are
  indexed by degree; the survey did not ask whether they should be a single graded
  object rather than two families.
- **miss-numerical-nfold-03** (*repository*) — `Examples/RankOne.lean`'s docstring
  records the surface specialization as deliberate unfinished work; the rest of
  that file's migration ledger was not read.
- **miss-numerical-nfold-04** (*repository*) — `Specializations/Threefold.lean`
  and `Specializations/Fourfold.lean` were read for their CY predicates only; the
  remaining declarations in both files are unsurveyed.
- **miss-numerical-nfold-05** (*adoption*) — surf-08's `extends` route was chosen
  over `abbrev` because `IsK3` has ~60 hypothesis positions; that count was
  produced by one grep and not cross-checked.
- **miss-numerical-nfold-06** (*mathematics*) — the numerical lane's
  `structureSheafEulerCharacteristic` is n-general but the `Numerical/` charge is
  pinned at `NumericalVarietyData 2`; whether the pin is essential or incidental was
  not determined.
- **miss-numerical-nfold-07** (*mathematics*) — no finding covers the **degree**
  function `∫Hⁿ` as an n-general object; it appears inline at three dimensions.
- **miss-numerical-nfold-08** (*repository*) — `RiemannRoch/General.lean` was cited
  at one line; its relationship to `RiemannRoch/Surface/` is a candidate
  root/leaf pair that was not examined.
- **miss-numerical-nfold-09** (*adoption*) — the `| 1 => 0` literal branch that
  preserves several `rfl`s in surf-07 was verified for three models; the `ℙ²` model
  was not re-checked after the correction.
- **miss-numerical-nfold-10** (*adoption*) — no audit-payload impact was computed
  for numerical-nfold-01 through -04, which touch the most-consumed structures in
  the lane.

### 5.D weak-tilting (10)

- **miss-weak-tilting-01** (*mathematics*) — the double tilt needed for threefold
  tilt stability does not exist in the tree; whether the single-tilt API composes is
  unverified and decides whether weak-tilting-07 is worth doing.
- **miss-weak-tilting-02** (*mathematics*) — `Weak/Support/` has two support
  predicates (quadratic and the plain inequality); only the quadratic pair was
  surveyed.
- **miss-weak-tilting-03** (*repository*) — `layers.md` rule 4 was quoted but the
  rest of the weak/ordinary parallel API was not enumerated; docs-05 names seven
  members of one family and there may be more.
- **miss-weak-tilting-04** (*repository*) — `Weak/Function/Slope.lean` and
  `Weak/Support/Predicate/` were read at cited lines only.
- **miss-weak-tilting-05** (*adoption*) — docs-05's refutation turns on the
  ordinary `charge_compatible` being strictly stronger; that strictness was asserted
  from the signature and not proved.
- **miss-weak-tilting-06** (*mathematics*) — the HN filtration's uniqueness proof
  is cited as `Hom`-vanishing in the weak-tilting-08 refutation; whether the weak
  and ordinary uniqueness proofs are the same proof was not checked, and that is a
  candidate leaf-copies-root.
- **miss-weak-tilting-07** (*mathematics*) — `Weak/Support/Predicate/ZeroChargeLattice.lean`
  was surveyed for saturation (lattices-08) but its `Quotient` API's relationship to
  `RelativeNumerical.Group` was only noted, not examined.
- **miss-weak-tilting-08** (*repository*) — the weak tree's umbrella deliberately
  omits the Bridgeland child; whether any proposed root in this lane would violate
  that omission was not checked for weak-tilting-04 through -06.
- **miss-weak-tilting-09** (*adoption*) — no count exists of how many weak-side
  declarations would change spelling if weak-tilting-01 lands.
- **miss-weak-tilting-10** (*adoption*) — the `PreStabilityCondition` `extends`
  edge is the repository's own precedent for this lane's shape; nobody checked
  whether that edge is used or merely declared.

### 5.E symmetry-metric (9)

- **miss-symmetry-metric-01** (*mathematics*) — the `GL⁺(2,ℝ)` action on stability
  conditions and the `Aut` action are two group actions on the same space; only the
  first was surveyed.
- **miss-symmetry-metric-02** (*mathematics*) — the orientation cocycle in
  `QuadraticForm/OrientationCocycle.lean` was surveyed for `pairingDet` only; its
  cocycle condition may be an instance of a general `H¹` statement.
- **miss-symmetry-metric-03** (*repository*) — `StabilityCondition/Metric.lean`
  was read at the instance line; the rest of the file is unsurveyed.
- **miss-symmetry-metric-04** (*repository*) — the `PositivePairOpen.lean` and
  `Orientation.lean` pair share more than `pairingDet`; the openness statements were
  not compared.
- **miss-symmetry-metric-05** (*adoption*) — lattices-04's root touches four files;
  no build-time estimate was made, and `BilinForm` files are import-heavy.
- **miss-symmetry-metric-06** (*mathematics*) — whether the `PlaneRegion` uniform
  constant is an operator norm in disguise was raised and not pursued.
- **miss-symmetry-metric-07** (*mathematics*) — the deformation/support-property
  connection (Bridgeland's theorem that the support property makes the space a
  manifold) has no root and was out of every lane's scope.
- **miss-symmetry-metric-08** (*repository*) — `symmetry-metric-03` through `-05`
  cite files in two directories; whether the proposed roots respect the geometry
  firewall was checked for the roots but not for their future consumers.
- **miss-symmetry-metric-09** (*adoption*) — no `#print axioms` payload impact was
  computed for this lane at all.

### 5.F dg (9)

- **miss-dg-01** (*mathematics*) — the dg enhancement's `CommShift` data (dg-04)
  and the dg category's own shift (dg-06) were surveyed separately; whether they are
  the same shift was not asked.
- **miss-dg-02** (*mathematics*) — `Algebra/Homology/DGCategory/` has a `Tensor`
  file that no lane opened.
- **miss-dg-03** (*repository*) — ADR-0010 and ADR-0011 were cited in the dg-07
  refutation from their titles; neither was read in full, and ADR-0011 may already
  record dg-01's root.
- **miss-dg-04** (*repository*) — `HomotopyCategory/DGEnhancement/` mirrors
  `Triangulated/DGEnhancement/`; the mirror was not checked for copied fields, which
  is precisely this audit's disease.
- **miss-dg-05** (*adoption*) — dg-04's `commShift_naturality` left a residual goal
  after three attempts; the note is recorded in the finding but no bound was put on
  the fix.
- **miss-dg-06** (*mathematics*) — the `Cochain` degree conventions differ by a
  sign between two files; whether that is a genuine convention split or a copy with
  a bug was not determined.
- **miss-dg-07** (*repository*) — `functorCategoryHasShift`'s zero consumers
  (sites-06) suggests other zero-consumer roots in `CategoryTheory/Shift/`; no sweep
  was run.
- **miss-dg-08** (*adoption*) — the dg lane's proposed roots were not checked
  against `lake exe runLinter`; several are `def`s that may need `@[simp]` or
  `@[reducible]` attributes the linter enforces.
- **miss-dg-09** (*adoption*) — no estimate of elaboration-time impact was made for
  dg-01, which sits under a heavily-imported module.

### 5.G triang (10)

- **miss-triang-01** (*mathematics*) — `Triangulated/Subcategory/` and
  `ObjectProperty/` both carry closure predicates; sites-05 found the abelian/
  triangulated mirror for one predicate and nobody swept the rest.
- **miss-triang-02** (*mathematics*) — admissibility of a subcategory is stated as
  the existence of adjoints in one place and as a semiorthogonal complement in
  another; the two were not compared.
- **miss-triang-03** (*repository*) — `Triangulated/SemiorthogonalDecomposition/Exceptional.lean`
  hosts the generic `IsExceptional` root that surf-06 reaches; the rest of that file
  is unsurveyed.
- **miss-triang-04** (*repository*) — `Triangulated/Generators/` and
  `Triangulated/CompactGeneration/` overlap by name; no lane opened either.
- **miss-triang-05** (*adoption*) — triang-04 through -07 all touch
  `Triangulated/`, the most-imported subtree; no combined rebuild estimate exists.
- **miss-triang-06** (*mathematics*) — the Verdier quotient appears in two
  constructions (the residual category and the localization); whether they reach one
  root was not asked.
- **miss-triang-07** (*mathematics*) — `Triangulated/TStructure/HeartBridge.lean`
  was cited for `heart_biprod` only; the bridge's other direction is unsurveyed.
- **miss-triang-08** (*repository*) — the triang lane cites nine files; the
  directory has substantially more, and the sampling strategy was breadth-first by
  filename, which systematically misses deep leaves.
- **miss-triang-09** (*adoption*) — no check that the proposed triang roots keep
  `Triangulated/` importable without `AlgebraicGeometry/`, which the firewall
  requires.
- **miss-triang-10** (*adoption*) — the gluing theorem named in the triang-08
  refutation is a missing theorem and therefore out of scope, but it should be filed
  as an issue and nobody did.

### 5.H geometry-derived (9)

- **miss-geometry-derived-01** (*mathematics*) — `Dqc/Comparison.lean` consumes
  supplied evidence; whether the evidence type is itself a copy of a coherence
  predicate was not checked.
- **miss-geometry-derived-02** (*mathematics*) — the three uses of "perfect"
  named in `placement.md` are related by one-way adapters; that ledger is exactly a
  recorded negative result and was not cross-referenced into this report's §2.6.
- **miss-geometry-derived-03** (*repository*) — `AlgebraicGeometry/DerivedCategory/Families/`
  was not opened by any lane despite being the natural home for relative charges
  (miss-charges-08).
- **miss-geometry-derived-04** (*repository*) — `FourierMukai/` kernels were cited
  once; the convolution API is unsurveyed.
- **miss-geometry-derived-05** (*adoption*) — geometry-derived-04's surviving
  deliverable is two transport lemmas; no home was chosen for them.
- **miss-geometry-derived-06** (*mathematics*) — base change of pre-stability data
  and base change of charges are the same operation at two levels; only one was
  surveyed.
- **miss-geometry-derived-07** (*repository*) — `Moduli/PerfectComplex/Comparison.lean`
  is named in `CLAUDE.md` as an adapter ledger and was never read.
- **miss-geometry-derived-08** (*adoption*) — the geometry lane's findings were
  costed in files touched, not in audit-payload lines, which is the binding cost in
  `AlgebraicGeometry/`.
- **miss-geometry-derived-09** (*adoption*) — no lane checked whether any proposed
  root would force `AlgebraicGeometry/DerivedCategory.lean` to import its `Stability`
  child, which the umbrella deliberately omits.

### 5.I lattices (10)

- **miss-lattices-01** (*mathematics*) — `Lattice/Arithmetic/` was not opened;
  discriminant and genus theory may already contain the Gram-determinant root
  lattices-04 proposes.
- **miss-lattices-02** (*mathematics*) — the three distinct surface lattices
  recorded as negative result N14 were distinguished by their forms; whether they
  share an *ambient* root (an even indefinite lattice of given signature) was not
  asked.
- **miss-lattices-03** (*repository*) — `Lattice/Numerical/RankTwo.lean`'s
  `NumLattice` carries no form while its docstring names `K_num(Ku(X))`; that gap is
  noted inside lattices-06 but is a candidate finding in its own right.
- **miss-lattices-04** (*repository*) — `Mukai/IntegralBridge.lean` was cited at
  one line; the bridge is the natural place for lattices-01's carrier unification
  and was not read.
- **miss-lattices-05** (*adoption*) — lattices-01 is the largest proposed change in
  the lane and its cost was not separated from lattices-05's, which folds into it.
- **miss-lattices-06** (*mathematics*) — the halved vs unhalved Mukai form
  (negative result N9) has a factor-of-two trap the repository documents; whether
  any *existing* lemma is stated on the wrong side was not audited.
- **miss-lattices-07** (*mathematics*) — `IsotropicSequence.lean`'s docstring
  claims neither existing isotropy notion is reusable; that claim was accepted and
  not tested.
- **miss-lattices-08** (*repository*) — `QuadraticForm/` has nine files and five
  were opened.
- **miss-lattices-09** (*adoption*) — lattices-07's `HasSignature` needs two
  producers on day one to pass the gate; only one was identified with certainty.
- **miss-lattices-10** (*adoption*) — no check whether `Matrix.toBilin'` is
  `@[simp]`-normalized in this tree's simp sets, which decides lattices-06's real
  cost.

### 5.J surf (10)

- **miss-surf-01** (*mathematics*) — `Surface/Enriques/` has a Torelli lane whose
  lattice predicates were not compared with `Lattice/Mukai/`.
- **miss-surf-02** (*mathematics*) — the K3 and abelian Mukai vectors differ by the
  Todd factor only; whether `Surface/SphericalMukai.lean` states the vector
  generically was not checked.
- **miss-surf-03** (*repository*) — `Examples/Surface/` has eight example files and
  five were opened; `BlowUpPlane.lean` was cited at one line.
- **miss-surf-04** (*repository*) — `Surface/Spherical.lean` duplicates three
  consequence proofs; whether other files under `Surface/` duplicate the same three
  was not swept.
- **miss-surf-05** (*adoption*) — surf-04's audit-line impact was counted for
  `AlgebraicGeometryAudit/Core.lean` only.
- **miss-surf-06** (*mathematics*) — `RiemannRoch/Surface/NumericalVariety.lean`'s
  `GeometricData` is the geometry-to-numerics bridge; whether an n-general
  `GeometricData` exists was not asked, and surf-08 needs one for CY3/CY4.
- **miss-surf-07** (*mathematics*) — del Pezzo and general-type surfaces appear in
  no example; whether the proposed roots cover them is untested by construction.
- **miss-surf-08** (*repository*) — `Surface/Enriques/Basic.lean`'s
  `IsEnriquesSurface` is an `outParam` Prop class; whether surf-06's hypothesis
  change breaks instance search was not verified.
- **miss-surf-09** (*adoption*) — surf-05's minimal fix deletes a theorem; whether
  that theorem is named in an audit payload was not checked.
- **miss-surf-10** (*adoption*) — surf-07's projections cannot be `rfl`; the number
  of `rfl` proofs that must be re-closed was estimated as "several" and not counted.

### 5.K sites (10)

- **miss-sites-01** (*mathematics*) — `Sites/Descent/` was not opened; descent data
  is cover-indexed local data, the same shape as sites-07's carrier.
- **miss-sites-02** (*mathematics*) — `SheafCohomology/Cech/` was not opened.
- **miss-sites-03** (*repository*) — `QuasicoherentData` has four hand-built sites,
  not two; the other two were counted but not read.
- **miss-sites-04** (*repository*) — `Sheaf/Presentation/Transport.lean` already
  owns `ofIso` and `over`; the rest of that file is unsurveyed and may already hold
  sites-07's root under another name.
- **miss-sites-05** (*adoption*) — sites-07's whnf non-termination risk is quoted
  from the leaf's own comment; the prototype the finding requires was not run.
- **miss-sites-06** (*mathematics*) — `Abelian/QuasiAbelian.lean` has two further
  copies of the chain-condition pattern (named inside sites-04); they were not
  costed.
- **miss-sites-07** (*repository*) — `Limits/Preserves/` has more files than the
  three sites-03 cites.
- **miss-sites-08** (*adoption*) — sites-05 drops the heart projection; whether
  `heart_biprod` should then be re-stated in terms of the root was left open.
- **miss-sites-09** (*mathematics*) — the Serre-class file and the coherent file
  share a byte-identical body; whether other Serre-class lemmas are likewise copied
  from the coherent side was not swept.
- **miss-sites-10** (*adoption*) — no lane checked whether the proposed
  `ObjectProperty/Extensions.lean` path collides with an existing Mathlib module of
  that name at this pin.

### 5.L docs (9)

- **miss-docs-01** (*repository*) — `docs/architecture/cutover-ledger.md` was never
  read; several findings propose moves that the ledger may already schedule.
- **miss-docs-02** (*repository*) — `docs/architecture/placement.md`'s "perfect"
  ledger is a recorded negative result and is not cross-referenced from
  `abstraction-tree.md`.
- **miss-docs-03** (*mathematics*) — the amended spine text in §2.4 was written
  against the `LinearAlgebra` and `AlgebraicGeometry` nodes; the `CategoryTheory`
  node was not re-read for the charge lane's categorical root.
- **miss-docs-04** (*mathematics*) — negative results N1–N18 now exist; the spine
  has no section for them and §2.6 proposes one without saying where it goes.
- **miss-docs-05** (*adoption*) — `CLAUDE.md` needs the same edit as docs-07 and is
  outside this audit's write scope; no follow-up PR was filed.
- **miss-docs-06** (*adoption*) — `scripts/single_instantiation_baseline.txt` needs
  a reason column; whether the gate script tolerates trailing comments on a baseline
  row was not checked.
- **miss-docs-07** (*repository*) — `docs/reviews/` has one tracked file; whether
  this report's section numbering matches any house convention could not be
  determined from a single sample.
- **miss-docs-08** (*mathematics*) — the design panel's Angle C won at 8.8; the
  losing angles' surviving ideas (the lattice-first `A₂` treatment in particular)
  were not folded into §2.3 and may still be needed for the cubic fourfold.
- **miss-docs-09** (*adoption*) — §2.7's PR slices were not sized; no slice has a
  file count or an estimated build time.

## 6. Totals

Twelve lanes, each surveyed independently and then judged by the three adversarial
lenses under the majority kill rule.  "Files examined" counts files opened by the
lane surveyor or by a lens verifying one of its citations; a file opened by two
lanes is counted in both, so the column sums to more than the number of distinct
files in the repository.

| Lane | Reported | Confirmed | Refuted | Missed notes | Files examined | High | Medium | Low |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| charges | 6 | 6 | 0 | 11 | 84 | 1 | 3 | 2 |
| walls | 8 | 7 | 1 | 10 | 96 | 2 | 5 | 0 |
| numerical-nfold | 8 | 8 | 0 | 10 | 71 | 4 | 4 | 0 |
| weak-tilting | 8 | 7 | 1 | 10 | 88 | 3 | 3 | 1 |
| symmetry-metric | 6 | 5 | 1 | 9 | 63 | 2 | 3 | 0 |
| dg | 7 | 6 | 1 | 9 | 79 | 2 | 3 | 1 |
| triang | 8 | 7 | 1 | 10 | 104 | 3 | 4 | 0 |
| geometry-derived | 6 | 5 | 1 | 9 | 92 | 4 | 1 | 0 |
| lattices | 8 | 8 | 0 | 10 | 67 | 3 | 5 | 0 |
| surf | 8 | 8 | 0 | 10 | 108 | 3 | 5 | 0 |
| sites | 8 | 8 | 0 | 10 | 81 | 2 | 5 | 1 |
| docs | 8 | 8 | 0 | 9 | 64 | 2 | 4 | 2 |
| **Total** | **89** | **83** | **6** | **117** | **997** | **31** | **45** | **7** |

Stated explicitly, because the counts are the part of this report a machine reads
first:

- **89** findings reported across twelve lanes.
- **83** confirmed — they survived all three lenses, or survived a single-lens
  dissent under the majority rule.
- **6** refuted — at least two lenses refused them; all six appear in §4 with their
  ids and the winning refutation.
- **117** verifier "missed" notes, all in §5 with ids, grouped by lane and
  attributed to the lens that raised them.
- **997** file-examinations, over twelve lanes.
- Impact split of the 83 confirmed findings: **31 high**, **45 medium**, **7 low**.
- Of the 83 confirmed, **11** carry a recorded single-lens dissent; the dissent is
  quoted in the finding's verdict bullet rather than being discarded.
- **18** negative results (N1–N18) were produced: fourteen from the central-charge
  design panel in §2.6 and four more from the refutations in §4.

## 7. Recommended next lanes

Ordered.  Each is one pull request, sized so it can be verified by a single
targeted build plus the audit executables, and each is stated so that it can be
started without re-reading this whole report.

1. **Land the exemplar's slice 1 — the abstract central-charge root.**  Add the
   root module and the two generic laws from §2.7, with no leaf touched and no
   rename.  This is the only slice that introduces new files and no migrations, so
   it can land while the leaves are still being argued about.  It also settles the
   `moments` indexing decision in code rather than in prose, which every later slice
   depends on.

2. **Surface and threefold projections (exemplar slices 2 and 3).**  Re-root the
   surface model on ℝ³ and the Bayer–Macrì–Toda model on ℝ⁴ as children at `n = 2`
   and `n = 3`, each by a proved agreement theorem, keeping the existing names as
   projections.  Do not rename anything in this PR; the rename is slice 4 and needs
   the `RestateHistoricalNames` bridge inventory that miss-charges-06 says is
   missing.

3. **lattices-08 plus sites-08.**  The two cheapest existing-root-unused findings,
   both one-file deletions against roots that already exist (`AddSubgroup.saturation`
   and `ObjectProperty.ContainsZero`).  Landing them first establishes the pattern
   for the rest of the audit and costs almost nothing to review.

4. **lattices-01 with lattices-05 folded in.**  The carrier unification is the
   largest single change in the lattice lane and absorbs the sphericity finding
   entirely; doing them together avoids writing a transport lemma that the carrier
   merge then deletes.  Budget for the factor-of-two trap the repository documents
   and for the deprecated `IsOrtho` spelling.

5. **surf-03 then surf-06.**  In that order: surf-06's one-line hypothesis change
   becomes a two-line change once surf-03's `middle_vanishing` field exists, and
   doing surf-06 first means writing a hypothesis that surf-03 immediately retires.

Then, in a second pass: promote the strongest of the 117 notes in §5 to findings
and put them through the same three lenses.  The notes most likely to become high
findings are **miss-lattices-03** (`NumLattice` carries no form while its docstring
names `K_num(Ku(X))`), **miss-surf-06** (no n-general `GeometricData`, which
surf-08's CY3 and CY4 bridges need), and **miss-charges-08** (charges over a
relative base, which the `Families/` machinery is already built for and no charge
lane reaches).
