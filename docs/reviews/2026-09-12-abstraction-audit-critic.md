# Completeness critic — abstraction-generalization audit

Produced by the audit's final stage, 2026-09-12. Read with
`2026-09-12-abstraction-generalization-audit.md`: this document contradicts
parts of it, and where they disagree this one was checked against the tree.

COMPLETENESS CRITIC — audit of /Users/chris.dare/Personal/SourceCode/dag-abstraction-audit/docs/reviews/2026-09-12-abstraction-generalization-audit.md (5,997 lines, read in full; every citation below re-verified by grep/sed against the worktree).

=====================================================================
COVERAGE ARITHMETIC FIRST (the report's own number is misleading)
=====================================================================
Tree: 1,053 `.lean` files in 211 directories under DerivedAlgGeo/.
Report §6 claims "997 file-examinations" and says the column double-counts.
Distinct files actually cited anywhere in the report (§1–§7): 383 of 1,053 (36%).
Distinct files cited in §1–§4 (the confirmed/refuted findings, i.e. what survived
review): 379.
Directories with >=1 cited file: 136 of 211. Directories with ZERO cited file: 75.
So "997 files examined" is a double-counted sum that is still smaller than the
1,053-file tree; real distinct coverage is about a third of it. Any reader who
takes 997 as near-total coverage is wrong by a factor of ~2.7.

=====================================================================
(1) DIRECTORIES NO LANE COVERED, AND WHAT IS HIDING IN THEM
=====================================================================
75 directories have no cited file. They contain 55 real `^structure`/`^class`
declarations (I excluded 3 grep false positives that are docstring prose:
Divisors/AssociatedSheaf/RationalSections.lean:41, Sites/Descent.lean:15,
Phase/NormalizedShift.lean:35). Ranked by duplicate risk:

A. DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai/ — 0 of 10 files
   cited; 26 declarations, of which 24 are `class Has*`. That is 24 of the 26
   `^class Has` declarations in the whole of AlgebraicGeometry/. They are
   pullback/pushforward twins of one datum:
     KernelSwap.lean:112 HasPullbackSwap  vs  :125 HasPushforwardSwap
     KernelUnit.lean:114 HasPullbackRetraction  vs  :128 HasPushforwardRetraction
     KernelAssociativity.lean:87 HasPullbackFactorization vs :101 HasPushforwardFactorization
     KernelConvolution.lean:164 HasProjectionFormula vs :256 HasProjectionFormulaRight,
       :275 HasCommonPullbackRoute vs :294 HasCommonPushforwardRoute
     KernelUnitConvolution.lean:81 HasUnitPullbackRightUnitor vs :93 …LeftUnitor
   Read side by side (KernelSwap.lean:112-131, KernelUnit.lean:114-137) each is
   literally {comm : a guard equation of morphisms, iso : a natural iso of the
   induced functor composites}. That is the compositor/unitor datum of a
   pseudofunctor SchemeBaseChange S → Cat. The repository ALREADY owns that root
   lane — CategoryTheory/Bicategory/Functor/Cat/Transport.lean:19
   (`namespace CategoryTheory.Pseudofunctor`) and
   Cat/ObjectProperty/UniversallyStable.lean:29 — and the canonical spine names it
   (docs/architecture/abstraction-tree.md:41 "└─ Pseudofunctor", :244 "affine
   stable subprestack  consumes pseudofunctor object property"). The spine's
   Fourier–Mukai node (abstraction-tree.md:130-136) lists only the categorical
   side (kernelTransform, kernelEvaluation, kernelConeTransformTriangleFunctor,
   CounitKernelConeData); the geometric convolution API has NO spine node at all.
   The report notices the hole only as an unverified aside:
   miss-geometry-derived-04 (line 5789) "FourierMukai/ kernels were cited once;
   the convolution API is unsurveyed." This is the largest single missed cluster
   in the tree and it is the same disease as the confirmed geometry-derived-01
   ("Coherent pullback and pushforward are one exact lift").

B. Representability, defined three times across two uncovered directories.
   CategoryTheory/Sites/Descent/StackInGroupoids/Morphism.lean:76
   `structure FiberRepresentation` + :86 `class IsRepresentable` (Nonempty of it);
   AlgebraicGeometry/Stacks/Algebraic.lean:209
   `structure StackMorphism.FiberRepresentationWithProperty extends
   f.FiberRepresentation` + :220 `class HasRepresentableProperty`;
   Algebraic.lean:315 `structure StackInGroupoids.DiagonalFiberRepresentation`
   + :330 `class HasRepresentableDiagonal`. The third is a from-scratch rebuild:
   the diagonal of F is a stack morphism F → F ×_G F, so HasRepresentableDiagonal
   should be IsRepresentable of that morphism, not a new structure with its own
   `representing : Over S` and `isomorphismEquiv` field. Also
   Sites/Descent/StackInGroupoids.lean:35,58,110 (StackInGroupoids, Cover,
   StackEquivalence) — all uncited.

C. AlgebraicGeometry/Moduli/Semistability/ — 0 of 4 files cited, 5 structures.
   Locus.lean:49 SchemeSemistableLocusIndex; :61 SchemeGenericSemistableLocusIndex
   (= index + genericPoint); FiniteType.lean:58 and :66 add the SAME one field
   `finiteType : IsFiniteTypeBaseChange index(.index).baseChange` to each of the
   two. Four structures = one root plus three one-field decorations, which is
   character-for-character the shape of the confirmed geometry-derived-04 ("Six
   one-field wrappers around Slicing.PreimageData"). Plus
   Moduli/HarderNarasimhan/RelativeFiltration.lean:56,97 (also uncited).

D. AlgebraicGeometry/IntersectionTheory/ — Snapper.lean:119 CoherentTwistFamily,
   :153 GeometricInduction; Surface/Number.lean:252 TwistContext, :268
   IntersectionContext. Four "a coherent sheaf plus a twisting datum plus a
   degree bound" records, none cited, none compared to
   Numerical/Stability/TwistedChern.lean (which charges-02/walls-03 do survey).

E. AlgebraicGeometry/Morphisms/ — AlmostDisconnected.lean:51 SupportData, :124
   GradedPieceData, :136 Witness; FiltrationProperty.lean:39 Witness. Two
   structures literally named `Witness` in one uncited directory.

F. Smaller uncited singletons worth a look: CategoryTheory/Monoidal/
   Triangulated.lean:42 IsCompatibleWithTriangulation;
   Algebra/Homology/Subcomplex.lean:53 SubcomplexData;
   StabilityCondition/Phase/NormalizedShift.lean:36 NormalizedShift.

G. Effectively uncovered (nominally "covered" by one file, so my strict metric
   misses them, but they are the biggest blind spots by file count):
   - Foundation/Deformation/ — 1 of 42 files cited. Contains
     SkewedStability.lean:32 SkewedStabilityFunction with its OWN
     :49 `charge`, :53 `phase`, :57 `ChargeNe`, :102 `structure IsSemistable`.
     This is a fourth copy of the charge/phase/IsSemistable calculus that the
     confirmed high finding weak-tilting-03 enumerates at only three sites.
   - Weak/Foundation/Slicing/ — 0 of 14 files cited.
   - AlgebraicGeometry/ProjectiveSpectrum/Modules/ — 1 of 28.
   - Algebra/Homology/SpectralSequence/ — 0 of 7; Algebra/Homology/ — 0 of 10.
   - AlgebraicGeometry/DerivedCategory/Dqc/ — 3 of 14.

=====================================================================
(2) CONFIRMED FINDINGS RESTING ON A CLAIM NO LENS CHECKED
=====================================================================
Verdict prose is mostly specific; the failures are of two kinds — a lens that
defers instead of checking, and an enumeration nobody ran against the tree.

2.1 geometry-derived-06 (impact HIGH, confidence 0.8) — proposes a NEW
`structure GeometricSerreFunctor` and its own adoption lens says
"only one leaf reaches even a repaired version" (report line ~1950). The
repository contract, docs/architecture/abstraction-tree.md:356-358, requires
"Adoption. Name two independent consumers". No lens tested the proposed root
against that clause; the repository lens instead answered a different question
("the bridge gives the already-baselined SerreFunctorData a second inhabitant" —
that is the OLD root, not the new one). The CI gate is silent here for a reason
no lens states: scripts/check_single_instantiation.py:55-58 has
GENERIC_SUBJECTS = {CategoryTheory, LinearAlgebra, Algebra, Topology, RingTheory,
AlgebraicTopology} and the proposed module is under AlgebraicGeometry/Duality/.
So this high finding is carried 2–1 over a documented one-inhabitant objection
with nobody checking the contract clause that governs it.

2.2 sites-06 (medium) — Mathematics verdict in full: "survives, with the same
corrections as dg-04." Its own body (line 4352) says "This is the same defect as
dg-04, reported independently by the sites lane; the declarations, parent
structure and proposed root are identical and are not repeated here." No lens
checked its equation; it is dg-04, and it is counted a second time in the
sites lane row of §6.

2.3 walls-02 vs lattices-02 — both confirmed HIGH, sharing 7 of 8 declarations
(Wall.NumClass.discr Walls/Numerical/Discriminant.lean:70; Wall.Threefold.discr
Walls/Threefold/Basic.lean:204; ChargeCoordinates.discr
Divisorial/Discriminant.lean:288; ChernCharacter.discriminant :227;
NumericalVarietyData.discriminant GrothendieckGroup/Discriminant.lean:31;
Surface.discrH Stability/Slope.lean:174; discrHBeta Stability/BMT.lean:103).
They propose DIFFERENT parents for the same leaves — walls-02 a new Δ_H on
H-degree vectors, lattices-02 the existing Mukai.selfPairing — and §2.6 N5 warns
"a root defining Δ_H := pairing n v v would … silently collapse to 0 for every
odd n". No lens compared the two findings; the report ships both as high with no
adjudication. That is exactly the failure mode the audit exists to catch,
committed by the audit.

2.4 charges-03 (medium) — its Mathematics verdict records a correction that
never reaches the deliverable: "Bayer–Lahoz–Macrì–Stellari induce stability on
Ku(cubic threefold) from the tilt charge rotated by 1/i = −i, not from the
Bayer–Macrì–Toda charge with ch₃ … the rotation exists as phaseTiltRotation
(1/2)". grep over §2 (lines 39–492) for `rotat|phaseTilt` returns nothing, and
the sketch's `tiltWallChargeFamily` (design-final.lean:567-569) is
`wallChargeFamily V P κ 2` with no rotation. The supporting claim "Walls are
unchanged by the rotation" is true but nobody cited the root that makes it true:
phaseTiltRotation is multiplication by exp(-πβi) ≠ 0
(Weak/Tilting/Semistable/TiltGeometry.lean:42-50), so ChargeFamily.wall_smul
(Walls/ChargeFamily.lean:322) discharges it. Also the citation is off by one:
the def is at TiltGeometry.lean:42, the report says :43.

2.5 weak-tilting-03 (HIGH) — enumerates `IsSemistable` at three sites
(Weak/Basic/Definitions.lean:198, Weak/Foundation/StabilityFunction/
WeakSlopeGeometry.lean:233, Basic.lean:141). `grep -rn` over the tree returns a
fourth: Foundation/Deformation/SkewedStability.lean:102, with its own
`charge` (:49) and `phase` (:53) abbrevs whose bodies are
`F.W (classOf C κ E)` and `relativePhase (F.charge E) F.α` — i.e. exactly
ClassDatum.charge (Weak/Charge.lean:91) at the ambient class datum. No lens ran
the enumeration; SkewedStabilityFunction is cited three times in the report
(lines 3279, 3304, 3324) but only in weak-tilting-04's CARRIER question, never
in weak-tilting-03's calculus question.

2.6 geometry-derived-04 (medium) — "Six one-field wrappers around
Slicing.PreimageData". A seventh preimage-data structure exists and appears
NOWHERE in the report: Phase/Order/Functoriality.lean:46
`structure SlicingOrderPreimageData (op : Slicing C → Slicing D) (obj : D → C)`,
whose `semistable_iff` is precisely "(op s).P φ E ↔ s.P φ (obj E)". Verified:
grep -c for `SlicingOrderPreimageData|InducedTStructuresLarge|
Slicing.InducedTStructures|NormalizedShift|CofiltrationData` over the report
returns 0, while all five exist (Functoriality.lean:46, Inducing.lean:248,
InducedTStructures.lean:46, NormalizedShift.lean:36, Cofiltration.lean:47).

2.7 lattices-05 (medium) — adoption lens REFUTED it and the verdict itself says
"the finding is folded into lattices-01". It is nevertheless counted as one of
the 83 confirmed.

2.8 Two verdicts that admit an unchecked step outright and were still confirmed:
dg-06 Mathematics — "survives at low, with the caveat that only one of the two
compatibilities was checked"; dg-04 Adoption — "`commShift_naturality` was NOT
verified — three attempts left a residual goal".

2.9 COUNT INTEGRITY. The 83/31-high figures double-count. Clusters the report
itself admits:
 - charges-01 (H) = walls-01 (H) = docs-02 (H). Line 896-897: "This is the same
   parent as charges-01 seen from the wall lane"; line 2536: "Identical to
   charges-01 and walls-01, found a third time from the documentation side."
 - numerical-nfold-01 (H) = surf-08 (M). Line 4130: "the same parent as
   numerical-nfold-01 seen from the surfaces lane."
 - dg-04 (M) = sites-06 (M). Line 4352.
 - charges-02 (M) = walls-03 (M): same four β-twist declarations
   (Threefold/Basic.lean:89,113; Divisorial/Coordinates.lean:63;
   Divisorial/Charge.lean:121; TwistedChern.lean:104,110), same parent equation.
 - numerical-nfold-06 (M) is the R3 transport half of charges-01: same two
   declarations (WallTransport.lean:112, ThreefoldWallTransport.lean:146).
 - walls-02 (H) / lattices-02 (H) as in 2.3.
Distinct confirmed findings are roughly 76, not 83; distinct HIGH roughly 27,
not 31. Nothing in §6 or §7 discloses this.

=====================================================================
(3) DOES THE SYNTHESIZED CENTRAL-CHARGE TREE HANDLE THESE FOUR?
=====================================================================
(a) The K3 √td correction — NO (slot present, never inhabited, and it leaves two
    √td data unbridged).
 Report's own lines: §2.3 R3 "corrComp V κ E k = ∑_{j≤k} chComp E j · κ(k-j)
 κ on the RIGHT slot"; §2.4 "├─ κ = 1 and κ = √td are two pullbacks
 different walls; not one family"; §2.5 "`mukaiVector` / `mukaiCharge` /
 `mukaiChargeFamily` (`Divisorial/Mukai.lean:112,173,224`) are unchanged and
 already correct"; §2.6 N8 "dualClass_ne_self (proved) shows absorbing κ requires
 κ^∨ = κ … dualClass_k3 (proved) shows K3's √td = (1,0,1) is the unique fixed
 case."
 Why NO: in design-final.lean every κ argument is instantiated at `unitCorr`
 (lines 546, 548, 556-558, 597); `sqrt`/`Todd` appear only in the N8 docstring
 (lines 450-452, 459-460). The value κ is supposed to take already exists in the
 repo with exactly κ's type — `NumericalVarietyData.sqrtToddComp : ℕ → A`,
 AlgebraicGeometry/Numerical/Mukai/SqrtTodd.lean:181 — and is never plugged in.
 Worse, the repository carries a SECOND √td datum at another layer that the tree
 leaves standing: `structure SqrtTodd` (Walls/Divisorial/Mukai.lean:77) with
 fields `divisor : D`, `number : ℝ` — i.e. the m = 2 truncation of κ — together
 with `SqrtTodd.k3 = ⟨0,1⟩` (:91), `mukaiCharge_trivial` (:187ff) and
 `mukaiCharge_k3` (:213ff). The tree never states that SqrtTodd is the truncated
 κ, and its own K3 constant is written in the OTHER spelling, `![1,0,1]`
 (design-final.lean:460), against the repo's `⟨0,1⟩`. So after the migration the
 tree still has two unrelated √td corrections, which is the disease under audit.

(b) The threefold ∫H³ weight in the rank slot — YES at the root, NO at the leaf.
 Report's lines: §2.3 R3 "hDegrees V P κ m E k = ∫ H^(n-k) · (ch·κ)_k";
 §2.6 N4 "slopeH (Stability/Slope.lean:133) is degH/rank, while hDegrees_zero
 (proved) shows slot 0 is rank · ∫Hⁿ. The honest theorem is
 slopeH = ∫Hⁿ · (d₁/d₀)."
 The repo agrees: ThreefoldWallTransport.lean:146 slot 0 is
 `degree (P.cls ^ 3) * (rank E)` (docstring at :141 "The first slot carries ∫H³")
 and slots 1-3 are `degree (chComp E k * P.cls ^ (3-k))`;
 WallTransport.lean:112 is the n = 2 twin with ∫H².
 Why only partly YES: the comparison theorem does not exist even in the sketch.
 §2.1's table lists `Polarised.surface_toNumClass_eq` as a `sorry` (line 553,
 class ROUTINE), and the n = 3 statement is not a declaration at all — it is a
 code comment, design-final.lean:560-561: "The n = 3 twin for
 ThreefoldWallTransport.lean:146 has the same shape." So the ∫H³ convention is
 modelled correctly and `hDegrees_zero` is proved generically, but no proof
 connects the actual threefold transport to the root.

(c) The parity sign of the Mukai pairing, even vs odd — YES as a theorem, NO as
    a bridge, and misapplied at n = 4.
 Report's lines: §2.2 "Angle B produced the single strongest result of the panel,
 the parity theorem ⟪v,w⟫ = (-1)ⁿ⟪w,v⟫ … it forces pairing 3 v v = 0 and is the
 reason the cubic threefold must go by tilt restriction while the cubic fourfold
 goes by the Mukai lattice"; §2.6 N1, N2.
 Verified proved: design-final.lean:347 `def pairing (n : ℕ)`, :359
 `pairing_comm_parity`, :392 `pairing_comm_even`, :402
 `pairing_self_eq_zero_odd` — real proofs, no sorry.
 Why not a clean YES: `Mukai.Graded.pairing n` is a NEW bilinear form on
 `Exp.HDeg n` and is never compared with the Mukai pairing the repository
 already has — `Mukai.realPairing v w = b v.2.1 w.2.1 - v.1*w.2.2 - w.1*v.2.2`
 (LinearAlgebra/Lattice/Mukai/RealForm.lean:87), `realBilin` (:100),
 `selfPairing` (Mukai/Basic.lean:143). grep of design-final.lean for
 realBilin/realPairing/realForm returns only lines 84-90, inside
 `expCharge_eq_pairCharge`. The two differ by the ∫Hⁿ normalisation that (b) is
 about, and the report already flags an adjacent factor trap (N9, "realForm is
 half the self-pairing"). So the design ships a second declaration named a Mukai
 pairing with no bridge to the first — a new instance of the disease, not a cure.

(d) Kuznetsov components of BOTH the cubic threefold and the cubic fourfold — NO
    for both, for different reasons.
 Cubic threefold. §2.3 R1a: "(n,m) = (3,2) tilt   the Ku(cubic threefold)
 ambient charge  NEW"; §2.6 N10: "The cubic-threefold Kuznetsov charge is
 (n,m) = (3,2), not the BMT ch₃ charge (3,3)". But the ambient charge is the
 TILT charge rotated by −i, as charges-03's own Mathematics verdict states, and
 that correction never reaches §2 (grep of lines 39-492 for rotat|phaseTilt: no
 hits). `tiltWallChargeFamily` (design-final.lean:567-569) is the untilted
 (3,2) charge with no rotation, no tilted heart, and no link to `Threefold.nu`
 (Walls/Threefold/Basic.lean:208) which is the only form the repo holds.
 Cubic fourfold. §2.3 R4: "cubic fourfold   n even ⇒ symmetric   ⇒
 pairCharge.restrict on A₂^⊥"; §2.4: "noncommutative: Ku(cubic fourfold)
 A₂ ⊆ H̃(Ku X); NOT a child of expCharge"; §2.6 N11. The sketch's justification
 is a category error — design-final.lean:654-657: "The cubic-fourfold Ku(X)
 charge reaches PeriodDomain.centralCharge DIRECTLY: … n = 4 is even so the
 restricted Mukai form is symmetric (Mukai.Graded.pairing_comm_parity)."
 `pairing_comm_parity` at n = 4 is a statement about `Exp.HDeg 4 = Fin 5 → ℝ`;
 H̃(Ku X, ℤ) for a cubic fourfold is rank 24 of signature (4,20). Parity of the
 compressed H-degree form says nothing about it. Nothing constructs A₂, A₂^⊥, or
 a `HasSignatureTwo` witness; `pairCharge.restrict` (design-final.lean:65) is a
 generic `.comp f` with no fourfold inhabitant, and `periodDomainChargeFamily`
 (:658) just repackages `PeriodDomain.centralCharge`
 (LinearAlgebra/QuadraticForm/CentralCharge.lean:61, verified). §2.7 concedes the
 point: "PR-11 and PR-12 · blocked on a real leaf." And N12's grep is confirmed
 exactly: `grep -rni kuznetsov DerivedAlgGeo` returns two disclaimers only
 (Surface/Enriques/Residual.lean:20, Lattice/Numerical/RankTwo.lean:13).
 Net: both Kuznetsov cases are covered by prose and by two abstract `example`s
 (design-final.lean:622, :631); neither is a node with a leaf, and the threefold
 route as written in §2 is the wrong ambient charge.

=====================================================================
(4) TEN FOLLOW-UP CHECKS, AGENT-SIZED, ORDERED BY VALUE
=====================================================================
1. FourierMukai pseudofunctor root. Read all 10 files of
   AlgebraicGeometry/DerivedCategory/FourierMukai/ and classify its 24
   `class Has*` declarations into {compositor at a commuting triangle, unitor at
   an identity, base-change square, projection formula}. Test whether
   CategoryTheory/Bicategory/Functor/Cat/Transport.lean's Pseudofunctor lane can
   own the first two. Deliverable: one root signature plus a table saying, per
   class, instance/extends/abbrev/theorem. Highest value: 24 declarations, zero
   lane coverage, and the spine has no node for them.

2. Instantiate κ at √td and close the two-√td split. Prove
   `wallChargeFamily V P V.sqrtToddComp 2` (κ from
   Numerical/Mukai/SqrtTodd.lean:181) reproduces the K3 Mukai charge, and state
   whether `Walls/Divisorial/Mukai.SqrtTodd` (:77, fields divisor/number) is the
   m = 2 truncation of κ, reconciling `SqrtTodd.k3 = ⟨0,1⟩` (:91) with the
   sketch's `![1,0,1]` (design-final.lean:460). Without this the κ slot has zero
   inhabitants and §2.4's "κ = √td" line is unbacked.

3. Discharge the two transport comparisons. Prove
   `Polarised.surface_toNumClass_eq` (currently `sorry`, design-final.lean:553)
   and WRITE the missing n = 3 twin for ThreefoldWallTransport.lean:146 that
   today exists only as a code comment. These are the only proofs that tie the
   ∫Hⁿ rank-slot convention to the actual leaves.

4. Adjudicate walls-02 vs lattices-02. Both HIGH, 7 shared declarations, rival
   parents (new Δ_H on H-degrees vs existing Mukai.selfPairing), N5 warning that
   the pairing route collapses at odd n. Pick one parent, record the other as a
   negative result per abstraction-tree.md:365.

5. Re-issue §6 with de-duplicated counts. Merge charges-01/walls-01/docs-02,
   numerical-nfold-01/surf-08, charges-02/walls-03, dg-04/sites-06, fold
   numerical-nfold-06 into charges-01's R3 and lattices-05 into lattices-01.
   Report distinct findings and state "N distinct of 89 reported". Current
   83/31-high is inflated by ~6-8.

6. Bridge or refute `Mukai.Graded.pairing n` against `Mukai.realPairing`
   (RealForm.lean:87) / `selfPairing` (Mukai/Basic.lean:143) on the rank-one
   slice, accounting for the ∫H² weight and N9's halving. Either a proved
   comparison or a recorded negative result; shipping a second unbridged "Mukai
   pairing" is the disease.

7. Fix the cubic-fourfold justification in R4. Replace
   "pairing_comm_parity at n = 4" (design-final.lean:655-657) with the actual
   requirement: a `HasSignatureTwo` witness on H̃(Ku X) and an A₂ sublattice
   datum, or downgrade R4's fourfold line to an open obligation. As written it
   is a non-sequitur about the wrong lattice.

8. Carry the −i rotation into the exemplar. Amend §2.3 R1a, §2.4, §2.5 and PR-8
   so the cubic-threefold ambient charge is the tilt charge composed with
   `phaseTiltRotation (1/2)` (TiltGeometry.lean:42 — fix the :43 citation), and
   cite `ChargeFamily.wall_smul` (Walls/ChargeFamily.lean:322) for wall
   invariance. The correction currently lives only in charges-03's verdict.

9. Root-review geometry-derived-06 against abstraction-tree.md:356-358. Name two
   independent consumers for `GeometricSerreFunctor` or downgrade it; note that
   scripts/check_single_instantiation.py:55-58 does not scan AlgebraicGeometry/,
   so CI will not catch a one-inhabitant root there.

10. Sweep the four un-enumerated sibling sets the lanes missed:
    (a) Foundation/Deformation/SkewedStability.lean:49,53,102 as the fourth
        charge/phase/IsSemistable copy against weak-tilting-03's ClassDatum root;
    (b) Phase/Order/Functoriality.lean:46 SlicingOrderPreimageData as a seventh
        sibling of geometry-derived-04, plus Inducing.lean:248 /
        InducedTStructures.lean:46 (all three appear 0 times in the report);
    (c) Moduli/Semistability/{Locus.lean:49,61, FiniteType.lean:58,66} as one
        index root with three one-field decorations;
    (d) Stacks/Algebraic.lean:315,330 DiagonalFiberRepresentation /
        HasRepresentableDiagonal as the diagonal case of
        Sites/Descent/StackInGroupoids/Morphism.lean:76,86.