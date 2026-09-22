# Generalization backlog

Append-only. One row per altitude finding that could not be acted on inside the
chunk that found it.

This file exists because a reviewer who notices that a theorem holds in greater
generality usually notices it while reviewing a frozen chunk that may not touch
the ancestor module. Before this file existed, that observation had nowhere to
go: the reviewer could either suppress it or make it a blocking `needs_changes`
the chunk could not legally satisfy. Both outcomes lost the finding.

**Deliberately outside `openspec/changes/`.** `openspec_digest` in
`scripts/loop_engine.py` hashes only the required artifacts under a change
directory. A backlog living there would be digest-frozen, and appending to it
mid-run would invalidate every passed ledger in the run. Here it is free to grow.

## Rules

- Append only. Never delete a row; change its state in place.
- A row is cheap. Record a lift you are unsure of rather than not recording it.
- A falsified lift is a **result**, not a retraction. `abstraction-tree.md` is
  explicit that a failed unification recorded with its counterexample is a
  successful architecture outcome. Keep the row and mark it `FALSIFIED`.
- Read this file in Phase 0, before choosing an implementation approach. A row
  here may already answer where the work belongs.

## States

| State | Meaning |
|---|---|
| `UNVERIFIED` | Proposed. The general statement has not been compiled. |
| `CONFIRMED <PR>` | The lift was implemented and merged. |
| `FALSIFIED <counterexample>` | The general statement is false. Leaves stay separate. |

## Row schema

```
### <date> — <leaf declaration>
- chunk:              <chunk id>
- reviewing commit:   <sha>
- found by:           <reviewer or advisor name>
- proposed ancestor:  <module or namespace>
- weaker hypotheses:  <the binder/typeclass set the proof actually needs>
- state:              UNVERIFIED | CONFIRMED <PR> | FALSIFIED <counterexample>
```

## Rows

### 2026-09-22 — compare the explicit affine `H^{-1}` witness with `CategoryTheory.Tor` (planned)
- chunk:              sf8-5-tor-witness-comparison
- reviewing commit:   b8306d6b
- found by:           altitude-scout
- proposed ancestor:  `CategoryTheory.Tor`, with a later comparison from the
  abstract left-derived tensor calculation to the displayed affine cochain
  representative
- weaker hypotheses:  an abelian monoidal preadditive category with projective
  resolutions and a chosen projective resolution; no distinguished `ℤ → ZMod 2`,
  no particular mapping-cone presentation, and no scheme-level pullback claim
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Tor.lean:44`
- source note:        The explicit nonzero `H^{-1}` witness is now proved in
  merged PR #1457. Mathlib's `Tor` derives the second tensor factor; the
  concrete `ModuleCat` specialization, selected projective-resolution
  comparison, chain/cochain indexing bridge, and restriction-of-scalars
  comparison remain unverified. Do not duplicate this row for the same lift.
- state:              UNVERIFIED
- progress note (2026-09-22): The current chunk implements only the concrete
  `ℤ → ZMod 2` specialization. Even if that comparison merges, the proposed
  abstract left-derived tensor comparison under the weaker hypotheses above
  remains `UNVERIFIED`.

### 2026-09-21 — `ZModTwoNonflatDerived.baseChangedConeIso` (planned)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           altitude-scout
- proposed ancestor:  `CochainComplex.mappingCone.mapHomologicalComplexIso`
- weaker hypotheses:  an additive functor between preadditive categories and
  an arbitrary cochain morphism; no scalar-extension ring map, `ℤ`, or
  `ZMod 2` is needed for the cone-transport comparison
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:636`
- source note:        This is the generic mapped-cone transport already suited
  to the representative-level comparison; whether a repository-facing wrapper
  is useful beyond the witness is unverified.
- state:              UNVERIFIED

### 2026-09-21 — `ZModTwoNonflatDerived.affineKProjectivePullbackObject_homology_negOne_not_isZero` (planned)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           altitude-scout
- proposed ancestor:  `ProjectiveResolution.isoLeftDerivedObj`, potentially
  followed by a comparison with the repository's bounded-above-projective
  affine pullback lane
- weaker hypotheses:  an additive functor out of an abelian category with
  projective resolutions and a selected projective resolution; this omits the
  specific affine ring map and does not assert a general scheme-level derived
  pullback theorem
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/LeftDerived.lean:112`
- source note:        The pinned theorem computes a left-derived functor from a
  projective resolution, but its chain indexing and its relation to the
  repository's K-projective representative have not been compared here.
- state:              UNVERIFIED

### 2026-09-21 — planned K-projective representative bridge (drop `K.IsStrictlyLE d`)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `KProjectiveHomotopyCategory.ofBoundedAboveProjectives`
  and `AlgebraicGeometry.DerivedCategory.Dqc.affineKProjectivePullbackObjIso`
- weaker hypotheses:  keep `[∀ n : ℤ, Projective (K.X n)]`, deliberately omit
  `[K.IsStrictlyLE d]` from the generic representative bridge
- pin status:         PIN-CONFIRMED
  `DerivedAlgGeo/Algebra/Homology/DerivedCategory/KProjective.lean:89-94` and
  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Dqc/AffineKProjectivePullback.lean:65-73`
- source note:        A 3.2-second bounded `~/.elan/bin/lake env lean /dev/stdin`
  probe instantiated both the object expression and
  `affineKProjectivePullbackObjIso f K d` without this binder. Both sites
  failed with `failed to synthesize instance of type class K.IsStrictlyLE d`.
- state:              FALSIFIED compiler witness: the current generic bridge
  cannot admit a complex without a strict upper bound.

### 2026-09-21 — planned K-projective representative bridge (drop degreewise projectivity)
- chunk:              sf8-5-nonflat-derived-effect
- reviewing commit:   49c33eda
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `KProjectiveHomotopyCategory.ofBoundedAboveProjectives`
  and `AlgebraicGeometry.DerivedCategory.Dqc.affineKProjectivePullbackObjIso`
- weaker hypotheses:  keep `[K.IsStrictlyLE d]`, deliberately omit
  `[∀ n : ℤ, Projective (K.X n)]` from the generic representative bridge
- pin status:         PIN-CONFIRMED
  `DerivedAlgGeo/Algebra/Homology/DerivedCategory/KProjective.lean:89-94` and
  `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Dqc/AffineKProjectivePullback.lean:65-73`
- source note:        A 6.8-second bounded `~/.elan/bin/lake env lean /dev/stdin`
  probe instantiated both the object expression and
  `affineKProjectivePullbackObjIso f K d` without this binder. Both sites
  failed with `failed to synthesize ∀ (n : ℤ), Projective (K.X n)` (after the
  pinned typeclass-heartbeat diagnostic).
- state:              FALSIFIED compiler witness: the current generic bridge
  cannot admit a merely bounded-above complex without degreewise projectivity.

### 2026-09-22 — `ExtensionClosure.le_of_closed` via a least-fixed-point comparison (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           altitude-scout
- proposed ancestor:  `OrderHom.lfp` and `OrderHom.lfp_le`, with a downstream
  equality comparing the existing owner `ExtensionClosure P` to the least
  fixed point of `Q ↦ P ⊔ IsZero ⊔ ObjectProperty.extensionProduct Q Q`
- weaker hypotheses:  the ancestor induction principle needs only a complete
  lattice, a monotone endomorphism `f`, and a prefixed point `f Q ≤ Q`; the
  proposed categorical specialization retains the owner's pretriangulated
  hypotheses and uses the existing extension product, without a new carrier
- pin status:         PIN-CONFIRMED `.lake/packages/mathlib/Mathlib/Order/FixedPoints.lean:58`
- source note:        At Mathlib revision
  `520045ab14e26149ee970e2e617ca04b09bde5d6`, `OrderHom.lfp_le` already proves
  the abstract minimality statement. The extension-product monotonicity
  lemmas are at `Mathlib/CategoryTheory/Triangulated/Subcategory.lean:230`
  and `:236`. The comparison equality remains uncompiled and is outside
  #918's finite-iterate/envelope scope. It would expose the order-theoretic
  source of the owner's induction principle; it does not by itself identify
  the one-sided `extensionProductIter` indexing or remove the hypotheses of
  the planned envelope comparison. No replacement of the owner is proposed.
- state:              UNVERIFIED

### 2026-09-22 — finite extension comparisons and generation-time bound (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the existing downstream `Dimension/ExtensionClosureComparison.lean`
- weaker hypotheses:  the owner's category, zero-object, integral-shift,
  preadditive, additive-shift, and `Pretriangulated` instances only; arbitrary
  `P`, arbitrary `n : ℕ` (including zero); neither `IsTriangulated C`,
  `P.Nonempty`, nor `P.ContainsZero`
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        A temporary Lean probe compiled finite-iterate inclusion,
  the inclusion of `⨆ n, (P ⊔ IsZero).extensionProductIter n` into
  `ExtensionClosure P`, and the pointwise singleton generation-time bound.
  The first two use induction and the owner's constructors; the last uses
  `monotone_extensionProductIter`, `le_retractClosure`, and
  `generationTime_le_coe_iff`. No ambient octahedron or nonempty witness is used.
- state:              L (proof-witness verified)

### 2026-09-22 — owner extension closure as the supremum of finite iterates (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the existing downstream `Dimension/ExtensionClosureComparison.lean`
- weaker hypotheses:  the owner's pretriangulated hypotheses plus
  `IsTriangulated C`; arbitrary `P`, without `P.Nonempty` or `P.ContainsZero`
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        A temporary Lean probe compiled both inclusions of
  `ExtensionClosure P = ⨆ n, (P ⊔ IsZero).extensionProductIter n`.
  The induction's extension case combines indices `n` and `m` at `n + (m + 1)`
  using `extensionProductIter_add'`; zero and generator cases use index zero.
  Adjoining `IsZero` handles the empty input. The ambient triangulated instance
  is genuinely used by the pinned associativity theorem in the reverse inclusion.
- state:              L (proof-witness verified)

### 2026-09-22 — raw distinguished-extension closure implies isomorphism closure (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `CategoryTheory.ObjectProperty` beside the triangulated
  closure vocabulary in Mathlib's `Triangulated/Subcategory`
- weaker hypotheses:  the owner's pretriangulated hypotheses, membership of
  every zero object in `Q`, and literal closure of `Q` under distinguished
  extensions; no separate `Q.IsClosedUnderIsomorphisms` hypothesis
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        A temporary Lean probe compiled `Q.IsClosedUnderIsomorphisms`
  by taking the distinguished cone of an isomorphism and using
  `Triangle.isZero₃_iff_isIso₁`. It then compiled `Q.ContainsZero` and
  `Q.IsTriangulatedClosed₂` from the same raw assumptions, and the converse
  induction corollary from those three classes. Thus the proposed typeclass
  corollary repackages equivalent closure assumptions; it is not a strict
  hypothesis weakening of the owner's raw induction principle.
- state:              L (proof-witness verified)

### 2026-09-22 — envelope comparison with supplied envelope closure (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  the existing downstream `Dimension/ExtensionClosureComparison.lean`
- weaker hypotheses:  the owner's pretriangulated hypotheses and `P.Nonempty`,
  replacing ambient `IsTriangulated C` by the specific
  `P.triangEnvelope.IsTriangulatedClosed₂` assumption
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        A temporary Lean probe compiled
  `ExtensionClosure P ≤ P.triangEnvelope` under this local closure assumption.
  The induction consumes extension closure of this envelope; Mathlib's ambient
  triangulated instance is one source of that fact. The planned #918 theorem
  retains its required ambient triangulated signature; this witness identifies
  the narrower hypothesis consumed by its proof and introduces no instance.
- state:              L (proof-witness verified)

### 2026-09-22 — envelope comparison without nonempty generators (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `ExtensionClosure P ≤ P.triangEnvelope`
- weaker hypotheses:  keep the ambient triangulated hypotheses and remove
  `P.Nonempty`, with no replacement
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        The direct induction probe failed to synthesize
  `P.triangEnvelope.ContainsZero`. A separate successful Lean proof verifies
  `¬ ExtensionClosure (⊥ : ObjectProperty C) ≤ (⊥ : ObjectProperty C).triangEnvelope`:
  the zero object belongs to the owner closure, while the empty Mathlib envelope
  simplifies to bottom. The counterexample already works in a pretriangulated category.
- state:              FALSIFIED compiled counterexample `P = ⊥`.

### 2026-09-22 — envelope comparison without ambient or supplied extension closure (planned)
- chunk:              rou1-2-extension-closure-comparison
- reviewing commit:   017337dd69bc916a05a05a62096ba618605bcaf9
- found by:           hypothesis-elimination-scout
- proposed ancestor:  `ExtensionClosure P ≤ P.triangEnvelope`
- weaker hypotheses:  keep `P.Nonempty` and the pretriangulated hypotheses;
  remove `IsTriangulated C` without supplying envelope extension closure
- pin status:         PIN-CONFIRMED Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
- source note:        The direct induction probe failed to synthesize
  `P.triangEnvelope.IsTriangulatedClosed₂`. At the pin, that instance uses
  `triangEnvelopeIter_add'`, which in turn needs ambient triangulated
  associativity. This is a failure of the proposed proof weakening, not a
  mathematical counterexample ruling out every possible proof in a
  pretriangulated category; the supplied-local-closure variant above compiles.
- state:              FALSIFIED compiler witness for the current proof route.
