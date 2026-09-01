# ADR-0010 — How a dg category is encoded, and where the H⁰ seam lives

- **Status:** partially superseded by ADR-0012. The bespoke `DGCategory`
  encoding remains accepted; the separate `DGLean` root and namespace do not.
- **Date:** 2026-08-13 (UTC) · **Amended:** 2026-08-14 (UTC)
- **Decider:** Chris Dare
- **Decision (Question 1, 2026-08-13):** **Option B — a bespoke `DGCategory`
  structure.** Taken on the measurement in
  `.claude/notes/2026-08-13-dg-surface-reconnaissance.md`, which showed the
  enriching category of Option A does not exist at the pin. Option A′ stays
  live as a separate `upstream-candidate` slice and is not a prerequisite of
  anything in DG1.
- **Decision (Question 2, root and namespace, 2026-08-14):** historical and
  superseded. ADR-0012 places this work in
  `DerivedAlgGeo/CategoryTheory/DGCategory` and namespace
  `CategoryTheory.DGCategory`.
- **Still open:** the DG4 dependency direction is not needed until DG4 and does
  not block DG1.
- **Related:** the CLAUDE.md taxonomy line *"Future derived-category and
  Fourier–Mukai libraries get dedicated roots with their first real theorem"*,
  ARCHITECTURE.md growth rule 6 (added 2026-08-14 by this amendment);
  `.claude/roadmap/dg-enhancements.yaml` (m0, e1);
  [`ADR-0011`](ADR-0011-hom-complexes-are-complexes-of-abelian-groups.md),
  which refines Question 1

## Context

The `dg-enhancements` track needs a dg category before it needs anything else.
Mathlib has no such object at `mathlib_rev` — a search for
`DifferentialGraded`, `DGCategory`, or a quasi-equivalence returns nothing —
but it has two different sets of parts from which one can be assembled, and
they lead to different long-run costs. The choice is not reversible cheaply:
every later definition in the track, and every transport lemma across the H⁰
seam, is stated against whichever encoding is chosen here.

What the pin does supply, and which both routes consume:

- `Algebra/Homology/HomotopyCategory/HomComplex` and its `Shift`,
  `Cohomology`, `Single`, and `Induction` companions — the Hom cochain complex
  between two cochain complexes, with `Cochain`, the differential `δ`, and the
  cohomological identification of its degree-zero classes. This is already the
  dg structure on complexes; neither route may re-derive it.
- `Algebra/Homology/Monoidal` — the monoidal structure on homological
  complexes, which is what an enrichment would enrich over.
- `CategoryTheory/Enriched/{Basic, EnrichedCat, Ordinary/Basic}` — enriched
  categories, and `EnrichedOrdinaryCategory`, whose shape ("an ordinary
  category together with an enrichment agreeing with its Homs") is exactly the
  shape a dg category has.
- `Algebra/Homology/HomotopyCategory/{Pretriangulated, Triangulated}`,
  `KInjective`, `KProjective`, and `Algebra/Homology/DerivedCategory/*` — the
  classical side of the seam, which this track compares against and does not
  fork.

**Measured 2026-08-13** against `mathlib_rev` exactly — see
`.claude/notes/2026-08-13-dg-surface-reconnaissance.md` for the commands, the
raw output, and the elaboration probes. Two results change this ADR:

1. **`CochainComplex (ModuleCat k) ℤ` is not monoidal at the pin.**
   `HomologicalComplex.HasTensor` does not synthesize for the ℤ-indexed shape,
   because the degree-`n` tensor is a coproduct over the infinite set
   `{(i,j) : i+j = n}` and Mathlib supplies only the finite-fibre instances.
   `ChainComplex (ModuleCat k) ℕ` *is* monoidal, which localizes the gap
   precisely. It is an instance/API gap, not a mathematical obstruction.
2. **The H⁰ seam is largely already proved.**
   `CochainComplex.HomComplex.CohomologyClass.homAddEquiv` gives
   Hⁿ(Hom•(K,L)) ≅ Hom_{K(C)}(K, L⟦n⟧) as an `AddEquiv`.

The first result invalidates Option A as originally written. The options below
are revised accordingly.

## Question 1 — the encoding

### Option A: enriched over cochain complexes

Define a dg category as an `EnrichedOrdinaryCategory (CochainComplex (ModuleCat k) ℤ) C`,
using the monoidal structure Mathlib already builds.

- Inherits enriched functors, enriched Yoneda, opposite and functor-category
  constructions as Mathlib grows them, rather than re-deriving each one.
- Makes "the underlying ordinary category" a projection rather than a
  construction, which is half of the H⁰ seam for free.
- Depends on the monoidal instance on `CochainComplex (ModuleCat k) ℤ` being
  usable at the pin — the load-bearing unknown, and the reason e1 exists.
- Universe and instance-resolution behaviour of the enriched API under a
  concrete monoidal category is unmeasured here.

### Option B: a bespoke `DGCategory` structure

Carry `Hom : C → C → CochainComplex (ModuleCat k) ℤ` with composition chain
maps and the associativity and unit axioms written out.

- No dependency on the enriched API elaborating well over this particular
  monoidal category.
- Every companion construction (opposite, product, functor dg category,
  Yoneda) is owner-authored and owner-maintained.
- Diverges from Mathlib's own vocabulary, which makes upstreaming any part of
  this track harder later — `upstream-candidate` becomes mostly unavailable.

### Option A′: build the ℤ-graded monoidal structure first, then enrich

Supply the missing `HasTensor` / `HasGoodTensor₁₂` / `HasGoodTensor₂₃`
instances for `HomologicalComplex C (ComplexShape.up ℤ)` under small-coproduct
hypotheses, in `ForMathlib`, then take Option A on top.

- The only route that ends with the track's declarations shaped like Mathlib's
  and genuinely upstreamable — the missing instances are themselves a clean
  `upstream-candidate`, useful to Mathlib independently of this repository.
- Pays a prerequisite before the first dg definition is written. The size of
  that prerequisite is not yet measured; measuring it is a spike, not a guess.
- Risks the track's first milestone becoming a homological-algebra milestone
  with no dg content, which is how a track loses its thread.

### Recommendation, not a decision

**Option B now, Option A′ as a separately scheduled `upstream-candidate` slice.**

The measurement inverted the original recommendation. Option A was recommended
on the argument that it spends the budget on the seam rather than on categorical
plumbing — but at this pin, Option A *is* plumbing: it requires building the
ℤ-graded monoidal structure before a single dg definition can be written.
Option B needs no monoidal structure at all, because `Cochain.comp` already
supplies the graded composition law directly.

The second measurement reinforces this. With `homAddEquiv` in hand, DG1's
headline theorem is close, and the fastest route to it does not pass through a
monoidal category.

**What changes either way.** Under B, `dg-enhancements-e2` carries the
structure and its companions (opposite, product, functor dg categories) are
owner-authored; the track should be assumed to stay in-repository, and
`upstream-candidate` mostly does not apply to it. Under A′, e2 stays small and
Mathlib-shaped, but DG1 acquires an unmeasured prerequisite ahead of its first
theorem. Choosing B does not foreclose A′: the ℤ-graded instances remain worth
building, and a later `EnrichedOrdinaryCategory` instance for a bespoke
`DGCategory` is an ordinary refactor rather than a rewrite.

## Question 2 — the root and the namespace

The repository has two owner-authored roots, `CohLean` and `BridgelandStabLean`,
and ARCHITECTURE.md's growth rule says a new subject gets its own root **with
its first real theorem**, not with its first definition.

- **Proposed root:** `DGLean`, matching `CohLean`'s naming, with subsystems
  `DGLean/Category` (dg categories, dg functors, H⁰), `DGLean/Enhancement`
  (the enhancement structure and transport), and `DGLean/Model` (C^dg, K^dg,
  D^dg).
- **Proposed trigger:** the root is created by the PR that proves
  `H⁰(C^dg A) ≌ HomotopyCategory A` (`dg-enhancements-e4`) — the first
  statement in the track that is a theorem about existing objects rather than
  a definition about new ones. Until then the work lives on a branch.
- **Rejected:** placing dg material under `BridgelandStabLean/`. The dg track
  is not about stability, and DG1–DG3 have no stability content at all. Only
  DG4 touches `BridgelandStabLean`, and it touches it as a consumer.
- **Also rejected:** a `Development/`-style holding pen as the permanent home.
  `Development/` is for compile-only API reconnaissance, and this is a
  library.

**Open sub-question for the decider:** whether the transport lemmas of DG4 live
in `DGLean/Enhancement/Transport` (dg-side, importing `BridgelandStabLean`) or
in `BridgelandStabLean/` (stability-side, importing `DGLean`). The dependency
direction is a one-way door once either root imports the other; the roadmap
assumes the former and does not depend on it.

## Consequences if this ADR stays open

`dg-enhancements-m0` may still complete: reconnaissance, coverage maps,
labels, milestones, and views need neither answer. `dg-enhancements-m1` cannot
start — e2 is the encoding, and writing it before the decision is how a
repository ends up with two.

---

## Amendment, 2026-08-14 — the root arrived at e2, and the rule cited above is not in the document named

Everything above is preserved verbatim as the record of what was decided on
2026-08-13 and why. Three things in Question 2 did not survive contact with the
tree.

### 1. The trigger fired two epics early, and was right to

`dg-enhancements-e2` (#343) created `DGLean/` on disk with `DGCategory`,
`DGCategoryStruct`, `DGFunctor`, `DGLinear`, the opposite and the product, and
fifteen proved lemmas, no `sorry` and no new axiom. It arrived gated rather
than promised: `DGLean` is a default target in `lakefile.toml`,
`scripts/DGLeanAudit.lean` runs under `scripts/check_audit.py`, and
`scripts/gates.sh` and CI both carry `dg-audit` and `runLinter-dg` with no
`scripts/nolints.json` entries.

The rule Question 2's trigger was meant to honour is CLAUDE.md's: a new root
arrives with **a theorem**, not with a bare definition. Its purpose is to stop a
root being minted for a signature nothing has been proved about. e2 clears that
bar — `dgComp_assoc`, `dgComp_leibniz`, `dgId_comp` and the opposite and product
laws are theorems about the objects the whole track is stated against.

What `dg-enhancements-e4` supplies is not the root's first theorem. It is the
root's first theorem about **an object the repository already had**. That is the
right gate for a *milestone*, and it stays m1's headline; it is the wrong gate
for a *directory*, because it makes the root's existence depend on a comparison
rather than on the subject having content of its own.

**Decision:** root creation at e2 is accepted as taken. The root name is
`DGLean`. Question 2's root half is closed.

### 2. The namespace half of Question 2 was not taken, and should be

Question 2 fixed *"the root **and the namespace**"*. The directory exists; the
namespace does not. At `a321683`, every declaration originating in a `DGLean`
module sits in the **root** namespace — `DGCategory`, `DGCategoryStruct`,
`DGFunctor`, `DGLinear`, `Const`, `constComplex`, `prodComplex`, `prodComp`,
`prodD`. No file under `DGLean/` opens `namespace DGLean`.

`CohLean` namespaces as `CohLean.AlgebraicGeometry.Proj.*` and
`BridgelandStabLean/Foundation` as `BridgelandStabLean.Foundation.*`. `Const`,
`prodD` and `prodComp` at the root are collision-shaped names, and Mathlib does
not declare library content at the root either.

**Decision:** the namespace is `DGLean`, with the subsystem namespaces proposed
in Question 2 (`DGLean.Category`, later `DGLean.Enhancement`, `DGLean.Model`)
beneath it. This is a rename, and it is cheapest before `dg-enhancements-e3` and
`-e4` state anything against the current names. It is follow-up work on `main`,
not a revert of #343.

### 3. The rule cited in Question 2 is not in the document it names

Question 2 opens: *"ARCHITECTURE.md's growth rule says a new subject gets its
own root with its first real theorem, not with its first definition."*

ARCHITECTURE.md's growth rules 1–5 are about placing a **module** under the
narrowest mathematical owner inside an existing library, exporting it through
its nearest umbrella, and keeping reconnaissance under `Development/`. None of
them mentions a library root. The sentence quoted is CLAUDE.md's, under
"Repository taxonomy".

So the miscitation is double: wrong document, and a rule that does not say this
at all. That is the actual reason Question 2 was answerable two ways —
ARCHITECTURE.md, the document that owns repository shape, had **no
root-creation rule**.

**Consequence:** ARCHITECTURE.md gains growth rule 6, stating when a subject
earns a root and that the namespace follows the root, and its package map gains
a `DGLean/Category` row. A root that CI gates but the architecture document does
not mention is drift on day one.

### What this amendment does not decide

The DG4 dependency direction — whether the transport lemmas live in
`DGLean/Enhancement/Transport` importing `BridgelandStabLean`, or in
`BridgelandStabLean/` importing `DGLean`. Unchanged, still open, still an owner
call, and still not needed until DG4.

---

## Amendment, 2026-09-01 — the path follows the encoding

Option B is a bespoke class built on `Algebra/Homology/HomotopyCategory/HomComplex`,
and it does not extend `EnrichedCategory`. Under the placement rule adopted on
2026-09-01 (`CLAUDE.md`, "The placement rule"), a bespoke carrier lives beside
the Mathlib API it is built on, so the subtree moved from
`CategoryTheory/Enriched/DGCategory/` to `Algebra/Homology/DGCategory/`. The
former path asserted an enrichment the type does not have.

Namespaces are unchanged (`CategoryTheory.DGCategory` and its children). If
Option A′ lands and `DGCategory` becomes an `EnrichedOrdinaryCategory`, the
subtree moves under `CategoryTheory/Enriched/` in the same change; that is the
reversal condition for this amendment.
