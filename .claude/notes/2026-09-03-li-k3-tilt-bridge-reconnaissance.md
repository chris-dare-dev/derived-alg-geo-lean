# The Li → K3 bridge: what the reparameterization actually is

**Date (UTC):** 2026-09-03
**Kind:** reconnaissance snapshot. Not a decision, not a roadmap, not a coverage map.
**Question asked:** the 2026 stability-existence papers are said to "simplify, or translate up to
some reparameterization to", Bridgeland's stability conditions on K3 surfaces. Is that true, what
exactly is the reparameterization, and does it change how this repository should approach
`math/0307164`?

**Answer in one line:** the reparameterization is real and it is the `GL⁺(2,ℝ)~` action — the group
this repository has already built — but the direction of travel is the opposite of "simplifies", and
the K3 lane should not be routed through Li.

---

## 1. What was verified, and against what

Both papers were read from PDFs fetched 2026-09-03, not from ar5iv or abstract pages.

| artifact | sha256 | note |
|---|---|---|
| `arXiv:2607.28411v1` (Li–Liu–Liu–Macrì–Perry–Stellari–Zhao) | `f8770154235fe2c82698513b4633b3ee509fa11f722190a4c9f573fca589a98c` | **Byte-identical to the hash pinned in `.claude/roadmap/projective-families.yaml`.** Independent confirmation that the roadmap's pin is live and reproducible. |
| `arXiv:1607.01262v3` (Macrì–Schmidt) | `a44058db37cf60c6399b279dbe09b2607033f7e67db0cc8a1a0144aba5727dae` | Now pinned as `registry/coverage-1607.01262.json`. |

`arXiv:2601.22994` (Li, *A remark on stability conditions on smooth projective varieties*) was read
only at abstract level; it is reference `[38]` of the above and is the general existence engine.

## 2. The chain, with coordinates

LLMPSZ §7.2 ("Tilt-stability"), page 44, on a smooth projective surface `X` over `ℂ`:

> For a geometric stability condition `σ` in `Stab†_{H_X}(D^b(X))`, we can use [25, Theorem 5.10] to
> deduce that, **up to the action of `GL⁺₂(ℝ)~`**, `σ` is as in [25, Proposition 5.15], and it
> satisfies the full support property with respect to `K_num(X)`.

and then, since geometric stability conditions with respect to `K_num(X)` are connected
([25, Theorem 5.36]), `Stab†_num(D^b(X))` is defined as the component containing all of them, giving

> **Proposition 7.6.** Let `X` be a smooth projective surface over `ℂ`. Then the stability conditions
> in `Stab†_num(D^b(X))` have a mass-Hom bound; in particular, this applies to all geometric stability
> conditions on `D^b(X)` with respect to `K_num(X)`.

`[25]` is **Dell, H., *Stability conditions on free abelian quotients*, Épijournal Géom. Algébrique 9
(2025), Art. 16** — resolved from the LLMPSZ bibliography. It is *not* Macrì–Schmidt, and it is not
Bayer–Macrì; do not cite it as either.

So the chain is:

```
Li 2601.22994          existence on every smooth projective X/ℂ
   ↓  [38] feeds
LLMPSZ 2607.28411      §7.2, Prop 7.6 (surfaces), Prop 7.7 (threefolds under BMT)
   ↓  cites
Dell [25] Thm 5.10     every GEOMETRIC stability condition on a surface is,
   + Prop 5.15         UP TO GL⁺₂(ℝ)~, the explicit tilt one
   ↓  specialise to a K3 with ω² > 2
Bridgeland math/0307164 §6   σ(β,ω) on the tilted heart A(β,ω)
```

**The reparameterization named in the question is `GL⁺(2,ℝ)~`.** That is the precise content, and it
is a classification statement, not a construction shortcut.

## 3. The correction: direction of travel

The premise "Li's construction simplifies the K3 case" does not survive contact with either paper.

- Bridgeland's K3 construction is two pages of lattice arithmetic, and this repository has already
  done most of it (§5 below).
- Li's route is: Schubert polynomials and the coinvariant-algebra filtration (§4) → `E^n` with
  isogeny rescaling (Lem 5.3) → `E → E/±1 = P¹` (Lem 6.1) → `S_n`-descent to `Pⁿ` (Prop 6.2) →
  embed `X` and resolve `ι_*O_X` (Thm 6.5). In this repository that is epics #212 and #217 with the
  geometry parked behind #195.

Formalizing K3 *via* Li would be a large regression. What the bridge genuinely buys is different and
still worth having: it makes the K3 conditions a **cross-check on the general machinery**, and it is
the direction in which the `projective-families` lane's investment eventually pays off on a specific
surface. It is a payoff direction, not an entry route.

## 4. What could not be verified, and must not be asserted

- **Dell's Theorem 5.10 and Proposition 5.15 were not read.** Everything above about them is
  LLMPSZ's *characterization* of them. Before any Lean statement is written against that
  classification, the Épijournal article must be pinned and read directly. Treat §2 as a pointer,
  not as a source-faithful quote of Dell.
- **"Geometric" is doing real work and is not defined above.** In this literature a geometric
  stability condition is one in which every skyscraper `O_x` is stable of one common phase. Whether
  Bridgeland's `σ(β,ω)` is geometric is `math/0307164` Lemma 6.3 plus §10, and **neither is in this
  tree**. The chain in §2 does not reach a K3 without that step.
- No claim here is a coverage claim. `registry/` mints nothing from this note.

## 5. Why this changes nothing about how to approach `math/0307164`

The reparameterization group is **already built**, and it is the largest single asset the bridge
would need:

- `StabilityCondition/Symmetry/GLTilde/` — `Action/`, `Covering/`, `Topology/`,
  `ComplexRepresentation.lean`. The universal-cover frontier item `gltilde-universal-cover` was
  discharged 2026-08-07 (see `registry/README.md`).
- `Symmetry/Combined/` — the combined action with `Aut`, components, period map, effective quotient.

What is missing on the K3 side is not the group. It is `math/0307164` §6 Lemma 6.2's case analysis
(#740 step 2), and that is blocked on Lemma 5.1 (`v(E)² ≥ −2`) — which **BG1 #914 supplies as typed
data**, with no `Ext` and no Serre duality, for rank ≤ 1 on a K3. The unblock route is
`#913 → #914 → #740`, entirely inside BG1, and it does not touch Li at all.

## 6. Disposition

1. **Do not route the K3 lane through Li.** Keep `stab-existence-*` (#212, #217) as its own track.
2. **The bridge is a statement-layer target, not a construction.** If it is ever formalized, the
   shape is the one `Families/Theorem22.lean` already uses: an inhabitant-free dependency ledger, per
   #217's "no inhabitant, no theorem to the conclusion, no axiom" rule.
3. **`registry/coverage-2601.22994.json` still does not exist**, though #217 scope item 4 calls for
   it. That is the cheapest next unit in the Li track and is independent of all geometry.
4. **Pin Dell before writing anything against §2 of this note.**
