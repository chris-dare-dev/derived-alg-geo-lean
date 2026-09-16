# Mathlib conventions, as they apply to this repository

Source of truth for the review agents and hooks in this repo. Distilled from
the Mathlib style guide, naming guide, and documentation guide
(<https://leanprover-community.github.io/contribute/>) plus the linters that
actually enforce them in `.lake/packages/mathlib/Mathlib/Tactic/Linter/`.

Two rules of use:

1. **If a linter enforces it, do not review it by hand.** Section 1 lists what
   the toolchain already catches. A reviewer that spends its attention there is
   wasting it.
2. **Everything in sections 2–4 is unenforceable by machine.** That is exactly
   why it is written down: it is the whole job of a review agent.

## 1. Already machine-checked — do not hand-review

Run by `.github/workflows/ci.yml` and by `CLAUDE.md`'s pre-push list.

| Gate | Catches |
|---|---|
| `lake exe lint-style` (text-based) | trailing whitespace, windows line endings, space before `;`, non-allowlisted unicode and variant selectors, `Adaptation note` strings |
| `lake exe lint-style` (syntax) | `set_option` left unscoped, unscoped `maxHeartbeats`, unclosed `section`/`namespace`, `.` used as a focusing dot instead of `·`, `$` instead of `<|`, `λ` instead of `fun`, files > 1500 lines, breakable lines > 100 chars, unscoped `open Classical`, `show` where `change` is meant, double underscores in names, `def` names containing `_` |
| `lake exe runLinter <Lib>` | missing docstrings on public defs, unused arguments, `simp` lemmas that don't apply, non-terminal `simp`-normal-form problems, deprecated-decl use, `dupNamespace` |
| the three subsystem audits and `check_audit.py` | `sorryAx` and unexpected axioms reaching the audit surface |
| `scripts/check_source_independence.py` | retired or external source roots re-entering the library |
| `scripts/check_mathlib_style.py` (edit hook, `gates.sh`) | unresolved merge-conflict markers left in a file by a rebase — the structural gates all parse `import` lines only, so a conflicted file passed every one of them until #1359 |

`lake exe runLinter DerivedAlgGeo` covers the complete stable library. The
development probes remain covered by the emitter and style checks.

## 2. Naming — reviewable, and the highest-value thing to review

A Mathlib name is a **readable transcription of the statement**, not a label.
Given only the name, a reader should be able to guess the statement back.

- Conclusion first, hypotheses after, joined by `_of_`, hypotheses in statement
  order. `A → B → C` is `C_of_A_of_B`.
- Casing: `Prop`-valued theorems `snake_case`; types, structures, classes and
  `Prop`s `UpperCamelCase`; everything else `lowerCamelCase`. An
  `UpperCamelCase` component embedded inside a `snake_case` name lowercases its
  first letter: `MonoidHom.toOneHom_injective`.
- Symbol dictionary: `∧ and`, `∨ or`, `→ of`/`imp`, `↔ iff`, `¬ not`,
  `= eq` (often dropped), `≠ ne`, `≤ le`, `< lt` (`ge`/`gt` only when the
  arguments are swapped), `+ add`, `* mul`, unary `- neg`, binary `- sub`,
  `• smul`, `∈ mem`, `∪ union`, `∩ inter`, `ᶜ compl`, `⨆ iSup`.
- Property words: `refl symm trans antisymm asymm congr comm assoc left_comm
  right_comm`, `left_cancel`/`right_cancel`, `inj`/`injective`,
  `mono monotone strictMono antitone`, and `pos neg nonneg nonpos` in preference
  to `zero_lt`, `lt_zero`.
- Predicates go in front (`isClosed_Icc`), except the established suffixes
  `_injective`, `_monotone`, `_strictMono`, `_mono`.
- American spelling.
- A trailing `'` **must** be explained in the docstring — what differs from the
  unprimed form, or why no better scheme exists. Mathlib's `docPrime` linter
  enforces this upstream; nothing in this repo does, so the reviewer must.

Repo-specific naming pressure: the abstract/geometric split in `CLAUDE.md` is a
naming obligation too. A lemma about an abstract Mukai lattice must not be named
as though it were about a variety or a derived category.

## 3. Statement shape

- Arguments belong to the **left of the colon**, not inside `∀`/`→`.
  `(n : ℝ) (h : 1 < n) : 0 < n` beats `: ∀ n, 1 < n → 0 < n`.
- No conjunctions in hypotheses — split into separate binders. No conjunctions
  in conclusions — split into two lemmas.
- Avoid disjunctive hypotheses unless splitting would multiply near-identical
  lemmas.
- Every argument explicitly typed; return type written out.
- Prefer the normal form of a statement to an equivalent variant
  (`s.Nonempty`, not an unfolded witness). In assumptions use `hne : x ≠ ⊥`; in
  conclusions use `⊥ < x`.
- Use `@[to_additive]`/`@[to_dual]` rather than hand-writing the variant.
- Definitions stay `semireducible` unless there is a stated reason; reach for a
  `structure` type synonym before `irreducible`.

## 4. Documentation — insight, not restatement

This is the section that matters most for the paper-facing work, and the one no
linter will ever check.

**Module docstring** (`/-! ... -/`, delimiters on their own lines, immediately
after the imports), in this order:

1. `# Title`
2. Summary of what the file is for
3. `## Main definitions`
4. `## Main results` / `## Main statements`
5. `## Notation` — required whenever the file introduces notation
6. `## Implementation notes` — design decisions, typeclass choices, why the
   `simp` normal form is what it is
7. `## References` — textbook, paper, or `docs/references.bib` key
8. `## Tags` — search keywords

**Declaration docstrings.** Required on every definition and every major
theorem; encouraged on any lemma with mathematical content. Complete sentences
end in a period. Other declarations go in backticks, fully qualified, so the
doc build links them. LaTeX via `$...$` / `$$...$$`.

**What "useful" means here.** Mathlib's own guidance is that a docstring
conveys *mathematical meaning* and is "allowed to lie slightly about the actual
implementation" to do so. Concretely, a docstring earns its place when it
answers something the signature cannot:

- *Why this hypothesis?* — which step breaks without `[Fact (b - a ≤ 1)]`.
- *Why this formulation?* — what the obvious alternative statement was, and what
  went wrong with it.
- *Where does it sit?* — the named result in the literature this is, or the
  special case of it, with a reference.
- *What is the proof idea?* — one sentence of strategy ("transport the universal
  property across the comparison isomorphism, then reflect through the fully
  faithful embedding"), not a transcription of the tactic block.
- *What is the trap?* — the abstract-vs-geometric distinction, a definitional
  unfolding a caller will expect and not get, a `simp` direction.

A docstring that restates the signature in English adds nothing and should be
flagged as a review finding, not accepted as coverage.

## 5. Deltas this repo deliberately keeps

Do not "fix" these toward Mathlib:

- **Copyright header.** Mathlib's `Header` linter wants
  `Copyright ... / Released under Apache 2.0 ... / Authors: ...`. This repo's
  owner-authored trunk is MIT and omits `Authors:`. Vendored Apache-2.0 source
  under `vendor/BridgelandStability/` keeps its upstream header verbatim —
  never rewrite one as MIT (`LICENSES/README.md`).
- **File length.** Mathlib caps files at 1500 lines and splits aggressively;
  this repo's module ownership in `CLAUDE.md` takes priority over splitting.
- **`upstreamableDecl`.** Mathlib's "move it higher" linter assumes the Mathlib
  import graph. Here the equivalent question is whether the declaration belongs
  in `Foundation/` (Mathlib-only, anchor-free) rather than downstream — same
  instinct, different target.
