# The statement registry

`bridgeland2007.json` is the only contract artifact in this repo, and the only
place a citation key is minted. Everything else is measured. The hand-authored
coverage maps below mint nothing.

Validate it with the contract package:

```sh
mfc registry validate registry/bridgeland2007.json \
  --frontier-kind-labels mathlib-gap unproved-here definitional-divergence source-review-pending
```

## The 1902.08184v4 coverage map — not a mint surface

`coverage-1902.08184v4.json` (issue #87) pins arXiv:1902.08184**v4**
("Stability conditions in families", Bayer–Lahoz–Macrì–Nuer–Perry–Stellari,
v4 of 2022-01-25, DOI 10.1007/s10240-021-00124-6) and maps its Parts I–VI and
the near-term section coordinates (§14, §§18/21, §§20–23) onto statuses.
At the 2026-08-11 issue-#82 mapping there are two `mapped` candidate
coordinates (§14 and §§18/21) and eight `target` coordinates. `mapped` names
candidate declarations and source coordinates; it is not a source-faithfulness
verdict. The only status that ever counts as coverage is `formalized`, which
requires review evidence plus explicit owner acceptance, and nothing has it. The map does not touch
`formalization.yaml`'s `source` (still the Bridgeland 2007 record), mints no
key, and contains no corpus-derived identifier — the local arXMCP notebook
holds 548 chunks of this paper but records no arXiv version (#44), so quotes,
when they are eventually added, are checked directly against the pinned v4
artifact, never against the corpus. Validate with:

```sh
python scripts/check_coverage_map.py
```

It fails on any status outside the vocabulary, any promotion without complete
evidence, and any `chunk_id`/notebook-slug key. Status promotion is owned by
the owner; agents propose it only by PR carrying the evidence fields.

## The 2607.28411v1 coverage map — zero-claim skeleton

`coverage-2607.28411.json` pins arXiv:2607.28411**v1** (Li–Liu–Liu–Macrì–
Perry–Stellari–Zhao) for issue #211 (transferred from source issue #141).
Section 3.4 has a `mapped` candidate binding with its required evidence; all
other coordinates remain `target`. Neither status is theorem coverage. The
dependency and issue workflow lives in
`.claude/roadmap/projective-families.yaml`; the coverage map remains the
version-pinned source ledger and is never inferred from roadmap progress.
Validate it
with:

```sh
python scripts/check_coverage_map.py registry/coverage-2607.28411.json
```

## The 1607.01262v3 coverage map — the exposition, named at last

`coverage-1607.01262.json` pins arXiv:1607.01262**v3** ("Lectures on Bridgeland
Stability", Macrì–Schmidt, v3 of 2019-10-30). Every part and every near-term
coordinate is `target`, and none has ever held another status.

It exists because the manuscript was cited **nowhere in the tree** while
`Walls/Numerical/Basic.lean` proved the conic normal form for tilt walls in the
`(s, t)` half plane — the subject of its §6.4, in `(α, β)` coordinates — and
`Walls/Numerical/Discriminant.lean` then removed that theorem's excluded point.
An untracked resemblance is the thing this directory exists to prevent, so the
coordinate is now named. Naming it asserts **no** correspondence between any
declaration and any statement of the source; that is status `mapped`, it needs
the evidence fields the validator demands, and no such review has happened.

Two cautions are recorded in the map itself and are worth repeating:

- **A lecture note is a weak artifact to map a formalization against.** Where it
  restates a theorem, the primary paper is what a future binding must be checked
  against — Arcara–Bertram and Bridgeland `math/0307164` §6 for the surface
  construction, Bayer–Macrì–Toda for the threefold material, Maciocia for the
  nested-wall ordering. This is the same caution `coverage-2407.05946.json`
  carries, for the same reason.
- **The journal reference is not interchangeable with the pin.** The Springer
  *Moduli of Curves* volume (2017) corresponds to v2; v3 postdates it by two
  years.

Section titles were read with `pdftotext -layout` from the pinned v3 PDF, not
from ar5iv or arXiv HTML — §6.3's full title is "Sketch of the proof of Theorem
6.10 and Theorem 6.13", and an HTML extraction that truncates it to "Sketch of
the proof" is wrong. Validate with:

```sh
python scripts/check_coverage_map.py registry/coverage-1607.01262.json
```

## The five dg-enhancement coverage maps — zero-claim skeletons

`.claude/roadmap/dg-enhancements.yaml` reads five Canonaco–Stellari-school
papers, and issue #328 pins each of them before any issue body cites a section
by memory. Every part and every near-term coordinate in all five is `target`;
none of them has ever held another status.

| file | pinned | what it is to this repository |
|---|---|---|
| `coverage-1312.5619.json` | v3, Adv. Math. 277 (2015) | Internal Homs in Hqe. The furthest out of reach — pinned so the parked epic's un-park trigger points at something concrete. |
| `coverage-1507.05509.json` | v5, JEMS 20 (2018) | Uniqueness for the derived category of a Grothendieck category. §2.1 is the track's most-read page: it is where the vocabulary DG1 needs is collected. |
| `coverage-2101.04404.json` | v1 | Uniqueness of enhancements, Theorems A and B. The paper DG2 and DG5 are written against. |
| `coverage-2402.04605.json` | v1 | Subcategories of weakly approximable triangulated categories. Vocabulary only; nothing here enters the library. |
| `coverage-2407.05946.json` | v2, Boll. UMI | The survey. A reading entry point, and the weakest possible thing to map a formalization against. |

Validate them the same way, one path per run:

```sh
for f in registry/coverage-{1312.5619,1507.05509,2101.04404,2402.04605,2407.05946}.json; do
  python scripts/check_coverage_map.py "$f"
done
```

Three things about these five that are not true of the two maps above:

- **The front/body split is editorial.** None of these papers declares Parts, so
  the schema's per-part status is hung on a two-element grouping this repository
  invented. Each map says so in its own `parts[0].note`. Do not read `part: "body"`
  as a claim about the source's structure.
- **Section titles were read from the pinned PDF**, with `pdftotext -layout`, not
  from ar5iv or arXiv HTML. Where a title contains typography JSON cannot carry
  safely (`T^b`, `D^?qc(X)`), it is transliterated and the PDF stays authoritative.
- **`coverage-2402.04605.json` records two author lists.** arXiv metadata names
  four authors; the PDF title page names three "with an appendix by Christian
  Haesemeyer". The arXiv list is the identity pin, the title page is the
  attribution, and `source.author_note` says which is which.

`kind_label` is a free per-topic string and `mfc lint` checks it against exactly
the list you pass here, so **a new label must be added to this command in the
same commit that introduces it**. Four are in use:

| label | means |
|---|---|
| `mathlib-gap` | the pinned Mathlib has no API to instantiate, so the claim is recorded as a conjunction of named theorems |
| `unproved-here` | the statement exists in the literature but no theorem inhabits it in this environment |
| `definitional-divergence` | what is formalized is a different object from the paper's, and the difference is not a presentation choice |
| `source-review-pending` | the mathematical premise is proved, but exact-head human source review and owner acceptance are still required to discharge the frontier item |

## Rules that are easy to break by typing

- **The registry id is minted once and never changes.** `a520a8d4f877`, from
  `mfc registry init`. It is the middle segment of every key and it is not
  derived from the notebook slug — slugs live in a machine-local sqlite database
  with no global registry, so two adopters both choosing the same one would
  collide silently.
- **A key contains zero corpus-derived bytes.** No `chunk_id`, no
  `corpus_version`, no notebook slug. `chunk_id` rotates on any re-parse, there
  is no alias table, and `merge_insert` has no delete arm — so an id we minted
  from corpus bytes is an id we break. `R-06` refuses a key shaped like one.
- **Edit a `quote` and you must recompute its `quote_sha256`.** `R-02` is the
  only rule that compares a digest to the text it summarizes rather than to
  another digest, and it will catch this.
- **`relation_claimed: exact` is not available while an entry has an open
  frontier item.** That is `E-05`. **Two** are open today:
  `autpairquot-not-aut-d` on `lem-8.2`, and `stability-mass-triangle` on
  `prop-8.1` and its obligation. Both `lem-8.2` and `prop-8.1` therefore remain
  non-`exact`.

  `gltilde-universal-cover` was discharged on 2026-08-07 by Chris Dare, on
  `GLTilde.universalCoverData` together with `exact_deckHom_toMatHom`. Note what
  that did **not** do: `lem-8.2` carried two items, so closing one moved it no
  closer to `exact`. A discharge is progress toward citability only when it was
  the last item on the entry.
- **A frontier item is a live gate, so a stale one silently opens the gate.**
  This is not hypothetical. `gltilde-universal-cover` asserted from 2026-08-05
  to 2026-08-06 that the covering-map, surjectivity and simple-connectedness
  facts were *"absent from Mathlib at the pinned revision and unproved here"* —
  of a tree that proved all three. It was minted before `GLTildeCover.lean`
  landed and never revisited. Had it been discharged as written, `E-05` would
  have permitted `exact` on Lemma 8.2 while the two gaps that actually block it
  had no item at all. **When you discharge an item, check that the reason it was
  open is still the reason you are closing it**, and check what *else* should be
  open before you do.
- **Discharging needs a named human.** `discharged_by` requires
  `discharged_by_reviewer`, and per
  [`ADR-0005`](../.claude/decisions/ADR-0005-trust-axes.md) an agent may not
  fill it. A machine review may correct a false `statement`; it may not close
  the item. This is why `gltilde-universal-cover` sat corrected-but-open from
  2026-08-06 to 2026-08-07: the review that found it false was not entitled to
  close it.
- **Discharging a frontier item is not a source-faithfulness review.** They are
  different axes and neither implies the other. `fidelity.human_review` is
  `none` and stays `none` until a human performs and records the four-axis
  review; the 2026-08-07 discharge did not touch it.

## Why JSON and not YAML

GitHub #34 specifies `bridgeland2007.yaml`. It is JSON, deliberately:

- The quotes are verbatim LaTeX — `$\operatorname{\mathcal{D}}$`, `\phi^{-}`,
  `{\tilde{\operatorname{GL^{+}}}}`. YAML has several ways to quote a string
  containing backslashes and they do not all round-trip to the same bytes. A
  re-serialization that changed one byte would break `quote_sha256` and the
  failure would look like corpus drift rather than like a formatting change.
- `mfc validate` reads YAML only when PyYAML is installed, and reports its
  absence as a missing capability. JSON has no such edge.

`load_artifact` accepts both, so this is reversible if the ergonomics ever
matter more than the byte-stability.

## Provenance of the current entries

Seven statements lifted verbatim from the `bridgeland-stability` arXMCP corpus
and two obligations that have no printed statement. Each quote was verified three
ways at mint time: the registry text is byte-identical to the corpus body, the
declared `quote_sha256` recomputes from it, and the corpus `chunk_id` itself
still recomputes as `sha256(NFC(body_text))[:16]` (every chunk of this paper has
`preamble_ref = NULL`, so the id reduces to that).

The second obligation, `obl-stability-mass-triangle`, was drafted by a machine
review on 2026-08-06 and **accepted by the owner on 2026-08-07**, at which point
`minted_by` was corrected from the draft marker to the owner. Two distinct
things must not be conflated here: the acceptance is of the **mint** — that the
obligation is well-posed and belongs in the registry — and is **not** a
discharge of the proof. The mathematics is now closed by
`stabilityMassSemistableLeftTriangleInequality`,
`stabilityMassTriangleInequality`, and
`stabilityDistanceTopologyCompatible`. The frontier item nevertheless remains
open (`discharged_by: null`) with label `source-review-pending`, because an
agent may not supply the named exact-head human review or owner acceptance.
Proposition 8.1 stays non-`exact` under E-05 until that governance step. No
`quote` was minted for the obligation, so the three-way verification above
does not apply and nothing corpus-derived entered the key. The `informal` field of `lem-3.4` was corrected in the same pass:
it had described Bridgeland's Lemma 4.3 (`P(I)` quasi-abelian) rather than the
extreme-phase monotonicity its own stored quote states.

**`mint_resolution` is `null` on every entry, with a reason.** No resolver has
been run — `tools/statement_resolve.py` (#43) does not exist. And the corpus
records `arxiv_version = ''` for every row (#44), so even a hash match would be
a match against a probable-but-unconfirmed v3. The version the formalization
targeted is confirmed v3 by the owner; the version that was *ingested* is not
confirmed by anything. Those are two facts and only one is known.
