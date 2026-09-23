# Tasks

## 1. Reusable Copier template — issue #182

- [x] 1.1 Add the pinned Copier template, optional anchor/direct-Mathlib branch, complete managed answers, honest metadata skeleton, external-declaration guidance, and false trust record.
  - Files: MFC `copier.yml`, `template/**`, `contract/mfc/cli.py`, `contract/mfc/scaffold.py`, `contract/README.md`, and `README.md`.
  - Acceptance: generated template has zero Bridgeland-specific bytes, stores the full source commit, and can update a generated adopter.
  - Verification: `rg -ni Bridgeland copier.yml template` returns no matches; `uvx --from copier==9.11.3 copier update --defaults --vcs-ref c7e9a6ad8f69bdc3d4967df8dc64d156c63675b7` succeeds in the adopter.
- [ ] 1.2 Create the separate MathFormalContract plan and run record after the owner resolves whether to initialize its missing OpenSpec root.
  - Files: MFC `openspec/config.yaml`, `openspec/changes/contract-v1-topic-template-gate/**`, and any MFC-local run manifest selected by that plan.
  - Acceptance: MFC planning and frozen file scopes live in MFC and do not claim the Derived issue controller's authority.
  - Verification: MFC OpenSpec validation passes and every MFC manifest path resolves inside the MFC checkout.

## 2. Real second-topic corpus — issue #183

- [x] 2.1 Register the `analytic-nt` arXMCP notebook and pin `1202.3670v4` in its seed list; give the notebook an accurate display name, topic description, and non-placeholder query.
  - Files: arXMCP `var/arxmcp/cache/notebooks.db`, `var/arxmcp/notebooks/analytic-nt/papers.txt`, and `var/arxmcp/notebooks/analytic-nt/queries.json`.
  - Acceptance: the notebook advertises analytic number theory and its only query points to the pinned source paper.
  - Verification: inspect the notebook record, `papers.txt`, and `queries.json`; none contains the generated placeholder query or blank display name.
- [ ] 2.2 Fetch and ingest the paper after the operator supplies the contact email required by arXMCP.
  - Files: arXMCP `var/arxmcp/corpus/raw/1202.3670v4/**`, `var/arxmcp/corpus/parsed/1202.3670v4/**`, and `var/arxmcp/notebooks/analytic-nt/lancedb/**`.
  - Acceptance: the version-pinned paper has fetched source, parsed content, and nonempty notebook chunks.
  - Verification: run `python3 tools/notebook_fetch.py analytic-nt` and `python3 tools/notebook_ingest.py analytic-nt`; inspect the per-paper fetch, parse, and chunk records.
- [ ] 2.3 Create and validate exactly five sourced registry entries, including an Iwaniec–Kowalski textbook entry in `digest_only` mode and an environment-bound `Nat.infinite_setOf_prime` external declaration with `relation_claimed: exact`.
  - Files: adopter `registry/analytic-nt.yaml`, `AnalyticNt.lean`, `attest/environment.json`, `attest/external-decls.json`, and `attest/lean-emission.json`.
  - Acceptance: all five entries resolve to the inspected sources; the external theorem uses the measured environment digest and is emitted as `scope: external` without increasing topic-local declaration count.
  - Verification: `mfc registry validate registry/analytic-nt.yaml --frontier-kind-labels prime-counting distribution-of-primes sieve`; `mfc registry external-decls registry/analytic-nt.yaml --out attest/external-decls.json`; inspect the emitted external row and exact relation.

## 3. Anchor-free adopter and evidence gate

- [x] 3.1 Generate the anchor-free analytic-number-theory adopter, pin Mathlib directly, formalize the finite-list Euclid argument, and annotate the existing Mathlib infinitude theorem directly.
  - Files: adopter `lakefile.toml`, `lake-manifest.json`, `formalization.yaml`, `AnalyticNt/Basic.lean`, and `AnalyticNt.lean`.
  - Acceptance: the direct Mathlib pin matches the reviewed environment; the finite-list proof has no `sorry` or added axiom; no wrapper is introduced solely to carry the citation.
  - Verification: `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build AnalyticNt` succeeds.
- [ ] 3.2 Run the adopter contract workflow against the five-entry registry, inspect environment digest, emission, scope, relation, axiom, and coverage records, and update the dated template trust record only after every gate passes.
  - Files: adopter `attest/template-trust.yaml`, `attest/axiom-policy.json`, `.github/workflows/contract.yml`, and all generated `attest/*` records.
  - Acceptance: the trust value and dated evidence exactly reflect the completed gate; if any evidence is missing or fails, `generalization_validated` remains false.
  - Verification: run the named MFC environment, emitter, bundle, lint, registry-validation, and coverage commands and inspect their outputs.

## 4. Repository-local review and issue completion — issue #137

- [ ] 4.1 Prepare distinct review scopes for Derived issue tracking and MathFormalContract implementation, with mathematical/source-faithfulness, repository-boundary, abstraction/adoption, and mathlib-style reviews on each frozen commit.
  - Files: Derived `openspec/changes/contract-v1-topic-template-gate/**`; MFC `openspec/changes/contract-v1-topic-template-gate/**` and any MFC-local manifest.
  - Acceptance: each review roster sees one exact commit and a file list confined to its own repository; each attempt is capped at three rounds.
  - Verification: validate each local plan and inspect each manifest's file list and `max_review_rounds_per_chunk`.
- [ ] 4.2 Recheck the Derived child-issue manifest and read-only preflight after both repository plans and gate evidence are ready; keep epic #137 out of any new branch-authored manifest.
  - Files: Derived `.claude/loop-specs/<child-issue-run>.yaml` and `openspec/changes/contract-v1-topic-template-gate/**`.
  - Acceptance: #182 and #183 have separate repository-local implementation evidence; #137 is handled only after both child issues are resolved; no provider action runs without default-branch owner authority.
  - Verification: `python3 scripts/loop_engine.py validate --spec .claude/loop-specs/<child-issue-run>.yaml` and `python3 scripts/loop_engine.py preflight --spec .claude/loop-specs/<child-issue-run>.yaml` report the live issue/dependency state, exact base, branch/PR collisions, identity, required checks, and authority.
- [ ] 4.3 Publish and close issues #182 and #183 only after their accepted implementation evidence is merged; close epic #137 only after both child issues are complete.
  - Files: the separate repository PRs and the three live Derived issues.
  - Acceptance: each child issue has a merged change proving its stated acceptance; the epic closes last; the false trust record remains whenever gate evidence is incomplete.
  - Verification: verify each merge commit and each live issue state through GitHub, and confirm the trust record still matches the gate evidence.
