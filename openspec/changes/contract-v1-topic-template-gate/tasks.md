# Tasks

## 1. Reusable Copier template — issue #182

- [x] 1.1 Add the pinned Copier template, optional anchor/direct-Mathlib branch, complete managed answers, honest metadata skeleton, external-declaration guidance, and false trust record in MathFormalContract; verify `rg -ni Bridgeland copier.yml template` returns no matches and `uvx --from copier==9.11.3 copier update --defaults --vcs-ref c7e9a6ad8f69bdc3d4967df8dc64d156c63675b7` succeeds in a generated topic.
- [ ] 1.2 Create the separate MathFormalContract plan and run record once the owner resolves whether to initialize its missing OpenSpec root; verify the MFC plan names only MFC files and does not claim the Derived issue controller's authority.

## 2. Real second-topic corpus — issue #183

- [x] 2.1 Register the `analytic-nt` arXMCP notebook and pin `1202.3670v4` in its seed list; verify `var/arxmcp/notebooks/analytic-nt/papers.txt` contains that versioned identifier.
- [ ] 2.2 Fetch and ingest the paper into that notebook after the operator supplies the contact email required by arXMCP; verify the fetch and ingest commands complete and the notebook has nonempty paper chunks.
- [ ] 2.3 Create and validate exactly five sourced registry entries, including an Iwaniec–Kowalski `textbook` entry in `digest_only` mode and an environment-bound `Nat.infinite_setOf_prime` external declaration with `relation_claimed: exact`; verify `mfc registry validate`, `mfc registry external-decls`, and the emitted external row.

## 3. Anchor-free adopter and evidence gate

- [x] 3.1 Generate the anchor-free analytic-number-theory adopter, pin Mathlib directly, formalize the finite-list Euclid argument, and annotate the existing Mathlib infinitude theorem directly; verify `LEAN_NUM_THREADS=2 ~/.elan/bin/lake build AnalyticNt` succeeds.
- [ ] 3.2 Run the adopter contract workflow against the five-entry registry, inspect environment digest, emission, scope, relation, axiom, and coverage records, and update the dated template trust record only after every gate passes; verify the named MFC lint, registry, and coverage commands pass and `generalization_validated` matches the evidence.

## 4. Repository-local review and issue completion — issue #137

- [ ] 4.1 Prepare distinct review scopes for Derived issue tracking and MathFormalContract implementation, with mathematical/source-faithfulness, repository-boundary, abstraction/adoption, and mathlib-style reviews on each frozen commit; verify each repository plan and file list stay within that repository and each attempt stops after three rounds.
- [ ] 4.2 Recheck the Derived manifest and read-only preflight after both repository plans and gate evidence are ready; verify strict OpenSpec validation, live issue/dependency state, exact base, branch/PR collision state, provider identity, and owner-granted actions.
- [ ] 4.3 Publish and close issues #182 and #183 only after their accepted implementation evidence is merged; close epic #137 only after both child issues are complete; verify each issue's live state and retain the false trust record whenever the evidence gate has not passed.
