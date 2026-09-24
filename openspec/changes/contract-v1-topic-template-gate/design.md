# Design

## Context

Issues #137, #182, and #183 are the full scope. The Copier template and external-declaration support live in MathFormalContract; the source notebook lives in arXMCP; the generated adopter demonstrates both. The reduced gate is one paper, five registry entries, and one direct external Mathlib theorem binding. The user asked for the whole batch and for an issue-first procedure, which authorizes these scoped repository changes and the normal PR/merge/closure steps.

The analytic notebook already contains version `1202.3670v4`. ar5iv supplied and arXMCP ingested the parsed paper; arXiv's raw `/e-print/` endpoint returned HTTP 406 with the neutral application User-Agent. The gate needs a fetched and ingested paper, not raw TeX. The Iwaniec–Kowalski row is a digest-only locator for publisher Table-of-Contents metadata (chapter 2, p. 31), not a claim that the textbook theorem text was inspected.

## Goals

- Satisfy the live issue acceptance criteria with traceable evidence.
- Make a new issue list sufficient to start an autonomous, issue-scoped loop.
- Keep mathematical claims and source provenance honest.
- Use repository PRs and their actual required checks as the publication boundary.

## Decisions

1. **The issues are the work order.** Read the live issue bodies and repository guidance, then implement. This batch needs one compact OpenSpec record in DerivedAlgGeo for progress; it does not need a separate MFC OpenSpec root, per-repository manifests, or repeated owner authorization. `gate:owner` labels are resolved by the user's explicit request for these exact issues.

2. **Contact email is optional.** The fetcher sends a stable arXMCP application User-Agent and adds an email only when configured. It keeps arXiv request pacing. The prior email prerequisite was not required by the API terms and blocked the requested corpus ingestion without improving source integrity.

3. **The generated topic uses the template's exact recorded commit and direct Mathlib pin.** It has no upstream anchor and imports no DerivedAlgGeo modules. `Nat.infinite_setOf_prime` is referenced directly with an environment-bound external declaration; no wrapper theorem is added just to carry the citation.

4. **Five registry rows carry provenance.** Four use quote digests from ingested sections of arXiv v4. The fifth uses the publisher's contents metadata digest and identifies itself as a locator only. The registry's exact relation remains an author claim about the existing Mathlib declaration; record a focused source/type comparison in the gate evidence.

5. **Trust is recorded at both levels.** The template's own `template/trust.yaml` is now true with dated evidence from this gate. Every newly generated topic still starts with `generalization_validated: false`; only the demonstrated analytic adopter sets its record true after registry validation, Lean build, environment binding, emission, and contract checks pass.

6. **Looping stays issue-first and risk-proportionate.** No manifest or OpenSpec artifact is required before work starts. Cross-repository changes use the repository that owns each file and can be reviewed together from the issue acceptance. Run relevant builds and tests, review the resulting diff, and open the PR. Extra review panels or ledgers are used when the issue or risk warrants them, not as universal start gates. Continue independent issues if one has a real external blocker.

## Risks / Trade-offs

- **A digest-only textbook row can be mistaken for theorem evidence.** Its registry note and PR evidence say it is only publisher contents metadata; the analytic theorem binding is supported by the arXiv entry and the pinned Mathlib declaration.
- **ar5iv HTML and raw TeX are not identical artifacts.** The issue requires the paper to be fetched and ingested, which the parsed version-pinned HTML satisfies; the raw endpoint failure is recorded and does not block that acceptance.
- **The change spans repositories.** Each change is committed and reviewed where its code lives, with the shared issue numbers in PR descriptions. A planning artifact in every repository would duplicate the same scope without adding evidence.
- **Protected branch rules can still refuse a merge.** Respect required checks and human review that GitHub enforces; do not turn unrelated planning steps into new blockers.

## Migration Plan

1. Complete and test the Copier template and generated emitter.
2. Make arXiv fetch usable without an email, then fetch and ingest the pinned paper.
3. Validate the five-entry adopter registry; build it; emit and inspect the external declaration; record the environment and dated trust evidence.
4. Publish the MFC change, verify required checks, and close #182 and #183 after the implementation is merged. Close #137 last after its children are complete.

If any gate evidence fails, keep the adopter trust record false and fix the concrete failure. Do not restart planning or ask the user to approve an already authorized issue-scoped implementation.
