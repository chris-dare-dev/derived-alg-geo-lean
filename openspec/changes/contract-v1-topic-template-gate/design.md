# Design

## Context

See `proposal.md` for the milestone motivation and `specs/topic-template-gate/spec.md` for acceptance behavior. The template and analytic adopter live in MathFormalContract, the source notebook and corpus live in arXMCP, and this repository tracks milestone 13. The generated adopter currently pins MathFormalContract at `c7e9a6ad8f69bdc3d4967df8dc64d156c63675b7` and Mathlib at `520045ab14e26149ee970e2e617ca04b09bde5d6`.

The Derived loop controller validates issue runs against one repository remote and one frozen file set. It cannot review or authorize edits in the MathFormalContract and arXMCP repositories from a Derived manifest. The current Derived default branch also has no `.claude/loop-authority.yaml`; issues #137 and #183 are explicitly owner-gated. No provider mutation is part of this change until the owner enables it.

Issue #137 is also labeled `epic`. The controller permits epic opt-in only for legacy manifests; a new branch-authored manifest cannot select #137. The child implementation issues must be completed in their own repository scopes first, with #137 handled as a separate owner-controlled closeout after both children are resolved.

## Goals / Non-Goals

**Goals:**

- Keep each repository's plan, code, and review scope local to that repository.
- Make the template's optional-anchor/direct-Mathlib branch explicit and reproducible from a complete Copier answer record.
- Demonstrate the direct external theorem binding on the pinned Mathlib theorem `Nat.infinite_setOf_prime`, without creating a wrapper theorem merely to hold a citation.
- Keep a failed or incomplete second-topic demonstration visible through a false template trust record.

**Non-Goals:**

- No changes to public `DerivedAlgGeo` Lean APIs, namespaces, ownership, umbrellas, or audits.
- No claim that the Euclid formalization demonstrates analytic number theory broadly; it is only a direct external binding and a small topic-local proof.
- No automatic merge, approval, issue closure, or publication.

## Decisions

1. **MathFormalContract owns the reusable template and external-declaration tooling.** The generated topic depends on the exact MathFormalContract commit and either an exact anchor pin or a direct exact Mathlib pin. The MFC package remains a dependency leaf; it does not add Mathlib or other transitive Lake dependencies.

2. **The analytic adopter uses Mathlib's existing theorem directly.** `Nat.infinite_setOf_prime` is defined in `Mathlib/Data/Nat/PrimeFin.lean` at the adopter's pinned Mathlib revision. The root module attaches the citation to this imported declaration, while the local finite-list proof remains in the topic namespace. There is no second carrier or wrapper, no DerivedAlgGeo import, and no stability or geometry dependency.

3. **The registry binds external declarations to an environment digest.** After the topic environment is measured, the registry records the exact digest with the fully qualified Mathlib name. MFC's external-emission path marks the theorem as `scope: external`; it does not inflate the topic's local declaration count. `relation_claimed: exact` remains an author claim until human mathematical review.

4. **The real source corpus is an explicit gate input.** The arXiv source is pinned to `1202.3670v4`; entries are not reported as corpus-resolved until arXMCP fetch and ingest produce matching evidence. The textbook entry records Iwaniec and Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004), as a `textbook` source with no version and `digest_only` quote mode. Any excerpt locator must be grounded in the copy actually inspected; this plan does not invent one.

5. **Repository-local plans do not imply shared mutation authority.** The Derived plan covers issue tracking and Derived-owned files. MathFormalContract needs its own approved repository-local plan before the MFC branch can be treated as a controlled loop run. arXMCP notebook state is a local data input, not a code change or an MFC review scope. One manifest must not name files outside its checkout.

6. **Review stays bounded and independent.** Each frozen chunk gets mathematical/source-faithfulness, repository-boundary, abstraction/adoption, and mathlib-style review on the same commit. A new attempt has at most three review/improve rounds. Bounded automatic recovery is disabled; after three unsuccessful rounds, preserve findings, prepare a separate research and plan-review proposal, inherit unresolved findings, and park the chunk until that plan is accepted.

## Risks / Trade-offs

- **The local arXMCP notebook can exist without a corpus** → keep `generalization_validated: false` and keep registry resolution explicitly pending until fetch and ingest complete.
- **A visible exact-relation annotation can overstate the paper-to-Mathlib match** → require source-faithfulness review of the pinned paper statement and exact Mathlib type before counting the external row as gate evidence.
- **The template code and tracked issues are in different repositories** → use distinct plans and review records; let the owner decide publication and issue-closure sequencing.
- **A topic can build while the evidence gate is incomplete** → report the Lean build separately from registry, corpus, and trust-gate completion.

## Migration Plan

1. Complete the separate MathFormalContract plan and implementation review; keep the template trust record false.
2. Fetch and ingest the version-pinned paper in the registered arXMCP notebook, then create and validate the five-entry registry, including the Iwaniec–Kowalski textbook entry and exact external Mathlib binding.
3. Run the named adopter build and contract workflow, inspect emitted scope and relation rows, and record dated gate evidence only if every required input passes.
4. Obtain owner review and authority for provider actions. Publish each repository's work independently, then close the Derived child issues and epic only after their accepted completion evidence is present.

Rollback consists of leaving or restoring the template trust record to `generalization_validated: false`; no source pin or generated adopter needs to be erased to do that.

## Open Questions

- The arXMCP fetcher requires the operator's contact email before it will request the paper. The notebook and pinned paper row are already scaffolded; fetch and ingest wait for the operator's answer.
- The MathFormalContract repository has no OpenSpec root. A separate MFC plan requires explicit direction to initialize OpenSpec there; the current MFC branch remains local until that plan and owner authority are resolved.
