# CI1.03 reviewer authority and receipt contract

Status: proposed contract for CI1.05 integration. This document and
`scripts/review_authority.py` are not branch protection, a required check, or
an active controller admission rule.

## Current authority

The owner removed `trust-guard.yml` in #1449 after establishing that the
repository has one human collaborator and agents use that collaborator's GitHub
credential. GitHub forbids self-approval. Current protection requires the
up-to-date `ci` check and zero approving reviews. The owner decision supports
continuing with technical agent review and normal protected merging; it does
not establish independent human approval. A GitHub review, comment, label or
PR edit made through the shared credential is attributable to that credential,
not to an independent person or agent. An external provider's distinct account
can prove its account identity through the provider API, but its review's
substance and human independence still need separate evidence.

The current receipt policy is `ci1-single-collaborator-v1`: four distinct
technical roles (`mathematics-adversary`, `repository-boundary-adversary`,
`abstraction-adversary`, `mathlib-reviewer`) on one exact head/base/file set,
with no required GitHub approval. This policy is proposed for the integration
controller. Its owner approval and adoption must be recorded on #1432/#1434
before either issue is called operationally verified. It does not change the
repository's existing run-loop review rule.

## Receipt and trust boundary

The version 1 receipt contains the repository and PR number; exact current
head and protected base commits; policy ID and canonical SHA-256; canonical
changed-file digest; four technical review IDs; optional GitHub review IDs;
and an explicit false `independent_human_approval` claim. Each technical
review in the trusted live snapshot has a distinct role and runtime identity,
passing verdict, active status, exact head/base/policy/file digests and an
artifact SHA-256. A trusted runtime supplies a unique positive review sequence;
the validator selects the greatest sequence for each role and identity, so
reordering a fetched array cannot revive an earlier pass. The trusted runtime
supplies the retained full reviewer text. The validator checks its SHA-256 and
the exact head/verdict trailer against the record. This does not authenticate
who wrote the text. The runtime must authenticate its own agent/session identity
independently of PR-controlled text. `technical_reviews_recorded` means these
records are current and complete; it never means a human approved.

The validator accepts **trusted** policy and snapshot arguments. CI1.05 must
load policy from the current protected-base Git object, and build the snapshot
through read-only API calls and trusted runtime review records. Neither the
policy, snapshot source flag nor the completeness flags may be accepted from
the PR checkout, issue labels, PR body, fork artifact, or a comment. The
validator's hashes are consistency checks, not signatures. A caller that
forges `source=trusted-read-only-adapter` defeats the contract; integration
must keep that constructor outside untrusted PR code.

The adapter must fetch every page of PR files and provider reviews, preserve
rename source and destination and removals, and mark a collection complete
only after its final page and must retain the absence of a `next` link. GitHub's PR file API caps responses at 3,000 files;
a cap or unknown continuation is incomplete. The adapter must read the live
PR/base/head and current review states both before and after collection. Any
change, missing page, truncated result, deleted/renamed file mismatch,
revocation, later conflicting review, new commit, base movement, or policy
change denies a current receipt. A label alone yields no review IDs. A
conflict resolution that changes the head or file set needs a fresh review
receipt. A no-conflict base merge still changes the exact base/head binding and
requires the controller to re-establish the receipt under its reviewed-change
rule before admission.

The validator can observe a current GitHub `APPROVED` review by a distinct
provider actor on the exact head when a future owner-approved policy requires
one. It rejects an author or shared-credential actor, a dismissed/superseded
approval, and incomplete provider results. The adapter supplies the
provider-observed author actor ID and each review's `submitted_at`; the
validator selects the latest submitted review per actor by submission time and
review ID, regardless of array order. An unsubmitted `PENDING` review has no
`submitted_at` and is excluded from that ordering. Even this observation is labeled
`github_approval_observed`, not `independent_human_approval`. The current
policy requires zero such reviews. A new required GitHub review setting,
independent account, or trust-surface check is an owner decision, not an
implicit consequence of this contract.

## Execution and limits

For a fork, metadata collection must use GET/read-only calls in a trusted
context. Do not check out or run fork code with privileged credentials. The
pure validator executes no PR code or provider mutation. It accepts only the
`pull_request` event. A merge-group candidate has a different tree and review
binding; it receives no review-validity claim until a trusted candidate
verifier and owner policy exist. Required CI, review validity, provider merge
eligibility and post-merge health remain separate claims as in
`gate-evidence-contract.md`.

`python3 -m unittest scripts.tests.test_review_authority` exercises replay,
stale head/base, trust-file changes, rename/removal, incomplete pages,
revocation, shared credentials, label-only claims and merge-group denial.
These are local contract fixtures. The first safe PR demonstration is this
contract's own PR: record its four independent technical reviewer outputs at
the exact commit and current base, its published head, required CI result and
normal protected merge separately. CI1.05 must consume the protected-base
contract and demonstrate live invalidation before #1432 can claim operational
completion.

GitHub API fields and pagination semantics: [PR reviews](https://docs.github.com/en/rest/pulls/reviews),
[PR files](https://docs.github.com/en/rest/pulls/pulls#list-pull-requests-files),
[review events](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#pull_request_review).
