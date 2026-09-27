# Independent review of the two #554 R&D handoffs

These are research-plan reviews, not a fourth source-review panel. The
reviewers made no source, PR or issue mutation. Both frozen implementation
attempts remain terminal; neither plan verdict authorizes a successor attempt
without its listed history and evidence prerequisites.

| Objective and submission | Exact research report SHA-256 | Independent reviewer | Verdict and reason |
| --- | --- | --- | --- |
| PR #1574, submission 1 | `dda6c5e0c936ad5283b94bd0ee13020dd2b2266d4b5c4c6cb2819678cf89c748` | SF8 abstraction adversary | NEEDS_CHANGES: removing `singleLeftTensorIso`'s premise was the terminal repair disguised as rearchitecture; main SHA was stale; raw reviews missing. |
| PR #1574, submission 2 | `8e766cf7c8ea9c64921bf67a4331f7338d6640b85deda170c6f5fdb2bc47f0ef` | SF8 abstraction adversary | READY for research handoff only: preserve historical invertible tensor API, prove generic colimits solely on canonical monoidal tensor, and use a scratch compile/linter probe. Full raw review inventory is still required before successor admission. |
| PR #1574, submission 3 | `ec264b00c2728dab155b327aebe94d630fdd73cb95fb964f48824cd9e2e8e3b9` | SF8 abstraction adversary | READY for research handoff only: correct the historical API description—`tensorLeftFunctor` exists for every sheaf, while its old preservation/additivity instances and finite-free comparison require invertibility. The changed canonical-tensor strategy, scratch probe and missing-review gate remain. |
| Controller preflight, submission 1 | `b5a4f560e7395025d1badc518f3a9242abc173512d987b225201135ad8cb0449` | SF8 style adversary | NEEDS_CHANGES: inventory must cover all three four-role rounds; the one-node live provider response cannot prove the CLI reports a complete connection. |
| Controller preflight, submission 2 | `2efeab0f85c093470f3944d896519252f95886498b0960387fc17e69b978f98f` | SF8 style adversary | READY for research handoff only: require complete review inventory and a provider completeness probe; use explicit paginated GraphQL if CLI completeness cannot be established. |

At review, PR #1574 was open and draft at
`7e19074188697d8c810905687ac5a9029759f06a`, behind `main`, with
required CI failed; #554 remained open. The local controller attempt had no
PR. These states must be refreshed before action. The style reviewer verified
the live #554 response as an open issue with `blockedBy` connection
`totalCount: 1` and a closed #1495 node. The abstraction reviewer attempted
a read-only scratch Lean probe in the cold report worktree; it failed on a
missing DerivedAlgGeo olean after ignored dependency downloads. That result
is neither positive nor negative proof evidence, and no tracked file changed.
On the exact #1574 PR base, the abstraction reviewer subsequently compiled
`rfl` for equality between the historical `tensorLeftFunctor L` and the
canonical `tensorLeft (C := X.Modules) L`. This is concrete root-agreement
evidence for the research design, not a compile of its restored-colimit
successor or a review of new source.

The #1574 report's missing-review statement records the inventory at its
last independently accepted digest. The twelve verbatim reviews were later
recovered from the named Codex transcript and copied into
[554-tensor-colimits-review-history.md](554-tensor-colimits-review-history.md).
An independent boundary audit matched all twelve role messages, line numbers,
hashes, findings and verdicts byte-for-byte to the transcript and found no
omitted negative finding or lift in the relevant windows. This resolves the
raw-review inventory gap without rewriting the digest-bound research report.
The separate [scratch probe](554-tensor-colimits-probe.md) subsequently built
the canonical colimit theorem and `LeftDerivedTensor` with the historical API
restored, then passed targeted `runLinter` for that derived module. The
repository-wide linter and required CI remain untested for the alternative.
No successor admission has been recorded, and neither the probe nor the plan
review changes #1574's terminal attempt.
