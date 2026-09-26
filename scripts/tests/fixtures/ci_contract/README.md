# CI contract fixtures

`test_ci_contract.py` constructs schema-v4 fixture records from the checked-in
gate inventory so every test continues to exercise the current mapping. The
records bind the provider ref and revision tuple, require a hash-bound provider
commit/tree proof with event-specific parent relationships, require typed
non-empty artifacts for applicable gates, and keep skipped gates artifact-free.
The cases
cover a complete candidate, missing tree identity, stale gate revision,
duplicate provider/name, pending required work, optional red auxiliary work,
unexpected skips, invalid push refs, broken revision bindings, missing
artifacts, an unknown schema, duplicate names across commit-status and check-run
producers, a modified inventory, a stale protected base, rerun mismatch,
cancelled and timed-out work, missing pins, neutral required conclusions,
independent auxiliary runs, missing optional checks, and scheduled Docs skips.
The factory uses fixed SHAs and run
identities, so a fixture failure is reproducible without a GitHub API call.

`publication-receipt-pr1500.json` is a live, exact-revision example. It binds
PR #1500's reviewed tree to GitHub's merge commit and both parents, retains the
CI1.01 contract evidence and check-run IDs, and records the separate
post-merge CI run. The historical PR predates the merge-readiness adapter, so that claim remains
`not_evaluated`; required CI passed while auxiliary health and the
all-pipelines claim remained false. `test_ci_github_evidence.py` validates its
receipt digest and claim relationships without network access. The fixture was
also passed to `verify_publication_provider_evidence` against the live GitHub
API, which re-read its protected inventory, merge candidate artifact, candidate
commit, PR identity, workflow run, check suites/runs, commit statuses and
post-merge run. GitHub clears the run's `pull_requests` field after merge; the
verifier can still establish this historical association from the exact merged
PR base/head and the run-bound candidate's ordered parents. A conflicting
nonempty live association is rejected.
