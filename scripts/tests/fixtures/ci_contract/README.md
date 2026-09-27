# CI contract fixtures

`test_ci_contract.py` constructs schema-v6 fixture records from the checked-in
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
Version 6 retains the v4 and v5 compatibility checks and adds a PR-only dynamic
workflow binding for AI Scan. Its raw green outcome remains unverified until a
provider-defined analysis/result signal can be bound to the run and head.

`publication-receipt-pr1500.json` is a historical exact-revision example. It
binds PR #1500's reviewed tree to GitHub's merge commit and parents, retains
CI1.01 contract evidence, canonical artifact payloads and check-run IDs, and
records a separate post-merge CI run. The historical PR predates the
merge-readiness adapter, so that claim remains `not_evaluated`; required CI
passed while auxiliary health and the all-pipelines claim remained false.
`test_ci_github_evidence.py` checks its receipt digest and claim relationships
without network access. The provider recheck reads the protected inventory,
merge candidate artifact, commit, PR identity, workflow, check suites/runs,
statuses and post-merge run. The snapshot retains its collected bytes while
the verifier compares the fields that carry the CI claim. GitHub may clear a
merged run's `pull_requests` field; a conflicting nonempty association is
rejected. This fixture does not establish a provider-enforced publication
guard for #1431.
