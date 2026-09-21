# CI contract fixtures

`test_ci_contract.py` constructs schema-v2 fixture records from the checked-in
gate inventory so every test continues to exercise the current mapping. The
records bind the provider ref and revision tuple, require typed non-empty
artifacts for applicable gates, and keep skipped gates artifact-free. The cases
cover a complete candidate, missing tree identity, stale gate revision,
duplicate provider/name, pending required work, optional red auxiliary work,
unexpected skips, invalid push refs, broken revision bindings, missing
artifacts, and an unknown schema. The factory uses fixed SHAs and run
identities, so a fixture failure is reproducible without a GitHub API call.
