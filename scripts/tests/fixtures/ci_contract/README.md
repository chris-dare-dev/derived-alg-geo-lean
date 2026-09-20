# CI contract fixtures

`test_ci_contract.py` constructs the fixture records from the checked-in gate
inventory so every test continues to exercise the current mapping. The cases
cover a complete candidate, missing tree identity, stale gate revision,
duplicate provider/name, pending required work, optional red auxiliary work,
unexpected skips, and an unknown schema. The factory uses fixed SHAs and run
identities, so a fixture failure is reproducible without a GitHub API call.
