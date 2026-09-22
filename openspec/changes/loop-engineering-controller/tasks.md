# Tasks

## 1. OpenSpec and controller foundation

- [x] 1.1 Initialize the repository OpenSpec structure and configure the Lean/mathlib, trust-boundary, and bounded-review context; verify `openspec validate loop-engineering-controller --strict --no-interactive` passes
- [x] 1.2 Add `scripts/loop_engine.py` with manifest validation, portable OpenSpec artifact checks, and explicit `PASS`/`FAIL`/`DISABLED` output; verify the script's unit tests pass
- [x] 1.3 Add a tracked two-to-three-issue pilot manifest that references an OpenSpec change and a separate ignored runtime ledger directory; verify manifest validation rejects missing artifacts and more than five review rounds

## 2. Review and mutation safeguards

- [x] 2.1 Add the three adversarial reviewer roles and connect their names to the manifest review panel; verify duplicate or missing reviewer evidence is rejected
- [x] 2.2 Add guarded provider actions for comments, issue closure, pushes, pull-request creation, approval, and explicitly opt-in merge; verify dry-run and refusal paths without contacting the provider
- [x] 2.4 Make merge method, auto-merge, administrator merge, branch deletion, and reviewed-head binding explicit in the manifest/controller; verify override refusal and command construction
- [x] 2.5 Make live preflight command launching and GitHub response-shape normalization portable on Windows; verify the preflight reports provider state instead of aborting on a local launcher error
- [x] 2.6 Add explicitly authorized progress PRs that cannot close an issue, while retaining strict complete-PR closure semantics; verify manifest authorization and non-closing-link refusal tests
- [x] 2.7 Bind approval and merge to either a short or full reviewed Git revision without weakening exact-head checks; verify prefix acceptance and mismatch refusal
- [x] 2.8 Prevent passed progress ledgers or still-open upstream issues from unlocking dependent chunks; verify downstream initialization fails closed
- [x] 2.9 Bind a successor manifest to a controller-attested, merged predecessor PR and recheck that binding at preflight, ledger initialization, PR creation, approval, and merge; verify valid squash history and every missing, mismatched, retargeted, or non-ancestor refusal path
- [x] 2.3 Require OpenSpec and no-sorry/repository gates in the local precheck path; verify the gate agreement remains synchronized

## 3. Pilot readiness

- [x] 3.1 Document the OpenSpec-first loop and the handoff between proposal, apply, review ledger, CI, and archive; verify a fresh checkout can discover the workflow
- [ ] 3.2 Run the disabled pilot's read-only validation, inspect live preflight failures, and record the exact prerequisites for enabling it; verify no GitHub mutation occurs during the dry run
